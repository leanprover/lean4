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
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_empty(lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__32(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Function"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__0_value;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "const"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__1 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__1_value;
static const lean_ctor_object l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 8, 186, 189, 152, 89, 197, 12)}};
static const lean_ctor_object l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__1_value),LEAN_SCALAR_PTR_LITERAL(231, 33, 22, 82, 100, 121, 126, 178)}};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__2 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__2_value;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__3 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__3_value;
static const lean_ctor_object l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__3_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__4 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__4_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__5;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__37(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__3_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "failed to transform matcher, type error when constructing new motive:"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__0_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__1;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "failed to transform matcher, type error when constructing new pre-splitter motive:"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__2 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__2_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__3;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "\nfailed with"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__4 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__4_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_9_ = lean_apply_7(v_k_1_, v_b_2_, v_c_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed(lean_object* v_k_10_, lean_object* v_b_11_, lean_object* v_c_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0(v_k_10_, v_b_11_, v_c_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
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
lean_dec_ref(v___x_98_);
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
lean_dec_ref(v___x_164_);
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
lean_dec_ref(v___x_194_);
lean_inc(v___y_160_);
lean_inc_ref(v___y_159_);
lean_inc(v___y_158_);
lean_inc_ref(v___y_157_);
v___x_196_ = l_Lean_Meta_isExprDefEq(v_unrefinedArgType_154_, v_a_195_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; uint8_t v___x_198_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_a_197_);
lean_dec_ref(v___x_196_);
v___x_198_ = lean_unbox(v_a_197_);
lean_dec(v_a_197_);
if (v___x_198_ == 0)
{
v_refined_167_ = v___x_151_;
v___y_168_ = v___y_157_;
v___y_169_ = v___y_158_;
v___y_170_ = v___y_159_;
v___y_171_ = v___y_160_;
goto v___jp_166_;
}
else
{
v_refined_167_ = v_refined_153_;
v___y_168_ = v___y_157_;
v___y_169_ = v___y_158_;
v___y_170_ = v___y_159_;
v___y_171_ = v___y_160_;
goto v___jp_166_;
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
lean_dec(v_a_165_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
v_a_199_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_196_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_196_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
else
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
lean_dec(v_a_165_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
lean_dec_ref(v_unrefinedArgType_154_);
v_a_207_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v___x_194_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_194_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
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
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
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
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
lean_dec_ref(v_unrefinedArgType_154_);
v_a_215_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_222_ == 0)
{
v___x_217_ = v___x_164_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_164_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
if (v_isShared_218_ == 0)
{
v___x_220_ = v___x_217_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_a_215_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0___boxed(lean_object* v_alt_223_, lean_object* v___x_224_, lean_object* v_xs_225_, lean_object* v_refined_226_, lean_object* v_unrefinedArgType_227_, lean_object* v_x_228_, lean_object* v_x_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
uint8_t v___x_4895__boxed_235_; uint8_t v_refined_boxed_236_; lean_object* v_res_237_; 
v___x_4895__boxed_235_ = lean_unbox(v___x_224_);
v_refined_boxed_236_ = lean_unbox(v_refined_226_);
v_res_237_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(v_alt_223_, v___x_4895__boxed_235_, v_xs_225_, v_refined_boxed_236_, v_unrefinedArgType_227_, v_x_228_, v_x_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
lean_dec_ref(v_x_229_);
lean_dec_ref(v_x_228_);
lean_dec_ref(v_xs_225_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(lean_object* v_msgData_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v___x_244_; lean_object* v_env_245_; lean_object* v___x_246_; lean_object* v_mctx_247_; lean_object* v_lctx_248_; lean_object* v_options_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_244_ = lean_st_ref_get(v___y_242_);
v_env_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc_ref(v_env_245_);
lean_dec(v___x_244_);
v___x_246_ = lean_st_ref_get(v___y_240_);
v_mctx_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc_ref(v_mctx_247_);
lean_dec(v___x_246_);
v_lctx_248_ = lean_ctor_get(v___y_239_, 2);
v_options_249_ = lean_ctor_get(v___y_241_, 2);
lean_inc_ref(v_options_249_);
lean_inc_ref(v_lctx_248_);
v___x_250_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_250_, 0, v_env_245_);
lean_ctor_set(v___x_250_, 1, v_mctx_247_);
lean_ctor_set(v___x_250_, 2, v_lctx_248_);
lean_ctor_set(v___x_250_, 3, v_options_249_);
v___x_251_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v_msgData_238_);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0___boxed(lean_object* v_msgData_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(v_msgData_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(lean_object* v_msg_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_ref_266_; lean_object* v___x_267_; lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_276_; 
v_ref_266_ = lean_ctor_get(v___y_263_, 5);
v___x_267_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(v_msg_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
v_a_268_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_276_ == 0)
{
v___x_270_ = v___x_267_;
v_isShared_271_ = v_isSharedCheck_276_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_267_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_276_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_274_; 
lean_inc(v_ref_266_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v_ref_266_);
lean_ctor_set(v___x_272_, 1, v_a_268_);
if (v_isShared_271_ == 0)
{
lean_ctor_set_tag(v___x_270_, 1);
lean_ctor_set(v___x_270_, 0, v___x_272_);
v___x_274_ = v___x_270_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg___boxed(lean_object* v_msg_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v_msg_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
return v_res_283_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1));
v___x_288_ = l_Lean_stringToMessageData(v___x_287_);
return v___x_288_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__4(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3));
v___x_291_ = l_Lean_stringToMessageData(v___x_290_);
return v___x_291_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__6(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5));
v___x_294_ = l_Lean_stringToMessageData(v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(uint8_t v___x_295_, uint8_t v_refined_296_, lean_object* v_unrefinedArgType_297_, lean_object* v_binderType_298_, lean_object* v_numParams_299_, lean_object* v_xs_300_, lean_object* v_alt_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___f_309_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_329_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; uint8_t v___y_334_; lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_307_ = lean_box(v___x_295_);
v___x_308_ = lean_box(v_refined_296_);
lean_inc_ref(v_xs_300_);
v___f_309_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0___boxed), 12, 5);
lean_closure_set(v___f_309_, 0, v_alt_301_);
lean_closure_set(v___f_309_, 1, v___x_307_);
lean_closure_set(v___f_309_, 2, v_xs_300_);
lean_closure_set(v___f_309_, 3, v___x_308_);
lean_closure_set(v___f_309_, 4, v_unrefinedArgType_297_);
v___x_342_ = lean_array_get_size(v_xs_300_);
v___x_343_ = lean_nat_dec_eq(v___x_342_, v_numParams_299_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_344_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__4, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__4_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__4);
v___x_345_ = l_Nat_reprFast(v_numParams_299_);
v___x_346_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
v___x_347_ = l_Lean_MessageData_ofFormat(v___x_346_);
v___x_348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_344_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
v___x_349_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__6, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__6_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__6);
v___x_350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_348_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
v___x_351_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_350_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_dec_ref(v___x_351_);
goto v___jp_337_;
}
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
lean_dec_ref(v___f_309_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec_ref(v_xs_300_);
lean_dec_ref(v_binderType_298_);
v_a_352_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_351_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_351_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
else
{
lean_dec(v_numParams_299_);
goto v___jp_337_;
}
v___jp_310_:
{
if (lean_obj_tag(v___y_315_) == 0)
{
lean_object* v_a_316_; lean_object* v___x_317_; uint8_t v___x_318_; lean_object* v___x_319_; 
v_a_316_ = lean_ctor_get(v___y_315_, 0);
lean_inc(v_a_316_);
lean_dec_ref(v___y_315_);
v___x_317_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__0));
v___x_318_ = 0;
v___x_319_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_a_316_, v___x_317_, v___f_309_, v___x_318_, v___x_318_, v___y_312_, v___y_314_, v___y_311_, v___y_313_);
return v___x_319_;
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
lean_dec(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec_ref(v___f_309_);
v_a_320_ = lean_ctor_get(v___y_315_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___y_315_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___y_315_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___y_315_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
v___jp_328_:
{
if (v___y_334_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; 
lean_dec_ref(v___y_330_);
v___x_335_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2);
v___x_336_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_335_, v___y_331_, v___y_333_, v___y_329_, v___y_332_);
v___y_311_ = v___y_329_;
v___y_312_ = v___y_331_;
v___y_313_ = v___y_332_;
v___y_314_ = v___y_333_;
v___y_315_ = v___x_336_;
goto v___jp_310_;
}
else
{
v___y_311_ = v___y_329_;
v___y_312_ = v___y_331_;
v___y_313_ = v___y_332_;
v___y_314_ = v___y_333_;
v___y_315_ = v___y_330_;
goto v___jp_310_;
}
}
v___jp_337_:
{
lean_object* v___x_338_; 
lean_inc(v___y_305_);
lean_inc_ref(v___y_304_);
lean_inc(v___y_303_);
lean_inc_ref(v___y_302_);
v___x_338_ = l_Lean_Meta_instantiateForall(v_binderType_298_, v_xs_300_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
lean_dec_ref(v_xs_300_);
if (lean_obj_tag(v___x_338_) == 0)
{
v___y_311_ = v___y_304_;
v___y_312_ = v___y_302_;
v___y_313_ = v___y_305_;
v___y_314_ = v___y_303_;
v___y_315_ = v___x_338_;
goto v___jp_310_;
}
else
{
lean_object* v_a_339_; uint8_t v___x_340_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_a_339_);
v___x_340_ = l_Lean_Exception_isInterrupt(v_a_339_);
if (v___x_340_ == 0)
{
uint8_t v___x_341_; 
v___x_341_ = l_Lean_Exception_isRuntime(v_a_339_);
v___y_329_ = v___y_304_;
v___y_330_ = v___x_338_;
v___y_331_ = v___y_302_;
v___y_332_ = v___y_305_;
v___y_333_ = v___y_303_;
v___y_334_ = v___x_341_;
goto v___jp_328_;
}
else
{
lean_dec(v_a_339_);
v___y_329_ = v___y_304_;
v___y_330_ = v___x_338_;
v___y_331_ = v___y_302_;
v___y_332_ = v___y_305_;
v___y_333_ = v___y_303_;
v___y_334_ = v___x_340_;
goto v___jp_328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed(lean_object* v___x_360_, lean_object* v_refined_361_, lean_object* v_unrefinedArgType_362_, lean_object* v_binderType_363_, lean_object* v_numParams_364_, lean_object* v_xs_365_, lean_object* v_alt_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
uint8_t v___x_5119__boxed_372_; uint8_t v_refined_boxed_373_; lean_object* v_res_374_; 
v___x_5119__boxed_372_ = lean_unbox(v___x_360_);
v_refined_boxed_373_ = lean_unbox(v_refined_361_);
v_res_374_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(v___x_5119__boxed_372_, v_refined_boxed_373_, v_unrefinedArgType_362_, v_binderType_363_, v_numParams_364_, v_xs_365_, v_alt_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
return v_res_374_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__0));
v___x_377_ = l_Lean_stringToMessageData(v___x_376_);
return v___x_377_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__2));
v___x_380_ = l_Lean_stringToMessageData(v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(lean_object* v_unrefinedArgType_381_, lean_object* v_typeNew_382_, lean_object* v_altNumParams_383_, lean_object* v_alts_384_, uint8_t v_refined_385_, lean_object* v_i_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = lean_array_get_size(v_alts_384_);
v___x_393_ = lean_nat_dec_lt(v_i_386_, v___x_392_);
if (v___x_393_ == 0)
{
lean_dec(v_i_386_);
lean_dec_ref(v_typeNew_382_);
lean_dec_ref(v_unrefinedArgType_381_);
if (v_refined_385_ == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; 
lean_dec_ref(v_alts_384_);
v___x_394_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1);
v___x_395_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_394_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
return v___x_395_;
}
else
{
lean_object* v___x_396_; 
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
v___x_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_396_, 0, v_alts_384_);
return v___x_396_;
}
}
else
{
lean_object* v___x_397_; 
lean_inc(v_a_390_);
lean_inc_ref(v_a_389_);
lean_inc(v_a_388_);
lean_inc_ref(v_a_387_);
v___x_397_ = l_Lean_Meta_whnfD(v_typeNew_382_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
lean_inc(v_a_398_);
lean_dec_ref(v___x_397_);
if (lean_obj_tag(v_a_398_) == 7)
{
lean_object* v_binderType_399_; lean_object* v_body_400_; lean_object* v___x_401_; lean_object* v_alt_402_; lean_object* v_numParams_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___f_406_; uint8_t v___x_407_; lean_object* v___x_408_; 
v_binderType_399_ = lean_ctor_get(v_a_398_, 1);
lean_inc_ref(v_binderType_399_);
v_body_400_ = lean_ctor_get(v_a_398_, 2);
lean_inc_ref(v_body_400_);
lean_dec_ref(v_a_398_);
v___x_401_ = lean_unsigned_to_nat(0u);
v_alt_402_ = lean_array_fget_borrowed(v_alts_384_, v_i_386_);
v_numParams_403_ = lean_array_get_borrowed(v___x_401_, v_altNumParams_383_, v_i_386_);
v___x_404_ = lean_box(v___x_393_);
v___x_405_ = lean_box(v_refined_385_);
lean_inc(v_numParams_403_);
lean_inc_ref(v_unrefinedArgType_381_);
v___f_406_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed), 12, 5);
lean_closure_set(v___f_406_, 0, v___x_404_);
lean_closure_set(v___f_406_, 1, v___x_405_);
lean_closure_set(v___f_406_, 2, v_unrefinedArgType_381_);
lean_closure_set(v___f_406_, 3, v_binderType_399_);
lean_closure_set(v___f_406_, 4, v_numParams_403_);
v___x_407_ = 0;
lean_inc(v_a_390_);
lean_inc_ref(v_a_389_);
lean_inc(v_a_388_);
lean_inc_ref(v_a_387_);
lean_inc(v_numParams_403_);
lean_inc(v_alt_402_);
v___x_408_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2___redArg(v_alt_402_, v_numParams_403_, v___f_406_, v___x_407_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v_fst_410_; lean_object* v_snd_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_a_409_);
lean_dec_ref(v___x_408_);
v_fst_410_ = lean_ctor_get(v_a_409_, 0);
lean_inc(v_fst_410_);
v_snd_411_ = lean_ctor_get(v_a_409_, 1);
lean_inc(v_snd_411_);
lean_dec(v_a_409_);
v___x_412_ = lean_expr_instantiate1(v_body_400_, v_fst_410_);
lean_dec_ref(v_body_400_);
v___x_413_ = lean_array_fset(v_alts_384_, v_i_386_, v_fst_410_);
v___x_414_ = lean_unsigned_to_nat(1u);
v___x_415_ = lean_nat_add(v_i_386_, v___x_414_);
lean_dec(v_i_386_);
v___x_416_ = lean_unbox(v_snd_411_);
lean_dec(v_snd_411_);
v_typeNew_382_ = v___x_412_;
v_alts_384_ = v___x_413_;
v_refined_385_ = v___x_416_;
v_i_386_ = v___x_415_;
goto _start;
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_dec_ref(v_body_400_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_i_386_);
lean_dec_ref(v_alts_384_);
lean_dec_ref(v_unrefinedArgType_381_);
v_a_418_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_408_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_408_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
else
{
lean_object* v___x_426_; lean_object* v___x_427_; 
lean_dec(v_a_398_);
lean_dec(v_i_386_);
lean_dec_ref(v_alts_384_);
lean_dec_ref(v_unrefinedArgType_381_);
v___x_426_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3);
v___x_427_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_426_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
return v___x_427_;
}
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_i_386_);
lean_dec_ref(v_alts_384_);
lean_dec_ref(v_unrefinedArgType_381_);
v_a_428_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_397_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_397_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___boxed(lean_object* v_unrefinedArgType_436_, lean_object* v_typeNew_437_, lean_object* v_altNumParams_438_, lean_object* v_alts_439_, lean_object* v_refined_440_, lean_object* v_i_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
uint8_t v_refined_boxed_447_; lean_object* v_res_448_; 
v_refined_boxed_447_ = lean_unbox(v_refined_440_);
v_res_448_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(v_unrefinedArgType_436_, v_typeNew_437_, v_altNumParams_438_, v_alts_439_, v_refined_boxed_447_, v_i_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_);
lean_dec_ref(v_altNumParams_438_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0(lean_object* v_00_u03b1_449_, lean_object* v_msg_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v_msg_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___boxed(lean_object* v_00_u03b1_457_, lean_object* v_msg_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0(v_00_u03b1_457_, v_msg_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(lean_object* v_e_465_, lean_object* v_k_466_, uint8_t v_cleanupAnnotations_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v___f_473_; uint8_t v___x_474_; uint8_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___f_473_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_473_, 0, v_k_466_);
v___x_474_ = 1;
v___x_475_ = 0;
v___x_476_ = lean_box(0);
v___x_477_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_465_, v___x_474_, v___x_475_, v___x_474_, v___x_475_, v___x_476_, v___f_473_, v_cleanupAnnotations_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_485_ == 0)
{
v___x_480_ = v___x_477_;
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_477_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_478_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
v_a_486_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_477_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_477_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg___boxed(lean_object* v_e_494_, lean_object* v_k_495_, lean_object* v_cleanupAnnotations_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_502_; lean_object* v_res_503_; 
v_cleanupAnnotations_boxed_502_ = lean_unbox(v_cleanupAnnotations_496_);
v_res_503_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_e_494_, v_k_495_, v_cleanupAnnotations_boxed_502_, v___y_497_, v___y_498_, v___y_499_, v___y_500_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1(lean_object* v_00_u03b1_504_, lean_object* v_e_505_, lean_object* v_k_506_, uint8_t v_cleanupAnnotations_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_e_505_, v_k_506_, v_cleanupAnnotations_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___boxed(lean_object* v_00_u03b1_514_, lean_object* v_e_515_, lean_object* v_k_516_, lean_object* v_cleanupAnnotations_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_523_; lean_object* v_res_524_; 
v_cleanupAnnotations_boxed_523_ = lean_unbox(v_cleanupAnnotations_517_);
v_res_524_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1(v_00_u03b1_514_, v_e_515_, v_k_516_, v_cleanupAnnotations_boxed_523_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(lean_object* v___x_525_, lean_object* v_motiveArgs_526_, lean_object* v_x_527_, lean_object* v_x_528_){
_start:
{
lean_object* v_zero_529_; uint8_t v_isZero_530_; 
v_zero_529_ = lean_unsigned_to_nat(0u);
v_isZero_530_ = lean_nat_dec_eq(v_x_527_, v_zero_529_);
if (v_isZero_530_ == 1)
{
lean_dec(v_x_527_);
return v_x_528_;
}
else
{
lean_object* v_one_531_; lean_object* v_n_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v_one_531_ = lean_unsigned_to_nat(1u);
v_n_532_ = lean_nat_sub(v_x_527_, v_one_531_);
lean_dec(v_x_527_);
v___x_533_ = lean_array_fget_borrowed(v___x_525_, v_n_532_);
v___x_534_ = l_Lean_Expr_isFVar(v___x_533_);
if (v___x_534_ == 0)
{
v_x_527_ = v_n_532_;
goto _start;
}
else
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_536_ = l_Lean_instInhabitedExpr;
v___x_537_ = lean_array_get_borrowed(v___x_536_, v_motiveArgs_526_, v_n_532_);
lean_inc(v___x_533_);
v___x_538_ = l_Lean_Expr_replaceFVar(v_x_528_, v___x_533_, v___x_537_);
lean_dec_ref(v_x_528_);
v_x_527_ = v_n_532_;
v_x_528_ = v___x_538_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0___boxed(lean_object* v___x_540_, lean_object* v_motiveArgs_541_, lean_object* v_x_542_, lean_object* v_x_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(v___x_540_, v_motiveArgs_541_, v_x_542_, v_x_543_);
lean_dec_ref(v_motiveArgs_541_);
lean_dec_ref(v___x_540_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(lean_object* v___x_545_, lean_object* v_motiveArgs_546_, lean_object* v_x_547_, lean_object* v_x_548_){
_start:
{
lean_object* v_zero_549_; uint8_t v_isZero_550_; 
v_zero_549_ = lean_unsigned_to_nat(0u);
v_isZero_550_ = lean_nat_dec_eq(v_x_547_, v_zero_549_);
if (v_isZero_550_ == 1)
{
return v_x_548_;
}
else
{
lean_object* v_one_551_; lean_object* v_n_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v_one_551_ = lean_unsigned_to_nat(1u);
v_n_552_ = lean_nat_sub(v_x_547_, v_one_551_);
v___x_553_ = lean_array_fget_borrowed(v___x_545_, v_n_552_);
v___x_554_ = l_Lean_Expr_isFVar(v___x_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; 
v___x_555_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(v___x_545_, v_motiveArgs_546_, v_n_552_, v_x_548_);
return v___x_555_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_556_ = l_Lean_instInhabitedExpr;
v___x_557_ = lean_array_get_borrowed(v___x_556_, v_motiveArgs_546_, v_n_552_);
lean_inc(v___x_553_);
v___x_558_ = l_Lean_Expr_replaceFVar(v_x_548_, v___x_553_, v___x_557_);
lean_dec_ref(v_x_548_);
v___x_559_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(v___x_545_, v_motiveArgs_546_, v_n_552_, v___x_558_);
return v___x_559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0___boxed(lean_object* v___x_560_, lean_object* v_motiveArgs_561_, lean_object* v_x_562_, lean_object* v_x_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(v___x_560_, v_motiveArgs_561_, v_x_562_, v_x_563_);
lean_dec(v_x_562_);
lean_dec_ref(v_motiveArgs_561_);
lean_dec_ref(v___x_560_);
return v_res_564_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = ((lean_object*)(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__0));
v___x_567_ = l_Lean_stringToMessageData(v___x_566_);
return v___x_567_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = ((lean_object*)(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__2));
v___x_570_ = l_Lean_stringToMessageData(v___x_569_);
return v___x_570_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = ((lean_object*)(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4));
v___x_573_ = l_Lean_stringToMessageData(v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0(lean_object* v_matcherApp_574_, lean_object* v_e_575_, lean_object* v_discrs_576_, lean_object* v_toMatcherInfo_577_, lean_object* v_remaining_578_, lean_object* v_params_579_, lean_object* v_matcherName_580_, lean_object* v_alts_581_, lean_object* v_matcherLevels_582_, lean_object* v_motiveArgs_583_, lean_object* v_motiveBody_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
uint8_t v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v_matcherLevels_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_734_ = lean_array_get_size(v_motiveArgs_583_);
v___x_735_ = lean_array_get_size(v_discrs_576_);
v___x_736_ = lean_nat_dec_eq(v___x_734_, v___x_735_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec_ref(v_motiveBody_584_);
lean_dec_ref(v_matcherLevels_582_);
lean_dec_ref(v_alts_581_);
lean_dec(v_matcherName_580_);
lean_dec_ref(v_params_579_);
lean_dec_ref(v_toMatcherInfo_577_);
lean_dec_ref(v_discrs_576_);
lean_dec_ref(v_e_575_);
lean_dec_ref(v_matcherApp_574_);
v___x_737_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_738_ = l_Nat_reprFast(v___x_735_);
v___x_739_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
v___x_740_ = l_Lean_MessageData_ofFormat(v___x_739_);
v___x_741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_737_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_741_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_743_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
v_a_745_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_744_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_744_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
else
{
v___y_694_ = v___y_585_;
v___y_695_ = v___y_586_;
v___y_696_ = v___y_587_;
v___y_697_ = v___y_588_;
goto v___jp_693_;
}
v___jp_590_:
{
lean_object* v___x_606_; 
lean_inc(v___y_605_);
lean_inc_ref(v___y_604_);
lean_inc(v___y_603_);
lean_inc_ref(v___y_602_);
v___x_606_ = lean_infer_type(v___y_593_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref(v___x_606_);
v___x_608_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_574_);
v___x_609_ = lean_unsigned_to_nat(0u);
v___x_610_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(v___y_595_, v_a_607_, v___x_608_, v___y_600_, v___y_591_, v___x_609_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
lean_dec_ref(v___x_608_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_623_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_623_ == 0)
{
v___x_613_ = v___x_610_;
v_isShared_614_ = v_isSharedCheck_623_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_610_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_623_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_621_; 
v___x_615_ = lean_unsigned_to_nat(1u);
v___x_616_ = lean_mk_empty_array_with_capacity(v___x_615_);
v___x_617_ = lean_array_push(v___x_616_, v_e_575_);
v___x_618_ = l_Array_append___redArg(v___x_617_, v___y_594_);
v___x_619_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_619_, 0, v___y_598_);
lean_ctor_set(v___x_619_, 1, v___y_597_);
lean_ctor_set(v___x_619_, 2, v___y_601_);
lean_ctor_set(v___x_619_, 3, v___y_596_);
lean_ctor_set(v___x_619_, 4, v___y_592_);
lean_ctor_set(v___x_619_, 5, v___y_599_);
lean_ctor_set(v___x_619_, 6, v_a_611_);
lean_ctor_set(v___x_619_, 7, v___x_618_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_619_);
v___x_621_ = v___x_613_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec_ref(v___y_601_);
lean_dec_ref(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec_ref(v___y_592_);
lean_dec_ref(v_e_575_);
v_a_624_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_610_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_610_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec_ref(v___y_592_);
lean_dec_ref(v_e_575_);
lean_dec_ref(v_matcherApp_574_);
v_a_632_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_606_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_606_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
v___jp_640_:
{
uint8_t v___x_654_; uint8_t v___x_655_; uint8_t v___x_656_; lean_object* v___x_657_; 
v___x_654_ = 0;
v___x_655_ = 1;
v___x_656_ = 1;
v___x_657_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_583_, v___y_646_, v___x_654_, v___x_655_, v___x_654_, v___x_655_, v___x_656_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref(v___x_657_);
lean_inc_ref(v_matcherLevels_649_);
v___x_659_ = lean_array_to_list(v_matcherLevels_649_);
lean_inc(v___y_644_);
v___x_660_ = l_Lean_mkConst(v___y_644_, v___x_659_);
v___x_661_ = l_Lean_mkAppN(v___x_660_, v___y_643_);
lean_inc(v_a_658_);
v___x_662_ = l_Lean_Expr_app___override(v___x_661_, v_a_658_);
v___x_663_ = l_Lean_mkAppN(v___x_662_, v___y_648_);
lean_inc(v___y_653_);
lean_inc_ref(v___y_652_);
lean_inc(v___y_651_);
lean_inc_ref(v___y_650_);
lean_inc_ref(v___x_663_);
v___x_664_ = l_Lean_Meta_isTypeCorrect(v___x_663_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; uint8_t v___x_666_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
lean_dec_ref(v___x_664_);
v___x_666_ = lean_unbox(v_a_665_);
lean_dec(v_a_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_dec_ref(v___x_663_);
lean_dec(v_a_658_);
lean_dec_ref(v_matcherLevels_649_);
lean_dec_ref(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec_ref(v___y_641_);
lean_dec_ref(v_e_575_);
lean_dec_ref(v_matcherApp_574_);
v___x_667_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1);
v___x_668_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_667_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
v_a_669_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_668_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_668_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
else
{
v___y_591_ = v___x_654_;
v___y_592_ = v_a_658_;
v___y_593_ = v___x_663_;
v___y_594_ = v___y_642_;
v___y_595_ = v___y_641_;
v___y_596_ = v___y_643_;
v___y_597_ = v___y_644_;
v___y_598_ = v___y_645_;
v___y_599_ = v___y_648_;
v___y_600_ = v___y_647_;
v___y_601_ = v_matcherLevels_649_;
v___y_602_ = v___y_650_;
v___y_603_ = v___y_651_;
v___y_604_ = v___y_652_;
v___y_605_ = v___y_653_;
goto v___jp_590_;
}
}
else
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_dec_ref(v___x_663_);
lean_dec(v_a_658_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec_ref(v_matcherLevels_649_);
lean_dec_ref(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec_ref(v___y_641_);
lean_dec_ref(v_e_575_);
lean_dec_ref(v_matcherApp_574_);
v_a_677_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_664_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_664_);
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
}
else
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_692_; 
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec_ref(v_matcherLevels_649_);
lean_dec_ref(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec_ref(v___y_641_);
lean_dec_ref(v_e_575_);
lean_dec_ref(v_matcherApp_574_);
v_a_685_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_692_ == 0)
{
v___x_687_ = v___x_657_;
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_657_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_690_; 
if (v_isShared_688_ == 0)
{
v___x_690_ = v___x_687_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_685_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
v___jp_693_:
{
lean_object* v___x_698_; 
lean_inc(v___y_697_);
lean_inc_ref(v___y_696_);
lean_inc(v___y_695_);
lean_inc_ref(v___y_694_);
lean_inc_ref(v_e_575_);
v___x_698_ = lean_infer_type(v_e_575_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref(v___x_698_);
v___x_700_ = lean_array_get_size(v_discrs_576_);
lean_inc(v_a_699_);
v___x_701_ = l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(v_discrs_576_, v_motiveArgs_583_, v___x_700_, v_a_699_);
lean_inc(v___y_697_);
lean_inc_ref(v___y_696_);
v___x_702_ = l_Lean_mkArrow(v___x_701_, v_motiveBody_584_, v___y_696_, v___y_697_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_uElimPos_x3f_703_; 
v_uElimPos_x3f_703_ = lean_ctor_get(v_toMatcherInfo_577_, 3);
if (lean_obj_tag(v_uElimPos_x3f_703_) == 0)
{
lean_object* v_a_704_; 
v_a_704_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_704_);
lean_dec_ref(v___x_702_);
v___y_641_ = v_a_699_;
v___y_642_ = v_remaining_578_;
v___y_643_ = v_params_579_;
v___y_644_ = v_matcherName_580_;
v___y_645_ = v_toMatcherInfo_577_;
v___y_646_ = v_a_704_;
v___y_647_ = v_alts_581_;
v___y_648_ = v_discrs_576_;
v_matcherLevels_649_ = v_matcherLevels_582_;
v___y_650_ = v___y_694_;
v___y_651_ = v___y_695_;
v___y_652_ = v___y_696_;
v___y_653_ = v___y_697_;
goto v___jp_640_;
}
else
{
lean_object* v_a_705_; lean_object* v_val_706_; lean_object* v___x_707_; 
v_a_705_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_705_);
lean_dec_ref(v___x_702_);
v_val_706_ = lean_ctor_get(v_uElimPos_x3f_703_, 0);
lean_inc(v___y_697_);
lean_inc_ref(v___y_696_);
lean_inc(v___y_695_);
lean_inc_ref(v___y_694_);
lean_inc(v_a_705_);
v___x_707_ = l_Lean_Meta_getLevel(v_a_705_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_709_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref(v___x_707_);
v___x_709_ = lean_array_set(v_matcherLevels_582_, v_val_706_, v_a_708_);
v___y_641_ = v_a_699_;
v___y_642_ = v_remaining_578_;
v___y_643_ = v_params_579_;
v___y_644_ = v_matcherName_580_;
v___y_645_ = v_toMatcherInfo_577_;
v___y_646_ = v_a_705_;
v___y_647_ = v_alts_581_;
v___y_648_ = v_discrs_576_;
v_matcherLevels_649_ = v___x_709_;
v___y_650_ = v___y_694_;
v___y_651_ = v___y_695_;
v___y_652_ = v___y_696_;
v___y_653_ = v___y_697_;
goto v___jp_640_;
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_dec(v_a_705_);
lean_dec(v_a_699_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec_ref(v_matcherLevels_582_);
lean_dec_ref(v_alts_581_);
lean_dec(v_matcherName_580_);
lean_dec_ref(v_params_579_);
lean_dec_ref(v_toMatcherInfo_577_);
lean_dec_ref(v_discrs_576_);
lean_dec_ref(v_e_575_);
lean_dec_ref(v_matcherApp_574_);
v_a_710_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_707_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_707_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec(v_a_699_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec_ref(v_matcherLevels_582_);
lean_dec_ref(v_alts_581_);
lean_dec(v_matcherName_580_);
lean_dec_ref(v_params_579_);
lean_dec_ref(v_toMatcherInfo_577_);
lean_dec_ref(v_discrs_576_);
lean_dec_ref(v_e_575_);
lean_dec_ref(v_matcherApp_574_);
v_a_718_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_702_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_702_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec_ref(v_motiveBody_584_);
lean_dec_ref(v_matcherLevels_582_);
lean_dec_ref(v_alts_581_);
lean_dec(v_matcherName_580_);
lean_dec_ref(v_params_579_);
lean_dec_ref(v_toMatcherInfo_577_);
lean_dec_ref(v_discrs_576_);
lean_dec_ref(v_e_575_);
lean_dec_ref(v_matcherApp_574_);
v_a_726_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_698_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_698_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___boxed(lean_object* v_matcherApp_753_, lean_object* v_e_754_, lean_object* v_discrs_755_, lean_object* v_toMatcherInfo_756_, lean_object* v_remaining_757_, lean_object* v_params_758_, lean_object* v_matcherName_759_, lean_object* v_alts_760_, lean_object* v_matcherLevels_761_, lean_object* v_motiveArgs_762_, lean_object* v_motiveBody_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_Meta_MatcherApp_addArg___lam__0(v_matcherApp_753_, v_e_754_, v_discrs_755_, v_toMatcherInfo_756_, v_remaining_757_, v_params_758_, v_matcherName_759_, v_alts_760_, v_matcherLevels_761_, v_motiveArgs_762_, v_motiveBody_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
lean_dec_ref(v_motiveArgs_762_);
lean_dec_ref(v_remaining_757_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg(lean_object* v_matcherApp_770_, lean_object* v_e_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v_toMatcherInfo_777_; lean_object* v_matcherName_778_; lean_object* v_matcherLevels_779_; lean_object* v_params_780_; lean_object* v_motive_781_; lean_object* v_discrs_782_; lean_object* v_alts_783_; lean_object* v_remaining_784_; lean_object* v___f_785_; uint8_t v___x_786_; lean_object* v___x_787_; 
v_toMatcherInfo_777_ = lean_ctor_get(v_matcherApp_770_, 0);
lean_inc_ref(v_toMatcherInfo_777_);
v_matcherName_778_ = lean_ctor_get(v_matcherApp_770_, 1);
lean_inc(v_matcherName_778_);
v_matcherLevels_779_ = lean_ctor_get(v_matcherApp_770_, 2);
lean_inc_ref(v_matcherLevels_779_);
v_params_780_ = lean_ctor_get(v_matcherApp_770_, 3);
lean_inc_ref(v_params_780_);
v_motive_781_ = lean_ctor_get(v_matcherApp_770_, 4);
lean_inc_ref(v_motive_781_);
v_discrs_782_ = lean_ctor_get(v_matcherApp_770_, 5);
lean_inc_ref(v_discrs_782_);
v_alts_783_ = lean_ctor_get(v_matcherApp_770_, 6);
lean_inc_ref(v_alts_783_);
v_remaining_784_ = lean_ctor_get(v_matcherApp_770_, 7);
lean_inc_ref(v_remaining_784_);
v___f_785_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_addArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_785_, 0, v_matcherApp_770_);
lean_closure_set(v___f_785_, 1, v_e_771_);
lean_closure_set(v___f_785_, 2, v_discrs_782_);
lean_closure_set(v___f_785_, 3, v_toMatcherInfo_777_);
lean_closure_set(v___f_785_, 4, v_remaining_784_);
lean_closure_set(v___f_785_, 5, v_params_780_);
lean_closure_set(v___f_785_, 6, v_matcherName_778_);
lean_closure_set(v___f_785_, 7, v_alts_783_);
lean_closure_set(v___f_785_, 8, v_matcherLevels_779_);
v___x_786_ = 0;
v___x_787_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_781_, v___f_785_, v___x_786_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___boxed(lean_object* v_matcherApp_788_, lean_object* v_e_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Lean_Meta_MatcherApp_addArg(v_matcherApp_788_, v_e_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg_x3f(lean_object* v_matcherApp_796_, lean_object* v_e_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_Meta_MatcherApp_addArg(v_matcherApp_796_, v_e_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_812_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_812_ == 0)
{
v___x_806_ = v___x_803_;
v_isShared_807_ = v_isSharedCheck_812_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_803_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_812_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_808_, 0, v_a_804_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v___x_808_);
v___x_810_ = v___x_806_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
else
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_828_; 
v_a_813_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_828_ == 0)
{
v___x_815_ = v___x_803_;
v_isShared_816_ = v_isSharedCheck_828_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_803_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_828_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
uint8_t v___y_818_; uint8_t v___x_826_; 
v___x_826_ = l_Lean_Exception_isInterrupt(v_a_813_);
if (v___x_826_ == 0)
{
uint8_t v___x_827_; 
lean_inc(v_a_813_);
v___x_827_ = l_Lean_Exception_isRuntime(v_a_813_);
v___y_818_ = v___x_827_;
goto v___jp_817_;
}
else
{
v___y_818_ = v___x_826_;
goto v___jp_817_;
}
v___jp_817_:
{
if (v___y_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_821_; 
lean_dec(v_a_813_);
v___x_819_ = lean_box(0);
if (v_isShared_816_ == 0)
{
lean_ctor_set_tag(v___x_815_, 0);
lean_ctor_set(v___x_815_, 0, v___x_819_);
v___x_821_ = v___x_815_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
else
{
lean_object* v___x_824_; 
if (v_isShared_816_ == 0)
{
v___x_824_ = v___x_815_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_813_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg_x3f___boxed(lean_object* v_matcherApp_829_, lean_object* v_e_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_matcherApp_829_, v_e_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg(lean_object* v_type_837_, lean_object* v_k_838_, uint8_t v_cleanupAnnotations_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v___f_845_; uint8_t v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___f_845_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_845_, 0, v_k_838_);
v___x_846_ = 0;
v___x_847_ = lean_box(0);
v___x_848_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_846_, v___x_847_, v_type_837_, v___f_845_, v_cleanupAnnotations_839_, v___x_846_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
v_a_857_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_848_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_848_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg___boxed(lean_object* v_type_865_, lean_object* v_k_866_, lean_object* v_cleanupAnnotations_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_873_; lean_object* v_res_874_; 
v_cleanupAnnotations_boxed_873_ = lean_unbox(v_cleanupAnnotations_867_);
v_res_874_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg(v_type_865_, v_k_866_, v_cleanupAnnotations_boxed_873_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3(lean_object* v_00_u03b1_875_, lean_object* v_type_876_, lean_object* v_k_877_, uint8_t v_cleanupAnnotations_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg(v_type_876_, v_k_877_, v_cleanupAnnotations_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___boxed(lean_object* v_00_u03b1_885_, lean_object* v_type_886_, lean_object* v_k_887_, lean_object* v_cleanupAnnotations_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_894_; lean_object* v_res_895_; 
v_cleanupAnnotations_boxed_894_ = lean_unbox(v_cleanupAnnotations_888_);
v_res_895_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3(v_00_u03b1_885_, v_type_886_, v_k_887_, v_cleanupAnnotations_boxed_894_, v___y_889_, v___y_890_, v___y_891_, v___y_892_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__1(size_t v_sz_896_, size_t v_i_897_, lean_object* v_bs_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
uint8_t v___x_904_; 
v___x_904_ = lean_usize_dec_lt(v_i_897_, v_sz_896_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; 
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v_bs_898_);
return v___x_905_;
}
else
{
lean_object* v_v_906_; lean_object* v___x_907_; 
v_v_906_ = lean_array_uget_borrowed(v_bs_898_, v_i_897_);
lean_inc(v___y_902_);
lean_inc_ref(v___y_901_);
lean_inc(v___y_900_);
lean_inc_ref(v___y_899_);
lean_inc(v_v_906_);
v___x_907_ = lean_infer_type(v_v_906_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v___x_909_; lean_object* v_bs_x27_910_; size_t v___x_911_; size_t v___x_912_; lean_object* v___x_913_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
lean_dec_ref(v___x_907_);
v___x_909_ = lean_unsigned_to_nat(0u);
v_bs_x27_910_ = lean_array_uset(v_bs_898_, v_i_897_, v___x_909_);
v___x_911_ = ((size_t)1ULL);
v___x_912_ = lean_usize_add(v_i_897_, v___x_911_);
v___x_913_ = lean_array_uset(v_bs_x27_910_, v_i_897_, v_a_908_);
v_i_897_ = v___x_912_;
v_bs_898_ = v___x_913_;
goto _start;
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec_ref(v_bs_898_);
v_a_915_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_907_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_907_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___boxed(lean_object* v_sz_923_, lean_object* v_i_924_, lean_object* v_bs_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
size_t v_sz_boxed_931_; size_t v_i_boxed_932_; lean_object* v_res_933_; 
v_sz_boxed_931_ = lean_unbox_usize(v_sz_923_);
lean_dec(v_sz_923_);
v_i_boxed_932_ = lean_unbox_usize(v_i_924_);
lean_dec(v_i_924_);
v_res_933_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__1(v_sz_boxed_931_, v_i_boxed_932_, v_bs_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
return v_res_933_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__1(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = ((lean_object*)(l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__0));
v___x_936_ = l_Lean_stringToMessageData(v___x_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0(uint8_t v___x_937_, uint8_t v___x_938_, uint8_t v___x_939_, lean_object* v_a_940_, lean_object* v_fvs_941_, lean_object* v_body_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_956_; uint8_t v___x_957_; 
v___x_956_ = lean_array_get_size(v_fvs_941_);
v___x_957_ = lean_nat_dec_eq(v___x_956_, v_a_940_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
v___x_958_ = lean_obj_once(&l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__1, &l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__1);
v___x_959_ = l_Nat_reprFast(v_a_940_);
v___x_960_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
v___x_961_ = l_Lean_MessageData_ofFormat(v___x_960_);
v___x_962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_958_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_964_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
v_a_966_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_965_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_965_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
else
{
lean_dec(v_a_940_);
goto v___jp_948_;
}
v___jp_948_:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_949_ = lean_unsigned_to_nat(2u);
v___x_950_ = l_Lean_Expr_getAppNumArgs(v_body_942_);
v___x_951_ = lean_nat_sub(v___x_950_, v___x_949_);
lean_dec(v___x_950_);
v___x_952_ = lean_unsigned_to_nat(1u);
v___x_953_ = lean_nat_sub(v___x_951_, v___x_952_);
lean_dec(v___x_951_);
v___x_954_ = l_Lean_Expr_getRevArg_x21(v_body_942_, v___x_953_);
v___x_955_ = l_Lean_Meta_mkLambdaFVars(v_fvs_941_, v___x_954_, v___x_937_, v___x_938_, v___x_937_, v___x_938_, v___x_939_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
return v___x_955_;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___boxed(lean_object* v___x_974_, lean_object* v___x_975_, lean_object* v___x_976_, lean_object* v_a_977_, lean_object* v_fvs_978_, lean_object* v_body_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
uint8_t v___x_4387__boxed_985_; uint8_t v___x_4388__boxed_986_; uint8_t v___x_4389__boxed_987_; lean_object* v_res_988_; 
v___x_4387__boxed_985_ = lean_unbox(v___x_974_);
v___x_4388__boxed_986_ = lean_unbox(v___x_975_);
v___x_4389__boxed_987_ = lean_unbox(v___x_976_);
v_res_988_ = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0(v___x_4387__boxed_985_, v___x_4388__boxed_986_, v___x_4389__boxed_987_, v_a_977_, v_fvs_978_, v_body_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec_ref(v_body_979_);
lean_dec_ref(v_fvs_978_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(lean_object* v_as_989_, lean_object* v_bs_990_, lean_object* v_i_991_, lean_object* v_cs_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_998_ = lean_array_get_size(v_as_989_);
v___x_999_ = lean_nat_dec_lt(v_i_991_, v___x_998_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; 
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v_i_991_);
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v_cs_992_);
return v___x_1000_;
}
else
{
lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_1001_ = lean_array_get_size(v_bs_990_);
v___x_1002_ = lean_nat_dec_lt(v_i_991_, v___x_1001_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; 
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v_i_991_);
v___x_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1003_, 0, v_cs_992_);
return v___x_1003_;
}
else
{
uint8_t v___x_1004_; uint8_t v___x_1005_; lean_object* v_a_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___f_1010_; lean_object* v_b_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1004_ = 0;
v___x_1005_ = 1;
v_a_1006_ = lean_array_fget_borrowed(v_as_989_, v_i_991_);
v___x_1007_ = lean_box(v___x_1004_);
v___x_1008_ = lean_box(v___x_1002_);
v___x_1009_ = lean_box(v___x_1005_);
lean_inc(v_a_1006_);
v___f_1010_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1010_, 0, v___x_1007_);
lean_closure_set(v___f_1010_, 1, v___x_1008_);
lean_closure_set(v___f_1010_, 2, v___x_1009_);
lean_closure_set(v___f_1010_, 3, v_a_1006_);
v_b_1011_ = lean_array_fget_borrowed(v_bs_990_, v_i_991_);
lean_inc(v_a_1006_);
v___x_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1012_, 0, v_a_1006_);
lean_inc(v___y_996_);
lean_inc_ref(v___y_995_);
lean_inc(v___y_994_);
lean_inc_ref(v___y_993_);
lean_inc(v_b_1011_);
v___x_1013_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_b_1011_, v___x_1012_, v___f_1010_, v___x_1004_, v___x_1004_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_a_1014_);
lean_dec_ref(v___x_1013_);
v___x_1015_ = lean_unsigned_to_nat(1u);
v___x_1016_ = lean_nat_add(v_i_991_, v___x_1015_);
lean_dec(v_i_991_);
v___x_1017_ = lean_array_push(v_cs_992_, v_a_1014_);
v_i_991_ = v___x_1016_;
v_cs_992_ = v___x_1017_;
goto _start;
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec_ref(v_cs_992_);
lean_dec(v_i_991_);
v_a_1019_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1013_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1013_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___boxed(lean_object* v_as_1027_, lean_object* v_bs_1028_, lean_object* v_i_1029_, lean_object* v_cs_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(v_as_1027_, v_bs_1028_, v_i_1029_, v_cs_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec_ref(v_bs_1028_);
lean_dec_ref(v_as_1027_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0(lean_object* v_matcherApp_1039_, lean_object* v_altAuxs_1040_, lean_object* v_x_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
size_t v_sz_1047_; size_t v___x_1048_; lean_object* v___x_1049_; 
v_sz_1047_ = lean_array_size(v_altAuxs_1040_);
v___x_1048_ = ((size_t)0ULL);
lean_inc(v___y_1045_);
lean_inc_ref(v___y_1044_);
lean_inc(v___y_1043_);
lean_inc_ref(v___y_1042_);
v___x_1049_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__1(v_sz_1047_, v___x_1048_, v_altAuxs_1040_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
if (lean_obj_tag(v___x_1049_) == 0)
{
lean_object* v_a_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_a_1050_);
lean_dec_ref(v___x_1049_);
v___x_1051_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_1039_);
v___x_1052_ = lean_unsigned_to_nat(0u);
v___x_1053_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_1054_ = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(v___x_1051_, v_a_1050_, v___x_1052_, v___x_1053_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v_a_1050_);
lean_dec_ref(v___x_1051_);
return v___x_1054_;
}
else
{
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec_ref(v_matcherApp_1039_);
return v___x_1049_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0___boxed(lean_object* v_matcherApp_1055_, lean_object* v_altAuxs_1056_, lean_object* v_x_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_Meta_MatcherApp_refineThrough___lam__0(v_matcherApp_1055_, v_altAuxs_1056_, v_x_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
lean_dec_ref(v_x_1057_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(lean_object* v___x_1064_, lean_object* v_motiveArgs_1065_, lean_object* v_i_1066_, lean_object* v_a_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_zero_1073_; uint8_t v_isZero_1074_; 
v_zero_1073_ = lean_unsigned_to_nat(0u);
v_isZero_1074_ = lean_nat_dec_eq(v_i_1066_, v_zero_1073_);
if (v_isZero_1074_ == 1)
{
lean_object* v___x_1075_; 
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v_i_1066_);
v___x_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1075_, 0, v_a_1067_);
return v___x_1075_;
}
else
{
lean_object* v_one_1076_; lean_object* v_n_1077_; lean_object* v_discr_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v_one_1076_ = lean_unsigned_to_nat(1u);
v_n_1077_ = lean_nat_sub(v_i_1066_, v_one_1076_);
lean_dec(v_i_1066_);
v_discr_1078_ = lean_array_fget_borrowed(v___x_1064_, v_n_1077_);
v___x_1079_ = lean_box(0);
lean_inc(v___y_1071_);
lean_inc_ref(v___y_1070_);
lean_inc(v___y_1069_);
lean_inc_ref(v___y_1068_);
lean_inc(v_discr_1078_);
v___x_1080_ = l_Lean_Meta_kabstract(v_a_1067_, v_discr_1078_, v___x_1079_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1082_; lean_object* v_motiveArg_1083_; lean_object* v___x_1084_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
lean_dec_ref(v___x_1080_);
v___x_1082_ = l_Lean_instInhabitedExpr;
v_motiveArg_1083_ = lean_array_get_borrowed(v___x_1082_, v_motiveArgs_1065_, v_n_1077_);
v___x_1084_ = lean_expr_instantiate1(v_a_1081_, v_motiveArg_1083_);
lean_dec(v_a_1081_);
v_i_1066_ = v_n_1077_;
v_a_1067_ = v___x_1084_;
goto _start;
}
else
{
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1086_; 
v_a_1086_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1086_);
lean_dec_ref(v___x_1080_);
v_i_1066_ = v_n_1077_;
v_a_1067_ = v_a_1086_;
goto _start;
}
else
{
lean_dec(v_n_1077_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
return v___x_1080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg___boxed(lean_object* v___x_1088_, lean_object* v_motiveArgs_1089_, lean_object* v_i_1090_, lean_object* v_a_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(v___x_1088_, v_motiveArgs_1089_, v_i_1090_, v_a_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec_ref(v_motiveArgs_1089_);
lean_dec_ref(v___x_1088_);
return v_res_1097_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__0));
v___x_1100_ = l_Lean_stringToMessageData(v___x_1099_);
return v___x_1100_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__2));
v___x_1103_ = l_Lean_stringToMessageData(v___x_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1(lean_object* v___f_1104_, lean_object* v_discrs_1105_, lean_object* v_e_1106_, lean_object* v_toMatcherInfo_1107_, lean_object* v_params_1108_, lean_object* v_matcherName_1109_, lean_object* v_matcherLevels_1110_, lean_object* v_motiveArgs_1111_, lean_object* v___motiveBody_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
_start:
{
uint8_t v___y_1119_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v_matcherLevels_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___x_1217_; lean_object* v___x_1218_; uint8_t v___x_1219_; 
v___x_1217_ = lean_array_get_size(v_motiveArgs_1111_);
v___x_1218_ = lean_array_get_size(v_discrs_1105_);
v___x_1219_ = lean_nat_dec_eq(v___x_1217_, v___x_1218_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
lean_dec_ref(v_matcherLevels_1110_);
lean_dec(v_matcherName_1109_);
lean_dec_ref(v_e_1106_);
lean_dec_ref(v___f_1104_);
v___x_1220_ = lean_obj_once(&l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3, &l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3_once, _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3);
v___x_1221_ = l_Nat_reprFast(v___x_1218_);
v___x_1222_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
v___x_1223_ = l_Lean_MessageData_ofFormat(v___x_1222_);
v___x_1224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1220_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_1226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1224_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_1226_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1227_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1227_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
else
{
v___y_1187_ = v___y_1113_;
v___y_1188_ = v___y_1114_;
v___y_1189_ = v___y_1115_;
v___y_1190_ = v___y_1116_;
goto v___jp_1186_;
}
v___jp_1118_:
{
lean_object* v___x_1126_; 
lean_inc(v___y_1125_);
lean_inc_ref(v___y_1124_);
lean_inc(v___y_1123_);
lean_inc_ref(v___y_1122_);
v___x_1126_ = lean_infer_type(v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1128_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_a_1127_);
lean_dec_ref(v___x_1126_);
v___x_1128_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg(v_a_1127_, v___y_1120_, v___y_1119_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
return v___x_1128_;
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec_ref(v___y_1120_);
v_a_1129_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1126_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1126_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
v___jp_1137_:
{
uint8_t v___x_1147_; uint8_t v___x_1148_; uint8_t v___x_1149_; lean_object* v___x_1150_; 
v___x_1147_ = 0;
v___x_1148_ = 1;
v___x_1149_ = 1;
v___x_1150_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_1111_, v___y_1140_, v___x_1147_, v___x_1148_, v___x_1147_, v___x_1148_, v___x_1149_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_a_1151_);
lean_dec_ref(v___x_1150_);
v___x_1152_ = lean_array_to_list(v_matcherLevels_1142_);
v___x_1153_ = l_Lean_mkConst(v___y_1139_, v___x_1152_);
v___x_1154_ = l_Lean_mkAppN(v___x_1153_, v___y_1138_);
v___x_1155_ = l_Lean_Expr_app___override(v___x_1154_, v_a_1151_);
v___x_1156_ = l_Lean_mkAppN(v___x_1155_, v___y_1141_);
lean_inc(v___y_1146_);
lean_inc_ref(v___y_1145_);
lean_inc(v___y_1144_);
lean_inc_ref(v___y_1143_);
lean_inc_ref(v___x_1156_);
v___x_1157_ = l_Lean_Meta_isTypeCorrect(v___x_1156_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; uint8_t v___x_1159_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_a_1158_);
lean_dec_ref(v___x_1157_);
v___x_1159_ = lean_unbox(v_a_1158_);
lean_dec(v_a_1158_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
lean_dec_ref(v___x_1156_);
lean_dec_ref(v___f_1104_);
v___x_1160_ = lean_obj_once(&l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1, &l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1_once, _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1);
v___x_1161_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_1160_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v___x_1161_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1161_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
else
{
v___y_1119_ = v___x_1147_;
v___y_1120_ = v___f_1104_;
v___y_1121_ = v___x_1156_;
v___y_1122_ = v___y_1143_;
v___y_1123_ = v___y_1144_;
v___y_1124_ = v___y_1145_;
v___y_1125_ = v___y_1146_;
goto v___jp_1118_;
}
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
lean_dec_ref(v___x_1156_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec_ref(v___f_1104_);
v_a_1170_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1157_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1157_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec_ref(v_matcherLevels_1142_);
lean_dec(v___y_1139_);
lean_dec_ref(v___f_1104_);
v_a_1178_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1150_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1150_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
v___jp_1186_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_array_get_size(v_discrs_1105_);
lean_inc(v___y_1190_);
lean_inc_ref(v___y_1189_);
lean_inc(v___y_1188_);
lean_inc_ref(v___y_1187_);
v___x_1192_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(v_discrs_1105_, v_motiveArgs_1111_, v___x_1191_, v_e_1106_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1194_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_a_1193_);
lean_dec_ref(v___x_1192_);
lean_inc(v___y_1190_);
lean_inc_ref(v___y_1189_);
lean_inc(v___y_1188_);
lean_inc_ref(v___y_1187_);
lean_inc(v_a_1193_);
v___x_1194_ = l_Lean_Meta_mkEq(v_a_1193_, v_a_1193_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_uElimPos_x3f_1195_; 
v_uElimPos_x3f_1195_ = lean_ctor_get(v_toMatcherInfo_1107_, 3);
if (lean_obj_tag(v_uElimPos_x3f_1195_) == 0)
{
lean_object* v_a_1196_; 
v_a_1196_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1196_);
lean_dec_ref(v___x_1194_);
v___y_1138_ = v_params_1108_;
v___y_1139_ = v_matcherName_1109_;
v___y_1140_ = v_a_1196_;
v___y_1141_ = v_discrs_1105_;
v_matcherLevels_1142_ = v_matcherLevels_1110_;
v___y_1143_ = v___y_1187_;
v___y_1144_ = v___y_1188_;
v___y_1145_ = v___y_1189_;
v___y_1146_ = v___y_1190_;
goto v___jp_1137_;
}
else
{
lean_object* v_a_1197_; lean_object* v_val_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v_a_1197_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1197_);
lean_dec_ref(v___x_1194_);
v_val_1198_ = lean_ctor_get(v_uElimPos_x3f_1195_, 0);
v___x_1199_ = lean_box(0);
v___x_1200_ = lean_array_set(v_matcherLevels_1110_, v_val_1198_, v___x_1199_);
v___y_1138_ = v_params_1108_;
v___y_1139_ = v_matcherName_1109_;
v___y_1140_ = v_a_1197_;
v___y_1141_ = v_discrs_1105_;
v_matcherLevels_1142_ = v___x_1200_;
v___y_1143_ = v___y_1187_;
v___y_1144_ = v___y_1188_;
v___y_1145_ = v___y_1189_;
v___y_1146_ = v___y_1190_;
goto v___jp_1137_;
}
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec_ref(v_matcherLevels_1110_);
lean_dec(v_matcherName_1109_);
lean_dec_ref(v___f_1104_);
v_a_1201_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1194_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1194_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec_ref(v_matcherLevels_1110_);
lean_dec(v_matcherName_1109_);
lean_dec_ref(v___f_1104_);
v_a_1209_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1192_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1192_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___boxed(lean_object* v___f_1236_, lean_object* v_discrs_1237_, lean_object* v_e_1238_, lean_object* v_toMatcherInfo_1239_, lean_object* v_params_1240_, lean_object* v_matcherName_1241_, lean_object* v_matcherLevels_1242_, lean_object* v_motiveArgs_1243_, lean_object* v___motiveBody_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_Meta_MatcherApp_refineThrough___lam__1(v___f_1236_, v_discrs_1237_, v_e_1238_, v_toMatcherInfo_1239_, v_params_1240_, v_matcherName_1241_, v_matcherLevels_1242_, v_motiveArgs_1243_, v___motiveBody_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
lean_dec_ref(v___motiveBody_1244_);
lean_dec_ref(v_motiveArgs_1243_);
lean_dec_ref(v_params_1240_);
lean_dec_ref(v_toMatcherInfo_1239_);
lean_dec_ref(v_discrs_1237_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough(lean_object* v_matcherApp_1251_, lean_object* v_e_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_){
_start:
{
lean_object* v_toMatcherInfo_1258_; lean_object* v_matcherName_1259_; lean_object* v_matcherLevels_1260_; lean_object* v_params_1261_; lean_object* v_motive_1262_; lean_object* v_discrs_1263_; lean_object* v___f_1264_; lean_object* v___f_1265_; uint8_t v___x_1266_; lean_object* v___x_1267_; 
v_toMatcherInfo_1258_ = lean_ctor_get(v_matcherApp_1251_, 0);
lean_inc_ref(v_toMatcherInfo_1258_);
v_matcherName_1259_ = lean_ctor_get(v_matcherApp_1251_, 1);
lean_inc(v_matcherName_1259_);
v_matcherLevels_1260_ = lean_ctor_get(v_matcherApp_1251_, 2);
lean_inc_ref(v_matcherLevels_1260_);
v_params_1261_ = lean_ctor_get(v_matcherApp_1251_, 3);
lean_inc_ref(v_params_1261_);
v_motive_1262_ = lean_ctor_get(v_matcherApp_1251_, 4);
lean_inc_ref(v_motive_1262_);
v_discrs_1263_ = lean_ctor_get(v_matcherApp_1251_, 5);
lean_inc_ref(v_discrs_1263_);
v___f_1264_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1264_, 0, v_matcherApp_1251_);
v___f_1265_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1265_, 0, v___f_1264_);
lean_closure_set(v___f_1265_, 1, v_discrs_1263_);
lean_closure_set(v___f_1265_, 2, v_e_1252_);
lean_closure_set(v___f_1265_, 3, v_toMatcherInfo_1258_);
lean_closure_set(v___f_1265_, 4, v_params_1261_);
lean_closure_set(v___f_1265_, 5, v_matcherName_1259_);
lean_closure_set(v___f_1265_, 6, v_matcherLevels_1260_);
v___x_1266_ = 0;
v___x_1267_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_1262_, v___f_1265_, v___x_1266_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___boxed(lean_object* v_matcherApp_1268_, lean_object* v_e_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_Meta_MatcherApp_refineThrough(v_matcherApp_1268_, v_e_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0(lean_object* v___x_1276_, lean_object* v_motiveArgs_1277_, lean_object* v_n_1278_, lean_object* v_i_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(v___x_1276_, v_motiveArgs_1277_, v_i_1279_, v_a_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___boxed(lean_object* v___x_1288_, lean_object* v_motiveArgs_1289_, lean_object* v_n_1290_, lean_object* v_i_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0(v___x_1288_, v_motiveArgs_1289_, v_n_1290_, v_i_1291_, v_a_1292_, v_a_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec(v_n_1290_);
lean_dec_ref(v_motiveArgs_1289_);
lean_dec_ref(v___x_1288_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough_x3f(lean_object* v_matcherApp_1300_, lean_object* v_e_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_Meta_MatcherApp_refineThrough(v_matcherApp_1300_, v_e_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1316_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1316_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1316_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1312_, 0, v_a_1308_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v___x_1312_);
v___x_1314_ = v___x_1310_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1332_; 
v_a_1317_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1319_ = v___x_1307_;
v_isShared_1320_ = v_isSharedCheck_1332_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1307_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1332_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
uint8_t v___y_1322_; uint8_t v___x_1330_; 
v___x_1330_ = l_Lean_Exception_isInterrupt(v_a_1317_);
if (v___x_1330_ == 0)
{
uint8_t v___x_1331_; 
lean_inc(v_a_1317_);
v___x_1331_ = l_Lean_Exception_isRuntime(v_a_1317_);
v___y_1322_ = v___x_1331_;
goto v___jp_1321_;
}
else
{
v___y_1322_ = v___x_1330_;
goto v___jp_1321_;
}
v___jp_1321_:
{
if (v___y_1322_ == 0)
{
lean_object* v___x_1323_; lean_object* v___x_1325_; 
lean_dec(v_a_1317_);
v___x_1323_ = lean_box(0);
if (v_isShared_1320_ == 0)
{
lean_ctor_set_tag(v___x_1319_, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1323_);
v___x_1325_ = v___x_1319_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
else
{
lean_object* v___x_1328_; 
if (v_isShared_1320_ == 0)
{
v___x_1328_ = v___x_1319_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1317_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough_x3f___boxed(lean_object* v_matcherApp_1333_, lean_object* v_e_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_Meta_MatcherApp_refineThrough_x3f(v_matcherApp_1333_, v_e_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(lean_object* v_lctx_1341_, lean_object* v_x_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v_keyedConfig_1348_; uint8_t v_trackZetaDelta_1349_; lean_object* v_zetaDeltaSet_1350_; lean_object* v_localInstances_1351_; lean_object* v_defEqCtx_x3f_1352_; lean_object* v_synthPendingDepth_1353_; lean_object* v_canUnfold_x3f_1354_; uint8_t v_univApprox_1355_; uint8_t v_inTypeClassResolution_1356_; uint8_t v_cacheInferType_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1365_; 
v_keyedConfig_1348_ = lean_ctor_get(v___y_1343_, 0);
v_trackZetaDelta_1349_ = lean_ctor_get_uint8(v___y_1343_, sizeof(void*)*7);
v_zetaDeltaSet_1350_ = lean_ctor_get(v___y_1343_, 1);
v_localInstances_1351_ = lean_ctor_get(v___y_1343_, 3);
v_defEqCtx_x3f_1352_ = lean_ctor_get(v___y_1343_, 4);
v_synthPendingDepth_1353_ = lean_ctor_get(v___y_1343_, 5);
v_canUnfold_x3f_1354_ = lean_ctor_get(v___y_1343_, 6);
v_univApprox_1355_ = lean_ctor_get_uint8(v___y_1343_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1356_ = lean_ctor_get_uint8(v___y_1343_, sizeof(void*)*7 + 2);
v_cacheInferType_1357_ = lean_ctor_get_uint8(v___y_1343_, sizeof(void*)*7 + 3);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___y_1343_);
if (v_isSharedCheck_1365_ == 0)
{
lean_object* v_unused_1366_; 
v_unused_1366_ = lean_ctor_get(v___y_1343_, 2);
lean_dec(v_unused_1366_);
v___x_1359_ = v___y_1343_;
v_isShared_1360_ = v_isSharedCheck_1365_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_canUnfold_x3f_1354_);
lean_inc(v_synthPendingDepth_1353_);
lean_inc(v_defEqCtx_x3f_1352_);
lean_inc(v_localInstances_1351_);
lean_inc(v_zetaDeltaSet_1350_);
lean_inc(v_keyedConfig_1348_);
lean_dec(v___y_1343_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1365_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 2, v_lctx_1341_);
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_keyedConfig_1348_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_zetaDeltaSet_1350_);
lean_ctor_set(v_reuseFailAlloc_1364_, 2, v_lctx_1341_);
lean_ctor_set(v_reuseFailAlloc_1364_, 3, v_localInstances_1351_);
lean_ctor_set(v_reuseFailAlloc_1364_, 4, v_defEqCtx_x3f_1352_);
lean_ctor_set(v_reuseFailAlloc_1364_, 5, v_synthPendingDepth_1353_);
lean_ctor_set(v_reuseFailAlloc_1364_, 6, v_canUnfold_x3f_1354_);
lean_ctor_set_uint8(v_reuseFailAlloc_1364_, sizeof(void*)*7, v_trackZetaDelta_1349_);
lean_ctor_set_uint8(v_reuseFailAlloc_1364_, sizeof(void*)*7 + 1, v_univApprox_1355_);
lean_ctor_set_uint8(v_reuseFailAlloc_1364_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1356_);
lean_ctor_set_uint8(v_reuseFailAlloc_1364_, sizeof(void*)*7 + 3, v_cacheInferType_1357_);
v___x_1362_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1363_; 
v___x_1363_ = lean_apply_5(v_x_1342_, v___x_1362_, v___y_1344_, v___y_1345_, v___y_1346_, lean_box(0));
return v___x_1363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg___boxed(lean_object* v_lctx_1367_, lean_object* v_x_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1367_, v_x_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(lean_object* v_00_u03b1_1375_, lean_object* v_lctx_1376_, lean_object* v_x_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1376_, v_x_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___boxed(lean_object* v_00_u03b1_1384_, lean_object* v_lctx_1385_, lean_object* v_x_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(v_00_u03b1_1384_, v_lctx_1385_, v_x_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(lean_object* v_as_1393_, size_t v_i_1394_, size_t v_stop_1395_, lean_object* v_b_1396_){
_start:
{
uint8_t v___x_1397_; 
v___x_1397_ = lean_usize_dec_eq(v_i_1394_, v_stop_1395_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; lean_object* v_fst_1399_; lean_object* v_snd_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; size_t v___x_1403_; size_t v___x_1404_; 
v___x_1398_ = lean_array_uget_borrowed(v_as_1393_, v_i_1394_);
v_fst_1399_ = lean_ctor_get(v___x_1398_, 0);
v_snd_1400_ = lean_ctor_get(v___x_1398_, 1);
v___x_1401_ = l_Lean_Expr_fvarId_x21(v_fst_1399_);
lean_inc(v_snd_1400_);
v___x_1402_ = l_Lean_LocalContext_setUserName(v_b_1396_, v___x_1401_, v_snd_1400_);
v___x_1403_ = ((size_t)1ULL);
v___x_1404_ = lean_usize_add(v_i_1394_, v___x_1403_);
v_i_1394_ = v___x_1404_;
v_b_1396_ = v___x_1402_;
goto _start;
}
else
{
return v_b_1396_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1___boxed(lean_object* v_as_1406_, lean_object* v_i_1407_, lean_object* v_stop_1408_, lean_object* v_b_1409_){
_start:
{
size_t v_i_boxed_1410_; size_t v_stop_boxed_1411_; lean_object* v_res_1412_; 
v_i_boxed_1410_ = lean_unbox_usize(v_i_1407_);
lean_dec(v_i_1407_);
v_stop_boxed_1411_ = lean_unbox_usize(v_stop_1408_);
lean_dec(v_stop_1408_);
v_res_1412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(v_as_1406_, v_i_boxed_1410_, v_stop_boxed_1411_, v_b_1409_);
lean_dec_ref(v_as_1406_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(lean_object* v_fvars_1413_, lean_object* v_names_1414_, lean_object* v_k_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_){
_start:
{
lean_object* v_lctx_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v_lctx_1421_ = lean_ctor_get(v_a_1416_, 2);
v___x_1422_ = l_Array_zip___redArg(v_fvars_1413_, v_names_1414_);
v___x_1423_ = lean_unsigned_to_nat(0u);
v___x_1424_ = lean_array_get_size(v___x_1422_);
v___x_1425_ = lean_nat_dec_lt(v___x_1423_, v___x_1424_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; 
lean_inc_ref(v_lctx_1421_);
lean_dec_ref(v___x_1422_);
v___x_1426_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1421_, v_k_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
return v___x_1426_;
}
else
{
uint8_t v___x_1427_; 
v___x_1427_ = lean_nat_dec_le(v___x_1424_, v___x_1424_);
if (v___x_1427_ == 0)
{
if (v___x_1425_ == 0)
{
lean_object* v___x_1428_; 
lean_inc_ref(v_lctx_1421_);
lean_dec_ref(v___x_1422_);
v___x_1428_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1421_, v_k_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
return v___x_1428_;
}
else
{
size_t v___x_1429_; size_t v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1429_ = ((size_t)0ULL);
v___x_1430_ = lean_usize_of_nat(v___x_1424_);
lean_inc_ref(v_lctx_1421_);
v___x_1431_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(v___x_1422_, v___x_1429_, v___x_1430_, v_lctx_1421_);
lean_dec_ref(v___x_1422_);
v___x_1432_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v___x_1431_, v_k_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
return v___x_1432_;
}
}
else
{
size_t v___x_1433_; size_t v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1433_ = ((size_t)0ULL);
v___x_1434_ = lean_usize_of_nat(v___x_1424_);
lean_inc_ref(v_lctx_1421_);
v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(v___x_1422_, v___x_1433_, v___x_1434_, v_lctx_1421_);
lean_dec_ref(v___x_1422_);
v___x_1436_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v___x_1435_, v_k_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
return v___x_1436_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg___boxed(lean_object* v_fvars_1437_, lean_object* v_names_1438_, lean_object* v_k_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_1437_, v_names_1438_, v_k_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_);
lean_dec_ref(v_names_1438_);
lean_dec_ref(v_fvars_1437_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl(lean_object* v_00_u03b1_1446_, lean_object* v_fvars_1447_, lean_object* v_names_1448_, lean_object* v_k_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_1447_, v_names_1448_, v_k_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___boxed(lean_object* v_00_u03b1_1456_, lean_object* v_fvars_1457_, lean_object* v_names_1458_, lean_object* v_k_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl(v_00_u03b1_1456_, v_fvars_1457_, v_names_1458_, v_k_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_);
lean_dec_ref(v_names_1458_);
lean_dec_ref(v_fvars_1457_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0(lean_object* v_k_1466_, lean_object* v_fvars_1467_, lean_object* v_names_1468_, lean_object* v_runInBase_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = lean_apply_2(v_runInBase_1469_, lean_box(0), v_k_1466_);
v___x_1476_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_1467_, v_names_1468_, v___x_1475_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0___boxed(lean_object* v_k_1477_, lean_object* v_fvars_1478_, lean_object* v_names_1479_, lean_object* v_runInBase_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0(v_k_1477_, v_fvars_1478_, v_names_1479_, v_runInBase_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
lean_dec_ref(v_names_1479_);
lean_dec_ref(v_fvars_1478_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg(lean_object* v_inst_1487_, lean_object* v_inst_1488_, lean_object* v_fvars_1489_, lean_object* v_names_1490_, lean_object* v_k_1491_){
_start:
{
lean_object* v_toBind_1492_; lean_object* v_liftWith_1493_; lean_object* v_restoreM_1494_; lean_object* v___f_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v_toBind_1492_ = lean_ctor_get(v_inst_1488_, 1);
lean_inc(v_toBind_1492_);
lean_dec_ref(v_inst_1488_);
v_liftWith_1493_ = lean_ctor_get(v_inst_1487_, 0);
lean_inc(v_liftWith_1493_);
v_restoreM_1494_ = lean_ctor_get(v_inst_1487_, 1);
lean_inc(v_restoreM_1494_);
lean_dec_ref(v_inst_1487_);
v___f_1495_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1495_, 0, v_k_1491_);
lean_closure_set(v___f_1495_, 1, v_fvars_1489_);
lean_closure_set(v___f_1495_, 2, v_names_1490_);
v___x_1496_ = lean_apply_2(v_liftWith_1493_, lean_box(0), v___f_1495_);
v___x_1497_ = lean_apply_1(v_restoreM_1494_, lean_box(0));
v___x_1498_ = lean_apply_4(v_toBind_1492_, lean_box(0), lean_box(0), v___x_1496_, v___x_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames(lean_object* v_n_1499_, lean_object* v_inst_1500_, lean_object* v_inst_1501_, lean_object* v_00_u03b1_1502_, lean_object* v_fvars_1503_, lean_object* v_names_1504_, lean_object* v_k_1505_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_Meta_MatcherApp_withUserNames___redArg(v_inst_1500_, v_inst_1501_, v_fvars_1503_, v_names_1504_, v_k_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0(lean_object* v_k_1507_, lean_object* v_runInBase_1508_, lean_object* v_ys_1509_, lean_object* v_args_1510_, lean_object* v___mask_1511_, lean_object* v___bodyType_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = lean_apply_2(v_k_1507_, v_ys_1509_, v_args_1510_);
v___x_1519_ = lean_apply_7(v_runInBase_1508_, lean_box(0), v___x_1518_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, lean_box(0));
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0___boxed(lean_object* v_k_1520_, lean_object* v_runInBase_1521_, lean_object* v_ys_1522_, lean_object* v_args_1523_, lean_object* v___mask_1524_, lean_object* v___bodyType_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0(v_k_1520_, v_runInBase_1521_, v_ys_1522_, v_args_1523_, v___mask_1524_, v___bodyType_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec_ref(v___bodyType_1525_);
lean_dec_ref(v___mask_1524_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1(lean_object* v_k_1532_, lean_object* v_origAltType_1533_, lean_object* v_altInfo_1534_, lean_object* v_runInBase_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v___f_1541_; lean_object* v___x_1542_; 
v___f_1541_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1541_, 0, v_k_1532_);
lean_closure_set(v___f_1541_, 1, v_runInBase_1535_);
v___x_1542_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_origAltType_1533_, v_altInfo_1534_, v___f_1541_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1___boxed(lean_object* v_k_1543_, lean_object* v_origAltType_1544_, lean_object* v_altInfo_1545_, lean_object* v_runInBase_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1(v_k_1543_, v_origAltType_1544_, v_altInfo_1545_, v_runInBase_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(lean_object* v_inst_1553_, lean_object* v_inst_1554_, lean_object* v_origAltType_1555_, lean_object* v_altInfo_1556_, lean_object* v_k_1557_){
_start:
{
lean_object* v_toBind_1558_; lean_object* v_liftWith_1559_; lean_object* v_restoreM_1560_; lean_object* v___f_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v_toBind_1558_ = lean_ctor_get(v_inst_1553_, 1);
lean_inc(v_toBind_1558_);
lean_dec_ref(v_inst_1553_);
v_liftWith_1559_ = lean_ctor_get(v_inst_1554_, 0);
lean_inc(v_liftWith_1559_);
v_restoreM_1560_ = lean_ctor_get(v_inst_1554_, 1);
lean_inc(v_restoreM_1560_);
lean_dec_ref(v_inst_1554_);
v___f_1561_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1___boxed), 9, 3);
lean_closure_set(v___f_1561_, 0, v_k_1557_);
lean_closure_set(v___f_1561_, 1, v_origAltType_1555_);
lean_closure_set(v___f_1561_, 2, v_altInfo_1556_);
v___x_1562_ = lean_apply_2(v_liftWith_1559_, lean_box(0), v___f_1561_);
v___x_1563_ = lean_apply_1(v_restoreM_1560_, lean_box(0));
v___x_1564_ = lean_apply_4(v_toBind_1558_, lean_box(0), lean_box(0), v___x_1562_, v___x_1563_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27(lean_object* v_n_1565_, lean_object* v_inst_1566_, lean_object* v_inst_1567_, lean_object* v_00_u03b1_1568_, lean_object* v_origAltType_1569_, lean_object* v_altInfo_1570_, lean_object* v_k_1571_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(v_inst_1566_, v_inst_1567_, v_origAltType_1569_, v_altInfo_1570_, v_k_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0(lean_object* v_inst_1573_, lean_object* v_inst_1574_, lean_object* v_x_1575_){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2);
v___x_1577_ = l_Lean_throwError___redArg(v_inst_1573_, v_inst_1574_, v___x_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed(lean_object* v_inst_1578_, lean_object* v_inst_1579_, lean_object* v_x_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__0(v_inst_1578_, v_inst_1579_, v_x_1580_);
lean_dec_ref(v_x_1580_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1(lean_object* v_inst_1582_, lean_object* v_x_1583_){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1584_ = l_Lean_Expr_fvarId_x21(v_x_1583_);
v___x_1585_ = lean_alloc_closure((void*)(l_Lean_FVarId_getUserName___boxed), 6, 1);
lean_closure_set(v___x_1585_, 0, v___x_1584_);
v___x_1586_ = lean_apply_2(v_inst_1582_, lean_box(0), v___x_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed(lean_object* v_inst_1587_, lean_object* v_x_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__1(v_inst_1587_, v_x_1588_);
lean_dec_ref(v_x_1588_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2(lean_object* v_inst_1590_, lean_object* v___f_1591_, lean_object* v_xs_1592_, lean_object* v_x_1593_){
_start:
{
size_t v_sz_1594_; size_t v___x_1595_; lean_object* v___x_1596_; 
v_sz_1594_ = lean_array_size(v_xs_1592_);
v___x_1595_ = ((size_t)0ULL);
v___x_1596_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1590_, v___f_1591_, v_sz_1594_, v___x_1595_, v_xs_1592_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed(lean_object* v_inst_1597_, lean_object* v___f_1598_, lean_object* v_xs_1599_, lean_object* v_x_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__2(v_inst_1597_, v___f_1598_, v_xs_1599_, v_x_1600_);
lean_dec_ref(v_x_1600_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__3(lean_object* v_toPure_1602_, lean_object* v_____do__lift_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = lean_apply_2(v_toPure_1602_, lean_box(0), v_____do__lift_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__4(lean_object* v_toPure_1605_, lean_object* v_____do__lift_1606_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = lean_apply_2(v_toPure_1605_, lean_box(0), v_____do__lift_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__5(lean_object* v_fst_1608_, lean_object* v_fst_1609_, lean_object* v___x_1610_, lean_object* v___x_1611_, lean_object* v_toPure_1612_, lean_object* v_____do__lift_1613_){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1614_ = lean_array_push(v_fst_1608_, v_____do__lift_1613_);
v___x_1615_ = lean_nat_add(v_fst_1609_, v___x_1610_);
v___x_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
lean_ctor_set(v___x_1616_, 1, v___x_1611_);
v___x_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1614_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
v___x_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
v___x_1619_ = lean_apply_2(v_toPure_1612_, lean_box(0), v___x_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__5___boxed(lean_object* v_fst_1620_, lean_object* v_fst_1621_, lean_object* v___x_1622_, lean_object* v___x_1623_, lean_object* v_toPure_1624_, lean_object* v_____do__lift_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__5(v_fst_1620_, v_fst_1621_, v___x_1622_, v___x_1623_, v_toPure_1624_, v_____do__lift_1625_);
lean_dec(v___x_1622_);
lean_dec(v_fst_1621_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6(uint8_t v_val_1627_, lean_object* v_a_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
if (v_val_1627_ == 0)
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_Meta_mkEqRefl(v_a_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
return v___x_1634_;
}
else
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_Meta_mkHEqRefl(v_a_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
return v___x_1635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed(lean_object* v_val_1636_, lean_object* v_a_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
uint8_t v_val_14255__boxed_1643_; lean_object* v_res_1644_; 
v_val_14255__boxed_1643_ = lean_unbox(v_val_1636_);
v_res_1644_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__6(v_val_14255__boxed_1643_, v_a_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7(lean_object* v_toPure_1645_, lean_object* v_inst_1646_, lean_object* v_toBind_1647_, lean_object* v_a_1648_, lean_object* v_x_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v_snd_1651_; lean_object* v_snd_1652_; lean_object* v_fst_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1701_; 
v_snd_1651_ = lean_ctor_get(v___y_1650_, 1);
lean_inc(v_snd_1651_);
v_snd_1652_ = lean_ctor_get(v_snd_1651_, 1);
lean_inc(v_snd_1652_);
v_fst_1653_ = lean_ctor_get(v___y_1650_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___y_1650_);
if (v_isSharedCheck_1701_ == 0)
{
lean_object* v_unused_1702_; 
v_unused_1702_ = lean_ctor_get(v___y_1650_, 1);
lean_dec(v_unused_1702_);
v___x_1655_ = v___y_1650_;
v_isShared_1656_ = v_isSharedCheck_1701_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_fst_1653_);
lean_dec(v___y_1650_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1701_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v_fst_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1699_; 
v_fst_1657_ = lean_ctor_get(v_snd_1651_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_snd_1651_);
if (v_isSharedCheck_1699_ == 0)
{
lean_object* v_unused_1700_; 
v_unused_1700_ = lean_ctor_get(v_snd_1651_, 1);
lean_dec(v_unused_1700_);
v___x_1659_ = v_snd_1651_;
v_isShared_1660_ = v_isSharedCheck_1699_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_fst_1657_);
lean_dec(v_snd_1651_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1699_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v_array_1661_; lean_object* v_start_1662_; lean_object* v_stop_1663_; uint8_t v___x_1664_; 
v_array_1661_ = lean_ctor_get(v_snd_1652_, 0);
v_start_1662_ = lean_ctor_get(v_snd_1652_, 1);
v_stop_1663_ = lean_ctor_get(v_snd_1652_, 2);
v___x_1664_ = lean_nat_dec_lt(v_start_1662_, v_stop_1663_);
if (v___x_1664_ == 0)
{
lean_object* v___x_1666_; 
lean_dec_ref(v_a_1648_);
lean_dec(v_toBind_1647_);
lean_dec(v_inst_1646_);
if (v_isShared_1660_ == 0)
{
v___x_1666_ = v___x_1659_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_fst_1657_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_snd_1652_);
v___x_1666_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
lean_object* v___x_1668_; 
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 1, v___x_1666_);
v___x_1668_ = v___x_1655_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_fst_1653_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
v___x_1670_ = lean_apply_2(v_toPure_1645_, lean_box(0), v___x_1669_);
return v___x_1670_;
}
}
}
else
{
lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1695_; 
lean_inc(v_stop_1663_);
lean_inc(v_start_1662_);
lean_inc_ref(v_array_1661_);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_snd_1652_);
if (v_isSharedCheck_1695_ == 0)
{
lean_object* v_unused_1696_; lean_object* v_unused_1697_; lean_object* v_unused_1698_; 
v_unused_1696_ = lean_ctor_get(v_snd_1652_, 2);
lean_dec(v_unused_1696_);
v_unused_1697_ = lean_ctor_get(v_snd_1652_, 1);
lean_dec(v_unused_1697_);
v_unused_1698_ = lean_ctor_get(v_snd_1652_, 0);
lean_dec(v_unused_1698_);
v___x_1674_ = v_snd_1652_;
v_isShared_1675_ = v_isSharedCheck_1695_;
goto v_resetjp_1673_;
}
else
{
lean_dec(v_snd_1652_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1695_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1676_ = lean_array_fget(v_array_1661_, v_start_1662_);
v___x_1677_ = lean_unsigned_to_nat(1u);
v___x_1678_ = lean_nat_add(v_start_1662_, v___x_1677_);
lean_dec(v_start_1662_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 1, v___x_1678_);
v___x_1680_ = v___x_1674_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_array_1661_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v___x_1678_);
lean_ctor_set(v_reuseFailAlloc_1694_, 2, v_stop_1663_);
v___x_1680_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v___x_1682_; 
lean_dec_ref(v_a_1648_);
lean_dec(v_toBind_1647_);
lean_dec(v_inst_1646_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 1, v___x_1680_);
v___x_1682_ = v___x_1659_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_fst_1657_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_object* v___x_1684_; 
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 1, v___x_1682_);
v___x_1684_ = v___x_1655_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_fst_1653_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v___x_1682_);
v___x_1684_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
v___x_1686_ = lean_apply_2(v_toPure_1645_, lean_box(0), v___x_1685_);
return v___x_1686_;
}
}
}
else
{
lean_object* v_val_1689_; lean_object* v___f_1690_; lean_object* v___f_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
lean_del_object(v___x_1659_);
lean_del_object(v___x_1655_);
v_val_1689_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_val_1689_);
lean_dec_ref(v___x_1676_);
v___f_1690_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_1690_, 0, v_fst_1653_);
lean_closure_set(v___f_1690_, 1, v_fst_1657_);
lean_closure_set(v___f_1690_, 2, v___x_1677_);
lean_closure_set(v___f_1690_, 3, v___x_1680_);
lean_closure_set(v___f_1690_, 4, v_toPure_1645_);
v___f_1691_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed), 7, 2);
lean_closure_set(v___f_1691_, 0, v_val_1689_);
lean_closure_set(v___f_1691_, 1, v_a_1648_);
v___x_1692_ = lean_apply_2(v_inst_1646_, lean_box(0), v___f_1691_);
v___x_1693_ = lean_apply_4(v_toBind_1647_, lean_box(0), lean_box(0), v___x_1692_, v___f_1690_);
return v___x_1693_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8(lean_object* v_heq_1703_, lean_object* v_fst_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Lean_mkArrow(v_heq_1703_, v_fst_1704_, v___y_1707_, v___y_1708_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed(lean_object* v_heq_1711_, lean_object* v_fst_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__8(v_heq_1711_, v_fst_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9(lean_object* v_heq_1721_, lean_object* v_fst_1722_, lean_object* v_fst_1723_, lean_object* v___x_1724_, lean_object* v___x_1725_, lean_object* v_toPure_1726_, lean_object* v_motiveBody_x27_1727_){
_start:
{
uint8_t v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1728_ = l_Lean_Expr_isHEq(v_heq_1721_);
v___x_1729_ = lean_box(v___x_1728_);
v___x_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
v___x_1731_ = lean_array_push(v_fst_1722_, v___x_1730_);
v___x_1732_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9___closed__0));
v___x_1733_ = lean_array_push(v_fst_1723_, v___x_1732_);
v___x_1734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1724_);
lean_ctor_set(v___x_1734_, 1, v___x_1725_);
v___x_1735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1733_);
lean_ctor_set(v___x_1735_, 1, v___x_1734_);
v___x_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1731_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
v___x_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1737_, 0, v_motiveBody_x27_1727_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
v___x_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
v___x_1739_ = lean_apply_2(v_toPure_1726_, lean_box(0), v___x_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9___boxed(lean_object* v_heq_1740_, lean_object* v_fst_1741_, lean_object* v_fst_1742_, lean_object* v___x_1743_, lean_object* v___x_1744_, lean_object* v_toPure_1745_, lean_object* v_motiveBody_x27_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__9(v_heq_1740_, v_fst_1741_, v_fst_1742_, v___x_1743_, v___x_1744_, v_toPure_1745_, v_motiveBody_x27_1746_);
lean_dec_ref(v_heq_1740_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10(lean_object* v_fst_1748_, lean_object* v_fst_1749_, lean_object* v_fst_1750_, lean_object* v___x_1751_, lean_object* v___x_1752_, lean_object* v_toPure_1753_, lean_object* v_inst_1754_, lean_object* v_toBind_1755_, lean_object* v_heq_1756_){
_start:
{
lean_object* v___f_1757_; lean_object* v___f_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
lean_inc_ref(v_heq_1756_);
v___f_1757_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed), 7, 2);
lean_closure_set(v___f_1757_, 0, v_heq_1756_);
lean_closure_set(v___f_1757_, 1, v_fst_1748_);
v___f_1758_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9___boxed), 7, 6);
lean_closure_set(v___f_1758_, 0, v_heq_1756_);
lean_closure_set(v___f_1758_, 1, v_fst_1749_);
lean_closure_set(v___f_1758_, 2, v_fst_1750_);
lean_closure_set(v___f_1758_, 3, v___x_1751_);
lean_closure_set(v___f_1758_, 4, v___x_1752_);
lean_closure_set(v___f_1758_, 5, v_toPure_1753_);
v___x_1759_ = lean_apply_2(v_inst_1754_, lean_box(0), v___f_1757_);
v___x_1760_ = lean_apply_4(v_toBind_1755_, lean_box(0), lean_box(0), v___x_1759_, v___f_1758_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11(lean_object* v___x_1761_, lean_object* v_a_1762_, lean_object* v_inst_1763_, lean_object* v_toBind_1764_, lean_object* v___f_1765_, lean_object* v_fst_1766_, lean_object* v_fst_1767_, lean_object* v___x_1768_, lean_object* v___x_1769_, lean_object* v___x_1770_, lean_object* v_fst_1771_, lean_object* v_toPure_1772_, uint8_t v_____do__lift_1773_){
_start:
{
if (v_____do__lift_1773_ == 0)
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
lean_dec(v_toPure_1772_);
lean_dec(v_fst_1771_);
lean_dec_ref(v___x_1770_);
lean_dec_ref(v___x_1769_);
lean_dec(v___x_1768_);
lean_dec(v_fst_1767_);
lean_dec(v_fst_1766_);
v___x_1774_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEqHEq___boxed), 7, 2);
lean_closure_set(v___x_1774_, 0, v___x_1761_);
lean_closure_set(v___x_1774_, 1, v_a_1762_);
v___x_1775_ = lean_apply_2(v_inst_1763_, lean_box(0), v___x_1774_);
v___x_1776_ = lean_apply_4(v_toBind_1764_, lean_box(0), lean_box(0), v___x_1775_, v___f_1765_);
return v___x_1776_;
}
else
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
lean_dec(v___f_1765_);
lean_dec(v_toBind_1764_);
lean_dec(v_inst_1763_);
lean_dec_ref(v_a_1762_);
lean_dec_ref(v___x_1761_);
v___x_1777_ = lean_box(0);
v___x_1778_ = lean_array_push(v_fst_1766_, v___x_1777_);
v___x_1779_ = lean_array_push(v_fst_1767_, v___x_1768_);
v___x_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1769_);
lean_ctor_set(v___x_1780_, 1, v___x_1770_);
v___x_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1779_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1778_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
v___x_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1783_, 0, v_fst_1771_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
v___x_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
v___x_1785_ = lean_apply_2(v_toPure_1772_, lean_box(0), v___x_1784_);
return v___x_1785_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed(lean_object* v___x_1786_, lean_object* v_a_1787_, lean_object* v_inst_1788_, lean_object* v_toBind_1789_, lean_object* v___f_1790_, lean_object* v_fst_1791_, lean_object* v_fst_1792_, lean_object* v___x_1793_, lean_object* v___x_1794_, lean_object* v___x_1795_, lean_object* v_fst_1796_, lean_object* v_toPure_1797_, lean_object* v_____do__lift_1798_){
_start:
{
uint8_t v_____do__lift_14446__boxed_1799_; lean_object* v_res_1800_; 
v_____do__lift_14446__boxed_1799_ = lean_unbox(v_____do__lift_1798_);
v_res_1800_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__11(v___x_1786_, v_a_1787_, v_inst_1788_, v_toBind_1789_, v___f_1790_, v_fst_1791_, v_fst_1792_, v___x_1793_, v___x_1794_, v___x_1795_, v_fst_1796_, v_toPure_1797_, v_____do__lift_14446__boxed_1799_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12(lean_object* v_toPure_1801_, uint8_t v_addEqualities_1802_, lean_object* v_inst_1803_, lean_object* v_toBind_1804_, lean_object* v_a_1805_, lean_object* v_x_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v_snd_1808_; lean_object* v_snd_1809_; lean_object* v_snd_1810_; lean_object* v_snd_1811_; lean_object* v_fst_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1918_; 
v_snd_1808_ = lean_ctor_get(v___y_1807_, 1);
lean_inc(v_snd_1808_);
v_snd_1809_ = lean_ctor_get(v_snd_1808_, 1);
lean_inc(v_snd_1809_);
v_snd_1810_ = lean_ctor_get(v_snd_1809_, 1);
lean_inc(v_snd_1810_);
v_snd_1811_ = lean_ctor_get(v_snd_1810_, 1);
lean_inc(v_snd_1811_);
v_fst_1812_ = lean_ctor_get(v___y_1807_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___y_1807_);
if (v_isSharedCheck_1918_ == 0)
{
lean_object* v_unused_1919_; 
v_unused_1919_ = lean_ctor_get(v___y_1807_, 1);
lean_dec(v_unused_1919_);
v___x_1814_ = v___y_1807_;
v_isShared_1815_ = v_isSharedCheck_1918_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_fst_1812_);
lean_dec(v___y_1807_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1918_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v_fst_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1916_; 
v_fst_1816_ = lean_ctor_get(v_snd_1808_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v_snd_1808_);
if (v_isSharedCheck_1916_ == 0)
{
lean_object* v_unused_1917_; 
v_unused_1917_ = lean_ctor_get(v_snd_1808_, 1);
lean_dec(v_unused_1917_);
v___x_1818_ = v_snd_1808_;
v_isShared_1819_ = v_isSharedCheck_1916_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_fst_1816_);
lean_dec(v_snd_1808_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1916_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v_fst_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1914_; 
v_fst_1820_ = lean_ctor_get(v_snd_1809_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_snd_1809_);
if (v_isSharedCheck_1914_ == 0)
{
lean_object* v_unused_1915_; 
v_unused_1915_ = lean_ctor_get(v_snd_1809_, 1);
lean_dec(v_unused_1915_);
v___x_1822_ = v_snd_1809_;
v_isShared_1823_ = v_isSharedCheck_1914_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_fst_1820_);
lean_dec(v_snd_1809_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1914_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v_fst_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1912_; 
v_fst_1824_ = lean_ctor_get(v_snd_1810_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v_snd_1810_);
if (v_isSharedCheck_1912_ == 0)
{
lean_object* v_unused_1913_; 
v_unused_1913_ = lean_ctor_get(v_snd_1810_, 1);
lean_dec(v_unused_1913_);
v___x_1826_ = v_snd_1810_;
v_isShared_1827_ = v_isSharedCheck_1912_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_fst_1824_);
lean_dec(v_snd_1810_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1912_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v_array_1828_; lean_object* v_start_1829_; lean_object* v_stop_1830_; uint8_t v___x_1831_; 
v_array_1828_ = lean_ctor_get(v_snd_1811_, 0);
v_start_1829_ = lean_ctor_get(v_snd_1811_, 1);
v_stop_1830_ = lean_ctor_get(v_snd_1811_, 2);
v___x_1831_ = lean_nat_dec_lt(v_start_1829_, v_stop_1830_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1833_; 
lean_dec_ref(v_a_1805_);
lean_dec(v_toBind_1804_);
lean_dec(v_inst_1803_);
if (v_isShared_1827_ == 0)
{
v___x_1833_ = v___x_1826_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_fst_1824_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_snd_1811_);
v___x_1833_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
lean_object* v___x_1835_; 
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 1, v___x_1833_);
v___x_1835_ = v___x_1822_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_fst_1820_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
lean_object* v___x_1837_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 1, v___x_1835_);
v___x_1837_ = v___x_1818_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_fst_1816_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
lean_object* v___x_1839_; 
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 1, v___x_1837_);
v___x_1839_ = v___x_1814_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_fst_1812_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1839_);
v___x_1841_ = lean_apply_2(v_toPure_1801_, lean_box(0), v___x_1840_);
return v___x_1841_;
}
}
}
}
}
else
{
lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1908_; 
lean_inc(v_stop_1830_);
lean_inc(v_start_1829_);
lean_inc_ref(v_array_1828_);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_snd_1811_);
if (v_isSharedCheck_1908_ == 0)
{
lean_object* v_unused_1909_; lean_object* v_unused_1910_; lean_object* v_unused_1911_; 
v_unused_1909_ = lean_ctor_get(v_snd_1811_, 2);
lean_dec(v_unused_1909_);
v_unused_1910_ = lean_ctor_get(v_snd_1811_, 1);
lean_dec(v_unused_1910_);
v_unused_1911_ = lean_ctor_get(v_snd_1811_, 0);
lean_dec(v_unused_1911_);
v___x_1847_ = v_snd_1811_;
v_isShared_1848_ = v_isSharedCheck_1908_;
goto v_resetjp_1846_;
}
else
{
lean_dec(v_snd_1811_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1908_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v_array_1849_; lean_object* v_start_1850_; lean_object* v_stop_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1856_; 
v_array_1849_ = lean_ctor_get(v_fst_1824_, 0);
v_start_1850_ = lean_ctor_get(v_fst_1824_, 1);
v_stop_1851_ = lean_ctor_get(v_fst_1824_, 2);
v___x_1852_ = lean_array_fget(v_array_1828_, v_start_1829_);
v___x_1853_ = lean_unsigned_to_nat(1u);
v___x_1854_ = lean_nat_add(v_start_1829_, v___x_1853_);
lean_dec(v_start_1829_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 1, v___x_1854_);
v___x_1856_ = v___x_1847_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_array_1828_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v___x_1854_);
lean_ctor_set(v_reuseFailAlloc_1907_, 2, v_stop_1830_);
v___x_1856_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
uint8_t v___x_1857_; 
v___x_1857_ = lean_nat_dec_lt(v_start_1850_, v_stop_1851_);
if (v___x_1857_ == 0)
{
lean_object* v___x_1859_; 
lean_dec(v___x_1852_);
lean_dec_ref(v_a_1805_);
lean_dec(v_toBind_1804_);
lean_dec(v_inst_1803_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 1, v___x_1856_);
v___x_1859_ = v___x_1826_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_fst_1824_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v___x_1856_);
v___x_1859_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
lean_object* v___x_1861_; 
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 1, v___x_1859_);
v___x_1861_ = v___x_1822_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_fst_1820_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1863_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 1, v___x_1861_);
v___x_1863_ = v___x_1818_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_fst_1816_);
lean_ctor_set(v_reuseFailAlloc_1869_, 1, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1865_; 
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 1, v___x_1863_);
v___x_1865_ = v___x_1814_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_fst_1812_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1865_);
v___x_1867_ = lean_apply_2(v_toPure_1801_, lean_box(0), v___x_1866_);
return v___x_1867_;
}
}
}
}
}
else
{
lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1903_; 
lean_inc(v_stop_1851_);
lean_inc(v_start_1850_);
lean_inc_ref(v_array_1849_);
v_isSharedCheck_1903_ = !lean_is_exclusive(v_fst_1824_);
if (v_isSharedCheck_1903_ == 0)
{
lean_object* v_unused_1904_; lean_object* v_unused_1905_; lean_object* v_unused_1906_; 
v_unused_1904_ = lean_ctor_get(v_fst_1824_, 2);
lean_dec(v_unused_1904_);
v_unused_1905_ = lean_ctor_get(v_fst_1824_, 1);
lean_dec(v_unused_1905_);
v_unused_1906_ = lean_ctor_get(v_fst_1824_, 0);
lean_dec(v_unused_1906_);
v___x_1873_ = v_fst_1824_;
v_isShared_1874_ = v_isSharedCheck_1903_;
goto v_resetjp_1872_;
}
else
{
lean_dec(v_fst_1824_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1903_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1878_; 
v___x_1875_ = lean_array_fget(v_array_1849_, v_start_1850_);
v___x_1876_ = lean_nat_add(v_start_1850_, v___x_1853_);
lean_dec(v_start_1850_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 1, v___x_1876_);
v___x_1878_ = v___x_1873_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_array_1849_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v___x_1876_);
lean_ctor_set(v_reuseFailAlloc_1902_, 2, v_stop_1851_);
v___x_1878_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
if (v_addEqualities_1802_ == 0)
{
lean_dec(v___x_1875_);
lean_dec_ref(v_a_1805_);
lean_dec(v_toBind_1804_);
lean_dec(v_inst_1803_);
goto v___jp_1879_;
}
else
{
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v___f_1897_; lean_object* v___f_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
lean_del_object(v___x_1826_);
lean_del_object(v___x_1822_);
lean_del_object(v___x_1818_);
lean_del_object(v___x_1814_);
lean_inc(v_toBind_1804_);
lean_inc(v_inst_1803_);
lean_inc(v_toPure_1801_);
lean_inc_ref(v___x_1856_);
lean_inc_ref(v___x_1878_);
lean_inc(v_fst_1820_);
lean_inc(v_fst_1816_);
lean_inc(v_fst_1812_);
v___f_1897_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__10), 9, 8);
lean_closure_set(v___f_1897_, 0, v_fst_1812_);
lean_closure_set(v___f_1897_, 1, v_fst_1816_);
lean_closure_set(v___f_1897_, 2, v_fst_1820_);
lean_closure_set(v___f_1897_, 3, v___x_1878_);
lean_closure_set(v___f_1897_, 4, v___x_1856_);
lean_closure_set(v___f_1897_, 5, v_toPure_1801_);
lean_closure_set(v___f_1897_, 6, v_inst_1803_);
lean_closure_set(v___f_1897_, 7, v_toBind_1804_);
lean_inc(v_toBind_1804_);
lean_inc(v_inst_1803_);
lean_inc_ref(v_a_1805_);
v___f_1898_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_1898_, 0, v___x_1875_);
lean_closure_set(v___f_1898_, 1, v_a_1805_);
lean_closure_set(v___f_1898_, 2, v_inst_1803_);
lean_closure_set(v___f_1898_, 3, v_toBind_1804_);
lean_closure_set(v___f_1898_, 4, v___f_1897_);
lean_closure_set(v___f_1898_, 5, v_fst_1816_);
lean_closure_set(v___f_1898_, 6, v_fst_1820_);
lean_closure_set(v___f_1898_, 7, v___x_1852_);
lean_closure_set(v___f_1898_, 8, v___x_1878_);
lean_closure_set(v___f_1898_, 9, v___x_1856_);
lean_closure_set(v___f_1898_, 10, v_fst_1812_);
lean_closure_set(v___f_1898_, 11, v_toPure_1801_);
v___x_1899_ = lean_alloc_closure((void*)(l_Lean_Meta_isProof___boxed), 6, 1);
lean_closure_set(v___x_1899_, 0, v_a_1805_);
v___x_1900_ = lean_apply_2(v_inst_1803_, lean_box(0), v___x_1899_);
v___x_1901_ = lean_apply_4(v_toBind_1804_, lean_box(0), lean_box(0), v___x_1900_, v___f_1898_);
return v___x_1901_;
}
else
{
lean_dec(v___x_1875_);
lean_dec_ref(v_a_1805_);
lean_dec(v_toBind_1804_);
lean_dec(v_inst_1803_);
goto v___jp_1879_;
}
}
v___jp_1879_:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1884_; 
v___x_1880_ = lean_box(0);
v___x_1881_ = lean_array_push(v_fst_1816_, v___x_1880_);
v___x_1882_ = lean_array_push(v_fst_1820_, v___x_1852_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 1, v___x_1856_);
lean_ctor_set(v___x_1826_, 0, v___x_1878_);
v___x_1884_ = v___x_1826_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v___x_1856_);
v___x_1884_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
lean_object* v___x_1886_; 
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 1, v___x_1884_);
lean_ctor_set(v___x_1822_, 0, v___x_1882_);
v___x_1886_ = v___x_1822_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1882_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v___x_1884_);
v___x_1886_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v___x_1888_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 1, v___x_1886_);
lean_ctor_set(v___x_1818_, 0, v___x_1881_);
v___x_1888_ = v___x_1818_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1881_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1890_; 
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 1, v___x_1888_);
v___x_1890_ = v___x_1814_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_fst_1812_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
v___x_1892_ = lean_apply_2(v_toPure_1801_, lean_box(0), v___x_1891_);
return v___x_1892_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12___boxed(lean_object* v_toPure_1920_, lean_object* v_addEqualities_1921_, lean_object* v_inst_1922_, lean_object* v_toBind_1923_, lean_object* v_a_1924_, lean_object* v_x_1925_, lean_object* v___y_1926_){
_start:
{
uint8_t v_addEqualities_boxed_1927_; lean_object* v_res_1928_; 
v_addEqualities_boxed_1927_ = lean_unbox(v_addEqualities_1921_);
v_res_1928_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__12(v_toPure_1920_, v_addEqualities_boxed_1927_, v_inst_1922_, v_toBind_1923_, v_a_1924_, v_x_1925_, v___y_1926_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__13(lean_object* v_fst_1929_, lean_object* v_fst_1930_, lean_object* v_____do__lift_1931_, lean_object* v_toPure_1932_, lean_object* v_____do__lift_1933_){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1934_, 0, v_fst_1929_);
lean_ctor_set(v___x_1934_, 1, v_fst_1930_);
v___x_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1935_, 0, v_____do__lift_1933_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
v___x_1936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1936_, 0, v_____do__lift_1931_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
v___x_1937_ = lean_apply_2(v_toPure_1932_, lean_box(0), v___x_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__14(lean_object* v_fst_1938_, lean_object* v_fst_1939_, lean_object* v_toPure_1940_, lean_object* v_fst_1941_, lean_object* v_inst_1942_, lean_object* v_toBind_1943_, lean_object* v_____do__lift_1944_){
_start:
{
lean_object* v___f_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___f_1945_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__13), 5, 4);
lean_closure_set(v___f_1945_, 0, v_fst_1938_);
lean_closure_set(v___f_1945_, 1, v_fst_1939_);
lean_closure_set(v___f_1945_, 2, v_____do__lift_1944_);
lean_closure_set(v___f_1945_, 3, v_toPure_1940_);
v___x_1946_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1946_, 0, v_fst_1941_);
v___x_1947_ = lean_apply_2(v_inst_1942_, lean_box(0), v___x_1946_);
v___x_1948_ = lean_apply_4(v_toBind_1943_, lean_box(0), lean_box(0), v___x_1947_, v___f_1945_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__15(lean_object* v_toPure_1949_, lean_object* v_inst_1950_, lean_object* v_toBind_1951_, lean_object* v_motiveArgs_1952_, lean_object* v_____s_1953_){
_start:
{
lean_object* v_snd_1954_; lean_object* v_snd_1955_; lean_object* v_fst_1956_; lean_object* v_fst_1957_; lean_object* v_fst_1958_; lean_object* v___f_1959_; uint8_t v___x_1960_; uint8_t v___x_1961_; uint8_t v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v_snd_1954_ = lean_ctor_get(v_____s_1953_, 1);
lean_inc(v_snd_1954_);
v_snd_1955_ = lean_ctor_get(v_snd_1954_, 1);
lean_inc(v_snd_1955_);
v_fst_1956_ = lean_ctor_get(v_____s_1953_, 0);
lean_inc(v_fst_1956_);
lean_dec_ref(v_____s_1953_);
v_fst_1957_ = lean_ctor_get(v_snd_1954_, 0);
lean_inc(v_fst_1957_);
lean_dec(v_snd_1954_);
v_fst_1958_ = lean_ctor_get(v_snd_1955_, 0);
lean_inc(v_fst_1958_);
lean_dec(v_snd_1955_);
lean_inc(v_toBind_1951_);
lean_inc(v_inst_1950_);
lean_inc(v_fst_1956_);
v___f_1959_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14), 7, 6);
lean_closure_set(v___f_1959_, 0, v_fst_1957_);
lean_closure_set(v___f_1959_, 1, v_fst_1958_);
lean_closure_set(v___f_1959_, 2, v_toPure_1949_);
lean_closure_set(v___f_1959_, 3, v_fst_1956_);
lean_closure_set(v___f_1959_, 4, v_inst_1950_);
lean_closure_set(v___f_1959_, 5, v_toBind_1951_);
v___x_1960_ = 0;
v___x_1961_ = 1;
v___x_1962_ = 1;
v___x_1963_ = lean_box(v___x_1960_);
v___x_1964_ = lean_box(v___x_1961_);
v___x_1965_ = lean_box(v___x_1960_);
v___x_1966_ = lean_box(v___x_1961_);
v___x_1967_ = lean_box(v___x_1962_);
v___x_1968_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1968_, 0, v_motiveArgs_1952_);
lean_closure_set(v___x_1968_, 1, v_fst_1956_);
lean_closure_set(v___x_1968_, 2, v___x_1963_);
lean_closure_set(v___x_1968_, 3, v___x_1964_);
lean_closure_set(v___x_1968_, 4, v___x_1965_);
lean_closure_set(v___x_1968_, 5, v___x_1966_);
lean_closure_set(v___x_1968_, 6, v___x_1967_);
v___x_1969_ = lean_apply_2(v_inst_1950_, lean_box(0), v___x_1968_);
v___x_1970_ = lean_apply_4(v_toBind_1951_, lean_box(0), lean_box(0), v___x_1969_, v___f_1959_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__16(lean_object* v_toMatcherInfo_1973_, lean_object* v_discrs_x27_1974_, lean_object* v_motiveArgs_1975_, lean_object* v_inst_1976_, lean_object* v___f_1977_, lean_object* v_toBind_1978_, lean_object* v___f_1979_, lean_object* v_motiveBody_x27_1980_){
_start:
{
lean_object* v_discrInfos_1981_; lean_object* v___x_1982_; lean_object* v_addHEqualities_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; size_t v_sz_1992_; size_t v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v_discrInfos_1981_ = lean_ctor_get(v_toMatcherInfo_1973_, 4);
lean_inc_ref(v_discrInfos_1981_);
lean_dec_ref(v_toMatcherInfo_1973_);
v___x_1982_ = lean_unsigned_to_nat(0u);
v_addHEqualities_1983_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___closed__0));
v___x_1984_ = lean_array_get_size(v_discrs_x27_1974_);
v___x_1985_ = l_Array_toSubarray___redArg(v_discrs_x27_1974_, v___x_1982_, v___x_1984_);
v___x_1986_ = lean_array_get_size(v_discrInfos_1981_);
v___x_1987_ = l_Array_toSubarray___redArg(v_discrInfos_1981_, v___x_1982_, v___x_1986_);
v___x_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1985_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1989_, 0, v_addHEqualities_1983_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1990_, 0, v_addHEqualities_1983_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
v___x_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1991_, 0, v_motiveBody_x27_1980_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v_sz_1992_ = lean_array_size(v_motiveArgs_1975_);
v___x_1993_ = ((size_t)0ULL);
v___x_1994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1976_, v_motiveArgs_1975_, v___f_1977_, v_sz_1992_, v___x_1993_, v___x_1991_);
v___x_1995_ = lean_apply_4(v_toBind_1978_, lean_box(0), lean_box(0), v___x_1994_, v___f_1979_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__17(lean_object* v_onMotive_1996_, lean_object* v_motiveArgs_1997_, lean_object* v_motiveBody_1998_, lean_object* v_toBind_1999_, lean_object* v___f_2000_, lean_object* v_____r_2001_){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = lean_apply_2(v_onMotive_1996_, v_motiveArgs_1997_, v_motiveBody_1998_);
v___x_2003_ = lean_apply_4(v_toBind_1999_, lean_box(0), lean_box(0), v___x_2002_, v___f_2000_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__18(lean_object* v___f_2004_, lean_object* v_____r_2005_){
_start:
{
lean_object* v___x_2006_; 
v___x_2006_ = lean_apply_1(v___f_2004_, v_____r_2005_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19(lean_object* v_toPure_2007_, lean_object* v_inst_2008_, lean_object* v_toBind_2009_, lean_object* v_toMatcherInfo_2010_, lean_object* v_discrs_x27_2011_, lean_object* v_inst_2012_, lean_object* v___f_2013_, lean_object* v_onMotive_2014_, lean_object* v_discrs_2015_, lean_object* v_inst_2016_, lean_object* v_motiveArgs_2017_, lean_object* v_motiveBody_2018_){
_start:
{
lean_object* v___f_2019_; lean_object* v___f_2020_; lean_object* v___f_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; 
lean_inc_ref(v_motiveArgs_2017_);
lean_inc(v_toBind_2009_);
v___f_2019_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__15), 5, 4);
lean_closure_set(v___f_2019_, 0, v_toPure_2007_);
lean_closure_set(v___f_2019_, 1, v_inst_2008_);
lean_closure_set(v___f_2019_, 2, v_toBind_2009_);
lean_closure_set(v___f_2019_, 3, v_motiveArgs_2017_);
lean_inc(v_toBind_2009_);
lean_inc_ref(v_inst_2012_);
lean_inc_ref(v_motiveArgs_2017_);
v___f_2020_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16), 8, 7);
lean_closure_set(v___f_2020_, 0, v_toMatcherInfo_2010_);
lean_closure_set(v___f_2020_, 1, v_discrs_x27_2011_);
lean_closure_set(v___f_2020_, 2, v_motiveArgs_2017_);
lean_closure_set(v___f_2020_, 3, v_inst_2012_);
lean_closure_set(v___f_2020_, 4, v___f_2013_);
lean_closure_set(v___f_2020_, 5, v_toBind_2009_);
lean_closure_set(v___f_2020_, 6, v___f_2019_);
lean_inc_ref(v___f_2020_);
lean_inc(v_toBind_2009_);
lean_inc_ref(v_motiveBody_2018_);
lean_inc_ref(v_motiveArgs_2017_);
lean_inc(v_onMotive_2014_);
v___f_2021_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__17), 6, 5);
lean_closure_set(v___f_2021_, 0, v_onMotive_2014_);
lean_closure_set(v___f_2021_, 1, v_motiveArgs_2017_);
lean_closure_set(v___f_2021_, 2, v_motiveBody_2018_);
lean_closure_set(v___f_2021_, 3, v_toBind_2009_);
lean_closure_set(v___f_2021_, 4, v___f_2020_);
v___x_2022_ = lean_array_get_size(v_motiveArgs_2017_);
v___x_2023_ = lean_array_get_size(v_discrs_2015_);
v___x_2024_ = lean_nat_dec_eq(v___x_2022_, v___x_2023_);
if (v___x_2024_ == 0)
{
lean_object* v___f_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
lean_dec_ref(v___f_2020_);
lean_dec_ref(v_motiveBody_2018_);
lean_dec_ref(v_motiveArgs_2017_);
lean_dec(v_onMotive_2014_);
v___f_2025_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__18), 2, 1);
lean_closure_set(v___f_2025_, 0, v___f_2021_);
v___x_2026_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_2027_ = l_Nat_reprFast(v___x_2023_);
v___x_2028_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2027_);
v___x_2029_ = l_Lean_MessageData_ofFormat(v___x_2028_);
v___x_2030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2026_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_2032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2030_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
v___x_2033_ = l_Lean_throwError___redArg(v_inst_2012_, v_inst_2016_, v___x_2032_);
v___x_2034_ = lean_apply_4(v_toBind_2009_, lean_box(0), lean_box(0), v___x_2033_, v___f_2025_);
return v___x_2034_;
}
else
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
lean_dec_ref(v___f_2021_);
lean_dec_ref(v_inst_2016_);
lean_dec_ref(v_inst_2012_);
v___x_2035_ = lean_box(0);
v___x_2036_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__17(v_onMotive_2014_, v_motiveArgs_2017_, v_motiveBody_2018_, v_toBind_2009_, v___f_2020_, v___x_2035_);
return v___x_2036_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19___boxed(lean_object* v_toPure_2037_, lean_object* v_inst_2038_, lean_object* v_toBind_2039_, lean_object* v_toMatcherInfo_2040_, lean_object* v_discrs_x27_2041_, lean_object* v_inst_2042_, lean_object* v___f_2043_, lean_object* v_onMotive_2044_, lean_object* v_discrs_2045_, lean_object* v_inst_2046_, lean_object* v_motiveArgs_2047_, lean_object* v_motiveBody_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__19(v_toPure_2037_, v_inst_2038_, v_toBind_2039_, v_toMatcherInfo_2040_, v_discrs_x27_2041_, v_inst_2042_, v___f_2043_, v_onMotive_2044_, v_discrs_2045_, v_inst_2046_, v_motiveArgs_2047_, v_motiveBody_2048_);
lean_dec_ref(v_discrs_2045_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20(lean_object* v_fst_2050_, lean_object* v_numParams_2051_, lean_object* v_numDiscrs_2052_, lean_object* v_altInfos_2053_, lean_object* v_uElimPos_x3f_2054_, lean_object* v_snd_2055_, lean_object* v_overlaps_2056_, lean_object* v_matcherName_2057_, lean_object* v_matcherLevels_2058_, lean_object* v_params_x27_2059_, lean_object* v_fst_2060_, lean_object* v_discrs_x27_2061_, lean_object* v_fst_2062_, lean_object* v_toPure_2063_, lean_object* v_____do__lift_2064_){
_start:
{
lean_object* v_remaining_x27_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v_remaining_x27_2065_ = l_Array_append___redArg(v_fst_2050_, v_____do__lift_2064_);
v___x_2066_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2066_, 0, v_numParams_2051_);
lean_ctor_set(v___x_2066_, 1, v_numDiscrs_2052_);
lean_ctor_set(v___x_2066_, 2, v_altInfos_2053_);
lean_ctor_set(v___x_2066_, 3, v_uElimPos_x3f_2054_);
lean_ctor_set(v___x_2066_, 4, v_snd_2055_);
lean_ctor_set(v___x_2066_, 5, v_overlaps_2056_);
v___x_2067_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
lean_ctor_set(v___x_2067_, 1, v_matcherName_2057_);
lean_ctor_set(v___x_2067_, 2, v_matcherLevels_2058_);
lean_ctor_set(v___x_2067_, 3, v_params_x27_2059_);
lean_ctor_set(v___x_2067_, 4, v_fst_2060_);
lean_ctor_set(v___x_2067_, 5, v_discrs_x27_2061_);
lean_ctor_set(v___x_2067_, 6, v_fst_2062_);
lean_ctor_set(v___x_2067_, 7, v_remaining_x27_2065_);
v___x_2068_ = lean_apply_2(v_toPure_2063_, lean_box(0), v___x_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20___boxed(lean_object* v_fst_2069_, lean_object* v_numParams_2070_, lean_object* v_numDiscrs_2071_, lean_object* v_altInfos_2072_, lean_object* v_uElimPos_x3f_2073_, lean_object* v_snd_2074_, lean_object* v_overlaps_2075_, lean_object* v_matcherName_2076_, lean_object* v_matcherLevels_2077_, lean_object* v_params_x27_2078_, lean_object* v_fst_2079_, lean_object* v_discrs_x27_2080_, lean_object* v_fst_2081_, lean_object* v_toPure_2082_, lean_object* v_____do__lift_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__20(v_fst_2069_, v_numParams_2070_, v_numDiscrs_2071_, v_altInfos_2072_, v_uElimPos_x3f_2073_, v_snd_2074_, v_overlaps_2075_, v_matcherName_2076_, v_matcherLevels_2077_, v_params_x27_2078_, v_fst_2079_, v_discrs_x27_2080_, v_fst_2081_, v_toPure_2082_, v_____do__lift_2083_);
lean_dec_ref(v_____do__lift_2083_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21(lean_object* v_fst_2085_, lean_object* v_numParams_2086_, lean_object* v_numDiscrs_2087_, lean_object* v_altInfos_2088_, lean_object* v_uElimPos_x3f_2089_, lean_object* v_snd_2090_, lean_object* v_overlaps_2091_, lean_object* v_matcherName_2092_, lean_object* v_matcherLevels_2093_, lean_object* v_params_x27_2094_, lean_object* v_fst_2095_, lean_object* v_discrs_x27_2096_, lean_object* v_toPure_2097_, lean_object* v_onRemaining_2098_, lean_object* v_remaining_2099_, lean_object* v_toBind_2100_, lean_object* v_____s_2101_){
_start:
{
lean_object* v_fst_2102_; lean_object* v___f_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v_fst_2102_ = lean_ctor_get(v_____s_2101_, 0);
lean_inc(v_fst_2102_);
lean_dec_ref(v_____s_2101_);
v___f_2103_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__20___boxed), 15, 14);
lean_closure_set(v___f_2103_, 0, v_fst_2085_);
lean_closure_set(v___f_2103_, 1, v_numParams_2086_);
lean_closure_set(v___f_2103_, 2, v_numDiscrs_2087_);
lean_closure_set(v___f_2103_, 3, v_altInfos_2088_);
lean_closure_set(v___f_2103_, 4, v_uElimPos_x3f_2089_);
lean_closure_set(v___f_2103_, 5, v_snd_2090_);
lean_closure_set(v___f_2103_, 6, v_overlaps_2091_);
lean_closure_set(v___f_2103_, 7, v_matcherName_2092_);
lean_closure_set(v___f_2103_, 8, v_matcherLevels_2093_);
lean_closure_set(v___f_2103_, 9, v_params_x27_2094_);
lean_closure_set(v___f_2103_, 10, v_fst_2095_);
lean_closure_set(v___f_2103_, 11, v_discrs_x27_2096_);
lean_closure_set(v___f_2103_, 12, v_fst_2102_);
lean_closure_set(v___f_2103_, 13, v_toPure_2097_);
v___x_2104_ = lean_apply_1(v_onRemaining_2098_, v_remaining_2099_);
v___x_2105_ = lean_apply_4(v_toBind_2100_, lean_box(0), lean_box(0), v___x_2104_, v___f_2103_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed(lean_object** _args){
lean_object* v_fst_2106_ = _args[0];
lean_object* v_numParams_2107_ = _args[1];
lean_object* v_numDiscrs_2108_ = _args[2];
lean_object* v_altInfos_2109_ = _args[3];
lean_object* v_uElimPos_x3f_2110_ = _args[4];
lean_object* v_snd_2111_ = _args[5];
lean_object* v_overlaps_2112_ = _args[6];
lean_object* v_matcherName_2113_ = _args[7];
lean_object* v_matcherLevels_2114_ = _args[8];
lean_object* v_params_x27_2115_ = _args[9];
lean_object* v_fst_2116_ = _args[10];
lean_object* v_discrs_x27_2117_ = _args[11];
lean_object* v_toPure_2118_ = _args[12];
lean_object* v_onRemaining_2119_ = _args[13];
lean_object* v_remaining_2120_ = _args[14];
lean_object* v_toBind_2121_ = _args[15];
lean_object* v_____s_2122_ = _args[16];
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__21(v_fst_2106_, v_numParams_2107_, v_numDiscrs_2108_, v_altInfos_2109_, v_uElimPos_x3f_2110_, v_snd_2111_, v_overlaps_2112_, v_matcherName_2113_, v_matcherLevels_2114_, v_params_x27_2115_, v_fst_2116_, v_discrs_x27_2117_, v_toPure_2118_, v_onRemaining_2119_, v_remaining_2120_, v_toBind_2121_, v_____s_2122_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22(lean_object* v_toPure_2124_, lean_object* v_next_2125_, lean_object* v_G_2126_, lean_object* v_____do__lift_2127_){
_start:
{
if (lean_obj_tag(v_____do__lift_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v___x_2129_; 
lean_dec(v_G_2126_);
v_a_2128_ = lean_ctor_get(v_____do__lift_2127_, 0);
lean_inc(v_a_2128_);
lean_dec_ref(v_____do__lift_2127_);
v___x_2129_ = lean_apply_2(v_toPure_2124_, lean_box(0), v_a_2128_);
return v___x_2129_;
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
lean_dec(v_toPure_2124_);
v_a_2130_ = lean_ctor_get(v_____do__lift_2127_, 0);
lean_inc(v_a_2130_);
lean_dec_ref(v_____do__lift_2127_);
v___x_2131_ = lean_unsigned_to_nat(1u);
v___x_2132_ = lean_nat_add(v_next_2125_, v___x_2131_);
v___x_2133_ = lean_apply_4(v_G_2126_, v___x_2132_, v_a_2130_, lean_box(0), lean_box(0));
return v___x_2133_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22___boxed(lean_object* v_toPure_2134_, lean_object* v_next_2135_, lean_object* v_G_2136_, lean_object* v_____do__lift_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__22(v_toPure_2134_, v_next_2135_, v_G_2136_, v_____do__lift_2137_);
lean_dec(v_next_2135_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23(lean_object* v_xs_2139_, lean_object* v_ys4_2140_, uint8_t v___x_2141_, uint8_t v___x_2142_, lean_object* v_inst_2143_, lean_object* v_alt_x27_2144_){
_start:
{
lean_object* v___x_2145_; uint8_t v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2145_ = l_Array_append___redArg(v_xs_2139_, v_ys4_2140_);
v___x_2146_ = 1;
v___x_2147_ = lean_box(v___x_2141_);
v___x_2148_ = lean_box(v___x_2142_);
v___x_2149_ = lean_box(v___x_2141_);
v___x_2150_ = lean_box(v___x_2142_);
v___x_2151_ = lean_box(v___x_2146_);
v___x_2152_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_2152_, 0, v___x_2145_);
lean_closure_set(v___x_2152_, 1, v_alt_x27_2144_);
lean_closure_set(v___x_2152_, 2, v___x_2147_);
lean_closure_set(v___x_2152_, 3, v___x_2148_);
lean_closure_set(v___x_2152_, 4, v___x_2149_);
lean_closure_set(v___x_2152_, 5, v___x_2150_);
lean_closure_set(v___x_2152_, 6, v___x_2151_);
v___x_2153_ = lean_apply_2(v_inst_2143_, lean_box(0), v___x_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed(lean_object* v_xs_2154_, lean_object* v_ys4_2155_, lean_object* v___x_2156_, lean_object* v___x_2157_, lean_object* v_inst_2158_, lean_object* v_alt_x27_2159_){
_start:
{
uint8_t v___x_14891__boxed_2160_; uint8_t v___x_14892__boxed_2161_; lean_object* v_res_2162_; 
v___x_14891__boxed_2160_ = lean_unbox(v___x_2156_);
v___x_14892__boxed_2161_ = lean_unbox(v___x_2157_);
v_res_2162_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__23(v_xs_2154_, v_ys4_2155_, v___x_14891__boxed_2160_, v___x_14892__boxed_2161_, v_inst_2158_, v_alt_x27_2159_);
lean_dec_ref(v_ys4_2155_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__24(lean_object* v_onAlt_2163_, lean_object* v_next_2164_, lean_object* v_altType_2165_, lean_object* v_xs_2166_, lean_object* v_toBind_2167_, lean_object* v___f_2168_, lean_object* v_alt_2169_){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = lean_apply_4(v_onAlt_2163_, v_next_2164_, v_altType_2165_, v_xs_2166_, v_alt_2169_);
v___x_2171_ = lean_apply_4(v_toBind_2167_, lean_box(0), lean_box(0), v___x_2170_, v___f_2168_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25(lean_object* v___x_2172_, lean_object* v_xs_2173_, lean_object* v_inst_2174_, lean_object* v_toBind_2175_, lean_object* v___f_2176_, lean_object* v_inst_2177_, lean_object* v_inst_2178_, lean_object* v_names_2179_){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
lean_inc_ref(v_xs_2173_);
v___x_2180_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLambda___boxed), 7, 2);
lean_closure_set(v___x_2180_, 0, v___x_2172_);
lean_closure_set(v___x_2180_, 1, v_xs_2173_);
v___x_2181_ = lean_apply_2(v_inst_2174_, lean_box(0), v___x_2180_);
v___x_2182_ = lean_apply_4(v_toBind_2175_, lean_box(0), lean_box(0), v___x_2181_, v___f_2176_);
v___x_2183_ = l_Lean_Meta_MatcherApp_withUserNames___redArg(v_inst_2177_, v_inst_2178_, v_xs_2173_, v_names_2179_, v___x_2182_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26(lean_object* v_xs_2184_, uint8_t v___x_2185_, uint8_t v___x_2186_, lean_object* v_inst_2187_, lean_object* v_onAlt_2188_, lean_object* v_next_2189_, lean_object* v_toBind_2190_, lean_object* v___x_2191_, lean_object* v_inst_2192_, lean_object* v_inst_2193_, lean_object* v___f_2194_, lean_object* v_ys4_2195_, lean_object* v_altType_2196_){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___f_2199_; lean_object* v___f_2200_; lean_object* v___f_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2197_ = lean_box(v___x_2185_);
v___x_2198_ = lean_box(v___x_2186_);
lean_inc(v_inst_2187_);
lean_inc_ref(v_xs_2184_);
v___f_2199_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed), 6, 5);
lean_closure_set(v___f_2199_, 0, v_xs_2184_);
lean_closure_set(v___f_2199_, 1, v_ys4_2195_);
lean_closure_set(v___f_2199_, 2, v___x_2197_);
lean_closure_set(v___f_2199_, 3, v___x_2198_);
lean_closure_set(v___f_2199_, 4, v_inst_2187_);
lean_inc(v_toBind_2190_);
lean_inc_ref(v_xs_2184_);
v___f_2200_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__24), 7, 6);
lean_closure_set(v___f_2200_, 0, v_onAlt_2188_);
lean_closure_set(v___f_2200_, 1, v_next_2189_);
lean_closure_set(v___f_2200_, 2, v_altType_2196_);
lean_closure_set(v___f_2200_, 3, v_xs_2184_);
lean_closure_set(v___f_2200_, 4, v_toBind_2190_);
lean_closure_set(v___f_2200_, 5, v___f_2199_);
lean_inc_ref(v_inst_2193_);
lean_inc_ref(v_inst_2192_);
lean_inc(v_toBind_2190_);
lean_inc_ref(v___x_2191_);
v___f_2201_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__25), 8, 7);
lean_closure_set(v___f_2201_, 0, v___x_2191_);
lean_closure_set(v___f_2201_, 1, v_xs_2184_);
lean_closure_set(v___f_2201_, 2, v_inst_2187_);
lean_closure_set(v___f_2201_, 3, v_toBind_2190_);
lean_closure_set(v___f_2201_, 4, v___f_2200_);
lean_closure_set(v___f_2201_, 5, v_inst_2192_);
lean_closure_set(v___f_2201_, 6, v_inst_2193_);
v___x_2202_ = l_Lean_Meta_lambdaTelescope___redArg(v_inst_2192_, v_inst_2193_, v___x_2191_, v___f_2194_, v___x_2185_);
v___x_2203_ = lean_apply_4(v_toBind_2190_, lean_box(0), lean_box(0), v___x_2202_, v___f_2201_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed(lean_object* v_xs_2204_, lean_object* v___x_2205_, lean_object* v___x_2206_, lean_object* v_inst_2207_, lean_object* v_onAlt_2208_, lean_object* v_next_2209_, lean_object* v_toBind_2210_, lean_object* v___x_2211_, lean_object* v_inst_2212_, lean_object* v_inst_2213_, lean_object* v___f_2214_, lean_object* v_ys4_2215_, lean_object* v_altType_2216_){
_start:
{
uint8_t v___x_14942__boxed_2217_; uint8_t v___x_14943__boxed_2218_; lean_object* v_res_2219_; 
v___x_14942__boxed_2217_ = lean_unbox(v___x_2205_);
v___x_14943__boxed_2218_ = lean_unbox(v___x_2206_);
v_res_2219_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__26(v_xs_2204_, v___x_14942__boxed_2217_, v___x_14943__boxed_2218_, v_inst_2207_, v_onAlt_2208_, v_next_2209_, v_toBind_2210_, v___x_2211_, v_inst_2212_, v_inst_2213_, v___f_2214_, v_ys4_2215_, v_altType_2216_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27(uint8_t v___x_2220_, uint8_t v___x_2221_, lean_object* v_inst_2222_, lean_object* v_onAlt_2223_, lean_object* v_next_2224_, lean_object* v_toBind_2225_, lean_object* v___x_2226_, lean_object* v_inst_2227_, lean_object* v_inst_2228_, lean_object* v___f_2229_, lean_object* v_fst_2230_, lean_object* v_xs_2231_, lean_object* v_altType_2232_){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___f_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2233_ = lean_box(v___x_2220_);
v___x_2234_ = lean_box(v___x_2221_);
lean_inc_ref(v_inst_2228_);
lean_inc_ref(v_inst_2227_);
v___f_2235_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed), 13, 11);
lean_closure_set(v___f_2235_, 0, v_xs_2231_);
lean_closure_set(v___f_2235_, 1, v___x_2233_);
lean_closure_set(v___f_2235_, 2, v___x_2234_);
lean_closure_set(v___f_2235_, 3, v_inst_2222_);
lean_closure_set(v___f_2235_, 4, v_onAlt_2223_);
lean_closure_set(v___f_2235_, 5, v_next_2224_);
lean_closure_set(v___f_2235_, 6, v_toBind_2225_);
lean_closure_set(v___f_2235_, 7, v___x_2226_);
lean_closure_set(v___f_2235_, 8, v_inst_2227_);
lean_closure_set(v___f_2235_, 9, v_inst_2228_);
lean_closure_set(v___f_2235_, 10, v___f_2229_);
v___x_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2236_, 0, v_fst_2230_);
v___x_2237_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2227_, v_inst_2228_, v_altType_2232_, v___x_2236_, v___f_2235_, v___x_2220_, v___x_2220_);
return v___x_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed(lean_object* v___x_2238_, lean_object* v___x_2239_, lean_object* v_inst_2240_, lean_object* v_onAlt_2241_, lean_object* v_next_2242_, lean_object* v_toBind_2243_, lean_object* v___x_2244_, lean_object* v_inst_2245_, lean_object* v_inst_2246_, lean_object* v___f_2247_, lean_object* v_fst_2248_, lean_object* v_xs_2249_, lean_object* v_altType_2250_){
_start:
{
uint8_t v___x_14977__boxed_2251_; uint8_t v___x_14978__boxed_2252_; lean_object* v_res_2253_; 
v___x_14977__boxed_2251_ = lean_unbox(v___x_2238_);
v___x_14978__boxed_2252_ = lean_unbox(v___x_2239_);
v_res_2253_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__27(v___x_14977__boxed_2251_, v___x_14978__boxed_2252_, v_inst_2240_, v_onAlt_2241_, v_next_2242_, v_toBind_2243_, v___x_2244_, v_inst_2245_, v_inst_2246_, v___f_2247_, v_fst_2248_, v_xs_2249_, v_altType_2250_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29(lean_object* v___x_2266_, lean_object* v_toPure_2267_, lean_object* v_toBind_2268_, lean_object* v___f_2269_, uint8_t v___x_2270_, uint8_t v___x_2271_, lean_object* v_inst_2272_, lean_object* v_onAlt_2273_, lean_object* v_inst_2274_, lean_object* v_inst_2275_, lean_object* v___f_2276_, lean_object* v_fst_2277_, lean_object* v_next_2278_, lean_object* v_acc_2279_, lean_object* v_h_2280_, lean_object* v_G_2281_){
_start:
{
uint8_t v___x_2282_; 
v___x_2282_ = lean_nat_dec_lt(v_next_2278_, v___x_2266_);
if (v___x_2282_ == 0)
{
lean_object* v___x_2283_; 
lean_dec(v_G_2281_);
lean_dec(v_next_2278_);
lean_dec(v_fst_2277_);
lean_dec(v___f_2276_);
lean_dec_ref(v_inst_2275_);
lean_dec_ref(v_inst_2274_);
lean_dec(v_onAlt_2273_);
lean_dec(v_inst_2272_);
lean_dec(v___f_2269_);
lean_dec(v_toBind_2268_);
v___x_2283_ = lean_apply_2(v_toPure_2267_, lean_box(0), v_acc_2279_);
return v___x_2283_;
}
else
{
lean_object* v_snd_2284_; lean_object* v_snd_2285_; lean_object* v_snd_2286_; lean_object* v_fst_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2397_; 
v_snd_2284_ = lean_ctor_get(v_acc_2279_, 1);
lean_inc(v_snd_2284_);
v_snd_2285_ = lean_ctor_get(v_snd_2284_, 1);
lean_inc(v_snd_2285_);
v_snd_2286_ = lean_ctor_get(v_snd_2285_, 1);
lean_inc(v_snd_2286_);
v_fst_2287_ = lean_ctor_get(v_acc_2279_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_acc_2279_);
if (v_isSharedCheck_2397_ == 0)
{
lean_object* v_unused_2398_; 
v_unused_2398_ = lean_ctor_get(v_acc_2279_, 1);
lean_dec(v_unused_2398_);
v___x_2289_ = v_acc_2279_;
v_isShared_2290_ = v_isSharedCheck_2397_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_fst_2287_);
lean_dec(v_acc_2279_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2397_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v_fst_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2395_; 
v_fst_2291_ = lean_ctor_get(v_snd_2284_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v_snd_2284_);
if (v_isSharedCheck_2395_ == 0)
{
lean_object* v_unused_2396_; 
v_unused_2396_ = lean_ctor_get(v_snd_2284_, 1);
lean_dec(v_unused_2396_);
v___x_2293_ = v_snd_2284_;
v_isShared_2294_ = v_isSharedCheck_2395_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_fst_2291_);
lean_dec(v_snd_2284_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2395_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v_fst_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2393_; 
v_fst_2295_ = lean_ctor_get(v_snd_2285_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v_snd_2285_);
if (v_isSharedCheck_2393_ == 0)
{
lean_object* v_unused_2394_; 
v_unused_2394_ = lean_ctor_get(v_snd_2285_, 1);
lean_dec(v_unused_2394_);
v___x_2297_ = v_snd_2285_;
v_isShared_2298_ = v_isSharedCheck_2393_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_fst_2295_);
lean_dec(v_snd_2285_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2393_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v_array_2299_; lean_object* v_start_2300_; lean_object* v_stop_2301_; lean_object* v___f_2302_; lean_object* v___y_2304_; uint8_t v___x_2307_; 
v_array_2299_ = lean_ctor_get(v_snd_2286_, 0);
v_start_2300_ = lean_ctor_get(v_snd_2286_, 1);
v_stop_2301_ = lean_ctor_get(v_snd_2286_, 2);
lean_inc(v_next_2278_);
lean_inc(v_toPure_2267_);
v___f_2302_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__22___boxed), 4, 3);
lean_closure_set(v___f_2302_, 0, v_toPure_2267_);
lean_closure_set(v___f_2302_, 1, v_next_2278_);
lean_closure_set(v___f_2302_, 2, v_G_2281_);
v___x_2307_ = lean_nat_dec_lt(v_start_2300_, v_stop_2301_);
if (v___x_2307_ == 0)
{
lean_object* v___x_2309_; 
lean_dec(v_next_2278_);
lean_dec(v_fst_2277_);
lean_dec(v___f_2276_);
lean_dec_ref(v_inst_2275_);
lean_dec_ref(v_inst_2274_);
lean_dec(v_onAlt_2273_);
lean_dec(v_inst_2272_);
if (v_isShared_2298_ == 0)
{
v___x_2309_ = v___x_2297_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_fst_2295_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v_snd_2286_);
v___x_2309_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
lean_object* v___x_2311_; 
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 1, v___x_2309_);
v___x_2311_ = v___x_2293_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_fst_2291_);
lean_ctor_set(v_reuseFailAlloc_2317_, 1, v___x_2309_);
v___x_2311_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
lean_object* v___x_2313_; 
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 1, v___x_2311_);
v___x_2313_ = v___x_2289_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_fst_2287_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2313_);
v___x_2315_ = lean_apply_2(v_toPure_2267_, lean_box(0), v___x_2314_);
v___y_2304_ = v___x_2315_;
goto v___jp_2303_;
}
}
}
}
else
{
lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2389_; 
lean_inc(v_stop_2301_);
lean_inc(v_start_2300_);
lean_inc_ref(v_array_2299_);
v_isSharedCheck_2389_ = !lean_is_exclusive(v_snd_2286_);
if (v_isSharedCheck_2389_ == 0)
{
lean_object* v_unused_2390_; lean_object* v_unused_2391_; lean_object* v_unused_2392_; 
v_unused_2390_ = lean_ctor_get(v_snd_2286_, 2);
lean_dec(v_unused_2390_);
v_unused_2391_ = lean_ctor_get(v_snd_2286_, 1);
lean_dec(v_unused_2391_);
v_unused_2392_ = lean_ctor_get(v_snd_2286_, 0);
lean_dec(v_unused_2392_);
v___x_2320_ = v_snd_2286_;
v_isShared_2321_ = v_isSharedCheck_2389_;
goto v_resetjp_2319_;
}
else
{
lean_dec(v_snd_2286_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2389_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v_array_2322_; lean_object* v_start_2323_; lean_object* v_stop_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2329_; 
v_array_2322_ = lean_ctor_get(v_fst_2295_, 0);
v_start_2323_ = lean_ctor_get(v_fst_2295_, 1);
v_stop_2324_ = lean_ctor_get(v_fst_2295_, 2);
v___x_2325_ = lean_array_fget(v_array_2299_, v_start_2300_);
v___x_2326_ = lean_unsigned_to_nat(1u);
v___x_2327_ = lean_nat_add(v_start_2300_, v___x_2326_);
lean_dec(v_start_2300_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 1, v___x_2327_);
v___x_2329_ = v___x_2320_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_array_2299_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v___x_2327_);
lean_ctor_set(v_reuseFailAlloc_2388_, 2, v_stop_2301_);
v___x_2329_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
uint8_t v___x_2330_; 
v___x_2330_ = lean_nat_dec_lt(v_start_2323_, v_stop_2324_);
if (v___x_2330_ == 0)
{
lean_object* v___x_2332_; 
lean_dec(v___x_2325_);
lean_dec(v_next_2278_);
lean_dec(v_fst_2277_);
lean_dec(v___f_2276_);
lean_dec_ref(v_inst_2275_);
lean_dec_ref(v_inst_2274_);
lean_dec(v_onAlt_2273_);
lean_dec(v_inst_2272_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 1, v___x_2329_);
v___x_2332_ = v___x_2297_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_fst_2295_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v___x_2329_);
v___x_2332_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
lean_object* v___x_2334_; 
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 1, v___x_2332_);
v___x_2334_ = v___x_2293_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_fst_2291_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v___x_2332_);
v___x_2334_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
lean_object* v___x_2336_; 
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 1, v___x_2334_);
v___x_2336_ = v___x_2289_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_fst_2287_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v___x_2334_);
v___x_2336_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
v___x_2338_ = lean_apply_2(v_toPure_2267_, lean_box(0), v___x_2337_);
v___y_2304_ = v___x_2338_;
goto v___jp_2303_;
}
}
}
}
else
{
lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2384_; 
lean_inc(v_stop_2324_);
lean_inc(v_start_2323_);
lean_inc_ref(v_array_2322_);
v_isSharedCheck_2384_ = !lean_is_exclusive(v_fst_2295_);
if (v_isSharedCheck_2384_ == 0)
{
lean_object* v_unused_2385_; lean_object* v_unused_2386_; lean_object* v_unused_2387_; 
v_unused_2385_ = lean_ctor_get(v_fst_2295_, 2);
lean_dec(v_unused_2385_);
v_unused_2386_ = lean_ctor_get(v_fst_2295_, 1);
lean_dec(v_unused_2386_);
v_unused_2387_ = lean_ctor_get(v_fst_2295_, 0);
lean_dec(v_unused_2387_);
v___x_2343_ = v_fst_2295_;
v_isShared_2344_ = v_isSharedCheck_2384_;
goto v_resetjp_2342_;
}
else
{
lean_dec(v_fst_2295_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2384_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v_array_2345_; lean_object* v_start_2346_; lean_object* v_stop_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2351_; 
v_array_2345_ = lean_ctor_get(v_fst_2291_, 0);
v_start_2346_ = lean_ctor_get(v_fst_2291_, 1);
v_stop_2347_ = lean_ctor_get(v_fst_2291_, 2);
v___x_2348_ = lean_array_fget(v_array_2322_, v_start_2323_);
v___x_2349_ = lean_nat_add(v_start_2323_, v___x_2326_);
lean_dec(v_start_2323_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 1, v___x_2349_);
v___x_2351_ = v___x_2343_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_array_2322_);
lean_ctor_set(v_reuseFailAlloc_2383_, 1, v___x_2349_);
lean_ctor_set(v_reuseFailAlloc_2383_, 2, v_stop_2324_);
v___x_2351_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
uint8_t v___x_2352_; 
v___x_2352_ = lean_nat_dec_lt(v_start_2346_, v_stop_2347_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2354_; 
lean_dec(v___x_2348_);
lean_dec(v___x_2325_);
lean_dec(v_next_2278_);
lean_dec(v_fst_2277_);
lean_dec(v___f_2276_);
lean_dec_ref(v_inst_2275_);
lean_dec_ref(v_inst_2274_);
lean_dec(v_onAlt_2273_);
lean_dec(v_inst_2272_);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 1, v___x_2329_);
lean_ctor_set(v___x_2297_, 0, v___x_2351_);
v___x_2354_ = v___x_2297_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2351_);
lean_ctor_set(v_reuseFailAlloc_2363_, 1, v___x_2329_);
v___x_2354_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
lean_object* v___x_2356_; 
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 1, v___x_2354_);
v___x_2356_ = v___x_2293_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_fst_2291_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
lean_object* v___x_2358_; 
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 1, v___x_2356_);
v___x_2358_ = v___x_2289_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_fst_2287_);
lean_ctor_set(v_reuseFailAlloc_2361_, 1, v___x_2356_);
v___x_2358_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
v___x_2360_ = lean_apply_2(v_toPure_2267_, lean_box(0), v___x_2359_);
v___y_2304_ = v___x_2360_;
goto v___jp_2303_;
}
}
}
}
else
{
lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2379_; 
lean_inc(v_stop_2347_);
lean_inc(v_start_2346_);
lean_inc_ref(v_array_2345_);
lean_del_object(v___x_2297_);
lean_del_object(v___x_2293_);
lean_del_object(v___x_2289_);
v_isSharedCheck_2379_ = !lean_is_exclusive(v_fst_2291_);
if (v_isSharedCheck_2379_ == 0)
{
lean_object* v_unused_2380_; lean_object* v_unused_2381_; lean_object* v_unused_2382_; 
v_unused_2380_ = lean_ctor_get(v_fst_2291_, 2);
lean_dec(v_unused_2380_);
v_unused_2381_ = lean_ctor_get(v_fst_2291_, 1);
lean_dec(v_unused_2381_);
v_unused_2382_ = lean_ctor_get(v_fst_2291_, 0);
lean_dec(v_unused_2382_);
v___x_2365_ = v_fst_2291_;
v_isShared_2366_ = v_isSharedCheck_2379_;
goto v_resetjp_2364_;
}
else
{
lean_dec(v_fst_2291_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2379_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___f_2370_; lean_object* v___x_2371_; lean_object* v___x_2373_; 
v___x_2367_ = lean_array_fget_borrowed(v_array_2345_, v_start_2346_);
v___x_2368_ = lean_box(v___x_2270_);
v___x_2369_ = lean_box(v___x_2271_);
lean_inc_ref(v_inst_2275_);
lean_inc_ref(v_inst_2274_);
lean_inc(v___x_2367_);
lean_inc(v_toBind_2268_);
v___f_2370_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed), 13, 11);
lean_closure_set(v___f_2370_, 0, v___x_2368_);
lean_closure_set(v___f_2370_, 1, v___x_2369_);
lean_closure_set(v___f_2370_, 2, v_inst_2272_);
lean_closure_set(v___f_2370_, 3, v_onAlt_2273_);
lean_closure_set(v___f_2370_, 4, v_next_2278_);
lean_closure_set(v___f_2370_, 5, v_toBind_2268_);
lean_closure_set(v___f_2370_, 6, v___x_2367_);
lean_closure_set(v___f_2370_, 7, v_inst_2274_);
lean_closure_set(v___f_2370_, 8, v_inst_2275_);
lean_closure_set(v___f_2370_, 9, v___f_2276_);
lean_closure_set(v___f_2370_, 10, v_fst_2277_);
v___x_2371_ = lean_nat_add(v_start_2346_, v___x_2326_);
lean_dec(v_start_2346_);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 1, v___x_2371_);
v___x_2373_ = v___x_2365_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_array_2345_);
lean_ctor_set(v_reuseFailAlloc_2378_, 1, v___x_2371_);
lean_ctor_set(v_reuseFailAlloc_2378_, 2, v_stop_2347_);
v___x_2373_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
lean_object* v___f_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___f_2374_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__28), 6, 5);
lean_closure_set(v___f_2374_, 0, v_fst_2287_);
lean_closure_set(v___f_2374_, 1, v___x_2351_);
lean_closure_set(v___f_2374_, 2, v___x_2329_);
lean_closure_set(v___f_2374_, 3, v___x_2373_);
lean_closure_set(v___f_2374_, 4, v_toPure_2267_);
v___x_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2348_);
v___x_2376_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2274_, v_inst_2275_, v___x_2325_, v___x_2375_, v___f_2370_, v___x_2270_, v___x_2270_);
lean_inc(v_toBind_2268_);
v___x_2377_ = lean_apply_4(v_toBind_2268_, lean_box(0), lean_box(0), v___x_2376_, v___f_2374_);
v___y_2304_ = v___x_2377_;
goto v___jp_2303_;
}
}
}
}
}
}
}
}
}
v___jp_2303_:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
lean_inc(v_toBind_2268_);
v___x_2305_ = lean_apply_4(v_toBind_2268_, lean_box(0), lean_box(0), v___y_2304_, v___f_2269_);
v___x_2306_ = lean_apply_4(v_toBind_2268_, lean_box(0), lean_box(0), v___x_2305_, v___f_2302_);
return v___x_2306_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29___boxed(lean_object* v___x_2399_, lean_object* v_toPure_2400_, lean_object* v_toBind_2401_, lean_object* v___f_2402_, lean_object* v___x_2403_, lean_object* v___x_2404_, lean_object* v_inst_2405_, lean_object* v_onAlt_2406_, lean_object* v_inst_2407_, lean_object* v_inst_2408_, lean_object* v___f_2409_, lean_object* v_fst_2410_, lean_object* v_next_2411_, lean_object* v_acc_2412_, lean_object* v_h_2413_, lean_object* v_G_2414_){
_start:
{
uint8_t v___x_15028__boxed_2415_; uint8_t v___x_15029__boxed_2416_; lean_object* v_res_2417_; 
v___x_15028__boxed_2415_ = lean_unbox(v___x_2403_);
v___x_15029__boxed_2416_ = lean_unbox(v___x_2404_);
v_res_2417_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__29(v___x_2399_, v_toPure_2400_, v_toBind_2401_, v___f_2402_, v___x_15028__boxed_2415_, v___x_15029__boxed_2416_, v_inst_2405_, v_onAlt_2406_, v_inst_2407_, v_inst_2408_, v___f_2409_, v_fst_2410_, v_next_2411_, v_acc_2412_, v_h_2413_, v_G_2414_);
lean_dec(v___x_2399_);
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
lean_inc(v___x_2420_);
v___x_2430_ = l_Array_toSubarray___redArg(v_alts_2419_, v___x_2420_, v___x_2421_);
lean_inc(v___x_2420_);
v___x_2431_ = l_Array_toSubarray___redArg(v___x_2427_, v___x_2420_, v___x_2428_);
lean_inc(v___x_2420_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31(lean_object* v_alts_2438_, lean_object* v_toPure_2439_, lean_object* v_toBind_2440_, lean_object* v___f_2441_, uint8_t v___x_2442_, uint8_t v___x_2443_, lean_object* v_inst_2444_, lean_object* v_onAlt_2445_, lean_object* v_inst_2446_, lean_object* v_inst_2447_, lean_object* v___f_2448_, lean_object* v_fst_2449_, lean_object* v_matcherApp_2450_, lean_object* v___x_2451_, lean_object* v_remaining_x27_2452_, lean_object* v___f_2453_, lean_object* v_aux_2454_, lean_object* v_____r_2455_){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___f_2459_; lean_object* v___f_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2456_ = lean_array_get_size(v_alts_2438_);
v___x_2457_ = lean_box(v___x_2442_);
v___x_2458_ = lean_box(v___x_2443_);
lean_inc(v_inst_2444_);
lean_inc(v_toBind_2440_);
v___f_2459_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__29___boxed), 16, 12);
lean_closure_set(v___f_2459_, 0, v___x_2456_);
lean_closure_set(v___f_2459_, 1, v_toPure_2439_);
lean_closure_set(v___f_2459_, 2, v_toBind_2440_);
lean_closure_set(v___f_2459_, 3, v___f_2441_);
lean_closure_set(v___f_2459_, 4, v___x_2457_);
lean_closure_set(v___f_2459_, 5, v___x_2458_);
lean_closure_set(v___f_2459_, 6, v_inst_2444_);
lean_closure_set(v___f_2459_, 7, v_onAlt_2445_);
lean_closure_set(v___f_2459_, 8, v_inst_2446_);
lean_closure_set(v___f_2459_, 9, v_inst_2447_);
lean_closure_set(v___f_2459_, 10, v___f_2448_);
lean_closure_set(v___f_2459_, 11, v_fst_2449_);
lean_inc(v_toBind_2440_);
v___f_2460_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__30), 9, 8);
lean_closure_set(v___f_2460_, 0, v_matcherApp_2450_);
lean_closure_set(v___f_2460_, 1, v_alts_2438_);
lean_closure_set(v___f_2460_, 2, v___x_2451_);
lean_closure_set(v___f_2460_, 3, v___x_2456_);
lean_closure_set(v___f_2460_, 4, v_remaining_x27_2452_);
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
lean_object* v_onAlt_2471_ = _args[7];
lean_object* v_inst_2472_ = _args[8];
lean_object* v_inst_2473_ = _args[9];
lean_object* v___f_2474_ = _args[10];
lean_object* v_fst_2475_ = _args[11];
lean_object* v_matcherApp_2476_ = _args[12];
lean_object* v___x_2477_ = _args[13];
lean_object* v_remaining_x27_2478_ = _args[14];
lean_object* v___f_2479_ = _args[15];
lean_object* v_aux_2480_ = _args[16];
lean_object* v_____r_2481_ = _args[17];
_start:
{
uint8_t v___x_15285__boxed_2482_; uint8_t v___x_15286__boxed_2483_; lean_object* v_res_2484_; 
v___x_15285__boxed_2482_ = lean_unbox(v___x_2468_);
v___x_15286__boxed_2483_ = lean_unbox(v___x_2469_);
v_res_2484_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__31(v_alts_2464_, v_toPure_2465_, v_toBind_2466_, v___f_2467_, v___x_15285__boxed_2482_, v___x_15286__boxed_2483_, v_inst_2470_, v_onAlt_2471_, v_inst_2472_, v_inst_2473_, v___f_2474_, v_fst_2475_, v_matcherApp_2476_, v___x_2477_, v_remaining_x27_2478_, v___f_2479_, v_aux_2480_, v_____r_2481_);
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
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34(lean_object* v_toPure_2508_, lean_object* v_next_2509_, lean_object* v_G_2510_, lean_object* v_____do__lift_2511_){
_start:
{
if (lean_obj_tag(v_____do__lift_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v___x_2513_; 
lean_dec(v_G_2510_);
v_a_2512_ = lean_ctor_get(v_____do__lift_2511_, 0);
lean_inc(v_a_2512_);
lean_dec_ref(v_____do__lift_2511_);
v___x_2513_ = lean_apply_2(v_toPure_2508_, lean_box(0), v_a_2512_);
return v___x_2513_;
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
lean_dec(v_toPure_2508_);
v_a_2514_ = lean_ctor_get(v_____do__lift_2511_, 0);
lean_inc(v_a_2514_);
lean_dec_ref(v_____do__lift_2511_);
v___x_2515_ = lean_unsigned_to_nat(1u);
v___x_2516_ = lean_nat_add(v_next_2509_, v___x_2515_);
v___x_2517_ = lean_apply_4(v_G_2510_, v___x_2516_, v_a_2514_, lean_box(0), lean_box(0));
return v___x_2517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed(lean_object* v_toPure_2518_, lean_object* v_next_2519_, lean_object* v_G_2520_, lean_object* v_____do__lift_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__34(v_toPure_2518_, v_next_2519_, v_G_2520_, v_____do__lift_2521_);
lean_dec(v_next_2519_);
return v_res_2522_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__5(void){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = lean_box(0);
v___x_2532_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__4));
v___x_2533_ = l_Lean_mkConst(v___x_2532_, v___x_2531_);
return v___x_2533_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__6(void){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2534_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__5);
v___x_2535_ = lean_unsigned_to_nat(2u);
v___x_2536_ = lean_mk_empty_array_with_capacity(v___x_2535_);
v___x_2537_ = lean_array_push(v___x_2536_, v___x_2534_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35(lean_object* v___x_2538_, lean_object* v_toPure_2539_, lean_object* v_inst_2540_, lean_object* v_alt_x27_2541_){
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
v___x_2544_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__2));
v___x_2545_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__6);
v___x_2546_ = lean_array_push(v___x_2545_, v_alt_x27_2541_);
v___x_2547_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___boxed), 7, 2);
lean_closure_set(v___x_2547_, 0, v___x_2544_);
lean_closure_set(v___x_2547_, 1, v___x_2546_);
v___x_2548_ = lean_apply_2(v_inst_2540_, lean_box(0), v___x_2547_);
return v___x_2548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed(lean_object* v___x_2549_, lean_object* v_toPure_2550_, lean_object* v_inst_2551_, lean_object* v_alt_x27_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__35(v___x_2549_, v_toPure_2550_, v_inst_2551_, v_alt_x27_2552_);
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
uint8_t v___x_15439__boxed_2581_; uint8_t v_useSplitter_boxed_2582_; lean_object* v_res_2583_; 
v___x_15439__boxed_2581_ = lean_unbox(v___x_2577_);
v_useSplitter_boxed_2582_ = lean_unbox(v_useSplitter_2578_);
v_res_2583_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__36(v_ys_2573_, v_ys2_2574_, v_ys3_2575_, v_ys4_2576_, v___x_15439__boxed_2581_, v_useSplitter_boxed_2582_, v_inst_2579_, v_alt_x27_2580_);
lean_dec_ref(v_ys4_2576_);
lean_dec_ref(v_ys3_2575_);
lean_dec_ref(v_ys2_2574_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__37(lean_object* v_onAlt_2584_, lean_object* v_next_2585_, lean_object* v_altType_2586_, lean_object* v___x_2587_, lean_object* v_toBind_2588_, lean_object* v___f_2589_, lean_object* v_alt_2590_){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2591_ = lean_apply_4(v_onAlt_2584_, v_next_2585_, v_altType_2586_, v___x_2587_, v_alt_2590_);
v___x_2592_ = lean_apply_4(v_toBind_2588_, lean_box(0), lean_box(0), v___x_2591_, v___f_2589_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38(lean_object* v_inst_2593_, lean_object* v_ys_2594_, lean_object* v_ys2_2595_, lean_object* v_ys3_2596_, uint8_t v___x_2597_, uint8_t v_useSplitter_2598_, lean_object* v_inst_2599_, lean_object* v_args_2600_, lean_object* v_onAlt_2601_, lean_object* v_next_2602_, lean_object* v_toBind_2603_, lean_object* v___x_2604_, lean_object* v___f_2605_, lean_object* v_ys4_2606_, lean_object* v_altType_2607_){
_start:
{
lean_object* v_toMonadExceptOf_2608_; lean_object* v_tryCatch_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___f_2612_; lean_object* v___x_2613_; lean_object* v___f_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v_toMonadExceptOf_2608_ = lean_ctor_get(v_inst_2593_, 0);
lean_inc_ref(v_toMonadExceptOf_2608_);
lean_dec_ref(v_inst_2593_);
v_tryCatch_2609_ = lean_ctor_get(v_toMonadExceptOf_2608_, 1);
lean_inc(v_tryCatch_2609_);
lean_dec_ref(v_toMonadExceptOf_2608_);
v___x_2610_ = lean_box(v___x_2597_);
v___x_2611_ = lean_box(v_useSplitter_2598_);
lean_inc(v_inst_2599_);
lean_inc_ref(v_ys3_2596_);
v___f_2612_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed), 8, 7);
lean_closure_set(v___f_2612_, 0, v_ys_2594_);
lean_closure_set(v___f_2612_, 1, v_ys2_2595_);
lean_closure_set(v___f_2612_, 2, v_ys3_2596_);
lean_closure_set(v___f_2612_, 3, v_ys4_2606_);
lean_closure_set(v___f_2612_, 4, v___x_2610_);
lean_closure_set(v___f_2612_, 5, v___x_2611_);
lean_closure_set(v___f_2612_, 6, v_inst_2599_);
v___x_2613_ = l_Array_append___redArg(v_args_2600_, v_ys3_2596_);
lean_dec_ref(v_ys3_2596_);
lean_inc(v_toBind_2603_);
lean_inc_ref(v___x_2613_);
v___f_2614_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37), 7, 6);
lean_closure_set(v___f_2614_, 0, v_onAlt_2601_);
lean_closure_set(v___f_2614_, 1, v_next_2602_);
lean_closure_set(v___f_2614_, 2, v_altType_2607_);
lean_closure_set(v___f_2614_, 3, v___x_2613_);
lean_closure_set(v___f_2614_, 4, v_toBind_2603_);
lean_closure_set(v___f_2614_, 5, v___f_2612_);
v___x_2615_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLambda___boxed), 7, 2);
lean_closure_set(v___x_2615_, 0, v___x_2604_);
lean_closure_set(v___x_2615_, 1, v___x_2613_);
v___x_2616_ = lean_apply_2(v_inst_2599_, lean_box(0), v___x_2615_);
v___x_2617_ = lean_apply_3(v_tryCatch_2609_, lean_box(0), v___x_2616_, v___f_2605_);
v___x_2618_ = lean_apply_4(v_toBind_2603_, lean_box(0), lean_box(0), v___x_2617_, v___f_2614_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed(lean_object* v_inst_2619_, lean_object* v_ys_2620_, lean_object* v_ys2_2621_, lean_object* v_ys3_2622_, lean_object* v___x_2623_, lean_object* v_useSplitter_2624_, lean_object* v_inst_2625_, lean_object* v_args_2626_, lean_object* v_onAlt_2627_, lean_object* v_next_2628_, lean_object* v_toBind_2629_, lean_object* v___x_2630_, lean_object* v___f_2631_, lean_object* v_ys4_2632_, lean_object* v_altType_2633_){
_start:
{
uint8_t v___x_15476__boxed_2634_; uint8_t v_useSplitter_boxed_2635_; lean_object* v_res_2636_; 
v___x_15476__boxed_2634_ = lean_unbox(v___x_2623_);
v_useSplitter_boxed_2635_ = lean_unbox(v_useSplitter_2624_);
v_res_2636_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__38(v_inst_2619_, v_ys_2620_, v_ys2_2621_, v_ys3_2622_, v___x_15476__boxed_2634_, v_useSplitter_boxed_2635_, v_inst_2625_, v_args_2626_, v_onAlt_2627_, v_next_2628_, v_toBind_2629_, v___x_2630_, v___f_2631_, v_ys4_2632_, v_altType_2633_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39(lean_object* v_inst_2637_, lean_object* v_ys_2638_, lean_object* v_ys2_2639_, uint8_t v___x_2640_, uint8_t v_useSplitter_2641_, lean_object* v_inst_2642_, lean_object* v_args_2643_, lean_object* v_onAlt_2644_, lean_object* v_next_2645_, lean_object* v_toBind_2646_, lean_object* v___x_2647_, lean_object* v___f_2648_, lean_object* v_fst_2649_, lean_object* v_inst_2650_, lean_object* v_inst_2651_, lean_object* v_ys3_2652_, lean_object* v_altType_2653_){
_start:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___f_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2654_ = lean_box(v___x_2640_);
v___x_2655_ = lean_box(v_useSplitter_2641_);
v___f_2656_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed), 15, 13);
lean_closure_set(v___f_2656_, 0, v_inst_2637_);
lean_closure_set(v___f_2656_, 1, v_ys_2638_);
lean_closure_set(v___f_2656_, 2, v_ys2_2639_);
lean_closure_set(v___f_2656_, 3, v_ys3_2652_);
lean_closure_set(v___f_2656_, 4, v___x_2654_);
lean_closure_set(v___f_2656_, 5, v___x_2655_);
lean_closure_set(v___f_2656_, 6, v_inst_2642_);
lean_closure_set(v___f_2656_, 7, v_args_2643_);
lean_closure_set(v___f_2656_, 8, v_onAlt_2644_);
lean_closure_set(v___f_2656_, 9, v_next_2645_);
lean_closure_set(v___f_2656_, 10, v_toBind_2646_);
lean_closure_set(v___f_2656_, 11, v___x_2647_);
lean_closure_set(v___f_2656_, 12, v___f_2648_);
v___x_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2657_, 0, v_fst_2649_);
v___x_2658_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2650_, v_inst_2651_, v_altType_2653_, v___x_2657_, v___f_2656_, v___x_2640_, v___x_2640_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39___boxed(lean_object** _args){
lean_object* v_inst_2659_ = _args[0];
lean_object* v_ys_2660_ = _args[1];
lean_object* v_ys2_2661_ = _args[2];
lean_object* v___x_2662_ = _args[3];
lean_object* v_useSplitter_2663_ = _args[4];
lean_object* v_inst_2664_ = _args[5];
lean_object* v_args_2665_ = _args[6];
lean_object* v_onAlt_2666_ = _args[7];
lean_object* v_next_2667_ = _args[8];
lean_object* v_toBind_2668_ = _args[9];
lean_object* v___x_2669_ = _args[10];
lean_object* v___f_2670_ = _args[11];
lean_object* v_fst_2671_ = _args[12];
lean_object* v_inst_2672_ = _args[13];
lean_object* v_inst_2673_ = _args[14];
lean_object* v_ys3_2674_ = _args[15];
lean_object* v_altType_2675_ = _args[16];
_start:
{
uint8_t v___x_15509__boxed_2676_; uint8_t v_useSplitter_boxed_2677_; lean_object* v_res_2678_; 
v___x_15509__boxed_2676_ = lean_unbox(v___x_2662_);
v_useSplitter_boxed_2677_ = lean_unbox(v_useSplitter_2663_);
v_res_2678_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__39(v_inst_2659_, v_ys_2660_, v_ys2_2661_, v___x_15509__boxed_2676_, v_useSplitter_boxed_2677_, v_inst_2664_, v_args_2665_, v_onAlt_2666_, v_next_2667_, v_toBind_2668_, v___x_2669_, v___f_2670_, v_fst_2671_, v_inst_2672_, v_inst_2673_, v_ys3_2674_, v_altType_2675_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40(lean_object* v_inst_2679_, lean_object* v_ys_2680_, uint8_t v___x_2681_, uint8_t v_useSplitter_2682_, lean_object* v_inst_2683_, lean_object* v_args_2684_, lean_object* v_onAlt_2685_, lean_object* v_next_2686_, lean_object* v_toBind_2687_, lean_object* v___x_2688_, lean_object* v___f_2689_, lean_object* v_fst_2690_, lean_object* v_inst_2691_, lean_object* v_inst_2692_, lean_object* v_numDiscrEqs_2693_, lean_object* v_ys2_2694_, lean_object* v_altType_2695_){
_start:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___f_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v___x_2696_ = lean_box(v___x_2681_);
v___x_2697_ = lean_box(v_useSplitter_2682_);
lean_inc_ref(v_inst_2692_);
lean_inc_ref(v_inst_2691_);
v___f_2698_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__39___boxed), 17, 15);
lean_closure_set(v___f_2698_, 0, v_inst_2679_);
lean_closure_set(v___f_2698_, 1, v_ys_2680_);
lean_closure_set(v___f_2698_, 2, v_ys2_2694_);
lean_closure_set(v___f_2698_, 3, v___x_2696_);
lean_closure_set(v___f_2698_, 4, v___x_2697_);
lean_closure_set(v___f_2698_, 5, v_inst_2683_);
lean_closure_set(v___f_2698_, 6, v_args_2684_);
lean_closure_set(v___f_2698_, 7, v_onAlt_2685_);
lean_closure_set(v___f_2698_, 8, v_next_2686_);
lean_closure_set(v___f_2698_, 9, v_toBind_2687_);
lean_closure_set(v___f_2698_, 10, v___x_2688_);
lean_closure_set(v___f_2698_, 11, v___f_2689_);
lean_closure_set(v___f_2698_, 12, v_fst_2690_);
lean_closure_set(v___f_2698_, 13, v_inst_2691_);
lean_closure_set(v___f_2698_, 14, v_inst_2692_);
v___x_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2699_, 0, v_numDiscrEqs_2693_);
v___x_2700_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2691_, v_inst_2692_, v_altType_2695_, v___x_2699_, v___f_2698_, v___x_2681_, v___x_2681_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed(lean_object** _args){
lean_object* v_inst_2701_ = _args[0];
lean_object* v_ys_2702_ = _args[1];
lean_object* v___x_2703_ = _args[2];
lean_object* v_useSplitter_2704_ = _args[3];
lean_object* v_inst_2705_ = _args[4];
lean_object* v_args_2706_ = _args[5];
lean_object* v_onAlt_2707_ = _args[6];
lean_object* v_next_2708_ = _args[7];
lean_object* v_toBind_2709_ = _args[8];
lean_object* v___x_2710_ = _args[9];
lean_object* v___f_2711_ = _args[10];
lean_object* v_fst_2712_ = _args[11];
lean_object* v_inst_2713_ = _args[12];
lean_object* v_inst_2714_ = _args[13];
lean_object* v_numDiscrEqs_2715_ = _args[14];
lean_object* v_ys2_2716_ = _args[15];
lean_object* v_altType_2717_ = _args[16];
_start:
{
uint8_t v___x_15540__boxed_2718_; uint8_t v_useSplitter_boxed_2719_; lean_object* v_res_2720_; 
v___x_15540__boxed_2718_ = lean_unbox(v___x_2703_);
v_useSplitter_boxed_2719_ = lean_unbox(v_useSplitter_2704_);
v_res_2720_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__40(v_inst_2701_, v_ys_2702_, v___x_15540__boxed_2718_, v_useSplitter_boxed_2719_, v_inst_2705_, v_args_2706_, v_onAlt_2707_, v_next_2708_, v_toBind_2709_, v___x_2710_, v___f_2711_, v_fst_2712_, v_inst_2713_, v_inst_2714_, v_numDiscrEqs_2715_, v_ys2_2716_, v_altType_2717_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41(lean_object* v___x_2721_, lean_object* v_inst_2722_, lean_object* v_inst_2723_, lean_object* v___f_2724_, uint8_t v___x_2725_, lean_object* v_toBind_2726_, lean_object* v___f_2727_, lean_object* v_altType_2728_){
_start:
{
lean_object* v_numOverlaps_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v_numOverlaps_2729_ = lean_ctor_get(v___x_2721_, 1);
lean_inc(v_numOverlaps_2729_);
v___x_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2730_, 0, v_numOverlaps_2729_);
v___x_2731_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2722_, v_inst_2723_, v_altType_2728_, v___x_2730_, v___f_2724_, v___x_2725_, v___x_2725_);
v___x_2732_ = lean_apply_4(v_toBind_2726_, lean_box(0), lean_box(0), v___x_2731_, v___f_2727_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed(lean_object* v___x_2733_, lean_object* v_inst_2734_, lean_object* v_inst_2735_, lean_object* v___f_2736_, lean_object* v___x_2737_, lean_object* v_toBind_2738_, lean_object* v___f_2739_, lean_object* v_altType_2740_){
_start:
{
uint8_t v___x_15574__boxed_2741_; lean_object* v_res_2742_; 
v___x_15574__boxed_2741_ = lean_unbox(v___x_2737_);
v_res_2742_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__41(v___x_2733_, v_inst_2734_, v_inst_2735_, v___f_2736_, v___x_15574__boxed_2741_, v_toBind_2738_, v___f_2739_, v_altType_2740_);
lean_dec_ref(v___x_2733_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__42(lean_object* v___f_2743_, lean_object* v_altType_2744_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = lean_apply_1(v___f_2743_, v_altType_2744_);
return v___x_2745_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2(void){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2750_ = lean_box(0);
v___x_2751_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__1));
v___x_2752_ = l_Lean_mkConst(v___x_2751_, v___x_2750_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44(uint8_t v_hasUnitThunk_2753_, lean_object* v_toPure_2754_, lean_object* v_toBind_2755_, lean_object* v___f_2756_, lean_object* v___x_2757_, lean_object* v_inst_2758_, lean_object* v___f_2759_, lean_object* v_altType_2760_){
_start:
{
if (v_hasUnitThunk_2753_ == 0)
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
lean_dec(v___f_2759_);
lean_dec(v_inst_2758_);
v___x_2761_ = lean_apply_2(v_toPure_2754_, lean_box(0), v_altType_2760_);
v___x_2762_ = lean_apply_4(v_toBind_2755_, lean_box(0), lean_box(0), v___x_2761_, v___f_2756_);
return v___x_2762_;
}
else
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
lean_dec(v___f_2756_);
lean_dec(v_toPure_2754_);
v___x_2763_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2);
v___x_2764_ = lean_mk_empty_array_with_capacity(v___x_2757_);
v___x_2765_ = lean_array_push(v___x_2764_, v___x_2763_);
v___x_2766_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateForall___boxed), 7, 2);
lean_closure_set(v___x_2766_, 0, v_altType_2760_);
lean_closure_set(v___x_2766_, 1, v___x_2765_);
v___x_2767_ = lean_apply_2(v_inst_2758_, lean_box(0), v___x_2766_);
v___x_2768_ = lean_apply_4(v_toBind_2755_, lean_box(0), lean_box(0), v___x_2767_, v___f_2759_);
return v___x_2768_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed(lean_object* v_hasUnitThunk_2769_, lean_object* v_toPure_2770_, lean_object* v_toBind_2771_, lean_object* v___f_2772_, lean_object* v___x_2773_, lean_object* v_inst_2774_, lean_object* v___f_2775_, lean_object* v_altType_2776_){
_start:
{
uint8_t v_hasUnitThunk_boxed_2777_; lean_object* v_res_2778_; 
v_hasUnitThunk_boxed_2777_ = lean_unbox(v_hasUnitThunk_2769_);
v_res_2778_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__44(v_hasUnitThunk_boxed_2777_, v_toPure_2770_, v_toBind_2771_, v___f_2772_, v___x_2773_, v_inst_2774_, v___f_2775_, v_altType_2776_);
lean_dec(v___x_2773_);
return v_res_2778_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3(void){
_start:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2782_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__2));
v___x_2783_ = lean_unsigned_to_nat(8u);
v___x_2784_ = lean_unsigned_to_nat(319u);
v___x_2785_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__1));
v___x_2786_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__0));
v___x_2787_ = l_mkPanicMessageWithDecl(v___x_2786_, v___x_2785_, v___x_2784_, v___x_2783_, v___x_2782_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43(lean_object* v___x_2788_, lean_object* v_inst_2789_, lean_object* v_inst_2790_, uint8_t v___x_2791_, uint8_t v_useSplitter_2792_, lean_object* v_inst_2793_, lean_object* v_onAlt_2794_, lean_object* v_next_2795_, lean_object* v_toBind_2796_, lean_object* v___x_2797_, lean_object* v___f_2798_, lean_object* v_fst_2799_, lean_object* v_inst_2800_, lean_object* v_numDiscrEqs_2801_, lean_object* v___f_2802_, uint8_t v_hasUnitThunk_2803_, lean_object* v_toPure_2804_, lean_object* v___x_2805_, lean_object* v___x_2806_, lean_object* v_ys_2807_, lean_object* v_args_2808_){
_start:
{
lean_object* v_numFields_2809_; lean_object* v___x_2810_; uint8_t v___x_2811_; 
v_numFields_2809_ = lean_ctor_get(v___x_2788_, 0);
v___x_2810_ = lean_array_get_size(v_ys_2807_);
v___x_2811_ = lean_nat_dec_eq(v___x_2810_, v_numFields_2809_);
if (v___x_2811_ == 0)
{
lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; 
lean_dec_ref(v_args_2808_);
lean_dec_ref(v_ys_2807_);
lean_dec_ref(v___x_2806_);
lean_dec(v___x_2805_);
lean_dec(v_toPure_2804_);
lean_dec(v___f_2802_);
lean_dec(v_numDiscrEqs_2801_);
lean_dec_ref(v_inst_2800_);
lean_dec(v_fst_2799_);
lean_dec(v___f_2798_);
lean_dec_ref(v___x_2797_);
lean_dec(v_toBind_2796_);
lean_dec(v_next_2795_);
lean_dec(v_onAlt_2794_);
lean_dec(v_inst_2793_);
lean_dec_ref(v_inst_2790_);
lean_dec_ref(v___x_2788_);
v___x_2812_ = l_Lean_instInhabitedExpr;
v___x_2813_ = l_instInhabitedOfMonad___redArg(v_inst_2789_, v___x_2812_);
v___x_2814_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3);
v___x_2815_ = l_panic___redArg(v___x_2813_, v___x_2814_);
return v___x_2815_;
}
else
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___f_2818_; lean_object* v___x_2819_; lean_object* v___f_2820_; lean_object* v___f_2821_; lean_object* v___x_2822_; lean_object* v___f_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2816_ = lean_box(v___x_2791_);
v___x_2817_ = lean_box(v_useSplitter_2792_);
lean_inc_ref(v_inst_2789_);
lean_inc_ref(v_inst_2800_);
lean_inc(v_toBind_2796_);
lean_inc(v_inst_2793_);
lean_inc_ref(v_ys_2807_);
v___f_2818_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed), 17, 15);
lean_closure_set(v___f_2818_, 0, v_inst_2790_);
lean_closure_set(v___f_2818_, 1, v_ys_2807_);
lean_closure_set(v___f_2818_, 2, v___x_2816_);
lean_closure_set(v___f_2818_, 3, v___x_2817_);
lean_closure_set(v___f_2818_, 4, v_inst_2793_);
lean_closure_set(v___f_2818_, 5, v_args_2808_);
lean_closure_set(v___f_2818_, 6, v_onAlt_2794_);
lean_closure_set(v___f_2818_, 7, v_next_2795_);
lean_closure_set(v___f_2818_, 8, v_toBind_2796_);
lean_closure_set(v___f_2818_, 9, v___x_2797_);
lean_closure_set(v___f_2818_, 10, v___f_2798_);
lean_closure_set(v___f_2818_, 11, v_fst_2799_);
lean_closure_set(v___f_2818_, 12, v_inst_2800_);
lean_closure_set(v___f_2818_, 13, v_inst_2789_);
lean_closure_set(v___f_2818_, 14, v_numDiscrEqs_2801_);
v___x_2819_ = lean_box(v___x_2791_);
lean_inc(v_toBind_2796_);
v___f_2820_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed), 8, 7);
lean_closure_set(v___f_2820_, 0, v___x_2788_);
lean_closure_set(v___f_2820_, 1, v_inst_2800_);
lean_closure_set(v___f_2820_, 2, v_inst_2789_);
lean_closure_set(v___f_2820_, 3, v___f_2818_);
lean_closure_set(v___f_2820_, 4, v___x_2819_);
lean_closure_set(v___f_2820_, 5, v_toBind_2796_);
lean_closure_set(v___f_2820_, 6, v___f_2802_);
v___f_2821_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__42), 2, 1);
lean_closure_set(v___f_2821_, 0, v___f_2820_);
v___x_2822_ = lean_box(v_hasUnitThunk_2803_);
lean_inc(v_inst_2793_);
lean_inc_ref(v___f_2821_);
lean_inc(v_toBind_2796_);
v___f_2823_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed), 8, 7);
lean_closure_set(v___f_2823_, 0, v___x_2822_);
lean_closure_set(v___f_2823_, 1, v_toPure_2804_);
lean_closure_set(v___f_2823_, 2, v_toBind_2796_);
lean_closure_set(v___f_2823_, 3, v___f_2821_);
lean_closure_set(v___f_2823_, 4, v___x_2805_);
lean_closure_set(v___f_2823_, 5, v_inst_2793_);
lean_closure_set(v___f_2823_, 6, v___f_2821_);
v___x_2824_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateForall___boxed), 7, 2);
lean_closure_set(v___x_2824_, 0, v___x_2806_);
lean_closure_set(v___x_2824_, 1, v_ys_2807_);
v___x_2825_ = lean_apply_2(v_inst_2793_, lean_box(0), v___x_2824_);
v___x_2826_ = lean_apply_4(v_toBind_2796_, lean_box(0), lean_box(0), v___x_2825_, v___f_2823_);
return v___x_2826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed(lean_object** _args){
lean_object* v___x_2827_ = _args[0];
lean_object* v_inst_2828_ = _args[1];
lean_object* v_inst_2829_ = _args[2];
lean_object* v___x_2830_ = _args[3];
lean_object* v_useSplitter_2831_ = _args[4];
lean_object* v_inst_2832_ = _args[5];
lean_object* v_onAlt_2833_ = _args[6];
lean_object* v_next_2834_ = _args[7];
lean_object* v_toBind_2835_ = _args[8];
lean_object* v___x_2836_ = _args[9];
lean_object* v___f_2837_ = _args[10];
lean_object* v_fst_2838_ = _args[11];
lean_object* v_inst_2839_ = _args[12];
lean_object* v_numDiscrEqs_2840_ = _args[13];
lean_object* v___f_2841_ = _args[14];
lean_object* v_hasUnitThunk_2842_ = _args[15];
lean_object* v_toPure_2843_ = _args[16];
lean_object* v___x_2844_ = _args[17];
lean_object* v___x_2845_ = _args[18];
lean_object* v_ys_2846_ = _args[19];
lean_object* v_args_2847_ = _args[20];
_start:
{
uint8_t v___x_15669__boxed_2848_; uint8_t v_useSplitter_boxed_2849_; uint8_t v_hasUnitThunk_boxed_2850_; lean_object* v_res_2851_; 
v___x_15669__boxed_2848_ = lean_unbox(v___x_2830_);
v_useSplitter_boxed_2849_ = lean_unbox(v_useSplitter_2831_);
v_hasUnitThunk_boxed_2850_ = lean_unbox(v_hasUnitThunk_2842_);
v_res_2851_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__43(v___x_2827_, v_inst_2828_, v_inst_2829_, v___x_15669__boxed_2848_, v_useSplitter_boxed_2849_, v_inst_2832_, v_onAlt_2833_, v_next_2834_, v_toBind_2835_, v___x_2836_, v___f_2837_, v_fst_2838_, v_inst_2839_, v_numDiscrEqs_2840_, v___f_2841_, v_hasUnitThunk_boxed_2850_, v_toPure_2843_, v___x_2844_, v___x_2845_, v_ys_2846_, v_args_2847_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45(lean_object* v_fst_2852_, lean_object* v___x_2853_, lean_object* v___x_2854_, lean_object* v___x_2855_, lean_object* v___x_2856_, lean_object* v___x_2857_, lean_object* v_toPure_2858_, lean_object* v_alt_x27_2859_){
_start:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2860_ = lean_array_push(v_fst_2852_, v_alt_x27_2859_);
v___x_2861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2853_);
lean_ctor_set(v___x_2861_, 1, v___x_2854_);
v___x_2862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2855_);
lean_ctor_set(v___x_2862_, 1, v___x_2861_);
v___x_2863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2856_);
lean_ctor_set(v___x_2863_, 1, v___x_2862_);
v___x_2864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2857_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
v___x_2865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2860_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
v___x_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
v___x_2867_ = lean_apply_2(v_toPure_2858_, lean_box(0), v___x_2866_);
return v___x_2867_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0(void){
_start:
{
lean_object* v___x_2868_; 
v___x_2868_ = l_Array_instInhabited(lean_box(0));
return v___x_2868_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1(void){
_start:
{
lean_object* v___x_2869_; 
v___x_2869_ = l_Subarray_empty(lean_box(0));
return v___x_2869_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2(void){
_start:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2870_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_2871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2870_);
lean_ctor_set(v___x_2871_, 1, v___x_2870_);
return v___x_2871_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__3(void){
_start:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2872_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2);
v___x_2873_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_2874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2873_);
lean_ctor_set(v___x_2874_, 1, v___x_2872_);
return v___x_2874_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__4(void){
_start:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2875_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__3);
v___x_2876_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_2877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
lean_ctor_set(v___x_2877_, 1, v___x_2875_);
return v___x_2877_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__5(void){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v___x_2878_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__4, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__4_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__4);
v___x_2879_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_2880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
lean_ctor_set(v___x_2880_, 1, v___x_2878_);
return v___x_2880_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__6(void){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2881_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__5);
v___x_2882_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0);
v___x_2883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2882_);
lean_ctor_set(v___x_2883_, 1, v___x_2881_);
return v___x_2883_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7(void){
_start:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2884_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__6);
v___x_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2884_);
return v___x_2885_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9(void){
_start:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2887_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__8));
v___x_2888_ = lean_unsigned_to_nat(6u);
v___x_2889_ = lean_unsigned_to_nat(317u);
v___x_2890_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__1));
v___x_2891_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__0));
v___x_2892_ = l_mkPanicMessageWithDecl(v___x_2891_, v___x_2890_, v___x_2889_, v___x_2888_, v___x_2887_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46(lean_object* v___x_2893_, lean_object* v_toPure_2894_, lean_object* v_toBind_2895_, lean_object* v___f_2896_, lean_object* v___x_2897_, lean_object* v_inst_2898_, lean_object* v_inst_2899_, lean_object* v_inst_2900_, uint8_t v___x_2901_, uint8_t v_useSplitter_2902_, lean_object* v_onAlt_2903_, lean_object* v___f_2904_, lean_object* v_fst_2905_, lean_object* v_inst_2906_, lean_object* v_numDiscrEqs_2907_, lean_object* v_next_2908_, lean_object* v_acc_2909_, lean_object* v_h_2910_, lean_object* v_G_2911_){
_start:
{
uint8_t v___x_2912_; 
v___x_2912_ = lean_nat_dec_lt(v_next_2908_, v___x_2893_);
if (v___x_2912_ == 0)
{
lean_object* v___x_2913_; 
lean_dec(v_G_2911_);
lean_dec(v_next_2908_);
lean_dec(v_numDiscrEqs_2907_);
lean_dec_ref(v_inst_2906_);
lean_dec(v_fst_2905_);
lean_dec(v___f_2904_);
lean_dec(v_onAlt_2903_);
lean_dec_ref(v_inst_2900_);
lean_dec(v_inst_2899_);
lean_dec_ref(v_inst_2898_);
lean_dec(v___f_2896_);
lean_dec(v_toBind_2895_);
v___x_2913_ = lean_apply_2(v_toPure_2894_, lean_box(0), v_acc_2909_);
return v___x_2913_;
}
else
{
lean_object* v_snd_2914_; lean_object* v_snd_2915_; lean_object* v_snd_2916_; lean_object* v_snd_2917_; lean_object* v_snd_2918_; lean_object* v_fst_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_3133_; 
v_snd_2914_ = lean_ctor_get(v_acc_2909_, 1);
lean_inc(v_snd_2914_);
v_snd_2915_ = lean_ctor_get(v_snd_2914_, 1);
lean_inc(v_snd_2915_);
v_snd_2916_ = lean_ctor_get(v_snd_2915_, 1);
lean_inc(v_snd_2916_);
v_snd_2917_ = lean_ctor_get(v_snd_2916_, 1);
lean_inc(v_snd_2917_);
v_snd_2918_ = lean_ctor_get(v_snd_2917_, 1);
lean_inc(v_snd_2918_);
v_fst_2919_ = lean_ctor_get(v_acc_2909_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v_acc_2909_);
if (v_isSharedCheck_3133_ == 0)
{
lean_object* v_unused_3134_; 
v_unused_3134_ = lean_ctor_get(v_acc_2909_, 1);
lean_dec(v_unused_3134_);
v___x_2921_ = v_acc_2909_;
v_isShared_2922_ = v_isSharedCheck_3133_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_fst_2919_);
lean_dec(v_acc_2909_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_3133_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v_fst_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_3131_; 
v_fst_2923_ = lean_ctor_get(v_snd_2914_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v_snd_2914_);
if (v_isSharedCheck_3131_ == 0)
{
lean_object* v_unused_3132_; 
v_unused_3132_ = lean_ctor_get(v_snd_2914_, 1);
lean_dec(v_unused_3132_);
v___x_2925_ = v_snd_2914_;
v_isShared_2926_ = v_isSharedCheck_3131_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_fst_2923_);
lean_dec(v_snd_2914_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_3131_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v_fst_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_3129_; 
v_fst_2927_ = lean_ctor_get(v_snd_2915_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v_snd_2915_);
if (v_isSharedCheck_3129_ == 0)
{
lean_object* v_unused_3130_; 
v_unused_3130_ = lean_ctor_get(v_snd_2915_, 1);
lean_dec(v_unused_3130_);
v___x_2929_ = v_snd_2915_;
v_isShared_2930_ = v_isSharedCheck_3129_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_fst_2927_);
lean_dec(v_snd_2915_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_3129_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v_fst_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_3127_; 
v_fst_2931_ = lean_ctor_get(v_snd_2916_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v_snd_2916_);
if (v_isSharedCheck_3127_ == 0)
{
lean_object* v_unused_3128_; 
v_unused_3128_ = lean_ctor_get(v_snd_2916_, 1);
lean_dec(v_unused_3128_);
v___x_2933_ = v_snd_2916_;
v_isShared_2934_ = v_isSharedCheck_3127_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_fst_2931_);
lean_dec(v_snd_2916_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_3127_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v_fst_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_3125_; 
v_fst_2935_ = lean_ctor_get(v_snd_2917_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v_snd_2917_);
if (v_isSharedCheck_3125_ == 0)
{
lean_object* v_unused_3126_; 
v_unused_3126_ = lean_ctor_get(v_snd_2917_, 1);
lean_dec(v_unused_3126_);
v___x_2937_ = v_snd_2917_;
v_isShared_2938_ = v_isSharedCheck_3125_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_fst_2935_);
lean_dec(v_snd_2917_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_3125_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v_array_2939_; lean_object* v_start_2940_; lean_object* v_stop_2941_; lean_object* v___f_2942_; lean_object* v___y_2944_; uint8_t v___x_2947_; 
v_array_2939_ = lean_ctor_get(v_snd_2918_, 0);
v_start_2940_ = lean_ctor_get(v_snd_2918_, 1);
v_stop_2941_ = lean_ctor_get(v_snd_2918_, 2);
lean_inc(v_next_2908_);
lean_inc(v_toPure_2894_);
v___f_2942_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed), 4, 3);
lean_closure_set(v___f_2942_, 0, v_toPure_2894_);
lean_closure_set(v___f_2942_, 1, v_next_2908_);
lean_closure_set(v___f_2942_, 2, v_G_2911_);
v___x_2947_ = lean_nat_dec_lt(v_start_2940_, v_stop_2941_);
if (v___x_2947_ == 0)
{
lean_object* v___x_2949_; 
lean_dec(v_next_2908_);
lean_dec(v_numDiscrEqs_2907_);
lean_dec_ref(v_inst_2906_);
lean_dec(v_fst_2905_);
lean_dec(v___f_2904_);
lean_dec(v_onAlt_2903_);
lean_dec_ref(v_inst_2900_);
lean_dec(v_inst_2899_);
lean_dec_ref(v_inst_2898_);
if (v_isShared_2938_ == 0)
{
v___x_2949_ = v___x_2937_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_fst_2935_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v_snd_2918_);
v___x_2949_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
lean_object* v___x_2951_; 
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 1, v___x_2949_);
v___x_2951_ = v___x_2933_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_fst_2931_);
lean_ctor_set(v_reuseFailAlloc_2963_, 1, v___x_2949_);
v___x_2951_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
lean_object* v___x_2953_; 
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 1, v___x_2951_);
v___x_2953_ = v___x_2929_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_fst_2927_);
lean_ctor_set(v_reuseFailAlloc_2962_, 1, v___x_2951_);
v___x_2953_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
lean_object* v___x_2955_; 
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 1, v___x_2953_);
v___x_2955_ = v___x_2925_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_fst_2923_);
lean_ctor_set(v_reuseFailAlloc_2961_, 1, v___x_2953_);
v___x_2955_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
lean_object* v___x_2957_; 
if (v_isShared_2922_ == 0)
{
lean_ctor_set(v___x_2921_, 1, v___x_2955_);
v___x_2957_ = v___x_2921_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_fst_2919_);
lean_ctor_set(v_reuseFailAlloc_2960_, 1, v___x_2955_);
v___x_2957_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2957_);
v___x_2959_ = lean_apply_2(v_toPure_2894_, lean_box(0), v___x_2958_);
v___y_2944_ = v___x_2959_;
goto v___jp_2943_;
}
}
}
}
}
}
else
{
lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_3121_; 
lean_inc(v_stop_2941_);
lean_inc(v_start_2940_);
lean_inc_ref(v_array_2939_);
v_isSharedCheck_3121_ = !lean_is_exclusive(v_snd_2918_);
if (v_isSharedCheck_3121_ == 0)
{
lean_object* v_unused_3122_; lean_object* v_unused_3123_; lean_object* v_unused_3124_; 
v_unused_3122_ = lean_ctor_get(v_snd_2918_, 2);
lean_dec(v_unused_3122_);
v_unused_3123_ = lean_ctor_get(v_snd_2918_, 1);
lean_dec(v_unused_3123_);
v_unused_3124_ = lean_ctor_get(v_snd_2918_, 0);
lean_dec(v_unused_3124_);
v___x_2966_ = v_snd_2918_;
v_isShared_2967_ = v_isSharedCheck_3121_;
goto v_resetjp_2965_;
}
else
{
lean_dec(v_snd_2918_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_3121_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v_array_2968_; lean_object* v_start_2969_; lean_object* v_stop_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2975_; 
v_array_2968_ = lean_ctor_get(v_fst_2935_, 0);
v_start_2969_ = lean_ctor_get(v_fst_2935_, 1);
v_stop_2970_ = lean_ctor_get(v_fst_2935_, 2);
v___x_2971_ = lean_array_fget(v_array_2939_, v_start_2940_);
v___x_2972_ = lean_unsigned_to_nat(1u);
v___x_2973_ = lean_nat_add(v_start_2940_, v___x_2972_);
lean_dec(v_start_2940_);
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 1, v___x_2973_);
v___x_2975_ = v___x_2966_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_array_2939_);
lean_ctor_set(v_reuseFailAlloc_3120_, 1, v___x_2973_);
lean_ctor_set(v_reuseFailAlloc_3120_, 2, v_stop_2941_);
v___x_2975_ = v_reuseFailAlloc_3120_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
uint8_t v___x_2976_; 
v___x_2976_ = lean_nat_dec_lt(v_start_2969_, v_stop_2970_);
if (v___x_2976_ == 0)
{
lean_object* v___x_2978_; 
lean_dec(v___x_2971_);
lean_dec(v_next_2908_);
lean_dec(v_numDiscrEqs_2907_);
lean_dec_ref(v_inst_2906_);
lean_dec(v_fst_2905_);
lean_dec(v___f_2904_);
lean_dec(v_onAlt_2903_);
lean_dec_ref(v_inst_2900_);
lean_dec(v_inst_2899_);
lean_dec_ref(v_inst_2898_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 1, v___x_2975_);
v___x_2978_ = v___x_2937_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_fst_2935_);
lean_ctor_set(v_reuseFailAlloc_2993_, 1, v___x_2975_);
v___x_2978_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
lean_object* v___x_2980_; 
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 1, v___x_2978_);
v___x_2980_ = v___x_2933_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_fst_2931_);
lean_ctor_set(v_reuseFailAlloc_2992_, 1, v___x_2978_);
v___x_2980_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
lean_object* v___x_2982_; 
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 1, v___x_2980_);
v___x_2982_ = v___x_2929_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_fst_2927_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v___x_2980_);
v___x_2982_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
lean_object* v___x_2984_; 
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 1, v___x_2982_);
v___x_2984_ = v___x_2925_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_fst_2923_);
lean_ctor_set(v_reuseFailAlloc_2990_, 1, v___x_2982_);
v___x_2984_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
lean_object* v___x_2986_; 
if (v_isShared_2922_ == 0)
{
lean_ctor_set(v___x_2921_, 1, v___x_2984_);
v___x_2986_ = v___x_2921_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_fst_2919_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v___x_2984_);
v___x_2986_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2986_);
v___x_2988_ = lean_apply_2(v_toPure_2894_, lean_box(0), v___x_2987_);
v___y_2944_ = v___x_2988_;
goto v___jp_2943_;
}
}
}
}
}
}
else
{
lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3116_; 
lean_inc(v_stop_2970_);
lean_inc(v_start_2969_);
lean_inc_ref(v_array_2968_);
v_isSharedCheck_3116_ = !lean_is_exclusive(v_fst_2935_);
if (v_isSharedCheck_3116_ == 0)
{
lean_object* v_unused_3117_; lean_object* v_unused_3118_; lean_object* v_unused_3119_; 
v_unused_3117_ = lean_ctor_get(v_fst_2935_, 2);
lean_dec(v_unused_3117_);
v_unused_3118_ = lean_ctor_get(v_fst_2935_, 1);
lean_dec(v_unused_3118_);
v_unused_3119_ = lean_ctor_get(v_fst_2935_, 0);
lean_dec(v_unused_3119_);
v___x_2995_ = v_fst_2935_;
v_isShared_2996_ = v_isSharedCheck_3116_;
goto v_resetjp_2994_;
}
else
{
lean_dec(v_fst_2935_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3116_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v_array_2997_; lean_object* v_start_2998_; lean_object* v_stop_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3003_; 
v_array_2997_ = lean_ctor_get(v_fst_2931_, 0);
v_start_2998_ = lean_ctor_get(v_fst_2931_, 1);
v_stop_2999_ = lean_ctor_get(v_fst_2931_, 2);
v___x_3000_ = lean_array_fget(v_array_2968_, v_start_2969_);
v___x_3001_ = lean_nat_add(v_start_2969_, v___x_2972_);
lean_dec(v_start_2969_);
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 1, v___x_3001_);
v___x_3003_ = v___x_2995_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_array_2968_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v___x_3001_);
lean_ctor_set(v_reuseFailAlloc_3115_, 2, v_stop_2970_);
v___x_3003_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
uint8_t v___x_3004_; 
v___x_3004_ = lean_nat_dec_lt(v_start_2998_, v_stop_2999_);
if (v___x_3004_ == 0)
{
lean_object* v___x_3006_; 
lean_dec(v___x_3000_);
lean_dec(v___x_2971_);
lean_dec(v_next_2908_);
lean_dec(v_numDiscrEqs_2907_);
lean_dec_ref(v_inst_2906_);
lean_dec(v_fst_2905_);
lean_dec(v___f_2904_);
lean_dec(v_onAlt_2903_);
lean_dec_ref(v_inst_2900_);
lean_dec(v_inst_2899_);
lean_dec_ref(v_inst_2898_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 1, v___x_2975_);
lean_ctor_set(v___x_2937_, 0, v___x_3003_);
v___x_3006_ = v___x_2937_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_3003_);
lean_ctor_set(v_reuseFailAlloc_3021_, 1, v___x_2975_);
v___x_3006_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
lean_object* v___x_3008_; 
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 1, v___x_3006_);
v___x_3008_ = v___x_2933_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_fst_2931_);
lean_ctor_set(v_reuseFailAlloc_3020_, 1, v___x_3006_);
v___x_3008_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
lean_object* v___x_3010_; 
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 1, v___x_3008_);
v___x_3010_ = v___x_2929_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_fst_2927_);
lean_ctor_set(v_reuseFailAlloc_3019_, 1, v___x_3008_);
v___x_3010_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
lean_object* v___x_3012_; 
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 1, v___x_3010_);
v___x_3012_ = v___x_2925_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_fst_2923_);
lean_ctor_set(v_reuseFailAlloc_3018_, 1, v___x_3010_);
v___x_3012_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
lean_object* v___x_3014_; 
if (v_isShared_2922_ == 0)
{
lean_ctor_set(v___x_2921_, 1, v___x_3012_);
v___x_3014_ = v___x_2921_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_fst_2919_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v___x_3012_);
v___x_3014_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3014_);
v___x_3016_ = lean_apply_2(v_toPure_2894_, lean_box(0), v___x_3015_);
v___y_2944_ = v___x_3016_;
goto v___jp_2943_;
}
}
}
}
}
}
else
{
lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3111_; 
lean_inc(v_stop_2999_);
lean_inc(v_start_2998_);
lean_inc_ref(v_array_2997_);
v_isSharedCheck_3111_ = !lean_is_exclusive(v_fst_2931_);
if (v_isSharedCheck_3111_ == 0)
{
lean_object* v_unused_3112_; lean_object* v_unused_3113_; lean_object* v_unused_3114_; 
v_unused_3112_ = lean_ctor_get(v_fst_2931_, 2);
lean_dec(v_unused_3112_);
v_unused_3113_ = lean_ctor_get(v_fst_2931_, 1);
lean_dec(v_unused_3113_);
v_unused_3114_ = lean_ctor_get(v_fst_2931_, 0);
lean_dec(v_unused_3114_);
v___x_3023_ = v_fst_2931_;
v_isShared_3024_ = v_isSharedCheck_3111_;
goto v_resetjp_3022_;
}
else
{
lean_dec(v_fst_2931_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3111_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v_array_3025_; lean_object* v_start_3026_; lean_object* v_stop_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3031_; 
v_array_3025_ = lean_ctor_get(v_fst_2927_, 0);
v_start_3026_ = lean_ctor_get(v_fst_2927_, 1);
v_stop_3027_ = lean_ctor_get(v_fst_2927_, 2);
v___x_3028_ = lean_array_fget(v_array_2997_, v_start_2998_);
v___x_3029_ = lean_nat_add(v_start_2998_, v___x_2972_);
lean_dec(v_start_2998_);
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 1, v___x_3029_);
v___x_3031_ = v___x_3023_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_array_2997_);
lean_ctor_set(v_reuseFailAlloc_3110_, 1, v___x_3029_);
lean_ctor_set(v_reuseFailAlloc_3110_, 2, v_stop_2999_);
v___x_3031_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
uint8_t v___x_3032_; 
v___x_3032_ = lean_nat_dec_lt(v_start_3026_, v_stop_3027_);
if (v___x_3032_ == 0)
{
lean_object* v___x_3034_; 
lean_dec(v___x_3028_);
lean_dec(v___x_3000_);
lean_dec(v___x_2971_);
lean_dec(v_next_2908_);
lean_dec(v_numDiscrEqs_2907_);
lean_dec_ref(v_inst_2906_);
lean_dec(v_fst_2905_);
lean_dec(v___f_2904_);
lean_dec(v_onAlt_2903_);
lean_dec_ref(v_inst_2900_);
lean_dec(v_inst_2899_);
lean_dec_ref(v_inst_2898_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 1, v___x_2975_);
lean_ctor_set(v___x_2937_, 0, v___x_3003_);
v___x_3034_ = v___x_2937_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3003_);
lean_ctor_set(v_reuseFailAlloc_3049_, 1, v___x_2975_);
v___x_3034_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
lean_object* v___x_3036_; 
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 1, v___x_3034_);
lean_ctor_set(v___x_2933_, 0, v___x_3031_);
v___x_3036_ = v___x_2933_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3031_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v___x_3034_);
v___x_3036_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
lean_object* v___x_3038_; 
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 1, v___x_3036_);
v___x_3038_ = v___x_2929_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_fst_2927_);
lean_ctor_set(v_reuseFailAlloc_3047_, 1, v___x_3036_);
v___x_3038_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
lean_object* v___x_3040_; 
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 1, v___x_3038_);
v___x_3040_ = v___x_2925_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_fst_2923_);
lean_ctor_set(v_reuseFailAlloc_3046_, 1, v___x_3038_);
v___x_3040_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_object* v___x_3042_; 
if (v_isShared_2922_ == 0)
{
lean_ctor_set(v___x_2921_, 1, v___x_3040_);
v___x_3042_ = v___x_2921_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_fst_2919_);
lean_ctor_set(v_reuseFailAlloc_3045_, 1, v___x_3040_);
v___x_3042_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3042_);
v___x_3044_ = lean_apply_2(v_toPure_2894_, lean_box(0), v___x_3043_);
v___y_2944_ = v___x_3044_;
goto v___jp_2943_;
}
}
}
}
}
}
else
{
lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3106_; 
lean_inc(v_stop_3027_);
lean_inc(v_start_3026_);
lean_inc_ref(v_array_3025_);
v_isSharedCheck_3106_ = !lean_is_exclusive(v_fst_2927_);
if (v_isSharedCheck_3106_ == 0)
{
lean_object* v_unused_3107_; lean_object* v_unused_3108_; lean_object* v_unused_3109_; 
v_unused_3107_ = lean_ctor_get(v_fst_2927_, 2);
lean_dec(v_unused_3107_);
v_unused_3108_ = lean_ctor_get(v_fst_2927_, 1);
lean_dec(v_unused_3108_);
v_unused_3109_ = lean_ctor_get(v_fst_2927_, 0);
lean_dec(v_unused_3109_);
v___x_3051_ = v_fst_2927_;
v_isShared_3052_ = v_isSharedCheck_3106_;
goto v_resetjp_3050_;
}
else
{
lean_dec(v_fst_2927_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3106_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v_array_3053_; lean_object* v_start_3054_; lean_object* v_stop_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3059_; 
v_array_3053_ = lean_ctor_get(v_fst_2923_, 0);
v_start_3054_ = lean_ctor_get(v_fst_2923_, 1);
v_stop_3055_ = lean_ctor_get(v_fst_2923_, 2);
v___x_3056_ = lean_array_fget(v_array_3025_, v_start_3026_);
v___x_3057_ = lean_nat_add(v_start_3026_, v___x_2972_);
lean_dec(v_start_3026_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 1, v___x_3057_);
v___x_3059_ = v___x_3051_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_array_3025_);
lean_ctor_set(v_reuseFailAlloc_3105_, 1, v___x_3057_);
lean_ctor_set(v_reuseFailAlloc_3105_, 2, v_stop_3027_);
v___x_3059_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
uint8_t v___x_3060_; 
v___x_3060_ = lean_nat_dec_lt(v_start_3054_, v_stop_3055_);
if (v___x_3060_ == 0)
{
lean_object* v___x_3062_; 
lean_dec(v___x_3056_);
lean_dec(v___x_3028_);
lean_dec(v___x_3000_);
lean_dec(v___x_2971_);
lean_dec(v_next_2908_);
lean_dec(v_numDiscrEqs_2907_);
lean_dec_ref(v_inst_2906_);
lean_dec(v_fst_2905_);
lean_dec(v___f_2904_);
lean_dec(v_onAlt_2903_);
lean_dec_ref(v_inst_2900_);
lean_dec(v_inst_2899_);
lean_dec_ref(v_inst_2898_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 1, v___x_2975_);
lean_ctor_set(v___x_2937_, 0, v___x_3003_);
v___x_3062_ = v___x_2937_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3003_);
lean_ctor_set(v_reuseFailAlloc_3077_, 1, v___x_2975_);
v___x_3062_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
lean_object* v___x_3064_; 
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 1, v___x_3062_);
lean_ctor_set(v___x_2933_, 0, v___x_3031_);
v___x_3064_ = v___x_2933_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3031_);
lean_ctor_set(v_reuseFailAlloc_3076_, 1, v___x_3062_);
v___x_3064_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
lean_object* v___x_3066_; 
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 1, v___x_3064_);
lean_ctor_set(v___x_2929_, 0, v___x_3059_);
v___x_3066_ = v___x_2929_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3059_);
lean_ctor_set(v_reuseFailAlloc_3075_, 1, v___x_3064_);
v___x_3066_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
lean_object* v___x_3068_; 
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 1, v___x_3066_);
v___x_3068_ = v___x_2925_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_fst_2923_);
lean_ctor_set(v_reuseFailAlloc_3074_, 1, v___x_3066_);
v___x_3068_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
lean_object* v___x_3070_; 
if (v_isShared_2922_ == 0)
{
lean_ctor_set(v___x_2921_, 1, v___x_3068_);
v___x_3070_ = v___x_2921_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_fst_2919_);
lean_ctor_set(v_reuseFailAlloc_3073_, 1, v___x_3068_);
v___x_3070_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3070_);
v___x_3072_ = lean_apply_2(v_toPure_2894_, lean_box(0), v___x_3071_);
v___y_2944_ = v___x_3072_;
goto v___jp_2943_;
}
}
}
}
}
}
else
{
lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3101_; 
lean_inc(v_stop_3055_);
lean_inc(v_start_3054_);
lean_inc_ref(v_array_3053_);
lean_del_object(v___x_2937_);
lean_del_object(v___x_2933_);
lean_del_object(v___x_2929_);
lean_del_object(v___x_2925_);
lean_del_object(v___x_2921_);
v_isSharedCheck_3101_ = !lean_is_exclusive(v_fst_2923_);
if (v_isSharedCheck_3101_ == 0)
{
lean_object* v_unused_3102_; lean_object* v_unused_3103_; lean_object* v_unused_3104_; 
v_unused_3102_ = lean_ctor_get(v_fst_2923_, 2);
lean_dec(v_unused_3102_);
v_unused_3103_ = lean_ctor_get(v_fst_2923_, 1);
lean_dec(v_unused_3103_);
v_unused_3104_ = lean_ctor_get(v_fst_2923_, 0);
lean_dec(v_unused_3104_);
v___x_3079_ = v_fst_2923_;
v_isShared_3080_ = v_isSharedCheck_3101_;
goto v_resetjp_3078_;
}
else
{
lean_dec(v_fst_2923_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3101_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v_numOverlaps_3081_; uint8_t v_hasUnitThunk_3082_; uint8_t v___x_3083_; 
v_numOverlaps_3081_ = lean_ctor_get(v___x_3056_, 1);
v_hasUnitThunk_3082_ = lean_ctor_get_uint8(v___x_3056_, sizeof(void*)*2);
v___x_3083_ = lean_nat_dec_eq(v_numOverlaps_3081_, v___x_2897_);
if (v___x_3083_ == 0)
{
lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
lean_del_object(v___x_3079_);
lean_dec_ref(v___x_3059_);
lean_dec(v___x_3056_);
lean_dec(v_stop_3055_);
lean_dec(v_start_3054_);
lean_dec_ref(v_array_3053_);
lean_dec_ref(v___x_3031_);
lean_dec(v___x_3028_);
lean_dec_ref(v___x_3003_);
lean_dec(v___x_3000_);
lean_dec_ref(v___x_2975_);
lean_dec(v___x_2971_);
lean_dec(v_fst_2919_);
lean_dec(v_next_2908_);
lean_dec(v_numDiscrEqs_2907_);
lean_dec_ref(v_inst_2906_);
lean_dec(v_fst_2905_);
lean_dec(v___f_2904_);
lean_dec(v_onAlt_2903_);
lean_dec_ref(v_inst_2900_);
lean_dec(v_inst_2899_);
lean_dec(v_toPure_2894_);
v___x_3084_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7);
v___x_3085_ = l_instInhabitedOfMonad___redArg(v_inst_2898_, v___x_3084_);
v___x_3086_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9);
v___x_3087_ = l_panic___redArg(v___x_3085_, v___x_3086_);
v___y_2944_ = v___x_3087_;
goto v___jp_2943_;
}
else
{
lean_object* v___f_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___f_3093_; lean_object* v___x_3094_; lean_object* v___x_3096_; 
lean_inc(v_inst_2899_);
lean_inc(v_toPure_2894_);
lean_inc(v___x_3028_);
v___f_3088_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed), 4, 3);
lean_closure_set(v___f_3088_, 0, v___x_3028_);
lean_closure_set(v___f_3088_, 1, v_toPure_2894_);
lean_closure_set(v___f_3088_, 2, v_inst_2899_);
v___x_3089_ = lean_array_fget_borrowed(v_array_3053_, v_start_3054_);
v___x_3090_ = lean_box(v___x_2901_);
v___x_3091_ = lean_box(v_useSplitter_2902_);
v___x_3092_ = lean_box(v_hasUnitThunk_3082_);
lean_inc(v_toPure_2894_);
lean_inc_ref(v_inst_2906_);
lean_inc(v___x_3089_);
lean_inc(v_toBind_2895_);
lean_inc_ref(v_inst_2898_);
v___f_3093_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed), 21, 19);
lean_closure_set(v___f_3093_, 0, v___x_3028_);
lean_closure_set(v___f_3093_, 1, v_inst_2898_);
lean_closure_set(v___f_3093_, 2, v_inst_2900_);
lean_closure_set(v___f_3093_, 3, v___x_3090_);
lean_closure_set(v___f_3093_, 4, v___x_3091_);
lean_closure_set(v___f_3093_, 5, v_inst_2899_);
lean_closure_set(v___f_3093_, 6, v_onAlt_2903_);
lean_closure_set(v___f_3093_, 7, v_next_2908_);
lean_closure_set(v___f_3093_, 8, v_toBind_2895_);
lean_closure_set(v___f_3093_, 9, v___x_3089_);
lean_closure_set(v___f_3093_, 10, v___f_2904_);
lean_closure_set(v___f_3093_, 11, v_fst_2905_);
lean_closure_set(v___f_3093_, 12, v_inst_2906_);
lean_closure_set(v___f_3093_, 13, v_numDiscrEqs_2907_);
lean_closure_set(v___f_3093_, 14, v___f_3088_);
lean_closure_set(v___f_3093_, 15, v___x_3092_);
lean_closure_set(v___f_3093_, 16, v_toPure_2894_);
lean_closure_set(v___f_3093_, 17, v___x_2972_);
lean_closure_set(v___f_3093_, 18, v___x_2971_);
v___x_3094_ = lean_nat_add(v_start_3054_, v___x_2972_);
lean_dec(v_start_3054_);
if (v_isShared_3080_ == 0)
{
lean_ctor_set(v___x_3079_, 1, v___x_3094_);
v___x_3096_ = v___x_3079_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_array_3053_);
lean_ctor_set(v_reuseFailAlloc_3100_, 1, v___x_3094_);
lean_ctor_set(v_reuseFailAlloc_3100_, 2, v_stop_3055_);
v___x_3096_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
lean_object* v___f_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___f_3097_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__45), 8, 7);
lean_closure_set(v___f_3097_, 0, v_fst_2919_);
lean_closure_set(v___f_3097_, 1, v___x_3003_);
lean_closure_set(v___f_3097_, 2, v___x_2975_);
lean_closure_set(v___f_3097_, 3, v___x_3031_);
lean_closure_set(v___f_3097_, 4, v___x_3059_);
lean_closure_set(v___f_3097_, 5, v___x_3096_);
lean_closure_set(v___f_3097_, 6, v_toPure_2894_);
v___x_3098_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(v_inst_2898_, v_inst_2906_, v___x_3000_, v___x_3056_, v___f_3093_);
lean_inc(v_toBind_2895_);
v___x_3099_ = lean_apply_4(v_toBind_2895_, lean_box(0), lean_box(0), v___x_3098_, v___f_3097_);
v___y_2944_ = v___x_3099_;
goto v___jp_2943_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_2943_:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; 
lean_inc(v_toBind_2895_);
v___x_2945_ = lean_apply_4(v_toBind_2895_, lean_box(0), lean_box(0), v___y_2944_, v___f_2896_);
v___x_2946_ = lean_apply_4(v_toBind_2895_, lean_box(0), lean_box(0), v___x_2945_, v___f_2942_);
return v___x_2946_;
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
lean_object* v___x_3135_ = _args[0];
lean_object* v_toPure_3136_ = _args[1];
lean_object* v_toBind_3137_ = _args[2];
lean_object* v___f_3138_ = _args[3];
lean_object* v___x_3139_ = _args[4];
lean_object* v_inst_3140_ = _args[5];
lean_object* v_inst_3141_ = _args[6];
lean_object* v_inst_3142_ = _args[7];
lean_object* v___x_3143_ = _args[8];
lean_object* v_useSplitter_3144_ = _args[9];
lean_object* v_onAlt_3145_ = _args[10];
lean_object* v___f_3146_ = _args[11];
lean_object* v_fst_3147_ = _args[12];
lean_object* v_inst_3148_ = _args[13];
lean_object* v_numDiscrEqs_3149_ = _args[14];
lean_object* v_next_3150_ = _args[15];
lean_object* v_acc_3151_ = _args[16];
lean_object* v_h_3152_ = _args[17];
lean_object* v_G_3153_ = _args[18];
_start:
{
uint8_t v___x_15828__boxed_3154_; uint8_t v_useSplitter_boxed_3155_; lean_object* v_res_3156_; 
v___x_15828__boxed_3154_ = lean_unbox(v___x_3143_);
v_useSplitter_boxed_3155_ = lean_unbox(v_useSplitter_3144_);
v_res_3156_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__46(v___x_3135_, v_toPure_3136_, v_toBind_3137_, v___f_3138_, v___x_3139_, v_inst_3140_, v_inst_3141_, v_inst_3142_, v___x_15828__boxed_3154_, v_useSplitter_boxed_3155_, v_onAlt_3145_, v___f_3146_, v_fst_3147_, v_inst_3148_, v_numDiscrEqs_3149_, v_next_3150_, v_acc_3151_, v_h_3152_, v_G_3153_);
lean_dec(v___x_3139_);
lean_dec(v___x_3135_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47(lean_object* v_fst_3157_, lean_object* v_numParams_3158_, lean_object* v_numDiscrs_3159_, lean_object* v_altInfos_3160_, lean_object* v_uElimPos_x3f_3161_, lean_object* v_snd_3162_, lean_object* v_overlaps_3163_, lean_object* v_splitterName_3164_, lean_object* v_matcherLevels_3165_, lean_object* v_params_x27_3166_, lean_object* v_fst_3167_, lean_object* v_discrs_x27_3168_, lean_object* v_fst_3169_, lean_object* v_toPure_3170_, lean_object* v_____do__lift_3171_){
_start:
{
lean_object* v_remaining_x27_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v_remaining_x27_3172_ = l_Array_append___redArg(v_fst_3157_, v_____do__lift_3171_);
v___x_3173_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3173_, 0, v_numParams_3158_);
lean_ctor_set(v___x_3173_, 1, v_numDiscrs_3159_);
lean_ctor_set(v___x_3173_, 2, v_altInfos_3160_);
lean_ctor_set(v___x_3173_, 3, v_uElimPos_x3f_3161_);
lean_ctor_set(v___x_3173_, 4, v_snd_3162_);
lean_ctor_set(v___x_3173_, 5, v_overlaps_3163_);
v___x_3174_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3173_);
lean_ctor_set(v___x_3174_, 1, v_splitterName_3164_);
lean_ctor_set(v___x_3174_, 2, v_matcherLevels_3165_);
lean_ctor_set(v___x_3174_, 3, v_params_x27_3166_);
lean_ctor_set(v___x_3174_, 4, v_fst_3167_);
lean_ctor_set(v___x_3174_, 5, v_discrs_x27_3168_);
lean_ctor_set(v___x_3174_, 6, v_fst_3169_);
lean_ctor_set(v___x_3174_, 7, v_remaining_x27_3172_);
v___x_3175_ = lean_apply_2(v_toPure_3170_, lean_box(0), v___x_3174_);
return v___x_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47___boxed(lean_object* v_fst_3176_, lean_object* v_numParams_3177_, lean_object* v_numDiscrs_3178_, lean_object* v_altInfos_3179_, lean_object* v_uElimPos_x3f_3180_, lean_object* v_snd_3181_, lean_object* v_overlaps_3182_, lean_object* v_splitterName_3183_, lean_object* v_matcherLevels_3184_, lean_object* v_params_x27_3185_, lean_object* v_fst_3186_, lean_object* v_discrs_x27_3187_, lean_object* v_fst_3188_, lean_object* v_toPure_3189_, lean_object* v_____do__lift_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__47(v_fst_3176_, v_numParams_3177_, v_numDiscrs_3178_, v_altInfos_3179_, v_uElimPos_x3f_3180_, v_snd_3181_, v_overlaps_3182_, v_splitterName_3183_, v_matcherLevels_3184_, v_params_x27_3185_, v_fst_3186_, v_discrs_x27_3187_, v_fst_3188_, v_toPure_3189_, v_____do__lift_3190_);
lean_dec_ref(v_____do__lift_3190_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48(lean_object* v_fst_3192_, lean_object* v_numParams_3193_, lean_object* v_numDiscrs_3194_, lean_object* v_altInfos_3195_, lean_object* v_uElimPos_x3f_3196_, lean_object* v_snd_3197_, lean_object* v_overlaps_3198_, lean_object* v_splitterName_3199_, lean_object* v_matcherLevels_3200_, lean_object* v_params_x27_3201_, lean_object* v_fst_3202_, lean_object* v_discrs_x27_3203_, lean_object* v_toPure_3204_, lean_object* v_onRemaining_3205_, lean_object* v_remaining_3206_, lean_object* v_toBind_3207_, lean_object* v_____s_3208_){
_start:
{
lean_object* v_fst_3209_; lean_object* v___f_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v_fst_3209_ = lean_ctor_get(v_____s_3208_, 0);
lean_inc(v_fst_3209_);
lean_dec_ref(v_____s_3208_);
v___f_3210_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__47___boxed), 15, 14);
lean_closure_set(v___f_3210_, 0, v_fst_3192_);
lean_closure_set(v___f_3210_, 1, v_numParams_3193_);
lean_closure_set(v___f_3210_, 2, v_numDiscrs_3194_);
lean_closure_set(v___f_3210_, 3, v_altInfos_3195_);
lean_closure_set(v___f_3210_, 4, v_uElimPos_x3f_3196_);
lean_closure_set(v___f_3210_, 5, v_snd_3197_);
lean_closure_set(v___f_3210_, 6, v_overlaps_3198_);
lean_closure_set(v___f_3210_, 7, v_splitterName_3199_);
lean_closure_set(v___f_3210_, 8, v_matcherLevels_3200_);
lean_closure_set(v___f_3210_, 9, v_params_x27_3201_);
lean_closure_set(v___f_3210_, 10, v_fst_3202_);
lean_closure_set(v___f_3210_, 11, v_discrs_x27_3203_);
lean_closure_set(v___f_3210_, 12, v_fst_3209_);
lean_closure_set(v___f_3210_, 13, v_toPure_3204_);
v___x_3211_ = lean_apply_1(v_onRemaining_3205_, v_remaining_3206_);
v___x_3212_ = lean_apply_4(v_toBind_3207_, lean_box(0), lean_box(0), v___x_3211_, v___f_3210_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed(lean_object** _args){
lean_object* v_fst_3213_ = _args[0];
lean_object* v_numParams_3214_ = _args[1];
lean_object* v_numDiscrs_3215_ = _args[2];
lean_object* v_altInfos_3216_ = _args[3];
lean_object* v_uElimPos_x3f_3217_ = _args[4];
lean_object* v_snd_3218_ = _args[5];
lean_object* v_overlaps_3219_ = _args[6];
lean_object* v_splitterName_3220_ = _args[7];
lean_object* v_matcherLevels_3221_ = _args[8];
lean_object* v_params_x27_3222_ = _args[9];
lean_object* v_fst_3223_ = _args[10];
lean_object* v_discrs_x27_3224_ = _args[11];
lean_object* v_toPure_3225_ = _args[12];
lean_object* v_onRemaining_3226_ = _args[13];
lean_object* v_remaining_3227_ = _args[14];
lean_object* v_toBind_3228_ = _args[15];
lean_object* v_____s_3229_ = _args[16];
_start:
{
lean_object* v_res_3230_; 
v_res_3230_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__48(v_fst_3213_, v_numParams_3214_, v_numDiscrs_3215_, v_altInfos_3216_, v_uElimPos_x3f_3217_, v_snd_3218_, v_overlaps_3219_, v_splitterName_3220_, v_matcherLevels_3221_, v_params_x27_3222_, v_fst_3223_, v_discrs_x27_3224_, v_toPure_3225_, v_onRemaining_3226_, v_remaining_3227_, v_toBind_3228_, v_____s_3229_);
return v_res_3230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49(lean_object* v_splitterMatchInfo_3231_, lean_object* v_fst_3232_, lean_object* v_numParams_3233_, lean_object* v_numDiscrs_3234_, lean_object* v_altInfos_3235_, lean_object* v_uElimPos_x3f_3236_, lean_object* v_snd_3237_, lean_object* v_overlaps_3238_, lean_object* v_splitterName_3239_, lean_object* v_matcherLevels_3240_, lean_object* v_params_x27_3241_, lean_object* v_fst_3242_, lean_object* v_discrs_x27_3243_, lean_object* v_toPure_3244_, lean_object* v_onRemaining_3245_, lean_object* v_remaining_3246_, lean_object* v_toBind_3247_, lean_object* v_origAltTypes_3248_, lean_object* v_alts_3249_, lean_object* v___x_3250_, lean_object* v___x_3251_, lean_object* v_remaining_x27_3252_, lean_object* v___f_3253_, lean_object* v_altTypes_3254_){
_start:
{
lean_object* v_altInfos_3255_; lean_object* v___f_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v_altInfos_3255_ = lean_ctor_get(v_splitterMatchInfo_3231_, 2);
lean_inc_ref(v_altInfos_3255_);
lean_dec_ref(v_splitterMatchInfo_3231_);
lean_inc(v_toBind_3247_);
lean_inc_ref(v_altInfos_3235_);
v___f_3256_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 17, 16);
lean_closure_set(v___f_3256_, 0, v_fst_3232_);
lean_closure_set(v___f_3256_, 1, v_numParams_3233_);
lean_closure_set(v___f_3256_, 2, v_numDiscrs_3234_);
lean_closure_set(v___f_3256_, 3, v_altInfos_3235_);
lean_closure_set(v___f_3256_, 4, v_uElimPos_x3f_3236_);
lean_closure_set(v___f_3256_, 5, v_snd_3237_);
lean_closure_set(v___f_3256_, 6, v_overlaps_3238_);
lean_closure_set(v___f_3256_, 7, v_splitterName_3239_);
lean_closure_set(v___f_3256_, 8, v_matcherLevels_3240_);
lean_closure_set(v___f_3256_, 9, v_params_x27_3241_);
lean_closure_set(v___f_3256_, 10, v_fst_3242_);
lean_closure_set(v___f_3256_, 11, v_discrs_x27_3243_);
lean_closure_set(v___f_3256_, 12, v_toPure_3244_);
lean_closure_set(v___f_3256_, 13, v_onRemaining_3245_);
lean_closure_set(v___f_3256_, 14, v_remaining_3246_);
lean_closure_set(v___f_3256_, 15, v_toBind_3247_);
v___x_3257_ = lean_array_get_size(v_altInfos_3235_);
v___x_3258_ = lean_array_get_size(v_altInfos_3255_);
v___x_3259_ = lean_array_get_size(v_origAltTypes_3248_);
v___x_3260_ = lean_array_get_size(v_altTypes_3254_);
lean_inc(v___x_3250_);
v___x_3261_ = l_Array_toSubarray___redArg(v_alts_3249_, v___x_3250_, v___x_3251_);
lean_inc(v___x_3250_);
v___x_3262_ = l_Array_toSubarray___redArg(v_altInfos_3235_, v___x_3250_, v___x_3257_);
lean_inc(v___x_3250_);
v___x_3263_ = l_Array_toSubarray___redArg(v_altInfos_3255_, v___x_3250_, v___x_3258_);
lean_inc(v___x_3250_);
v___x_3264_ = l_Array_toSubarray___redArg(v_origAltTypes_3248_, v___x_3250_, v___x_3259_);
lean_inc(v___x_3250_);
v___x_3265_ = l_Array_toSubarray___redArg(v_altTypes_3254_, v___x_3250_, v___x_3260_);
v___x_3266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3264_);
lean_ctor_set(v___x_3266_, 1, v___x_3265_);
v___x_3267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3263_);
lean_ctor_set(v___x_3267_, 1, v___x_3266_);
v___x_3268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3262_);
lean_ctor_set(v___x_3268_, 1, v___x_3267_);
v___x_3269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3261_);
lean_ctor_set(v___x_3269_, 1, v___x_3268_);
v___x_3270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3270_, 0, v_remaining_x27_3252_);
lean_ctor_set(v___x_3270_, 1, v___x_3269_);
v___x_3271_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3253_, v___x_3250_, v___x_3270_, lean_box(0));
v___x_3272_ = lean_apply_4(v_toBind_3247_, lean_box(0), lean_box(0), v___x_3271_, v___f_3256_);
return v___x_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed(lean_object** _args){
lean_object* v_splitterMatchInfo_3273_ = _args[0];
lean_object* v_fst_3274_ = _args[1];
lean_object* v_numParams_3275_ = _args[2];
lean_object* v_numDiscrs_3276_ = _args[3];
lean_object* v_altInfos_3277_ = _args[4];
lean_object* v_uElimPos_x3f_3278_ = _args[5];
lean_object* v_snd_3279_ = _args[6];
lean_object* v_overlaps_3280_ = _args[7];
lean_object* v_splitterName_3281_ = _args[8];
lean_object* v_matcherLevels_3282_ = _args[9];
lean_object* v_params_x27_3283_ = _args[10];
lean_object* v_fst_3284_ = _args[11];
lean_object* v_discrs_x27_3285_ = _args[12];
lean_object* v_toPure_3286_ = _args[13];
lean_object* v_onRemaining_3287_ = _args[14];
lean_object* v_remaining_3288_ = _args[15];
lean_object* v_toBind_3289_ = _args[16];
lean_object* v_origAltTypes_3290_ = _args[17];
lean_object* v_alts_3291_ = _args[18];
lean_object* v___x_3292_ = _args[19];
lean_object* v___x_3293_ = _args[20];
lean_object* v_remaining_x27_3294_ = _args[21];
lean_object* v___f_3295_ = _args[22];
lean_object* v_altTypes_3296_ = _args[23];
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__49(v_splitterMatchInfo_3273_, v_fst_3274_, v_numParams_3275_, v_numDiscrs_3276_, v_altInfos_3277_, v_uElimPos_x3f_3278_, v_snd_3279_, v_overlaps_3280_, v_splitterName_3281_, v_matcherLevels_3282_, v_params_x27_3283_, v_fst_3284_, v_discrs_x27_3285_, v_toPure_3286_, v_onRemaining_3287_, v_remaining_3288_, v_toBind_3289_, v_origAltTypes_3290_, v_alts_3291_, v___x_3292_, v___x_3293_, v_remaining_x27_3294_, v___f_3295_, v_altTypes_3296_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__50(lean_object* v___x_3298_, lean_object* v_aux2_3299_, lean_object* v_inst_3300_, lean_object* v_toBind_3301_, lean_object* v___f_3302_, lean_object* v_____r_3303_){
_start:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3304_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_3304_, 0, v___x_3298_);
lean_closure_set(v___x_3304_, 1, v_aux2_3299_);
v___x_3305_ = lean_apply_2(v_inst_3300_, lean_box(0), v___x_3304_);
v___x_3306_ = lean_apply_4(v_toBind_3301_, lean_box(0), lean_box(0), v___x_3305_, v___f_3302_);
return v___x_3306_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1(void){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3308_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__0));
v___x_3309_ = l_Lean_stringToMessageData(v___x_3308_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53(lean_object* v___x_3310_, lean_object* v_params_x27_3311_, lean_object* v_fst_3312_, lean_object* v_discrs_x27_3313_, lean_object* v_fst_3314_, lean_object* v_numParams_3315_, lean_object* v_numDiscrs_3316_, lean_object* v_altInfos_3317_, lean_object* v_uElimPos_x3f_3318_, lean_object* v_snd_3319_, lean_object* v_overlaps_3320_, lean_object* v_matcherLevels_3321_, lean_object* v_toPure_3322_, lean_object* v_onRemaining_3323_, lean_object* v_remaining_3324_, lean_object* v_toBind_3325_, lean_object* v_origAltTypes_3326_, lean_object* v_alts_3327_, lean_object* v___x_3328_, lean_object* v___x_3329_, lean_object* v_remaining_x27_3330_, lean_object* v___f_3331_, lean_object* v_inst_3332_, lean_object* v___x_3333_, lean_object* v_liftWith_3334_, lean_object* v_restoreM_3335_, lean_object* v_matchEqns_3336_){
_start:
{
lean_object* v_splitterName_3337_; lean_object* v_splitterMatchInfo_3338_; lean_object* v___x_3339_; lean_object* v_aux2_3340_; lean_object* v_aux2_3341_; lean_object* v_aux2_3342_; lean_object* v___x_3343_; lean_object* v___f_3344_; lean_object* v___f_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___f_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___f_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v_splitterName_3337_ = lean_ctor_get(v_matchEqns_3336_, 1);
lean_inc(v_splitterName_3337_);
v_splitterMatchInfo_3338_ = lean_ctor_get(v_matchEqns_3336_, 2);
lean_inc_ref(v_splitterMatchInfo_3338_);
lean_dec_ref(v_matchEqns_3336_);
lean_inc(v_splitterName_3337_);
v___x_3339_ = l_Lean_mkConst(v_splitterName_3337_, v___x_3310_);
v_aux2_3340_ = l_Lean_mkAppN(v___x_3339_, v_params_x27_3311_);
lean_inc_ref(v_fst_3312_);
v_aux2_3341_ = l_Lean_Expr_app___override(v_aux2_3340_, v_fst_3312_);
v_aux2_3342_ = l_Lean_mkAppN(v_aux2_3341_, v_discrs_x27_3313_);
lean_inc_ref(v_aux2_3342_);
v___x_3343_ = l_Lean_indentExpr(v_aux2_3342_);
lean_inc(v___x_3329_);
lean_inc(v_toBind_3325_);
v___f_3344_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed), 24, 23);
lean_closure_set(v___f_3344_, 0, v_splitterMatchInfo_3338_);
lean_closure_set(v___f_3344_, 1, v_fst_3314_);
lean_closure_set(v___f_3344_, 2, v_numParams_3315_);
lean_closure_set(v___f_3344_, 3, v_numDiscrs_3316_);
lean_closure_set(v___f_3344_, 4, v_altInfos_3317_);
lean_closure_set(v___f_3344_, 5, v_uElimPos_x3f_3318_);
lean_closure_set(v___f_3344_, 6, v_snd_3319_);
lean_closure_set(v___f_3344_, 7, v_overlaps_3320_);
lean_closure_set(v___f_3344_, 8, v_splitterName_3337_);
lean_closure_set(v___f_3344_, 9, v_matcherLevels_3321_);
lean_closure_set(v___f_3344_, 10, v_params_x27_3311_);
lean_closure_set(v___f_3344_, 11, v_fst_3312_);
lean_closure_set(v___f_3344_, 12, v_discrs_x27_3313_);
lean_closure_set(v___f_3344_, 13, v_toPure_3322_);
lean_closure_set(v___f_3344_, 14, v_onRemaining_3323_);
lean_closure_set(v___f_3344_, 15, v_remaining_3324_);
lean_closure_set(v___f_3344_, 16, v_toBind_3325_);
lean_closure_set(v___f_3344_, 17, v_origAltTypes_3326_);
lean_closure_set(v___f_3344_, 18, v_alts_3327_);
lean_closure_set(v___f_3344_, 19, v___x_3328_);
lean_closure_set(v___f_3344_, 20, v___x_3329_);
lean_closure_set(v___f_3344_, 21, v_remaining_x27_3330_);
lean_closure_set(v___f_3344_, 22, v___f_3331_);
lean_inc(v_toBind_3325_);
lean_inc(v_inst_3332_);
lean_inc_ref(v_aux2_3342_);
v___f_3345_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__50), 6, 5);
lean_closure_set(v___f_3345_, 0, v___x_3329_);
lean_closure_set(v___f_3345_, 1, v_aux2_3342_);
lean_closure_set(v___f_3345_, 2, v_inst_3332_);
lean_closure_set(v___f_3345_, 3, v_toBind_3325_);
lean_closure_set(v___f_3345_, 4, v___f_3344_);
v___x_3346_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1);
v___x_3347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3346_);
lean_ctor_set(v___x_3347_, 1, v___x_3343_);
v___x_3348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3347_);
lean_ctor_set(v___x_3348_, 1, v___x_3333_);
v___f_3349_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3349_, 0, v___x_3348_);
v___x_3350_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(v___x_3350_, 0, v_aux2_3342_);
v___x_3351_ = lean_apply_2(v_inst_3332_, lean_box(0), v___x_3350_);
v___f_3352_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3352_, 0, v___x_3351_);
lean_closure_set(v___f_3352_, 1, v___f_3349_);
v___x_3353_ = lean_apply_2(v_liftWith_3334_, lean_box(0), v___f_3352_);
v___x_3354_ = lean_apply_1(v_restoreM_3335_, lean_box(0));
lean_inc(v_toBind_3325_);
v___x_3355_ = lean_apply_4(v_toBind_3325_, lean_box(0), lean_box(0), v___x_3353_, v___x_3354_);
v___x_3356_ = lean_apply_4(v_toBind_3325_, lean_box(0), lean_box(0), v___x_3355_, v___f_3345_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed(lean_object** _args){
lean_object* v___x_3357_ = _args[0];
lean_object* v_params_x27_3358_ = _args[1];
lean_object* v_fst_3359_ = _args[2];
lean_object* v_discrs_x27_3360_ = _args[3];
lean_object* v_fst_3361_ = _args[4];
lean_object* v_numParams_3362_ = _args[5];
lean_object* v_numDiscrs_3363_ = _args[6];
lean_object* v_altInfos_3364_ = _args[7];
lean_object* v_uElimPos_x3f_3365_ = _args[8];
lean_object* v_snd_3366_ = _args[9];
lean_object* v_overlaps_3367_ = _args[10];
lean_object* v_matcherLevels_3368_ = _args[11];
lean_object* v_toPure_3369_ = _args[12];
lean_object* v_onRemaining_3370_ = _args[13];
lean_object* v_remaining_3371_ = _args[14];
lean_object* v_toBind_3372_ = _args[15];
lean_object* v_origAltTypes_3373_ = _args[16];
lean_object* v_alts_3374_ = _args[17];
lean_object* v___x_3375_ = _args[18];
lean_object* v___x_3376_ = _args[19];
lean_object* v_remaining_x27_3377_ = _args[20];
lean_object* v___f_3378_ = _args[21];
lean_object* v_inst_3379_ = _args[22];
lean_object* v___x_3380_ = _args[23];
lean_object* v_liftWith_3381_ = _args[24];
lean_object* v_restoreM_3382_ = _args[25];
lean_object* v_matchEqns_3383_ = _args[26];
_start:
{
lean_object* v_res_3384_; 
v_res_3384_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__53(v___x_3357_, v_params_x27_3358_, v_fst_3359_, v_discrs_x27_3360_, v_fst_3361_, v_numParams_3362_, v_numDiscrs_3363_, v_altInfos_3364_, v_uElimPos_x3f_3365_, v_snd_3366_, v_overlaps_3367_, v_matcherLevels_3368_, v_toPure_3369_, v_onRemaining_3370_, v_remaining_3371_, v_toBind_3372_, v_origAltTypes_3373_, v_alts_3374_, v___x_3375_, v___x_3376_, v_remaining_x27_3377_, v___f_3378_, v_inst_3379_, v___x_3380_, v_liftWith_3381_, v_restoreM_3382_, v_matchEqns_3383_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51(lean_object* v___x_3385_, lean_object* v_params_x27_3386_, lean_object* v_fst_3387_, lean_object* v_discrs_x27_3388_, lean_object* v_fst_3389_, lean_object* v_numParams_3390_, lean_object* v_numDiscrs_3391_, lean_object* v_altInfos_3392_, lean_object* v_uElimPos_x3f_3393_, lean_object* v_snd_3394_, lean_object* v_overlaps_3395_, lean_object* v_matcherLevels_3396_, lean_object* v_toPure_3397_, lean_object* v_onRemaining_3398_, lean_object* v_remaining_3399_, lean_object* v_toBind_3400_, lean_object* v_alts_3401_, lean_object* v___x_3402_, lean_object* v___x_3403_, lean_object* v_remaining_x27_3404_, lean_object* v___f_3405_, lean_object* v_inst_3406_, lean_object* v___x_3407_, lean_object* v_liftWith_3408_, lean_object* v_restoreM_3409_, lean_object* v_matcherName_3410_, lean_object* v_origAltTypes_3411_){
_start:
{
lean_object* v___f_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
lean_inc(v_inst_3406_);
lean_inc(v_toBind_3400_);
v___f_3412_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed), 27, 26);
lean_closure_set(v___f_3412_, 0, v___x_3385_);
lean_closure_set(v___f_3412_, 1, v_params_x27_3386_);
lean_closure_set(v___f_3412_, 2, v_fst_3387_);
lean_closure_set(v___f_3412_, 3, v_discrs_x27_3388_);
lean_closure_set(v___f_3412_, 4, v_fst_3389_);
lean_closure_set(v___f_3412_, 5, v_numParams_3390_);
lean_closure_set(v___f_3412_, 6, v_numDiscrs_3391_);
lean_closure_set(v___f_3412_, 7, v_altInfos_3392_);
lean_closure_set(v___f_3412_, 8, v_uElimPos_x3f_3393_);
lean_closure_set(v___f_3412_, 9, v_snd_3394_);
lean_closure_set(v___f_3412_, 10, v_overlaps_3395_);
lean_closure_set(v___f_3412_, 11, v_matcherLevels_3396_);
lean_closure_set(v___f_3412_, 12, v_toPure_3397_);
lean_closure_set(v___f_3412_, 13, v_onRemaining_3398_);
lean_closure_set(v___f_3412_, 14, v_remaining_3399_);
lean_closure_set(v___f_3412_, 15, v_toBind_3400_);
lean_closure_set(v___f_3412_, 16, v_origAltTypes_3411_);
lean_closure_set(v___f_3412_, 17, v_alts_3401_);
lean_closure_set(v___f_3412_, 18, v___x_3402_);
lean_closure_set(v___f_3412_, 19, v___x_3403_);
lean_closure_set(v___f_3412_, 20, v_remaining_x27_3404_);
lean_closure_set(v___f_3412_, 21, v___f_3405_);
lean_closure_set(v___f_3412_, 22, v_inst_3406_);
lean_closure_set(v___f_3412_, 23, v___x_3407_);
lean_closure_set(v___f_3412_, 24, v_liftWith_3408_);
lean_closure_set(v___f_3412_, 25, v_restoreM_3409_);
v___x_3413_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_getEquationsFor___boxed), 6, 1);
lean_closure_set(v___x_3413_, 0, v_matcherName_3410_);
v___x_3414_ = lean_apply_2(v_inst_3406_, lean_box(0), v___x_3413_);
v___x_3415_ = lean_apply_4(v_toBind_3400_, lean_box(0), lean_box(0), v___x_3414_, v___f_3412_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed(lean_object** _args){
lean_object* v___x_3416_ = _args[0];
lean_object* v_params_x27_3417_ = _args[1];
lean_object* v_fst_3418_ = _args[2];
lean_object* v_discrs_x27_3419_ = _args[3];
lean_object* v_fst_3420_ = _args[4];
lean_object* v_numParams_3421_ = _args[5];
lean_object* v_numDiscrs_3422_ = _args[6];
lean_object* v_altInfos_3423_ = _args[7];
lean_object* v_uElimPos_x3f_3424_ = _args[8];
lean_object* v_snd_3425_ = _args[9];
lean_object* v_overlaps_3426_ = _args[10];
lean_object* v_matcherLevels_3427_ = _args[11];
lean_object* v_toPure_3428_ = _args[12];
lean_object* v_onRemaining_3429_ = _args[13];
lean_object* v_remaining_3430_ = _args[14];
lean_object* v_toBind_3431_ = _args[15];
lean_object* v_alts_3432_ = _args[16];
lean_object* v___x_3433_ = _args[17];
lean_object* v___x_3434_ = _args[18];
lean_object* v_remaining_x27_3435_ = _args[19];
lean_object* v___f_3436_ = _args[20];
lean_object* v_inst_3437_ = _args[21];
lean_object* v___x_3438_ = _args[22];
lean_object* v_liftWith_3439_ = _args[23];
lean_object* v_restoreM_3440_ = _args[24];
lean_object* v_matcherName_3441_ = _args[25];
lean_object* v_origAltTypes_3442_ = _args[26];
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__51(v___x_3416_, v_params_x27_3417_, v_fst_3418_, v_discrs_x27_3419_, v_fst_3420_, v_numParams_3421_, v_numDiscrs_3422_, v_altInfos_3423_, v_uElimPos_x3f_3424_, v_snd_3425_, v_overlaps_3426_, v_matcherLevels_3427_, v_toPure_3428_, v_onRemaining_3429_, v_remaining_3430_, v_toBind_3431_, v_alts_3432_, v___x_3433_, v___x_3434_, v_remaining_x27_3435_, v___f_3436_, v_inst_3437_, v___x_3438_, v_liftWith_3439_, v_restoreM_3440_, v_matcherName_3441_, v_origAltTypes_3442_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52(lean_object* v_alts_3444_, lean_object* v_toPure_3445_, lean_object* v_toBind_3446_, lean_object* v___f_3447_, lean_object* v___x_3448_, lean_object* v_inst_3449_, lean_object* v_inst_3450_, lean_object* v_inst_3451_, uint8_t v___x_3452_, uint8_t v_useSplitter_3453_, lean_object* v_onAlt_3454_, lean_object* v___f_3455_, lean_object* v_fst_3456_, lean_object* v_inst_3457_, lean_object* v_numDiscrEqs_3458_, lean_object* v___x_3459_, lean_object* v_params_x27_3460_, lean_object* v_fst_3461_, lean_object* v_discrs_x27_3462_, lean_object* v_fst_3463_, lean_object* v_numParams_3464_, lean_object* v_numDiscrs_3465_, lean_object* v_altInfos_3466_, lean_object* v_uElimPos_x3f_3467_, lean_object* v_snd_3468_, lean_object* v_overlaps_3469_, lean_object* v_matcherLevels_3470_, lean_object* v_onRemaining_3471_, lean_object* v_remaining_3472_, lean_object* v_remaining_x27_3473_, lean_object* v___x_3474_, lean_object* v_liftWith_3475_, lean_object* v_restoreM_3476_, lean_object* v_matcherName_3477_, lean_object* v_aux1_3478_, lean_object* v_____r_3479_){
_start:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___f_3483_; lean_object* v___f_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3480_ = lean_array_get_size(v_alts_3444_);
v___x_3481_ = lean_box(v___x_3452_);
v___x_3482_ = lean_box(v_useSplitter_3453_);
lean_inc(v_inst_3450_);
lean_inc(v___x_3448_);
lean_inc(v_toBind_3446_);
lean_inc(v_toPure_3445_);
v___f_3483_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46___boxed), 19, 15);
lean_closure_set(v___f_3483_, 0, v___x_3480_);
lean_closure_set(v___f_3483_, 1, v_toPure_3445_);
lean_closure_set(v___f_3483_, 2, v_toBind_3446_);
lean_closure_set(v___f_3483_, 3, v___f_3447_);
lean_closure_set(v___f_3483_, 4, v___x_3448_);
lean_closure_set(v___f_3483_, 5, v_inst_3449_);
lean_closure_set(v___f_3483_, 6, v_inst_3450_);
lean_closure_set(v___f_3483_, 7, v_inst_3451_);
lean_closure_set(v___f_3483_, 8, v___x_3481_);
lean_closure_set(v___f_3483_, 9, v___x_3482_);
lean_closure_set(v___f_3483_, 10, v_onAlt_3454_);
lean_closure_set(v___f_3483_, 11, v___f_3455_);
lean_closure_set(v___f_3483_, 12, v_fst_3456_);
lean_closure_set(v___f_3483_, 13, v_inst_3457_);
lean_closure_set(v___f_3483_, 14, v_numDiscrEqs_3458_);
lean_inc(v_inst_3450_);
lean_inc(v_toBind_3446_);
v___f_3484_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed), 27, 26);
lean_closure_set(v___f_3484_, 0, v___x_3459_);
lean_closure_set(v___f_3484_, 1, v_params_x27_3460_);
lean_closure_set(v___f_3484_, 2, v_fst_3461_);
lean_closure_set(v___f_3484_, 3, v_discrs_x27_3462_);
lean_closure_set(v___f_3484_, 4, v_fst_3463_);
lean_closure_set(v___f_3484_, 5, v_numParams_3464_);
lean_closure_set(v___f_3484_, 6, v_numDiscrs_3465_);
lean_closure_set(v___f_3484_, 7, v_altInfos_3466_);
lean_closure_set(v___f_3484_, 8, v_uElimPos_x3f_3467_);
lean_closure_set(v___f_3484_, 9, v_snd_3468_);
lean_closure_set(v___f_3484_, 10, v_overlaps_3469_);
lean_closure_set(v___f_3484_, 11, v_matcherLevels_3470_);
lean_closure_set(v___f_3484_, 12, v_toPure_3445_);
lean_closure_set(v___f_3484_, 13, v_onRemaining_3471_);
lean_closure_set(v___f_3484_, 14, v_remaining_3472_);
lean_closure_set(v___f_3484_, 15, v_toBind_3446_);
lean_closure_set(v___f_3484_, 16, v_alts_3444_);
lean_closure_set(v___f_3484_, 17, v___x_3448_);
lean_closure_set(v___f_3484_, 18, v___x_3480_);
lean_closure_set(v___f_3484_, 19, v_remaining_x27_3473_);
lean_closure_set(v___f_3484_, 20, v___f_3483_);
lean_closure_set(v___f_3484_, 21, v_inst_3450_);
lean_closure_set(v___f_3484_, 22, v___x_3474_);
lean_closure_set(v___f_3484_, 23, v_liftWith_3475_);
lean_closure_set(v___f_3484_, 24, v_restoreM_3476_);
lean_closure_set(v___f_3484_, 25, v_matcherName_3477_);
v___x_3485_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_3485_, 0, v___x_3480_);
lean_closure_set(v___x_3485_, 1, v_aux1_3478_);
v___x_3486_ = lean_apply_2(v_inst_3450_, lean_box(0), v___x_3485_);
v___x_3487_ = lean_apply_4(v_toBind_3446_, lean_box(0), lean_box(0), v___x_3486_, v___f_3484_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed(lean_object** _args){
lean_object* v_alts_3488_ = _args[0];
lean_object* v_toPure_3489_ = _args[1];
lean_object* v_toBind_3490_ = _args[2];
lean_object* v___f_3491_ = _args[3];
lean_object* v___x_3492_ = _args[4];
lean_object* v_inst_3493_ = _args[5];
lean_object* v_inst_3494_ = _args[6];
lean_object* v_inst_3495_ = _args[7];
lean_object* v___x_3496_ = _args[8];
lean_object* v_useSplitter_3497_ = _args[9];
lean_object* v_onAlt_3498_ = _args[10];
lean_object* v___f_3499_ = _args[11];
lean_object* v_fst_3500_ = _args[12];
lean_object* v_inst_3501_ = _args[13];
lean_object* v_numDiscrEqs_3502_ = _args[14];
lean_object* v___x_3503_ = _args[15];
lean_object* v_params_x27_3504_ = _args[16];
lean_object* v_fst_3505_ = _args[17];
lean_object* v_discrs_x27_3506_ = _args[18];
lean_object* v_fst_3507_ = _args[19];
lean_object* v_numParams_3508_ = _args[20];
lean_object* v_numDiscrs_3509_ = _args[21];
lean_object* v_altInfos_3510_ = _args[22];
lean_object* v_uElimPos_x3f_3511_ = _args[23];
lean_object* v_snd_3512_ = _args[24];
lean_object* v_overlaps_3513_ = _args[25];
lean_object* v_matcherLevels_3514_ = _args[26];
lean_object* v_onRemaining_3515_ = _args[27];
lean_object* v_remaining_3516_ = _args[28];
lean_object* v_remaining_x27_3517_ = _args[29];
lean_object* v___x_3518_ = _args[30];
lean_object* v_liftWith_3519_ = _args[31];
lean_object* v_restoreM_3520_ = _args[32];
lean_object* v_matcherName_3521_ = _args[33];
lean_object* v_aux1_3522_ = _args[34];
lean_object* v_____r_3523_ = _args[35];
_start:
{
uint8_t v___x_16459__boxed_3524_; uint8_t v_useSplitter_boxed_3525_; lean_object* v_res_3526_; 
v___x_16459__boxed_3524_ = lean_unbox(v___x_3496_);
v_useSplitter_boxed_3525_ = lean_unbox(v_useSplitter_3497_);
v_res_3526_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__52(v_alts_3488_, v_toPure_3489_, v_toBind_3490_, v___f_3491_, v___x_3492_, v_inst_3493_, v_inst_3494_, v_inst_3495_, v___x_16459__boxed_3524_, v_useSplitter_boxed_3525_, v_onAlt_3498_, v___f_3499_, v_fst_3500_, v_inst_3501_, v_numDiscrEqs_3502_, v___x_3503_, v_params_x27_3504_, v_fst_3505_, v_discrs_x27_3506_, v_fst_3507_, v_numParams_3508_, v_numDiscrs_3509_, v_altInfos_3510_, v_uElimPos_x3f_3511_, v_snd_3512_, v_overlaps_3513_, v_matcherLevels_3514_, v_onRemaining_3515_, v_remaining_3516_, v_remaining_x27_3517_, v___x_3518_, v_liftWith_3519_, v_restoreM_3520_, v_matcherName_3521_, v_aux1_3522_, v_____r_3523_);
return v_res_3526_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__1(void){
_start:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3528_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__0));
v___x_3529_ = l_Lean_stringToMessageData(v___x_3528_);
return v___x_3529_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__3(void){
_start:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3531_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__2));
v___x_3532_ = l_Lean_stringToMessageData(v___x_3531_);
return v___x_3532_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__5(void){
_start:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3534_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__4));
v___x_3535_ = l_Lean_stringToMessageData(v___x_3534_);
return v___x_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56(lean_object* v_numParams_3536_, lean_object* v_numDiscrs_3537_, lean_object* v_altInfos_3538_, lean_object* v_uElimPos_x3f_3539_, lean_object* v_snd_3540_, lean_object* v_overlaps_3541_, lean_object* v_matcherName_3542_, lean_object* v_matcherLevels_3543_, lean_object* v_params_x27_3544_, lean_object* v_fst_3545_, lean_object* v_discrs_x27_3546_, lean_object* v_toPure_3547_, lean_object* v_onRemaining_3548_, lean_object* v_remaining_3549_, lean_object* v_toBind_3550_, lean_object* v_inst_3551_, lean_object* v_alts_3552_, lean_object* v___f_3553_, uint8_t v___x_3554_, lean_object* v_inst_3555_, lean_object* v_onAlt_3556_, lean_object* v_inst_3557_, lean_object* v___f_3558_, lean_object* v_matcherApp_3559_, lean_object* v___x_3560_, lean_object* v_remaining_x27_3561_, uint8_t v_useSplitter_3562_, uint8_t v_isCasesOn_3563_, lean_object* v___f_3564_, lean_object* v_inst_3565_, lean_object* v___f_3566_, lean_object* v_numDiscrEqs_3567_, lean_object* v_____s_3568_){
_start:
{
lean_object* v_snd_3569_; lean_object* v_fst_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3631_; 
v_snd_3569_ = lean_ctor_get(v_____s_3568_, 1);
v_fst_3570_ = lean_ctor_get(v_____s_3568_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v_____s_3568_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3572_ = v_____s_3568_;
v_isShared_3573_ = v_isSharedCheck_3631_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_snd_3569_);
lean_inc(v_fst_3570_);
lean_dec(v_____s_3568_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3631_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v_fst_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3629_; 
v_fst_3574_ = lean_ctor_get(v_snd_3569_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v_snd_3569_);
if (v_isSharedCheck_3629_ == 0)
{
lean_object* v_unused_3630_; 
v_unused_3630_ = lean_ctor_get(v_snd_3569_, 1);
lean_dec(v_unused_3630_);
v___x_3576_ = v_snd_3569_;
v_isShared_3577_ = v_isSharedCheck_3629_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_fst_3574_);
lean_dec(v_snd_3569_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3629_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___f_3578_; 
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
lean_inc(v_fst_3570_);
v___f_3578_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed), 17, 16);
lean_closure_set(v___f_3578_, 0, v_fst_3570_);
lean_closure_set(v___f_3578_, 1, v_numParams_3536_);
lean_closure_set(v___f_3578_, 2, v_numDiscrs_3537_);
lean_closure_set(v___f_3578_, 3, v_altInfos_3538_);
lean_closure_set(v___f_3578_, 4, v_uElimPos_x3f_3539_);
lean_closure_set(v___f_3578_, 5, v_snd_3540_);
lean_closure_set(v___f_3578_, 6, v_overlaps_3541_);
lean_closure_set(v___f_3578_, 7, v_matcherName_3542_);
lean_closure_set(v___f_3578_, 8, v_matcherLevels_3543_);
lean_closure_set(v___f_3578_, 9, v_params_x27_3544_);
lean_closure_set(v___f_3578_, 10, v_fst_3545_);
lean_closure_set(v___f_3578_, 11, v_discrs_x27_3546_);
lean_closure_set(v___f_3578_, 12, v_toPure_3547_);
lean_closure_set(v___f_3578_, 13, v_onRemaining_3548_);
lean_closure_set(v___f_3578_, 14, v_remaining_3549_);
lean_closure_set(v___f_3578_, 15, v_toBind_3550_);
if (v_useSplitter_3562_ == 0)
{
lean_del_object(v___x_3572_);
lean_dec(v_fst_3570_);
lean_dec(v_numDiscrEqs_3567_);
lean_dec(v___f_3566_);
lean_dec_ref(v_inst_3565_);
lean_dec(v___f_3564_);
lean_dec_ref(v_remaining_3549_);
lean_dec(v_onRemaining_3548_);
lean_dec_ref(v_overlaps_3541_);
lean_dec_ref(v_snd_3540_);
lean_dec(v_uElimPos_x3f_3539_);
lean_dec_ref(v_altInfos_3538_);
lean_dec(v_numDiscrs_3537_);
lean_dec(v_numParams_3536_);
goto v___jp_3579_;
}
else
{
if (v_isCasesOn_3563_ == 0)
{
lean_object* v_liftWith_3604_; lean_object* v_restoreM_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v_aux1_3608_; lean_object* v_aux1_3609_; lean_object* v_aux1_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3614_; 
lean_dec_ref(v___f_3578_);
lean_del_object(v___x_3576_);
lean_dec_ref(v_matcherApp_3559_);
lean_dec(v___f_3558_);
lean_dec(v___f_3553_);
v_liftWith_3604_ = lean_ctor_get(v_inst_3551_, 0);
lean_inc(v_liftWith_3604_);
v_restoreM_3605_ = lean_ctor_get(v_inst_3551_, 1);
lean_inc(v_restoreM_3605_);
lean_inc_ref(v_matcherLevels_3543_);
v___x_3606_ = lean_array_to_list(v_matcherLevels_3543_);
lean_inc(v___x_3606_);
lean_inc(v_matcherName_3542_);
v___x_3607_ = l_Lean_mkConst(v_matcherName_3542_, v___x_3606_);
v_aux1_3608_ = l_Lean_mkAppN(v___x_3607_, v_params_x27_3544_);
lean_inc_ref(v_fst_3545_);
v_aux1_3609_ = l_Lean_Expr_app___override(v_aux1_3608_, v_fst_3545_);
v_aux1_3610_ = l_Lean_mkAppN(v_aux1_3609_, v_discrs_x27_3546_);
lean_inc_ref(v_aux1_3610_);
v___x_3611_ = l_Lean_indentExpr(v_aux1_3610_);
v___x_3612_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__3);
if (v_isShared_3573_ == 0)
{
lean_ctor_set_tag(v___x_3572_, 7);
lean_ctor_set(v___x_3572_, 1, v___x_3611_);
lean_ctor_set(v___x_3572_, 0, v___x_3612_);
v___x_3614_ = v___x_3572_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v___x_3612_);
lean_ctor_set(v_reuseFailAlloc_3628_, 1, v___x_3611_);
v___x_3614_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___f_3618_; lean_object* v___x_3619_; lean_object* v___f_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___f_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3615_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__5);
v___x_3616_ = lean_box(v___x_3554_);
v___x_3617_ = lean_box(v_useSplitter_3562_);
lean_inc_ref(v_aux1_3610_);
lean_inc(v_restoreM_3605_);
lean_inc(v_liftWith_3604_);
lean_inc(v_inst_3555_);
lean_inc(v_toBind_3550_);
v___f_3618_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed), 36, 35);
lean_closure_set(v___f_3618_, 0, v_alts_3552_);
lean_closure_set(v___f_3618_, 1, v_toPure_3547_);
lean_closure_set(v___f_3618_, 2, v_toBind_3550_);
lean_closure_set(v___f_3618_, 3, v___f_3564_);
lean_closure_set(v___f_3618_, 4, v___x_3560_);
lean_closure_set(v___f_3618_, 5, v_inst_3557_);
lean_closure_set(v___f_3618_, 6, v_inst_3555_);
lean_closure_set(v___f_3618_, 7, v_inst_3565_);
lean_closure_set(v___f_3618_, 8, v___x_3616_);
lean_closure_set(v___f_3618_, 9, v___x_3617_);
lean_closure_set(v___f_3618_, 10, v_onAlt_3556_);
lean_closure_set(v___f_3618_, 11, v___f_3566_);
lean_closure_set(v___f_3618_, 12, v_fst_3574_);
lean_closure_set(v___f_3618_, 13, v_inst_3551_);
lean_closure_set(v___f_3618_, 14, v_numDiscrEqs_3567_);
lean_closure_set(v___f_3618_, 15, v___x_3606_);
lean_closure_set(v___f_3618_, 16, v_params_x27_3544_);
lean_closure_set(v___f_3618_, 17, v_fst_3545_);
lean_closure_set(v___f_3618_, 18, v_discrs_x27_3546_);
lean_closure_set(v___f_3618_, 19, v_fst_3570_);
lean_closure_set(v___f_3618_, 20, v_numParams_3536_);
lean_closure_set(v___f_3618_, 21, v_numDiscrs_3537_);
lean_closure_set(v___f_3618_, 22, v_altInfos_3538_);
lean_closure_set(v___f_3618_, 23, v_uElimPos_x3f_3539_);
lean_closure_set(v___f_3618_, 24, v_snd_3540_);
lean_closure_set(v___f_3618_, 25, v_overlaps_3541_);
lean_closure_set(v___f_3618_, 26, v_matcherLevels_3543_);
lean_closure_set(v___f_3618_, 27, v_onRemaining_3548_);
lean_closure_set(v___f_3618_, 28, v_remaining_3549_);
lean_closure_set(v___f_3618_, 29, v_remaining_x27_3561_);
lean_closure_set(v___f_3618_, 30, v___x_3615_);
lean_closure_set(v___f_3618_, 31, v_liftWith_3604_);
lean_closure_set(v___f_3618_, 32, v_restoreM_3605_);
lean_closure_set(v___f_3618_, 33, v_matcherName_3542_);
lean_closure_set(v___f_3618_, 34, v_aux1_3610_);
v___x_3619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3614_);
lean_ctor_set(v___x_3619_, 1, v___x_3615_);
v___f_3620_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3620_, 0, v___x_3619_);
v___x_3621_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(v___x_3621_, 0, v_aux1_3610_);
v___x_3622_ = lean_apply_2(v_inst_3555_, lean_box(0), v___x_3621_);
v___f_3623_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3623_, 0, v___x_3622_);
lean_closure_set(v___f_3623_, 1, v___f_3620_);
v___x_3624_ = lean_apply_2(v_liftWith_3604_, lean_box(0), v___f_3623_);
v___x_3625_ = lean_apply_1(v_restoreM_3605_, lean_box(0));
lean_inc(v_toBind_3550_);
v___x_3626_ = lean_apply_4(v_toBind_3550_, lean_box(0), lean_box(0), v___x_3624_, v___x_3625_);
v___x_3627_ = lean_apply_4(v_toBind_3550_, lean_box(0), lean_box(0), v___x_3626_, v___f_3618_);
return v___x_3627_;
}
}
else
{
lean_del_object(v___x_3572_);
lean_dec(v_fst_3570_);
lean_dec(v_numDiscrEqs_3567_);
lean_dec(v___f_3566_);
lean_dec_ref(v_inst_3565_);
lean_dec(v___f_3564_);
lean_dec_ref(v_remaining_3549_);
lean_dec(v_onRemaining_3548_);
lean_dec_ref(v_overlaps_3541_);
lean_dec_ref(v_snd_3540_);
lean_dec(v_uElimPos_x3f_3539_);
lean_dec_ref(v_altInfos_3538_);
lean_dec(v_numDiscrs_3537_);
lean_dec(v_numParams_3536_);
goto v___jp_3579_;
}
}
v___jp_3579_:
{
lean_object* v_liftWith_3580_; lean_object* v_restoreM_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v_aux_3584_; lean_object* v_aux_3585_; lean_object* v_aux_3586_; lean_object* v___x_3587_; uint8_t v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___f_3591_; lean_object* v___x_3592_; lean_object* v___x_3594_; 
v_liftWith_3580_ = lean_ctor_get(v_inst_3551_, 0);
lean_inc(v_liftWith_3580_);
v_restoreM_3581_ = lean_ctor_get(v_inst_3551_, 1);
lean_inc(v_restoreM_3581_);
v___x_3582_ = lean_array_to_list(v_matcherLevels_3543_);
v___x_3583_ = l_Lean_mkConst(v_matcherName_3542_, v___x_3582_);
v_aux_3584_ = l_Lean_mkAppN(v___x_3583_, v_params_x27_3544_);
lean_dec_ref(v_params_x27_3544_);
v_aux_3585_ = l_Lean_Expr_app___override(v_aux_3584_, v_fst_3545_);
v_aux_3586_ = l_Lean_mkAppN(v_aux_3585_, v_discrs_x27_3546_);
lean_dec_ref(v_discrs_x27_3546_);
lean_inc_ref(v_aux_3586_);
v___x_3587_ = l_Lean_indentExpr(v_aux_3586_);
v___x_3588_ = 1;
v___x_3589_ = lean_box(v___x_3554_);
v___x_3590_ = lean_box(v___x_3588_);
lean_inc_ref(v_aux_3586_);
lean_inc(v_inst_3555_);
lean_inc(v_toBind_3550_);
v___f_3591_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 18, 17);
lean_closure_set(v___f_3591_, 0, v_alts_3552_);
lean_closure_set(v___f_3591_, 1, v_toPure_3547_);
lean_closure_set(v___f_3591_, 2, v_toBind_3550_);
lean_closure_set(v___f_3591_, 3, v___f_3553_);
lean_closure_set(v___f_3591_, 4, v___x_3589_);
lean_closure_set(v___f_3591_, 5, v___x_3590_);
lean_closure_set(v___f_3591_, 6, v_inst_3555_);
lean_closure_set(v___f_3591_, 7, v_onAlt_3556_);
lean_closure_set(v___f_3591_, 8, v_inst_3551_);
lean_closure_set(v___f_3591_, 9, v_inst_3557_);
lean_closure_set(v___f_3591_, 10, v___f_3558_);
lean_closure_set(v___f_3591_, 11, v_fst_3574_);
lean_closure_set(v___f_3591_, 12, v_matcherApp_3559_);
lean_closure_set(v___f_3591_, 13, v___x_3560_);
lean_closure_set(v___f_3591_, 14, v_remaining_x27_3561_);
lean_closure_set(v___f_3591_, 15, v___f_3578_);
lean_closure_set(v___f_3591_, 16, v_aux_3586_);
v___x_3592_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__1);
if (v_isShared_3577_ == 0)
{
lean_ctor_set_tag(v___x_3576_, 7);
lean_ctor_set(v___x_3576_, 1, v___x_3587_);
lean_ctor_set(v___x_3576_, 0, v___x_3592_);
v___x_3594_ = v___x_3576_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v___x_3592_);
lean_ctor_set(v_reuseFailAlloc_3603_, 1, v___x_3587_);
v___x_3594_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
lean_object* v___f_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___f_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___f_3595_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3595_, 0, v___x_3594_);
v___x_3596_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(v___x_3596_, 0, v_aux_3586_);
v___x_3597_ = lean_apply_2(v_inst_3555_, lean_box(0), v___x_3596_);
v___f_3598_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3598_, 0, v___x_3597_);
lean_closure_set(v___f_3598_, 1, v___f_3595_);
v___x_3599_ = lean_apply_2(v_liftWith_3580_, lean_box(0), v___f_3598_);
v___x_3600_ = lean_apply_1(v_restoreM_3581_, lean_box(0));
lean_inc(v_toBind_3550_);
v___x_3601_ = lean_apply_4(v_toBind_3550_, lean_box(0), lean_box(0), v___x_3599_, v___x_3600_);
v___x_3602_ = lean_apply_4(v_toBind_3550_, lean_box(0), lean_box(0), v___x_3601_, v___f_3591_);
return v___x_3602_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56___boxed(lean_object** _args){
lean_object* v_numParams_3632_ = _args[0];
lean_object* v_numDiscrs_3633_ = _args[1];
lean_object* v_altInfos_3634_ = _args[2];
lean_object* v_uElimPos_x3f_3635_ = _args[3];
lean_object* v_snd_3636_ = _args[4];
lean_object* v_overlaps_3637_ = _args[5];
lean_object* v_matcherName_3638_ = _args[6];
lean_object* v_matcherLevels_3639_ = _args[7];
lean_object* v_params_x27_3640_ = _args[8];
lean_object* v_fst_3641_ = _args[9];
lean_object* v_discrs_x27_3642_ = _args[10];
lean_object* v_toPure_3643_ = _args[11];
lean_object* v_onRemaining_3644_ = _args[12];
lean_object* v_remaining_3645_ = _args[13];
lean_object* v_toBind_3646_ = _args[14];
lean_object* v_inst_3647_ = _args[15];
lean_object* v_alts_3648_ = _args[16];
lean_object* v___f_3649_ = _args[17];
lean_object* v___x_3650_ = _args[18];
lean_object* v_inst_3651_ = _args[19];
lean_object* v_onAlt_3652_ = _args[20];
lean_object* v_inst_3653_ = _args[21];
lean_object* v___f_3654_ = _args[22];
lean_object* v_matcherApp_3655_ = _args[23];
lean_object* v___x_3656_ = _args[24];
lean_object* v_remaining_x27_3657_ = _args[25];
lean_object* v_useSplitter_3658_ = _args[26];
lean_object* v_isCasesOn_3659_ = _args[27];
lean_object* v___f_3660_ = _args[28];
lean_object* v_inst_3661_ = _args[29];
lean_object* v___f_3662_ = _args[30];
lean_object* v_numDiscrEqs_3663_ = _args[31];
lean_object* v_____s_3664_ = _args[32];
_start:
{
uint8_t v___x_16531__boxed_3665_; uint8_t v_useSplitter_boxed_3666_; uint8_t v_isCasesOn_boxed_3667_; lean_object* v_res_3668_; 
v___x_16531__boxed_3665_ = lean_unbox(v___x_3650_);
v_useSplitter_boxed_3666_ = lean_unbox(v_useSplitter_3658_);
v_isCasesOn_boxed_3667_ = lean_unbox(v_isCasesOn_3659_);
v_res_3668_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__56(v_numParams_3632_, v_numDiscrs_3633_, v_altInfos_3634_, v_uElimPos_x3f_3635_, v_snd_3636_, v_overlaps_3637_, v_matcherName_3638_, v_matcherLevels_3639_, v_params_x27_3640_, v_fst_3641_, v_discrs_x27_3642_, v_toPure_3643_, v_onRemaining_3644_, v_remaining_3645_, v_toBind_3646_, v_inst_3647_, v_alts_3648_, v___f_3649_, v___x_16531__boxed_3665_, v_inst_3651_, v_onAlt_3652_, v_inst_3653_, v___f_3654_, v_matcherApp_3655_, v___x_3656_, v_remaining_x27_3657_, v_useSplitter_boxed_3666_, v_isCasesOn_boxed_3667_, v___f_3660_, v_inst_3661_, v___f_3662_, v_numDiscrEqs_3663_, v_____s_3664_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54(lean_object* v_numParams_3669_, lean_object* v_numDiscrs_3670_, lean_object* v_altInfos_3671_, lean_object* v_uElimPos_x3f_3672_, lean_object* v_snd_3673_, lean_object* v_overlaps_3674_, lean_object* v_matcherName_3675_, lean_object* v_params_x27_3676_, lean_object* v_fst_3677_, lean_object* v_discrs_x27_3678_, lean_object* v_toPure_3679_, lean_object* v_onRemaining_3680_, lean_object* v_remaining_3681_, lean_object* v_toBind_3682_, lean_object* v_inst_3683_, lean_object* v_alts_3684_, lean_object* v___f_3685_, uint8_t v___x_3686_, lean_object* v_inst_3687_, lean_object* v_onAlt_3688_, lean_object* v_inst_3689_, lean_object* v___f_3690_, lean_object* v_matcherApp_3691_, uint8_t v_useSplitter_3692_, uint8_t v_isCasesOn_3693_, lean_object* v___f_3694_, lean_object* v_inst_3695_, lean_object* v___f_3696_, lean_object* v_numDiscrEqs_3697_, lean_object* v_fst_3698_, lean_object* v___f_3699_, lean_object* v_matcherLevels_3700_){
_start:
{
lean_object* v___x_3701_; lean_object* v_remaining_x27_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___f_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; size_t v_sz_3713_; size_t v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3701_ = lean_unsigned_to_nat(0u);
v_remaining_x27_3702_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_3703_ = lean_box(v___x_3686_);
v___x_3704_ = lean_box(v_useSplitter_3692_);
v___x_3705_ = lean_box(v_isCasesOn_3693_);
lean_inc_ref(v_inst_3689_);
lean_inc(v_toBind_3682_);
lean_inc_ref(v_discrs_x27_3678_);
v___f_3706_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56___boxed), 33, 32);
lean_closure_set(v___f_3706_, 0, v_numParams_3669_);
lean_closure_set(v___f_3706_, 1, v_numDiscrs_3670_);
lean_closure_set(v___f_3706_, 2, v_altInfos_3671_);
lean_closure_set(v___f_3706_, 3, v_uElimPos_x3f_3672_);
lean_closure_set(v___f_3706_, 4, v_snd_3673_);
lean_closure_set(v___f_3706_, 5, v_overlaps_3674_);
lean_closure_set(v___f_3706_, 6, v_matcherName_3675_);
lean_closure_set(v___f_3706_, 7, v_matcherLevels_3700_);
lean_closure_set(v___f_3706_, 8, v_params_x27_3676_);
lean_closure_set(v___f_3706_, 9, v_fst_3677_);
lean_closure_set(v___f_3706_, 10, v_discrs_x27_3678_);
lean_closure_set(v___f_3706_, 11, v_toPure_3679_);
lean_closure_set(v___f_3706_, 12, v_onRemaining_3680_);
lean_closure_set(v___f_3706_, 13, v_remaining_3681_);
lean_closure_set(v___f_3706_, 14, v_toBind_3682_);
lean_closure_set(v___f_3706_, 15, v_inst_3683_);
lean_closure_set(v___f_3706_, 16, v_alts_3684_);
lean_closure_set(v___f_3706_, 17, v___f_3685_);
lean_closure_set(v___f_3706_, 18, v___x_3703_);
lean_closure_set(v___f_3706_, 19, v_inst_3687_);
lean_closure_set(v___f_3706_, 20, v_onAlt_3688_);
lean_closure_set(v___f_3706_, 21, v_inst_3689_);
lean_closure_set(v___f_3706_, 22, v___f_3690_);
lean_closure_set(v___f_3706_, 23, v_matcherApp_3691_);
lean_closure_set(v___f_3706_, 24, v___x_3701_);
lean_closure_set(v___f_3706_, 25, v_remaining_x27_3702_);
lean_closure_set(v___f_3706_, 26, v___x_3704_);
lean_closure_set(v___f_3706_, 27, v___x_3705_);
lean_closure_set(v___f_3706_, 28, v___f_3694_);
lean_closure_set(v___f_3706_, 29, v_inst_3695_);
lean_closure_set(v___f_3706_, 30, v___f_3696_);
lean_closure_set(v___f_3706_, 31, v_numDiscrEqs_3697_);
v___x_3707_ = l_Array_reverse___redArg(v_fst_3698_);
v___x_3708_ = lean_array_get_size(v___x_3707_);
v___x_3709_ = l_Array_toSubarray___redArg(v___x_3707_, v___x_3701_, v___x_3708_);
v___x_3710_ = l_Array_reverse___redArg(v_discrs_x27_3678_);
v___x_3711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3701_);
lean_ctor_set(v___x_3711_, 1, v___x_3709_);
v___x_3712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3712_, 0, v_remaining_x27_3702_);
lean_ctor_set(v___x_3712_, 1, v___x_3711_);
v_sz_3713_ = lean_array_size(v___x_3710_);
v___x_3714_ = ((size_t)0ULL);
v___x_3715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3689_, v___x_3710_, v___f_3699_, v_sz_3713_, v___x_3714_, v___x_3712_);
v___x_3716_ = lean_apply_4(v_toBind_3682_, lean_box(0), lean_box(0), v___x_3715_, v___f_3706_);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed(lean_object** _args){
lean_object* v_numParams_3717_ = _args[0];
lean_object* v_numDiscrs_3718_ = _args[1];
lean_object* v_altInfos_3719_ = _args[2];
lean_object* v_uElimPos_x3f_3720_ = _args[3];
lean_object* v_snd_3721_ = _args[4];
lean_object* v_overlaps_3722_ = _args[5];
lean_object* v_matcherName_3723_ = _args[6];
lean_object* v_params_x27_3724_ = _args[7];
lean_object* v_fst_3725_ = _args[8];
lean_object* v_discrs_x27_3726_ = _args[9];
lean_object* v_toPure_3727_ = _args[10];
lean_object* v_onRemaining_3728_ = _args[11];
lean_object* v_remaining_3729_ = _args[12];
lean_object* v_toBind_3730_ = _args[13];
lean_object* v_inst_3731_ = _args[14];
lean_object* v_alts_3732_ = _args[15];
lean_object* v___f_3733_ = _args[16];
lean_object* v___x_3734_ = _args[17];
lean_object* v_inst_3735_ = _args[18];
lean_object* v_onAlt_3736_ = _args[19];
lean_object* v_inst_3737_ = _args[20];
lean_object* v___f_3738_ = _args[21];
lean_object* v_matcherApp_3739_ = _args[22];
lean_object* v_useSplitter_3740_ = _args[23];
lean_object* v_isCasesOn_3741_ = _args[24];
lean_object* v___f_3742_ = _args[25];
lean_object* v_inst_3743_ = _args[26];
lean_object* v___f_3744_ = _args[27];
lean_object* v_numDiscrEqs_3745_ = _args[28];
lean_object* v_fst_3746_ = _args[29];
lean_object* v___f_3747_ = _args[30];
lean_object* v_matcherLevels_3748_ = _args[31];
_start:
{
uint8_t v___x_16680__boxed_3749_; uint8_t v_useSplitter_boxed_3750_; uint8_t v_isCasesOn_boxed_3751_; lean_object* v_res_3752_; 
v___x_16680__boxed_3749_ = lean_unbox(v___x_3734_);
v_useSplitter_boxed_3750_ = lean_unbox(v_useSplitter_3740_);
v_isCasesOn_boxed_3751_ = lean_unbox(v_isCasesOn_3741_);
v_res_3752_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__54(v_numParams_3717_, v_numDiscrs_3718_, v_altInfos_3719_, v_uElimPos_x3f_3720_, v_snd_3721_, v_overlaps_3722_, v_matcherName_3723_, v_params_x27_3724_, v_fst_3725_, v_discrs_x27_3726_, v_toPure_3727_, v_onRemaining_3728_, v_remaining_3729_, v_toBind_3730_, v_inst_3731_, v_alts_3732_, v___f_3733_, v___x_16680__boxed_3749_, v_inst_3735_, v_onAlt_3736_, v_inst_3737_, v___f_3738_, v_matcherApp_3739_, v_useSplitter_boxed_3750_, v_isCasesOn_boxed_3751_, v___f_3742_, v_inst_3743_, v___f_3744_, v_numDiscrEqs_3745_, v_fst_3746_, v___f_3747_, v_matcherLevels_3748_);
return v_res_3752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55(lean_object* v___f_3753_, lean_object* v_matcherLevels_3754_){
_start:
{
lean_object* v___x_3755_; 
v___x_3755_ = lean_apply_1(v___f_3753_, v_matcherLevels_3754_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58(lean_object* v_toMatcherInfo_3756_, lean_object* v_matcherName_3757_, lean_object* v_params_x27_3758_, lean_object* v_discrs_x27_3759_, lean_object* v_toPure_3760_, lean_object* v_onRemaining_3761_, lean_object* v_remaining_3762_, lean_object* v_toBind_3763_, lean_object* v_inst_3764_, lean_object* v_alts_3765_, lean_object* v___f_3766_, uint8_t v___x_3767_, lean_object* v_inst_3768_, lean_object* v_onAlt_3769_, lean_object* v_inst_3770_, lean_object* v___f_3771_, lean_object* v_matcherApp_3772_, uint8_t v_useSplitter_3773_, uint8_t v_isCasesOn_3774_, lean_object* v___f_3775_, lean_object* v_inst_3776_, lean_object* v___f_3777_, lean_object* v_numDiscrEqs_3778_, lean_object* v___f_3779_, lean_object* v_matcherLevels_3780_, lean_object* v_____x_3781_){
_start:
{
lean_object* v_snd_3782_; lean_object* v_snd_3783_; lean_object* v_fst_3784_; lean_object* v_fst_3785_; lean_object* v_fst_3786_; lean_object* v_snd_3787_; lean_object* v_numParams_3788_; lean_object* v_numDiscrs_3789_; lean_object* v_altInfos_3790_; lean_object* v_uElimPos_x3f_3791_; lean_object* v_overlaps_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___f_3796_; 
v_snd_3782_ = lean_ctor_get(v_____x_3781_, 1);
lean_inc(v_snd_3782_);
v_snd_3783_ = lean_ctor_get(v_snd_3782_, 1);
lean_inc(v_snd_3783_);
v_fst_3784_ = lean_ctor_get(v_____x_3781_, 0);
lean_inc(v_fst_3784_);
lean_dec_ref(v_____x_3781_);
v_fst_3785_ = lean_ctor_get(v_snd_3782_, 0);
lean_inc(v_fst_3785_);
lean_dec(v_snd_3782_);
v_fst_3786_ = lean_ctor_get(v_snd_3783_, 0);
lean_inc(v_fst_3786_);
v_snd_3787_ = lean_ctor_get(v_snd_3783_, 1);
lean_inc(v_snd_3787_);
lean_dec(v_snd_3783_);
v_numParams_3788_ = lean_ctor_get(v_toMatcherInfo_3756_, 0);
lean_inc(v_numParams_3788_);
v_numDiscrs_3789_ = lean_ctor_get(v_toMatcherInfo_3756_, 1);
lean_inc(v_numDiscrs_3789_);
v_altInfos_3790_ = lean_ctor_get(v_toMatcherInfo_3756_, 2);
lean_inc_ref(v_altInfos_3790_);
v_uElimPos_x3f_3791_ = lean_ctor_get(v_toMatcherInfo_3756_, 3);
lean_inc(v_uElimPos_x3f_3791_);
v_overlaps_3792_ = lean_ctor_get(v_toMatcherInfo_3756_, 5);
lean_inc_ref(v_overlaps_3792_);
lean_dec_ref(v_toMatcherInfo_3756_);
v___x_3793_ = lean_box(v___x_3767_);
v___x_3794_ = lean_box(v_useSplitter_3773_);
v___x_3795_ = lean_box(v_isCasesOn_3774_);
lean_inc(v_toBind_3763_);
lean_inc(v_toPure_3760_);
lean_inc(v_uElimPos_x3f_3791_);
v___f_3796_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed), 32, 31);
lean_closure_set(v___f_3796_, 0, v_numParams_3788_);
lean_closure_set(v___f_3796_, 1, v_numDiscrs_3789_);
lean_closure_set(v___f_3796_, 2, v_altInfos_3790_);
lean_closure_set(v___f_3796_, 3, v_uElimPos_x3f_3791_);
lean_closure_set(v___f_3796_, 4, v_snd_3787_);
lean_closure_set(v___f_3796_, 5, v_overlaps_3792_);
lean_closure_set(v___f_3796_, 6, v_matcherName_3757_);
lean_closure_set(v___f_3796_, 7, v_params_x27_3758_);
lean_closure_set(v___f_3796_, 8, v_fst_3784_);
lean_closure_set(v___f_3796_, 9, v_discrs_x27_3759_);
lean_closure_set(v___f_3796_, 10, v_toPure_3760_);
lean_closure_set(v___f_3796_, 11, v_onRemaining_3761_);
lean_closure_set(v___f_3796_, 12, v_remaining_3762_);
lean_closure_set(v___f_3796_, 13, v_toBind_3763_);
lean_closure_set(v___f_3796_, 14, v_inst_3764_);
lean_closure_set(v___f_3796_, 15, v_alts_3765_);
lean_closure_set(v___f_3796_, 16, v___f_3766_);
lean_closure_set(v___f_3796_, 17, v___x_3793_);
lean_closure_set(v___f_3796_, 18, v_inst_3768_);
lean_closure_set(v___f_3796_, 19, v_onAlt_3769_);
lean_closure_set(v___f_3796_, 20, v_inst_3770_);
lean_closure_set(v___f_3796_, 21, v___f_3771_);
lean_closure_set(v___f_3796_, 22, v_matcherApp_3772_);
lean_closure_set(v___f_3796_, 23, v___x_3794_);
lean_closure_set(v___f_3796_, 24, v___x_3795_);
lean_closure_set(v___f_3796_, 25, v___f_3775_);
lean_closure_set(v___f_3796_, 26, v_inst_3776_);
lean_closure_set(v___f_3796_, 27, v___f_3777_);
lean_closure_set(v___f_3796_, 28, v_numDiscrEqs_3778_);
lean_closure_set(v___f_3796_, 29, v_fst_3786_);
lean_closure_set(v___f_3796_, 30, v___f_3779_);
if (lean_obj_tag(v_uElimPos_x3f_3791_) == 0)
{
lean_object* v___f_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
lean_dec(v_fst_3785_);
v___f_3797_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55), 2, 1);
lean_closure_set(v___f_3797_, 0, v___f_3796_);
v___x_3798_ = lean_apply_2(v_toPure_3760_, lean_box(0), v_matcherLevels_3780_);
v___x_3799_ = lean_apply_4(v_toBind_3763_, lean_box(0), lean_box(0), v___x_3798_, v___f_3797_);
return v___x_3799_;
}
else
{
lean_object* v_val_3800_; lean_object* v___f_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
v_val_3800_ = lean_ctor_get(v_uElimPos_x3f_3791_, 0);
lean_inc(v_val_3800_);
lean_dec_ref(v_uElimPos_x3f_3791_);
v___f_3801_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55), 2, 1);
lean_closure_set(v___f_3801_, 0, v___f_3796_);
v___x_3802_ = lean_array_set(v_matcherLevels_3780_, v_val_3800_, v_fst_3785_);
lean_dec(v_val_3800_);
v___x_3803_ = lean_apply_2(v_toPure_3760_, lean_box(0), v___x_3802_);
v___x_3804_ = lean_apply_4(v_toBind_3763_, lean_box(0), lean_box(0), v___x_3803_, v___f_3801_);
return v___x_3804_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed(lean_object** _args){
lean_object* v_toMatcherInfo_3805_ = _args[0];
lean_object* v_matcherName_3806_ = _args[1];
lean_object* v_params_x27_3807_ = _args[2];
lean_object* v_discrs_x27_3808_ = _args[3];
lean_object* v_toPure_3809_ = _args[4];
lean_object* v_onRemaining_3810_ = _args[5];
lean_object* v_remaining_3811_ = _args[6];
lean_object* v_toBind_3812_ = _args[7];
lean_object* v_inst_3813_ = _args[8];
lean_object* v_alts_3814_ = _args[9];
lean_object* v___f_3815_ = _args[10];
lean_object* v___x_3816_ = _args[11];
lean_object* v_inst_3817_ = _args[12];
lean_object* v_onAlt_3818_ = _args[13];
lean_object* v_inst_3819_ = _args[14];
lean_object* v___f_3820_ = _args[15];
lean_object* v_matcherApp_3821_ = _args[16];
lean_object* v_useSplitter_3822_ = _args[17];
lean_object* v_isCasesOn_3823_ = _args[18];
lean_object* v___f_3824_ = _args[19];
lean_object* v_inst_3825_ = _args[20];
lean_object* v___f_3826_ = _args[21];
lean_object* v_numDiscrEqs_3827_ = _args[22];
lean_object* v___f_3828_ = _args[23];
lean_object* v_matcherLevels_3829_ = _args[24];
lean_object* v_____x_3830_ = _args[25];
_start:
{
uint8_t v___x_16749__boxed_3831_; uint8_t v_useSplitter_boxed_3832_; uint8_t v_isCasesOn_boxed_3833_; lean_object* v_res_3834_; 
v___x_16749__boxed_3831_ = lean_unbox(v___x_3816_);
v_useSplitter_boxed_3832_ = lean_unbox(v_useSplitter_3822_);
v_isCasesOn_boxed_3833_ = lean_unbox(v_isCasesOn_3823_);
v_res_3834_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__58(v_toMatcherInfo_3805_, v_matcherName_3806_, v_params_x27_3807_, v_discrs_x27_3808_, v_toPure_3809_, v_onRemaining_3810_, v_remaining_3811_, v_toBind_3812_, v_inst_3813_, v_alts_3814_, v___f_3815_, v___x_16749__boxed_3831_, v_inst_3817_, v_onAlt_3818_, v_inst_3819_, v___f_3820_, v_matcherApp_3821_, v_useSplitter_boxed_3832_, v_isCasesOn_boxed_3833_, v___f_3824_, v_inst_3825_, v___f_3826_, v_numDiscrEqs_3827_, v___f_3828_, v_matcherLevels_3829_, v_____x_3830_);
return v_res_3834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57(lean_object* v_toPure_3835_, lean_object* v_inst_3836_, lean_object* v_toBind_3837_, lean_object* v_toMatcherInfo_3838_, lean_object* v_inst_3839_, lean_object* v___f_3840_, lean_object* v_onMotive_3841_, lean_object* v_discrs_3842_, lean_object* v_inst_3843_, lean_object* v_matcherName_3844_, lean_object* v_params_x27_3845_, lean_object* v_onRemaining_3846_, lean_object* v_remaining_3847_, lean_object* v_inst_3848_, lean_object* v_alts_3849_, lean_object* v___f_3850_, lean_object* v_onAlt_3851_, lean_object* v___f_3852_, lean_object* v_matcherApp_3853_, uint8_t v_useSplitter_3854_, uint8_t v_isCasesOn_3855_, lean_object* v___f_3856_, lean_object* v___f_3857_, lean_object* v_numDiscrEqs_3858_, lean_object* v___f_3859_, lean_object* v_matcherLevels_3860_, lean_object* v_motive_3861_, lean_object* v_discrs_x27_3862_){
_start:
{
lean_object* v___f_3863_; uint8_t v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___f_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
lean_inc_ref(v_inst_3843_);
lean_inc_ref(v_inst_3839_);
lean_inc_ref(v_discrs_x27_3862_);
lean_inc_ref(v_toMatcherInfo_3838_);
lean_inc(v_toBind_3837_);
lean_inc(v_inst_3836_);
lean_inc(v_toPure_3835_);
v___f_3863_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__19___boxed), 12, 10);
lean_closure_set(v___f_3863_, 0, v_toPure_3835_);
lean_closure_set(v___f_3863_, 1, v_inst_3836_);
lean_closure_set(v___f_3863_, 2, v_toBind_3837_);
lean_closure_set(v___f_3863_, 3, v_toMatcherInfo_3838_);
lean_closure_set(v___f_3863_, 4, v_discrs_x27_3862_);
lean_closure_set(v___f_3863_, 5, v_inst_3839_);
lean_closure_set(v___f_3863_, 6, v___f_3840_);
lean_closure_set(v___f_3863_, 7, v_onMotive_3841_);
lean_closure_set(v___f_3863_, 8, v_discrs_3842_);
lean_closure_set(v___f_3863_, 9, v_inst_3843_);
v___x_3864_ = 0;
v___x_3865_ = lean_box(v___x_3864_);
v___x_3866_ = lean_box(v_useSplitter_3854_);
v___x_3867_ = lean_box(v_isCasesOn_3855_);
lean_inc_ref(v_inst_3839_);
lean_inc_ref(v_inst_3848_);
lean_inc(v_toBind_3837_);
v___f_3868_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed), 26, 25);
lean_closure_set(v___f_3868_, 0, v_toMatcherInfo_3838_);
lean_closure_set(v___f_3868_, 1, v_matcherName_3844_);
lean_closure_set(v___f_3868_, 2, v_params_x27_3845_);
lean_closure_set(v___f_3868_, 3, v_discrs_x27_3862_);
lean_closure_set(v___f_3868_, 4, v_toPure_3835_);
lean_closure_set(v___f_3868_, 5, v_onRemaining_3846_);
lean_closure_set(v___f_3868_, 6, v_remaining_3847_);
lean_closure_set(v___f_3868_, 7, v_toBind_3837_);
lean_closure_set(v___f_3868_, 8, v_inst_3848_);
lean_closure_set(v___f_3868_, 9, v_alts_3849_);
lean_closure_set(v___f_3868_, 10, v___f_3850_);
lean_closure_set(v___f_3868_, 11, v___x_3865_);
lean_closure_set(v___f_3868_, 12, v_inst_3836_);
lean_closure_set(v___f_3868_, 13, v_onAlt_3851_);
lean_closure_set(v___f_3868_, 14, v_inst_3839_);
lean_closure_set(v___f_3868_, 15, v___f_3852_);
lean_closure_set(v___f_3868_, 16, v_matcherApp_3853_);
lean_closure_set(v___f_3868_, 17, v___x_3866_);
lean_closure_set(v___f_3868_, 18, v___x_3867_);
lean_closure_set(v___f_3868_, 19, v___f_3856_);
lean_closure_set(v___f_3868_, 20, v_inst_3843_);
lean_closure_set(v___f_3868_, 21, v___f_3857_);
lean_closure_set(v___f_3868_, 22, v_numDiscrEqs_3858_);
lean_closure_set(v___f_3868_, 23, v___f_3859_);
lean_closure_set(v___f_3868_, 24, v_matcherLevels_3860_);
v___x_3869_ = l_Lean_Meta_lambdaTelescope___redArg(v_inst_3848_, v_inst_3839_, v_motive_3861_, v___f_3863_, v___x_3864_);
v___x_3870_ = lean_apply_4(v_toBind_3837_, lean_box(0), lean_box(0), v___x_3869_, v___f_3868_);
return v___x_3870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed(lean_object** _args){
lean_object* v_toPure_3871_ = _args[0];
lean_object* v_inst_3872_ = _args[1];
lean_object* v_toBind_3873_ = _args[2];
lean_object* v_toMatcherInfo_3874_ = _args[3];
lean_object* v_inst_3875_ = _args[4];
lean_object* v___f_3876_ = _args[5];
lean_object* v_onMotive_3877_ = _args[6];
lean_object* v_discrs_3878_ = _args[7];
lean_object* v_inst_3879_ = _args[8];
lean_object* v_matcherName_3880_ = _args[9];
lean_object* v_params_x27_3881_ = _args[10];
lean_object* v_onRemaining_3882_ = _args[11];
lean_object* v_remaining_3883_ = _args[12];
lean_object* v_inst_3884_ = _args[13];
lean_object* v_alts_3885_ = _args[14];
lean_object* v___f_3886_ = _args[15];
lean_object* v_onAlt_3887_ = _args[16];
lean_object* v___f_3888_ = _args[17];
lean_object* v_matcherApp_3889_ = _args[18];
lean_object* v_useSplitter_3890_ = _args[19];
lean_object* v_isCasesOn_3891_ = _args[20];
lean_object* v___f_3892_ = _args[21];
lean_object* v___f_3893_ = _args[22];
lean_object* v_numDiscrEqs_3894_ = _args[23];
lean_object* v___f_3895_ = _args[24];
lean_object* v_matcherLevels_3896_ = _args[25];
lean_object* v_motive_3897_ = _args[26];
lean_object* v_discrs_x27_3898_ = _args[27];
_start:
{
uint8_t v_useSplitter_boxed_3899_; uint8_t v_isCasesOn_boxed_3900_; lean_object* v_res_3901_; 
v_useSplitter_boxed_3899_ = lean_unbox(v_useSplitter_3890_);
v_isCasesOn_boxed_3900_ = lean_unbox(v_isCasesOn_3891_);
v_res_3901_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__57(v_toPure_3871_, v_inst_3872_, v_toBind_3873_, v_toMatcherInfo_3874_, v_inst_3875_, v___f_3876_, v_onMotive_3877_, v_discrs_3878_, v_inst_3879_, v_matcherName_3880_, v_params_x27_3881_, v_onRemaining_3882_, v_remaining_3883_, v_inst_3884_, v_alts_3885_, v___f_3886_, v_onAlt_3887_, v___f_3888_, v_matcherApp_3889_, v_useSplitter_boxed_3899_, v_isCasesOn_boxed_3900_, v___f_3892_, v___f_3893_, v_numDiscrEqs_3894_, v___f_3895_, v_matcherLevels_3896_, v_motive_3897_, v_discrs_x27_3898_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59(lean_object* v_toPure_3902_, lean_object* v_inst_3903_, lean_object* v_toBind_3904_, lean_object* v_toMatcherInfo_3905_, lean_object* v_inst_3906_, lean_object* v___f_3907_, lean_object* v_onMotive_3908_, lean_object* v_discrs_3909_, lean_object* v_inst_3910_, lean_object* v_matcherName_3911_, lean_object* v_onRemaining_3912_, lean_object* v_remaining_3913_, lean_object* v_inst_3914_, lean_object* v_alts_3915_, lean_object* v___f_3916_, lean_object* v_onAlt_3917_, lean_object* v___f_3918_, lean_object* v_matcherApp_3919_, uint8_t v_useSplitter_3920_, uint8_t v_isCasesOn_3921_, lean_object* v___f_3922_, lean_object* v___f_3923_, lean_object* v_numDiscrEqs_3924_, lean_object* v___f_3925_, lean_object* v_matcherLevels_3926_, lean_object* v_motive_3927_, lean_object* v_onParams_3928_, lean_object* v_params_x27_3929_){
_start:
{
lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___f_3932_; size_t v_sz_3933_; size_t v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; 
v___x_3930_ = lean_box(v_useSplitter_3920_);
v___x_3931_ = lean_box(v_isCasesOn_3921_);
lean_inc_ref(v_discrs_3909_);
lean_inc_ref(v_inst_3906_);
lean_inc(v_toBind_3904_);
v___f_3932_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed), 28, 27);
lean_closure_set(v___f_3932_, 0, v_toPure_3902_);
lean_closure_set(v___f_3932_, 1, v_inst_3903_);
lean_closure_set(v___f_3932_, 2, v_toBind_3904_);
lean_closure_set(v___f_3932_, 3, v_toMatcherInfo_3905_);
lean_closure_set(v___f_3932_, 4, v_inst_3906_);
lean_closure_set(v___f_3932_, 5, v___f_3907_);
lean_closure_set(v___f_3932_, 6, v_onMotive_3908_);
lean_closure_set(v___f_3932_, 7, v_discrs_3909_);
lean_closure_set(v___f_3932_, 8, v_inst_3910_);
lean_closure_set(v___f_3932_, 9, v_matcherName_3911_);
lean_closure_set(v___f_3932_, 10, v_params_x27_3929_);
lean_closure_set(v___f_3932_, 11, v_onRemaining_3912_);
lean_closure_set(v___f_3932_, 12, v_remaining_3913_);
lean_closure_set(v___f_3932_, 13, v_inst_3914_);
lean_closure_set(v___f_3932_, 14, v_alts_3915_);
lean_closure_set(v___f_3932_, 15, v___f_3916_);
lean_closure_set(v___f_3932_, 16, v_onAlt_3917_);
lean_closure_set(v___f_3932_, 17, v___f_3918_);
lean_closure_set(v___f_3932_, 18, v_matcherApp_3919_);
lean_closure_set(v___f_3932_, 19, v___x_3930_);
lean_closure_set(v___f_3932_, 20, v___x_3931_);
lean_closure_set(v___f_3932_, 21, v___f_3922_);
lean_closure_set(v___f_3932_, 22, v___f_3923_);
lean_closure_set(v___f_3932_, 23, v_numDiscrEqs_3924_);
lean_closure_set(v___f_3932_, 24, v___f_3925_);
lean_closure_set(v___f_3932_, 25, v_matcherLevels_3926_);
lean_closure_set(v___f_3932_, 26, v_motive_3927_);
v_sz_3933_ = lean_array_size(v_discrs_3909_);
v___x_3934_ = ((size_t)0ULL);
v___x_3935_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_3906_, v_onParams_3928_, v_sz_3933_, v___x_3934_, v_discrs_3909_);
v___x_3936_ = lean_apply_4(v_toBind_3904_, lean_box(0), lean_box(0), v___x_3935_, v___f_3932_);
return v___x_3936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed(lean_object** _args){
lean_object* v_toPure_3937_ = _args[0];
lean_object* v_inst_3938_ = _args[1];
lean_object* v_toBind_3939_ = _args[2];
lean_object* v_toMatcherInfo_3940_ = _args[3];
lean_object* v_inst_3941_ = _args[4];
lean_object* v___f_3942_ = _args[5];
lean_object* v_onMotive_3943_ = _args[6];
lean_object* v_discrs_3944_ = _args[7];
lean_object* v_inst_3945_ = _args[8];
lean_object* v_matcherName_3946_ = _args[9];
lean_object* v_onRemaining_3947_ = _args[10];
lean_object* v_remaining_3948_ = _args[11];
lean_object* v_inst_3949_ = _args[12];
lean_object* v_alts_3950_ = _args[13];
lean_object* v___f_3951_ = _args[14];
lean_object* v_onAlt_3952_ = _args[15];
lean_object* v___f_3953_ = _args[16];
lean_object* v_matcherApp_3954_ = _args[17];
lean_object* v_useSplitter_3955_ = _args[18];
lean_object* v_isCasesOn_3956_ = _args[19];
lean_object* v___f_3957_ = _args[20];
lean_object* v___f_3958_ = _args[21];
lean_object* v_numDiscrEqs_3959_ = _args[22];
lean_object* v___f_3960_ = _args[23];
lean_object* v_matcherLevels_3961_ = _args[24];
lean_object* v_motive_3962_ = _args[25];
lean_object* v_onParams_3963_ = _args[26];
lean_object* v_params_x27_3964_ = _args[27];
_start:
{
uint8_t v_useSplitter_boxed_3965_; uint8_t v_isCasesOn_boxed_3966_; lean_object* v_res_3967_; 
v_useSplitter_boxed_3965_ = lean_unbox(v_useSplitter_3955_);
v_isCasesOn_boxed_3966_ = lean_unbox(v_isCasesOn_3956_);
v_res_3967_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__59(v_toPure_3937_, v_inst_3938_, v_toBind_3939_, v_toMatcherInfo_3940_, v_inst_3941_, v___f_3942_, v_onMotive_3943_, v_discrs_3944_, v_inst_3945_, v_matcherName_3946_, v_onRemaining_3947_, v_remaining_3948_, v_inst_3949_, v_alts_3950_, v___f_3951_, v_onAlt_3952_, v___f_3953_, v_matcherApp_3954_, v_useSplitter_boxed_3965_, v_isCasesOn_boxed_3966_, v___f_3957_, v___f_3958_, v_numDiscrEqs_3959_, v___f_3960_, v_matcherLevels_3961_, v_motive_3962_, v_onParams_3963_, v_params_x27_3964_);
return v_res_3967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60(lean_object* v_toPure_3968_, lean_object* v_inst_3969_, lean_object* v_toBind_3970_, lean_object* v_toMatcherInfo_3971_, lean_object* v_inst_3972_, lean_object* v___f_3973_, lean_object* v_onMotive_3974_, lean_object* v_discrs_3975_, lean_object* v_inst_3976_, lean_object* v_matcherName_3977_, lean_object* v_onRemaining_3978_, lean_object* v_remaining_3979_, lean_object* v_inst_3980_, lean_object* v_alts_3981_, lean_object* v___f_3982_, lean_object* v_onAlt_3983_, lean_object* v___f_3984_, lean_object* v_matcherApp_3985_, uint8_t v_useSplitter_3986_, uint8_t v_isCasesOn_3987_, lean_object* v___f_3988_, lean_object* v___f_3989_, lean_object* v___f_3990_, lean_object* v_matcherLevels_3991_, lean_object* v_motive_3992_, lean_object* v_onParams_3993_, lean_object* v_params_3994_, lean_object* v_numDiscrEqs_3995_){
_start:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___f_3998_; size_t v_sz_3999_; size_t v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_3996_ = lean_box(v_useSplitter_3986_);
v___x_3997_ = lean_box(v_isCasesOn_3987_);
lean_inc(v_onParams_3993_);
lean_inc_ref(v_inst_3972_);
lean_inc(v_toBind_3970_);
v___f_3998_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed), 28, 27);
lean_closure_set(v___f_3998_, 0, v_toPure_3968_);
lean_closure_set(v___f_3998_, 1, v_inst_3969_);
lean_closure_set(v___f_3998_, 2, v_toBind_3970_);
lean_closure_set(v___f_3998_, 3, v_toMatcherInfo_3971_);
lean_closure_set(v___f_3998_, 4, v_inst_3972_);
lean_closure_set(v___f_3998_, 5, v___f_3973_);
lean_closure_set(v___f_3998_, 6, v_onMotive_3974_);
lean_closure_set(v___f_3998_, 7, v_discrs_3975_);
lean_closure_set(v___f_3998_, 8, v_inst_3976_);
lean_closure_set(v___f_3998_, 9, v_matcherName_3977_);
lean_closure_set(v___f_3998_, 10, v_onRemaining_3978_);
lean_closure_set(v___f_3998_, 11, v_remaining_3979_);
lean_closure_set(v___f_3998_, 12, v_inst_3980_);
lean_closure_set(v___f_3998_, 13, v_alts_3981_);
lean_closure_set(v___f_3998_, 14, v___f_3982_);
lean_closure_set(v___f_3998_, 15, v_onAlt_3983_);
lean_closure_set(v___f_3998_, 16, v___f_3984_);
lean_closure_set(v___f_3998_, 17, v_matcherApp_3985_);
lean_closure_set(v___f_3998_, 18, v___x_3996_);
lean_closure_set(v___f_3998_, 19, v___x_3997_);
lean_closure_set(v___f_3998_, 20, v___f_3988_);
lean_closure_set(v___f_3998_, 21, v___f_3989_);
lean_closure_set(v___f_3998_, 22, v_numDiscrEqs_3995_);
lean_closure_set(v___f_3998_, 23, v___f_3990_);
lean_closure_set(v___f_3998_, 24, v_matcherLevels_3991_);
lean_closure_set(v___f_3998_, 25, v_motive_3992_);
lean_closure_set(v___f_3998_, 26, v_onParams_3993_);
v_sz_3999_ = lean_array_size(v_params_3994_);
v___x_4000_ = ((size_t)0ULL);
v___x_4001_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_3972_, v_onParams_3993_, v_sz_3999_, v___x_4000_, v_params_3994_);
v___x_4002_ = lean_apply_4(v_toBind_3970_, lean_box(0), lean_box(0), v___x_4001_, v___f_3998_);
return v___x_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed(lean_object** _args){
lean_object* v_toPure_4003_ = _args[0];
lean_object* v_inst_4004_ = _args[1];
lean_object* v_toBind_4005_ = _args[2];
lean_object* v_toMatcherInfo_4006_ = _args[3];
lean_object* v_inst_4007_ = _args[4];
lean_object* v___f_4008_ = _args[5];
lean_object* v_onMotive_4009_ = _args[6];
lean_object* v_discrs_4010_ = _args[7];
lean_object* v_inst_4011_ = _args[8];
lean_object* v_matcherName_4012_ = _args[9];
lean_object* v_onRemaining_4013_ = _args[10];
lean_object* v_remaining_4014_ = _args[11];
lean_object* v_inst_4015_ = _args[12];
lean_object* v_alts_4016_ = _args[13];
lean_object* v___f_4017_ = _args[14];
lean_object* v_onAlt_4018_ = _args[15];
lean_object* v___f_4019_ = _args[16];
lean_object* v_matcherApp_4020_ = _args[17];
lean_object* v_useSplitter_4021_ = _args[18];
lean_object* v_isCasesOn_4022_ = _args[19];
lean_object* v___f_4023_ = _args[20];
lean_object* v___f_4024_ = _args[21];
lean_object* v___f_4025_ = _args[22];
lean_object* v_matcherLevels_4026_ = _args[23];
lean_object* v_motive_4027_ = _args[24];
lean_object* v_onParams_4028_ = _args[25];
lean_object* v_params_4029_ = _args[26];
lean_object* v_numDiscrEqs_4030_ = _args[27];
_start:
{
uint8_t v_useSplitter_boxed_4031_; uint8_t v_isCasesOn_boxed_4032_; lean_object* v_res_4033_; 
v_useSplitter_boxed_4031_ = lean_unbox(v_useSplitter_4021_);
v_isCasesOn_boxed_4032_ = lean_unbox(v_isCasesOn_4022_);
v_res_4033_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__60(v_toPure_4003_, v_inst_4004_, v_toBind_4005_, v_toMatcherInfo_4006_, v_inst_4007_, v___f_4008_, v_onMotive_4009_, v_discrs_4010_, v_inst_4011_, v_matcherName_4012_, v_onRemaining_4013_, v_remaining_4014_, v_inst_4015_, v_alts_4016_, v___f_4017_, v_onAlt_4018_, v___f_4019_, v_matcherApp_4020_, v_useSplitter_boxed_4031_, v_isCasesOn_boxed_4032_, v___f_4023_, v___f_4024_, v___f_4025_, v_matcherLevels_4026_, v_motive_4027_, v_onParams_4028_, v_params_4029_, v_numDiscrEqs_4030_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__61(lean_object* v___f_4034_, lean_object* v_numDiscrEqs_4035_){
_start:
{
lean_object* v___x_4036_; 
v___x_4036_ = lean_apply_1(v___f_4034_, v_numDiscrEqs_4035_);
return v___x_4036_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1(void){
_start:
{
lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4038_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__0));
v___x_4039_ = l_Lean_stringToMessageData(v___x_4038_);
return v___x_4039_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3(void){
_start:
{
lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4041_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__2));
v___x_4042_ = l_Lean_stringToMessageData(v___x_4041_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63(lean_object* v_matcherName_4043_, lean_object* v_inst_4044_, lean_object* v_inst_4045_, lean_object* v_toBind_4046_, lean_object* v___f_4047_, lean_object* v_toPure_4048_, lean_object* v___f_4049_, lean_object* v_____do__lift_4050_){
_start:
{
if (lean_obj_tag(v_____do__lift_4050_) == 0)
{
lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; 
lean_dec(v___f_4049_);
lean_dec(v_toPure_4048_);
v___x_4051_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1);
v___x_4052_ = l_Lean_MessageData_ofName(v_matcherName_4043_);
v___x_4053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4051_);
lean_ctor_set(v___x_4053_, 1, v___x_4052_);
v___x_4054_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3);
v___x_4055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4053_);
lean_ctor_set(v___x_4055_, 1, v___x_4054_);
v___x_4056_ = l_Lean_throwError___redArg(v_inst_4044_, v_inst_4045_, v___x_4055_);
v___x_4057_ = lean_apply_4(v_toBind_4046_, lean_box(0), lean_box(0), v___x_4056_, v___f_4047_);
return v___x_4057_;
}
else
{
lean_object* v_val_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
lean_dec(v___f_4047_);
lean_dec_ref(v_inst_4045_);
lean_dec_ref(v_inst_4044_);
lean_dec(v_matcherName_4043_);
v_val_4058_ = lean_ctor_get(v_____do__lift_4050_, 0);
v___x_4059_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_4058_);
v___x_4060_ = lean_apply_2(v_toPure_4048_, lean_box(0), v___x_4059_);
v___x_4061_ = lean_apply_4(v_toBind_4046_, lean_box(0), lean_box(0), v___x_4060_, v___f_4049_);
return v___x_4061_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed(lean_object* v_matcherName_4062_, lean_object* v_inst_4063_, lean_object* v_inst_4064_, lean_object* v_toBind_4065_, lean_object* v___f_4066_, lean_object* v_toPure_4067_, lean_object* v___f_4068_, lean_object* v_____do__lift_4069_){
_start:
{
lean_object* v_res_4070_; 
v_res_4070_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__63(v_matcherName_4062_, v_inst_4063_, v_inst_4064_, v_toBind_4065_, v___f_4066_, v_toPure_4067_, v___f_4068_, v_____do__lift_4069_);
lean_dec(v_____do__lift_4069_);
return v_res_4070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64(lean_object* v_matcherApp_4071_, lean_object* v_toPure_4072_, lean_object* v_inst_4073_, lean_object* v_toBind_4074_, lean_object* v_inst_4075_, lean_object* v___f_4076_, lean_object* v_onMotive_4077_, lean_object* v_inst_4078_, lean_object* v_onRemaining_4079_, lean_object* v_inst_4080_, lean_object* v___f_4081_, lean_object* v_onAlt_4082_, lean_object* v___f_4083_, uint8_t v_useSplitter_4084_, lean_object* v___f_4085_, lean_object* v___f_4086_, lean_object* v___f_4087_, lean_object* v_onParams_4088_, lean_object* v_inst_4089_, lean_object* v_____do__lift_4090_){
_start:
{
lean_object* v_toMatcherInfo_4091_; lean_object* v_matcherName_4092_; lean_object* v_matcherLevels_4093_; lean_object* v_params_4094_; lean_object* v_motive_4095_; lean_object* v_discrs_4096_; lean_object* v_alts_4097_; lean_object* v_remaining_4098_; uint8_t v_isCasesOn_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___f_4102_; 
v_toMatcherInfo_4091_ = lean_ctor_get(v_matcherApp_4071_, 0);
lean_inc_ref(v_toMatcherInfo_4091_);
v_matcherName_4092_ = lean_ctor_get(v_matcherApp_4071_, 1);
lean_inc(v_matcherName_4092_);
v_matcherLevels_4093_ = lean_ctor_get(v_matcherApp_4071_, 2);
lean_inc_ref(v_matcherLevels_4093_);
v_params_4094_ = lean_ctor_get(v_matcherApp_4071_, 3);
lean_inc_ref(v_params_4094_);
v_motive_4095_ = lean_ctor_get(v_matcherApp_4071_, 4);
lean_inc_ref(v_motive_4095_);
v_discrs_4096_ = lean_ctor_get(v_matcherApp_4071_, 5);
lean_inc_ref(v_discrs_4096_);
v_alts_4097_ = lean_ctor_get(v_matcherApp_4071_, 6);
lean_inc_ref(v_alts_4097_);
v_remaining_4098_ = lean_ctor_get(v_matcherApp_4071_, 7);
lean_inc_ref(v_remaining_4098_);
lean_inc(v_matcherName_4092_);
v_isCasesOn_4099_ = l_Lean_isCasesOnRecursor(v_____do__lift_4090_, v_matcherName_4092_);
v___x_4100_ = lean_box(v_useSplitter_4084_);
v___x_4101_ = lean_box(v_isCasesOn_4099_);
lean_inc(v_matcherName_4092_);
lean_inc_ref(v_inst_4078_);
lean_inc_ref(v_inst_4075_);
lean_inc(v_toBind_4074_);
lean_inc(v_toPure_4072_);
v___f_4102_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed), 28, 27);
lean_closure_set(v___f_4102_, 0, v_toPure_4072_);
lean_closure_set(v___f_4102_, 1, v_inst_4073_);
lean_closure_set(v___f_4102_, 2, v_toBind_4074_);
lean_closure_set(v___f_4102_, 3, v_toMatcherInfo_4091_);
lean_closure_set(v___f_4102_, 4, v_inst_4075_);
lean_closure_set(v___f_4102_, 5, v___f_4076_);
lean_closure_set(v___f_4102_, 6, v_onMotive_4077_);
lean_closure_set(v___f_4102_, 7, v_discrs_4096_);
lean_closure_set(v___f_4102_, 8, v_inst_4078_);
lean_closure_set(v___f_4102_, 9, v_matcherName_4092_);
lean_closure_set(v___f_4102_, 10, v_onRemaining_4079_);
lean_closure_set(v___f_4102_, 11, v_remaining_4098_);
lean_closure_set(v___f_4102_, 12, v_inst_4080_);
lean_closure_set(v___f_4102_, 13, v_alts_4097_);
lean_closure_set(v___f_4102_, 14, v___f_4081_);
lean_closure_set(v___f_4102_, 15, v_onAlt_4082_);
lean_closure_set(v___f_4102_, 16, v___f_4083_);
lean_closure_set(v___f_4102_, 17, v_matcherApp_4071_);
lean_closure_set(v___f_4102_, 18, v___x_4100_);
lean_closure_set(v___f_4102_, 19, v___x_4101_);
lean_closure_set(v___f_4102_, 20, v___f_4085_);
lean_closure_set(v___f_4102_, 21, v___f_4086_);
lean_closure_set(v___f_4102_, 22, v___f_4087_);
lean_closure_set(v___f_4102_, 23, v_matcherLevels_4093_);
lean_closure_set(v___f_4102_, 24, v_motive_4095_);
lean_closure_set(v___f_4102_, 25, v_onParams_4088_);
lean_closure_set(v___f_4102_, 26, v_params_4094_);
if (v_isCasesOn_4099_ == 0)
{
lean_object* v___f_4103_; lean_object* v___f_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___f_4103_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61), 2, 1);
lean_closure_set(v___f_4103_, 0, v___f_4102_);
lean_inc_ref(v___f_4103_);
lean_inc(v_toBind_4074_);
lean_inc_ref(v_inst_4075_);
lean_inc(v_matcherName_4092_);
v___f_4104_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed), 8, 7);
lean_closure_set(v___f_4104_, 0, v_matcherName_4092_);
lean_closure_set(v___f_4104_, 1, v_inst_4075_);
lean_closure_set(v___f_4104_, 2, v_inst_4078_);
lean_closure_set(v___f_4104_, 3, v_toBind_4074_);
lean_closure_set(v___f_4104_, 4, v___f_4103_);
lean_closure_set(v___f_4104_, 5, v_toPure_4072_);
lean_closure_set(v___f_4104_, 6, v___f_4103_);
v___x_4105_ = l_Lean_Meta_getMatcherInfo_x3f___redArg(v_inst_4075_, v_inst_4089_, v_matcherName_4092_);
v___x_4106_ = lean_apply_4(v_toBind_4074_, lean_box(0), lean_box(0), v___x_4105_, v___f_4104_);
return v___x_4106_;
}
else
{
lean_object* v___f_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; 
lean_dec(v_matcherName_4092_);
lean_dec_ref(v_inst_4089_);
lean_dec_ref(v_inst_4078_);
lean_dec_ref(v_inst_4075_);
v___f_4107_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61), 2, 1);
lean_closure_set(v___f_4107_, 0, v___f_4102_);
v___x_4108_ = lean_unsigned_to_nat(0u);
v___x_4109_ = lean_apply_2(v_toPure_4072_, lean_box(0), v___x_4108_);
v___x_4110_ = lean_apply_4(v_toBind_4074_, lean_box(0), lean_box(0), v___x_4109_, v___f_4107_);
return v___x_4110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed(lean_object** _args){
lean_object* v_matcherApp_4111_ = _args[0];
lean_object* v_toPure_4112_ = _args[1];
lean_object* v_inst_4113_ = _args[2];
lean_object* v_toBind_4114_ = _args[3];
lean_object* v_inst_4115_ = _args[4];
lean_object* v___f_4116_ = _args[5];
lean_object* v_onMotive_4117_ = _args[6];
lean_object* v_inst_4118_ = _args[7];
lean_object* v_onRemaining_4119_ = _args[8];
lean_object* v_inst_4120_ = _args[9];
lean_object* v___f_4121_ = _args[10];
lean_object* v_onAlt_4122_ = _args[11];
lean_object* v___f_4123_ = _args[12];
lean_object* v_useSplitter_4124_ = _args[13];
lean_object* v___f_4125_ = _args[14];
lean_object* v___f_4126_ = _args[15];
lean_object* v___f_4127_ = _args[16];
lean_object* v_onParams_4128_ = _args[17];
lean_object* v_inst_4129_ = _args[18];
lean_object* v_____do__lift_4130_ = _args[19];
_start:
{
uint8_t v_useSplitter_boxed_4131_; lean_object* v_res_4132_; 
v_useSplitter_boxed_4131_ = lean_unbox(v_useSplitter_4124_);
v_res_4132_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__64(v_matcherApp_4111_, v_toPure_4112_, v_inst_4113_, v_toBind_4114_, v_inst_4115_, v___f_4116_, v_onMotive_4117_, v_inst_4118_, v_onRemaining_4119_, v_inst_4120_, v___f_4121_, v_onAlt_4122_, v___f_4123_, v_useSplitter_boxed_4131_, v___f_4125_, v___f_4126_, v___f_4127_, v_onParams_4128_, v_inst_4129_, v_____do__lift_4130_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg(lean_object* v_inst_4133_, lean_object* v_inst_4134_, lean_object* v_inst_4135_, lean_object* v_inst_4136_, lean_object* v_inst_4137_, lean_object* v_matcherApp_4138_, uint8_t v_useSplitter_4139_, uint8_t v_addEqualities_4140_, lean_object* v_onParams_4141_, lean_object* v_onMotive_4142_, lean_object* v_onAlt_4143_, lean_object* v_onRemaining_4144_){
_start:
{
lean_object* v_toApplicative_4145_; lean_object* v_toBind_4146_; lean_object* v_getEnv_4147_; lean_object* v_toPure_4148_; lean_object* v___f_4149_; lean_object* v___f_4150_; lean_object* v___f_4151_; lean_object* v___f_4152_; lean_object* v___f_4153_; lean_object* v___f_4154_; lean_object* v___x_4155_; lean_object* v___f_4156_; lean_object* v___x_4157_; lean_object* v___f_4158_; lean_object* v___x_4159_; 
v_toApplicative_4145_ = lean_ctor_get(v_inst_4135_, 0);
v_toBind_4146_ = lean_ctor_get(v_inst_4135_, 1);
lean_inc(v_toBind_4146_);
v_getEnv_4147_ = lean_ctor_get(v_inst_4137_, 0);
lean_inc(v_getEnv_4147_);
v_toPure_4148_ = lean_ctor_get(v_toApplicative_4145_, 1);
lean_inc(v_toPure_4148_);
lean_inc_ref(v_inst_4136_);
lean_inc_ref(v_inst_4135_);
v___f_4149_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4149_, 0, v_inst_4135_);
lean_closure_set(v___f_4149_, 1, v_inst_4136_);
lean_inc(v_inst_4133_);
v___f_4150_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4150_, 0, v_inst_4133_);
lean_inc_ref(v_inst_4135_);
v___f_4151_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4151_, 0, v_inst_4135_);
lean_closure_set(v___f_4151_, 1, v___f_4150_);
lean_inc(v_toPure_4148_);
v___f_4152_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__3), 2, 1);
lean_closure_set(v___f_4152_, 0, v_toPure_4148_);
lean_inc(v_toPure_4148_);
v___f_4153_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__4), 2, 1);
lean_closure_set(v___f_4153_, 0, v_toPure_4148_);
lean_inc(v_toBind_4146_);
lean_inc(v_inst_4133_);
lean_inc(v_toPure_4148_);
v___f_4154_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7), 6, 3);
lean_closure_set(v___f_4154_, 0, v_toPure_4148_);
lean_closure_set(v___f_4154_, 1, v_inst_4133_);
lean_closure_set(v___f_4154_, 2, v_toBind_4146_);
v___x_4155_ = lean_box(v_addEqualities_4140_);
lean_inc(v_toBind_4146_);
lean_inc(v_inst_4133_);
lean_inc(v_toPure_4148_);
v___f_4156_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__12___boxed), 7, 4);
lean_closure_set(v___f_4156_, 0, v_toPure_4148_);
lean_closure_set(v___f_4156_, 1, v___x_4155_);
lean_closure_set(v___f_4156_, 2, v_inst_4133_);
lean_closure_set(v___f_4156_, 3, v_toBind_4146_);
v___x_4157_ = lean_box(v_useSplitter_4139_);
lean_inc(v_toBind_4146_);
v___f_4158_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed), 20, 19);
lean_closure_set(v___f_4158_, 0, v_matcherApp_4138_);
lean_closure_set(v___f_4158_, 1, v_toPure_4148_);
lean_closure_set(v___f_4158_, 2, v_inst_4133_);
lean_closure_set(v___f_4158_, 3, v_toBind_4146_);
lean_closure_set(v___f_4158_, 4, v_inst_4135_);
lean_closure_set(v___f_4158_, 5, v___f_4156_);
lean_closure_set(v___f_4158_, 6, v_onMotive_4142_);
lean_closure_set(v___f_4158_, 7, v_inst_4136_);
lean_closure_set(v___f_4158_, 8, v_onRemaining_4144_);
lean_closure_set(v___f_4158_, 9, v_inst_4134_);
lean_closure_set(v___f_4158_, 10, v___f_4152_);
lean_closure_set(v___f_4158_, 11, v_onAlt_4143_);
lean_closure_set(v___f_4158_, 12, v___f_4151_);
lean_closure_set(v___f_4158_, 13, v___x_4157_);
lean_closure_set(v___f_4158_, 14, v___f_4153_);
lean_closure_set(v___f_4158_, 15, v___f_4149_);
lean_closure_set(v___f_4158_, 16, v___f_4154_);
lean_closure_set(v___f_4158_, 17, v_onParams_4141_);
lean_closure_set(v___f_4158_, 18, v_inst_4137_);
v___x_4159_ = lean_apply_4(v_toBind_4146_, lean_box(0), lean_box(0), v_getEnv_4147_, v___f_4158_);
return v___x_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___boxed(lean_object* v_inst_4160_, lean_object* v_inst_4161_, lean_object* v_inst_4162_, lean_object* v_inst_4163_, lean_object* v_inst_4164_, lean_object* v_matcherApp_4165_, lean_object* v_useSplitter_4166_, lean_object* v_addEqualities_4167_, lean_object* v_onParams_4168_, lean_object* v_onMotive_4169_, lean_object* v_onAlt_4170_, lean_object* v_onRemaining_4171_){
_start:
{
uint8_t v_useSplitter_boxed_4172_; uint8_t v_addEqualities_boxed_4173_; lean_object* v_res_4174_; 
v_useSplitter_boxed_4172_ = lean_unbox(v_useSplitter_4166_);
v_addEqualities_boxed_4173_ = lean_unbox(v_addEqualities_4167_);
v_res_4174_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_4160_, v_inst_4161_, v_inst_4162_, v_inst_4163_, v_inst_4164_, v_matcherApp_4165_, v_useSplitter_boxed_4172_, v_addEqualities_boxed_4173_, v_onParams_4168_, v_onMotive_4169_, v_onAlt_4170_, v_onRemaining_4171_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform(lean_object* v_n_4175_, lean_object* v_inst_4176_, lean_object* v_inst_4177_, lean_object* v_inst_4178_, lean_object* v_inst_4179_, lean_object* v_inst_4180_, lean_object* v_inst_4181_, lean_object* v_inst_4182_, lean_object* v_inst_4183_, lean_object* v_matcherApp_4184_, uint8_t v_useSplitter_4185_, uint8_t v_addEqualities_4186_, lean_object* v_onParams_4187_, lean_object* v_onMotive_4188_, lean_object* v_onAlt_4189_, lean_object* v_onRemaining_4190_){
_start:
{
lean_object* v___x_4191_; 
v___x_4191_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_4176_, v_inst_4177_, v_inst_4178_, v_inst_4179_, v_inst_4180_, v_matcherApp_4184_, v_useSplitter_4185_, v_addEqualities_4186_, v_onParams_4187_, v_onMotive_4188_, v_onAlt_4189_, v_onRemaining_4190_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___boxed(lean_object* v_n_4192_, lean_object* v_inst_4193_, lean_object* v_inst_4194_, lean_object* v_inst_4195_, lean_object* v_inst_4196_, lean_object* v_inst_4197_, lean_object* v_inst_4198_, lean_object* v_inst_4199_, lean_object* v_inst_4200_, lean_object* v_matcherApp_4201_, lean_object* v_useSplitter_4202_, lean_object* v_addEqualities_4203_, lean_object* v_onParams_4204_, lean_object* v_onMotive_4205_, lean_object* v_onAlt_4206_, lean_object* v_onRemaining_4207_){
_start:
{
uint8_t v_useSplitter_boxed_4208_; uint8_t v_addEqualities_boxed_4209_; lean_object* v_res_4210_; 
v_useSplitter_boxed_4208_ = lean_unbox(v_useSplitter_4202_);
v_addEqualities_boxed_4209_ = lean_unbox(v_addEqualities_4203_);
v_res_4210_ = l_Lean_Meta_MatcherApp_transform(v_n_4192_, v_inst_4193_, v_inst_4194_, v_inst_4195_, v_inst_4196_, v_inst_4197_, v_inst_4198_, v_inst_4199_, v_inst_4200_, v_matcherApp_4201_, v_useSplitter_boxed_4208_, v_addEqualities_boxed_4209_, v_onParams_4204_, v_onMotive_4205_, v_onAlt_4206_, v_onRemaining_4207_);
lean_dec(v_inst_4200_);
lean_dec(v_inst_4199_);
lean_dec_ref(v_inst_4198_);
return v_res_4210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0(lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
lean_object* v___x_4217_; 
v___x_4217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4217_, 0, v___y_4211_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0___boxed(lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_){
_start:
{
lean_object* v_res_4224_; 
v_res_4224_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__0(v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
return v_res_4224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1(lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_){
_start:
{
lean_object* v___x_4231_; 
v___x_4231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4231_, 0, v___y_4225_);
return v___x_4231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1___boxed(lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_){
_start:
{
lean_object* v_res_4238_; 
v_res_4238_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__1(v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_);
lean_dec(v___y_4236_);
lean_dec_ref(v___y_4235_);
lean_dec(v___y_4234_);
lean_dec_ref(v___y_4233_);
return v_res_4238_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(lean_object* v_opts_4239_, lean_object* v_opt_4240_){
_start:
{
lean_object* v_name_4241_; lean_object* v_defValue_4242_; lean_object* v_map_4243_; lean_object* v___x_4244_; 
v_name_4241_ = lean_ctor_get(v_opt_4240_, 0);
v_defValue_4242_ = lean_ctor_get(v_opt_4240_, 1);
v_map_4243_ = lean_ctor_get(v_opts_4239_, 0);
v___x_4244_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4243_, v_name_4241_);
if (lean_obj_tag(v___x_4244_) == 0)
{
uint8_t v___x_4245_; 
v___x_4245_ = lean_unbox(v_defValue_4242_);
return v___x_4245_;
}
else
{
lean_object* v_val_4246_; 
v_val_4246_ = lean_ctor_get(v___x_4244_, 0);
lean_inc(v_val_4246_);
lean_dec_ref(v___x_4244_);
if (lean_obj_tag(v_val_4246_) == 1)
{
uint8_t v_v_4247_; 
v_v_4247_ = lean_ctor_get_uint8(v_val_4246_, 0);
lean_dec_ref(v_val_4246_);
return v_v_4247_;
}
else
{
uint8_t v___x_4248_; 
lean_dec(v_val_4246_);
v___x_4248_ = lean_unbox(v_defValue_4242_);
return v___x_4248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11___boxed(lean_object* v_opts_4249_, lean_object* v_opt_4250_){
_start:
{
uint8_t v_res_4251_; lean_object* v_r_4252_; 
v_res_4251_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(v_opts_4249_, v_opt_4250_);
lean_dec_ref(v_opt_4250_);
lean_dec_ref(v_opts_4249_);
v_r_4252_ = lean_box(v_res_4251_);
return v_r_4252_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(uint8_t v___y_4261_, uint8_t v_suppressElabErrors_4262_, lean_object* v_x_4263_){
_start:
{
if (lean_obj_tag(v_x_4263_) == 1)
{
lean_object* v_pre_4264_; 
v_pre_4264_ = lean_ctor_get(v_x_4263_, 0);
switch(lean_obj_tag(v_pre_4264_))
{
case 1:
{
lean_object* v_pre_4265_; 
v_pre_4265_ = lean_ctor_get(v_pre_4264_, 0);
switch(lean_obj_tag(v_pre_4265_))
{
case 0:
{
lean_object* v_str_4266_; lean_object* v_str_4267_; lean_object* v___x_4268_; uint8_t v___x_4269_; 
v_str_4266_ = lean_ctor_get(v_x_4263_, 1);
v_str_4267_ = lean_ctor_get(v_pre_4264_, 1);
v___x_4268_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_4269_ = lean_string_dec_eq(v_str_4267_, v___x_4268_);
if (v___x_4269_ == 0)
{
lean_object* v___x_4270_; uint8_t v___x_4271_; 
v___x_4270_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_4271_ = lean_string_dec_eq(v_str_4267_, v___x_4270_);
if (v___x_4271_ == 0)
{
return v___y_4261_;
}
else
{
lean_object* v___x_4272_; uint8_t v___x_4273_; 
v___x_4272_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_4273_ = lean_string_dec_eq(v_str_4266_, v___x_4272_);
if (v___x_4273_ == 0)
{
return v___y_4261_;
}
else
{
return v_suppressElabErrors_4262_;
}
}
}
else
{
lean_object* v___x_4274_; uint8_t v___x_4275_; 
v___x_4274_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_4275_ = lean_string_dec_eq(v_str_4266_, v___x_4274_);
if (v___x_4275_ == 0)
{
return v___y_4261_;
}
else
{
return v_suppressElabErrors_4262_;
}
}
}
case 1:
{
lean_object* v_pre_4276_; 
v_pre_4276_ = lean_ctor_get(v_pre_4265_, 0);
if (lean_obj_tag(v_pre_4276_) == 0)
{
lean_object* v_str_4277_; lean_object* v_str_4278_; lean_object* v_str_4279_; lean_object* v___x_4280_; uint8_t v___x_4281_; 
v_str_4277_ = lean_ctor_get(v_x_4263_, 1);
v_str_4278_ = lean_ctor_get(v_pre_4264_, 1);
v_str_4279_ = lean_ctor_get(v_pre_4265_, 1);
v___x_4280_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_4281_ = lean_string_dec_eq(v_str_4279_, v___x_4280_);
if (v___x_4281_ == 0)
{
return v___y_4261_;
}
else
{
lean_object* v___x_4282_; uint8_t v___x_4283_; 
v___x_4282_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_4283_ = lean_string_dec_eq(v_str_4278_, v___x_4282_);
if (v___x_4283_ == 0)
{
return v___y_4261_;
}
else
{
lean_object* v___x_4284_; uint8_t v___x_4285_; 
v___x_4284_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_4285_ = lean_string_dec_eq(v_str_4277_, v___x_4284_);
if (v___x_4285_ == 0)
{
return v___y_4261_;
}
else
{
return v_suppressElabErrors_4262_;
}
}
}
}
else
{
return v___y_4261_;
}
}
default: 
{
return v___y_4261_;
}
}
}
case 0:
{
lean_object* v_str_4286_; lean_object* v___x_4287_; uint8_t v___x_4288_; 
v_str_4286_ = lean_ctor_get(v_x_4263_, 1);
v___x_4287_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_4288_ = lean_string_dec_eq(v_str_4286_, v___x_4287_);
if (v___x_4288_ == 0)
{
return v___y_4261_;
}
else
{
return v_suppressElabErrors_4262_;
}
}
default: 
{
return v___y_4261_;
}
}
}
else
{
return v___y_4261_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___y_4289_, lean_object* v_suppressElabErrors_4290_, lean_object* v_x_4291_){
_start:
{
uint8_t v___y_32220__boxed_4292_; uint8_t v_suppressElabErrors_boxed_4293_; uint8_t v_res_4294_; lean_object* v_r_4295_; 
v___y_32220__boxed_4292_ = lean_unbox(v___y_4289_);
v_suppressElabErrors_boxed_4293_ = lean_unbox(v_suppressElabErrors_4290_);
v_res_4294_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(v___y_32220__boxed_4292_, v_suppressElabErrors_boxed_4293_, v_x_4291_);
lean_dec(v_x_4291_);
v_r_4295_ = lean_box(v_res_4294_);
return v_r_4295_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(lean_object* v_ref_4297_, lean_object* v_msgData_4298_, uint8_t v_severity_4299_, uint8_t v_isSilent_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_){
_start:
{
uint8_t v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; uint8_t v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; lean_object* v___y_4343_; uint8_t v___y_4344_; uint8_t v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; uint8_t v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4368_; uint8_t v___y_4369_; uint8_t v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; uint8_t v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4379_; lean_object* v___y_4380_; uint8_t v___y_4381_; uint8_t v___y_4382_; lean_object* v___y_4383_; lean_object* v___y_4384_; uint8_t v___y_4385_; uint8_t v___x_4390_; lean_object* v___y_4392_; uint8_t v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; uint8_t v___y_4397_; uint8_t v___y_4398_; uint8_t v___y_4400_; uint8_t v___x_4415_; 
v___x_4390_ = 2;
v___x_4415_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4299_, v___x_4390_);
if (v___x_4415_ == 0)
{
v___y_4400_ = v___x_4415_;
goto v___jp_4399_;
}
else
{
uint8_t v___x_4416_; 
lean_inc_ref(v_msgData_4298_);
v___x_4416_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4298_);
v___y_4400_ = v___x_4416_;
goto v___jp_4399_;
}
v___jp_4306_:
{
lean_object* v___x_4316_; lean_object* v_currNamespace_4317_; lean_object* v_openDecls_4318_; lean_object* v_env_4319_; lean_object* v_nextMacroScope_4320_; lean_object* v_ngen_4321_; lean_object* v_auxDeclNGen_4322_; lean_object* v_traceState_4323_; lean_object* v_cache_4324_; lean_object* v_messages_4325_; lean_object* v_infoState_4326_; lean_object* v_snapshotTasks_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4341_; 
v___x_4316_ = lean_st_ref_take(v___y_4315_);
v_currNamespace_4317_ = lean_ctor_get(v___y_4314_, 6);
lean_inc(v_currNamespace_4317_);
v_openDecls_4318_ = lean_ctor_get(v___y_4314_, 7);
lean_inc(v_openDecls_4318_);
lean_dec_ref(v___y_4314_);
v_env_4319_ = lean_ctor_get(v___x_4316_, 0);
v_nextMacroScope_4320_ = lean_ctor_get(v___x_4316_, 1);
v_ngen_4321_ = lean_ctor_get(v___x_4316_, 2);
v_auxDeclNGen_4322_ = lean_ctor_get(v___x_4316_, 3);
v_traceState_4323_ = lean_ctor_get(v___x_4316_, 4);
v_cache_4324_ = lean_ctor_get(v___x_4316_, 5);
v_messages_4325_ = lean_ctor_get(v___x_4316_, 6);
v_infoState_4326_ = lean_ctor_get(v___x_4316_, 7);
v_snapshotTasks_4327_ = lean_ctor_get(v___x_4316_, 8);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4316_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4329_ = v___x_4316_;
v_isShared_4330_ = v_isSharedCheck_4341_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_snapshotTasks_4327_);
lean_inc(v_infoState_4326_);
lean_inc(v_messages_4325_);
lean_inc(v_cache_4324_);
lean_inc(v_traceState_4323_);
lean_inc(v_auxDeclNGen_4322_);
lean_inc(v_ngen_4321_);
lean_inc(v_nextMacroScope_4320_);
lean_inc(v_env_4319_);
lean_dec(v___x_4316_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4341_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4336_; 
v___x_4331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4331_, 0, v_currNamespace_4317_);
lean_ctor_set(v___x_4331_, 1, v_openDecls_4318_);
v___x_4332_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4332_, 0, v___x_4331_);
lean_ctor_set(v___x_4332_, 1, v___y_4309_);
v___x_4333_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4333_, 0, v___y_4311_);
lean_ctor_set(v___x_4333_, 1, v___y_4308_);
lean_ctor_set(v___x_4333_, 2, v___y_4313_);
lean_ctor_set(v___x_4333_, 3, v___y_4310_);
lean_ctor_set(v___x_4333_, 4, v___x_4332_);
lean_ctor_set_uint8(v___x_4333_, sizeof(void*)*5, v___y_4307_);
lean_ctor_set_uint8(v___x_4333_, sizeof(void*)*5 + 1, v___y_4312_);
lean_ctor_set_uint8(v___x_4333_, sizeof(void*)*5 + 2, v_isSilent_4300_);
v___x_4334_ = l_Lean_MessageLog_add(v___x_4333_, v_messages_4325_);
if (v_isShared_4330_ == 0)
{
lean_ctor_set(v___x_4329_, 6, v___x_4334_);
v___x_4336_ = v___x_4329_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_env_4319_);
lean_ctor_set(v_reuseFailAlloc_4340_, 1, v_nextMacroScope_4320_);
lean_ctor_set(v_reuseFailAlloc_4340_, 2, v_ngen_4321_);
lean_ctor_set(v_reuseFailAlloc_4340_, 3, v_auxDeclNGen_4322_);
lean_ctor_set(v_reuseFailAlloc_4340_, 4, v_traceState_4323_);
lean_ctor_set(v_reuseFailAlloc_4340_, 5, v_cache_4324_);
lean_ctor_set(v_reuseFailAlloc_4340_, 6, v___x_4334_);
lean_ctor_set(v_reuseFailAlloc_4340_, 7, v_infoState_4326_);
lean_ctor_set(v_reuseFailAlloc_4340_, 8, v_snapshotTasks_4327_);
v___x_4336_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; 
v___x_4337_ = lean_st_ref_set(v___y_4315_, v___x_4336_);
v___x_4338_ = lean_box(0);
v___x_4339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4339_, 0, v___x_4338_);
return v___x_4339_;
}
}
}
v___jp_4342_:
{
lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v_a_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4366_; 
v___x_4351_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4298_);
v___x_4352_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(v___x_4351_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4366_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4366_ == 0)
{
v___x_4355_ = v___x_4352_;
v_isShared_4356_ = v_isSharedCheck_4366_;
goto v_resetjp_4354_;
}
else
{
lean_inc(v_a_4353_);
lean_dec(v___x_4352_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4366_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
lean_inc_ref(v___y_4347_);
v___x_4357_ = l_Lean_FileMap_toPosition(v___y_4347_, v___y_4346_);
lean_dec(v___y_4346_);
v___x_4358_ = l_Lean_FileMap_toPosition(v___y_4347_, v___y_4350_);
lean_dec(v___y_4350_);
v___x_4359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4359_, 0, v___x_4358_);
v___x_4360_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___closed__0));
if (v___y_4345_ == 0)
{
lean_del_object(v___x_4355_);
lean_dec_ref(v___y_4343_);
v___y_4307_ = v___y_4344_;
v___y_4308_ = v___x_4357_;
v___y_4309_ = v_a_4353_;
v___y_4310_ = v___x_4360_;
v___y_4311_ = v___y_4348_;
v___y_4312_ = v___y_4349_;
v___y_4313_ = v___x_4359_;
v___y_4314_ = v___y_4303_;
v___y_4315_ = v___y_4304_;
goto v___jp_4306_;
}
else
{
uint8_t v___x_4361_; 
lean_inc(v_a_4353_);
v___x_4361_ = l_Lean_MessageData_hasTag(v___y_4343_, v_a_4353_);
if (v___x_4361_ == 0)
{
lean_object* v___x_4362_; lean_object* v___x_4364_; 
lean_dec_ref(v___x_4359_);
lean_dec_ref(v___x_4357_);
lean_dec(v_a_4353_);
lean_dec_ref(v___y_4348_);
lean_dec_ref(v___y_4303_);
v___x_4362_ = lean_box(0);
if (v_isShared_4356_ == 0)
{
lean_ctor_set(v___x_4355_, 0, v___x_4362_);
v___x_4364_ = v___x_4355_;
goto v_reusejp_4363_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v___x_4362_);
v___x_4364_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4363_;
}
v_reusejp_4363_:
{
return v___x_4364_;
}
}
else
{
lean_del_object(v___x_4355_);
v___y_4307_ = v___y_4344_;
v___y_4308_ = v___x_4357_;
v___y_4309_ = v_a_4353_;
v___y_4310_ = v___x_4360_;
v___y_4311_ = v___y_4348_;
v___y_4312_ = v___y_4349_;
v___y_4313_ = v___x_4359_;
v___y_4314_ = v___y_4303_;
v___y_4315_ = v___y_4304_;
goto v___jp_4306_;
}
}
}
}
v___jp_4367_:
{
lean_object* v___x_4376_; 
v___x_4376_ = l_Lean_Syntax_getTailPos_x3f(v___y_4371_, v___y_4369_);
lean_dec(v___y_4371_);
if (lean_obj_tag(v___x_4376_) == 0)
{
lean_inc(v___y_4375_);
v___y_4343_ = v___y_4368_;
v___y_4344_ = v___y_4369_;
v___y_4345_ = v___y_4370_;
v___y_4346_ = v___y_4375_;
v___y_4347_ = v___y_4372_;
v___y_4348_ = v___y_4373_;
v___y_4349_ = v___y_4374_;
v___y_4350_ = v___y_4375_;
goto v___jp_4342_;
}
else
{
lean_object* v_val_4377_; 
v_val_4377_ = lean_ctor_get(v___x_4376_, 0);
lean_inc(v_val_4377_);
lean_dec_ref(v___x_4376_);
v___y_4343_ = v___y_4368_;
v___y_4344_ = v___y_4369_;
v___y_4345_ = v___y_4370_;
v___y_4346_ = v___y_4375_;
v___y_4347_ = v___y_4372_;
v___y_4348_ = v___y_4373_;
v___y_4349_ = v___y_4374_;
v___y_4350_ = v_val_4377_;
goto v___jp_4342_;
}
}
v___jp_4378_:
{
lean_object* v_ref_4386_; lean_object* v___x_4387_; 
v_ref_4386_ = l_Lean_replaceRef(v_ref_4297_, v___y_4380_);
lean_dec(v___y_4380_);
v___x_4387_ = l_Lean_Syntax_getPos_x3f(v_ref_4386_, v___y_4381_);
if (lean_obj_tag(v___x_4387_) == 0)
{
lean_object* v___x_4388_; 
v___x_4388_ = lean_unsigned_to_nat(0u);
v___y_4368_ = v___y_4379_;
v___y_4369_ = v___y_4381_;
v___y_4370_ = v___y_4382_;
v___y_4371_ = v_ref_4386_;
v___y_4372_ = v___y_4383_;
v___y_4373_ = v___y_4384_;
v___y_4374_ = v___y_4385_;
v___y_4375_ = v___x_4388_;
goto v___jp_4367_;
}
else
{
lean_object* v_val_4389_; 
v_val_4389_ = lean_ctor_get(v___x_4387_, 0);
lean_inc(v_val_4389_);
lean_dec_ref(v___x_4387_);
v___y_4368_ = v___y_4379_;
v___y_4369_ = v___y_4381_;
v___y_4370_ = v___y_4382_;
v___y_4371_ = v_ref_4386_;
v___y_4372_ = v___y_4383_;
v___y_4373_ = v___y_4384_;
v___y_4374_ = v___y_4385_;
v___y_4375_ = v_val_4389_;
goto v___jp_4367_;
}
}
v___jp_4391_:
{
if (v___y_4398_ == 0)
{
v___y_4379_ = v___y_4394_;
v___y_4380_ = v___y_4392_;
v___y_4381_ = v___y_4397_;
v___y_4382_ = v___y_4393_;
v___y_4383_ = v___y_4395_;
v___y_4384_ = v___y_4396_;
v___y_4385_ = v_severity_4299_;
goto v___jp_4378_;
}
else
{
v___y_4379_ = v___y_4394_;
v___y_4380_ = v___y_4392_;
v___y_4381_ = v___y_4397_;
v___y_4382_ = v___y_4393_;
v___y_4383_ = v___y_4395_;
v___y_4384_ = v___y_4396_;
v___y_4385_ = v___x_4390_;
goto v___jp_4378_;
}
}
v___jp_4399_:
{
if (v___y_4400_ == 0)
{
lean_object* v_fileName_4401_; lean_object* v_fileMap_4402_; lean_object* v_options_4403_; lean_object* v_ref_4404_; uint8_t v_suppressElabErrors_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___f_4408_; uint8_t v___x_4409_; uint8_t v___x_4410_; 
v_fileName_4401_ = lean_ctor_get(v___y_4303_, 0);
v_fileMap_4402_ = lean_ctor_get(v___y_4303_, 1);
v_options_4403_ = lean_ctor_get(v___y_4303_, 2);
v_ref_4404_ = lean_ctor_get(v___y_4303_, 5);
v_suppressElabErrors_4405_ = lean_ctor_get_uint8(v___y_4303_, sizeof(void*)*14 + 1);
v___x_4406_ = lean_box(v___y_4400_);
v___x_4407_ = lean_box(v_suppressElabErrors_4405_);
v___f_4408_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4408_, 0, v___x_4406_);
lean_closure_set(v___f_4408_, 1, v___x_4407_);
v___x_4409_ = 1;
v___x_4410_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4299_, v___x_4409_);
if (v___x_4410_ == 0)
{
lean_inc_ref(v_fileName_4401_);
lean_inc_ref(v_fileMap_4402_);
lean_inc(v_ref_4404_);
v___y_4392_ = v_ref_4404_;
v___y_4393_ = v_suppressElabErrors_4405_;
v___y_4394_ = v___f_4408_;
v___y_4395_ = v_fileMap_4402_;
v___y_4396_ = v_fileName_4401_;
v___y_4397_ = v___y_4400_;
v___y_4398_ = v___x_4410_;
goto v___jp_4391_;
}
else
{
lean_object* v___x_4411_; uint8_t v___x_4412_; 
v___x_4411_ = l_Lean_warningAsError;
v___x_4412_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(v_options_4403_, v___x_4411_);
lean_inc_ref(v_fileName_4401_);
lean_inc_ref(v_fileMap_4402_);
lean_inc(v_ref_4404_);
v___y_4392_ = v_ref_4404_;
v___y_4393_ = v_suppressElabErrors_4405_;
v___y_4394_ = v___f_4408_;
v___y_4395_ = v_fileMap_4402_;
v___y_4396_ = v_fileName_4401_;
v___y_4397_ = v___y_4400_;
v___y_4398_ = v___x_4412_;
goto v___jp_4391_;
}
}
else
{
lean_object* v___x_4413_; lean_object* v___x_4414_; 
lean_dec_ref(v___y_4303_);
lean_dec_ref(v_msgData_4298_);
v___x_4413_ = lean_box(0);
v___x_4414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4414_, 0, v___x_4413_);
return v___x_4414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_4417_, lean_object* v_msgData_4418_, lean_object* v_severity_4419_, lean_object* v_isSilent_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_){
_start:
{
uint8_t v_severity_boxed_4426_; uint8_t v_isSilent_boxed_4427_; lean_object* v_res_4428_; 
v_severity_boxed_4426_ = lean_unbox(v_severity_4419_);
v_isSilent_boxed_4427_ = lean_unbox(v_isSilent_4420_);
v_res_4428_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(v_ref_4417_, v_msgData_4418_, v_severity_boxed_4426_, v_isSilent_boxed_4427_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
lean_dec(v___y_4424_);
lean_dec(v___y_4422_);
lean_dec_ref(v___y_4421_);
lean_dec(v_ref_4417_);
return v_res_4428_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(lean_object* v_msgData_4429_, uint8_t v_severity_4430_, uint8_t v_isSilent_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_){
_start:
{
lean_object* v_ref_4437_; lean_object* v___x_4438_; 
v_ref_4437_ = lean_ctor_get(v___y_4434_, 5);
lean_inc(v_ref_4437_);
v___x_4438_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(v_ref_4437_, v_msgData_4429_, v_severity_4430_, v_isSilent_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
lean_dec(v_ref_4437_);
return v___x_4438_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0___boxed(lean_object* v_msgData_4439_, lean_object* v_severity_4440_, lean_object* v_isSilent_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_){
_start:
{
uint8_t v_severity_boxed_4447_; uint8_t v_isSilent_boxed_4448_; lean_object* v_res_4449_; 
v_severity_boxed_4447_ = lean_unbox(v_severity_4440_);
v_isSilent_boxed_4448_ = lean_unbox(v_isSilent_4441_);
v_res_4449_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(v_msgData_4439_, v_severity_boxed_4447_, v_isSilent_boxed_4448_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_);
lean_dec(v___y_4445_);
lean_dec(v___y_4443_);
lean_dec_ref(v___y_4442_);
return v_res_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(lean_object* v_msgData_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_){
_start:
{
uint8_t v___x_4456_; uint8_t v___x_4457_; lean_object* v___x_4458_; 
v___x_4456_ = 0;
v___x_4457_ = 0;
v___x_4458_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(v_msgData_4450_, v___x_4456_, v___x_4457_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
return v___x_4458_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0___boxed(lean_object* v_msgData_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_){
_start:
{
lean_object* v_res_4465_; 
v_res_4465_ = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(v_msgData_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_);
lean_dec(v___y_4463_);
lean_dec(v___y_4461_);
lean_dec_ref(v___y_4460_);
return v_res_4465_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1(void){
_start:
{
lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___x_4467_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0));
v___x_4468_ = l_Lean_stringToMessageData(v___x_4467_);
return v___x_4468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2(uint8_t v___x_4469_, lean_object* v___altIdx_4470_, lean_object* v_expAltType_4471_, lean_object* v___altParams_4472_, lean_object* v_alt_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_){
_start:
{
lean_object* v___x_4479_; 
lean_inc(v___y_4477_);
lean_inc_ref(v___y_4476_);
lean_inc(v___y_4475_);
lean_inc_ref(v___y_4474_);
lean_inc_ref(v_alt_4473_);
v___x_4479_ = lean_infer_type(v_alt_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
if (lean_obj_tag(v___x_4479_) == 0)
{
lean_object* v_a_4480_; lean_object* v___x_4481_; 
v_a_4480_ = lean_ctor_get(v___x_4479_, 0);
lean_inc(v_a_4480_);
lean_dec_ref(v___x_4479_);
lean_inc(v___y_4477_);
lean_inc_ref(v___y_4476_);
lean_inc(v___y_4475_);
lean_inc_ref(v___y_4474_);
v___x_4481_ = l_Lean_Meta_mkEq(v_expAltType_4471_, v_a_4480_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v_a_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; 
v_a_4482_ = lean_ctor_get(v___x_4481_, 0);
lean_inc(v_a_4482_);
lean_dec_ref(v___x_4481_);
v___x_4483_ = lean_box(0);
lean_inc_ref(v___y_4474_);
v___x_4484_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4482_, v___x_4483_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
if (lean_obj_tag(v___x_4484_) == 0)
{
lean_object* v_a_4485_; lean_object* v___y_4487_; lean_object* v___x_4497_; lean_object* v___x_4498_; 
v_a_4485_ = lean_ctor_get(v___x_4484_, 0);
lean_inc(v_a_4485_);
lean_dec_ref(v___x_4484_);
v___x_4497_ = l_Lean_Expr_mvarId_x21(v_a_4485_);
lean_inc(v___y_4477_);
lean_inc_ref(v___y_4476_);
lean_inc(v___y_4475_);
lean_inc_ref(v___y_4474_);
v___x_4498_ = l_Lean_Meta_Split_simpMatchTarget(v___x_4497_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
if (lean_obj_tag(v___x_4498_) == 0)
{
lean_object* v_a_4499_; lean_object* v___x_4500_; 
v_a_4499_ = lean_ctor_get(v___x_4498_, 0);
lean_inc(v_a_4499_);
lean_dec_ref(v___x_4498_);
lean_inc(v___y_4477_);
lean_inc_ref(v___y_4476_);
lean_inc(v___y_4475_);
lean_inc_ref(v___y_4474_);
lean_inc(v_a_4499_);
v___x_4500_ = l_Lean_MVarId_refl(v_a_4499_, v___x_4469_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
if (lean_obj_tag(v___x_4500_) == 0)
{
lean_dec(v_a_4499_);
v___y_4487_ = v___x_4500_;
goto v___jp_4486_;
}
else
{
lean_object* v_a_4501_; uint8_t v___y_4503_; uint8_t v___x_4516_; 
v_a_4501_ = lean_ctor_get(v___x_4500_, 0);
lean_inc(v_a_4501_);
v___x_4516_ = l_Lean_Exception_isInterrupt(v_a_4501_);
if (v___x_4516_ == 0)
{
uint8_t v___x_4517_; 
v___x_4517_ = l_Lean_Exception_isRuntime(v_a_4501_);
v___y_4503_ = v___x_4517_;
goto v___jp_4502_;
}
else
{
lean_dec(v_a_4501_);
v___y_4503_ = v___x_4516_;
goto v___jp_4502_;
}
v___jp_4502_:
{
if (v___y_4503_ == 0)
{
lean_object* v___x_4505_; uint8_t v_isShared_4506_; uint8_t v_isSharedCheck_4514_; 
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4500_);
if (v_isSharedCheck_4514_ == 0)
{
lean_object* v_unused_4515_; 
v_unused_4515_ = lean_ctor_get(v___x_4500_, 0);
lean_dec(v_unused_4515_);
v___x_4505_ = v___x_4500_;
v_isShared_4506_ = v_isSharedCheck_4514_;
goto v_resetjp_4504_;
}
else
{
lean_dec(v___x_4500_);
v___x_4505_ = lean_box(0);
v_isShared_4506_ = v_isSharedCheck_4514_;
goto v_resetjp_4504_;
}
v_resetjp_4504_:
{
lean_object* v___x_4507_; lean_object* v___x_4509_; 
v___x_4507_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1, &l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1);
lean_inc(v_a_4499_);
if (v_isShared_4506_ == 0)
{
lean_ctor_set(v___x_4505_, 0, v_a_4499_);
v___x_4509_ = v___x_4505_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4499_);
v___x_4509_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
lean_object* v___x_4510_; lean_object* v___x_4511_; 
v___x_4510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4507_);
lean_ctor_set(v___x_4510_, 1, v___x_4509_);
lean_inc_ref(v___y_4476_);
v___x_4511_ = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(v___x_4510_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
if (lean_obj_tag(v___x_4511_) == 0)
{
lean_object* v___x_4512_; 
lean_dec_ref(v___x_4511_);
lean_inc(v___y_4477_);
lean_inc_ref(v___y_4476_);
lean_inc(v___y_4475_);
lean_inc_ref(v___y_4474_);
v___x_4512_ = l_Lean_MVarId_admit(v_a_4499_, v___x_4469_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
v___y_4487_ = v___x_4512_;
goto v___jp_4486_;
}
else
{
lean_dec(v_a_4499_);
v___y_4487_ = v___x_4511_;
goto v___jp_4486_;
}
}
}
}
else
{
lean_dec(v_a_4499_);
v___y_4487_ = v___x_4500_;
goto v___jp_4486_;
}
}
}
}
else
{
lean_object* v_a_4518_; lean_object* v___x_4520_; uint8_t v_isShared_4521_; uint8_t v_isSharedCheck_4525_; 
lean_dec(v_a_4485_);
lean_dec(v___y_4477_);
lean_dec_ref(v___y_4476_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec_ref(v_alt_4473_);
v_a_4518_ = lean_ctor_get(v___x_4498_, 0);
v_isSharedCheck_4525_ = !lean_is_exclusive(v___x_4498_);
if (v_isSharedCheck_4525_ == 0)
{
v___x_4520_ = v___x_4498_;
v_isShared_4521_ = v_isSharedCheck_4525_;
goto v_resetjp_4519_;
}
else
{
lean_inc(v_a_4518_);
lean_dec(v___x_4498_);
v___x_4520_ = lean_box(0);
v_isShared_4521_ = v_isSharedCheck_4525_;
goto v_resetjp_4519_;
}
v_resetjp_4519_:
{
lean_object* v___x_4523_; 
if (v_isShared_4521_ == 0)
{
v___x_4523_ = v___x_4520_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4524_; 
v_reuseFailAlloc_4524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4524_, 0, v_a_4518_);
v___x_4523_ = v_reuseFailAlloc_4524_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
return v___x_4523_;
}
}
}
v___jp_4486_:
{
if (lean_obj_tag(v___y_4487_) == 0)
{
lean_object* v___x_4488_; 
lean_dec_ref(v___y_4487_);
v___x_4488_ = l_Lean_Meta_mkEqMPR(v_a_4485_, v_alt_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
return v___x_4488_;
}
else
{
lean_object* v_a_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4496_; 
lean_dec(v_a_4485_);
lean_dec(v___y_4477_);
lean_dec_ref(v___y_4476_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec_ref(v_alt_4473_);
v_a_4489_ = lean_ctor_get(v___y_4487_, 0);
v_isSharedCheck_4496_ = !lean_is_exclusive(v___y_4487_);
if (v_isSharedCheck_4496_ == 0)
{
v___x_4491_ = v___y_4487_;
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_a_4489_);
lean_dec(v___y_4487_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4494_; 
if (v_isShared_4492_ == 0)
{
v___x_4494_ = v___x_4491_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v_a_4489_);
v___x_4494_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
return v___x_4494_;
}
}
}
}
}
else
{
lean_dec(v___y_4477_);
lean_dec_ref(v___y_4476_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec_ref(v_alt_4473_);
return v___x_4484_;
}
}
else
{
lean_dec(v___y_4477_);
lean_dec_ref(v___y_4476_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec_ref(v_alt_4473_);
return v___x_4481_;
}
}
else
{
lean_dec(v___y_4477_);
lean_dec_ref(v___y_4476_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec_ref(v_alt_4473_);
lean_dec_ref(v_expAltType_4471_);
return v___x_4479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___boxed(lean_object* v___x_4526_, lean_object* v___altIdx_4527_, lean_object* v_expAltType_4528_, lean_object* v___altParams_4529_, lean_object* v_alt_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_){
_start:
{
uint8_t v___x_32543__boxed_4536_; lean_object* v_res_4537_; 
v___x_32543__boxed_4536_ = lean_unbox(v___x_4526_);
v_res_4537_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__2(v___x_32543__boxed_4536_, v___altIdx_4527_, v_expAltType_4528_, v___altParams_4529_, v_alt_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
lean_dec_ref(v___altParams_4529_);
lean_dec(v___altIdx_4527_);
return v_res_4537_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(lean_object* v___x_4538_, lean_object* v_e_4539_){
_start:
{
uint8_t v___x_4540_; lean_object* v_d_4542_; lean_object* v_b_4543_; 
v___x_4540_ = l_Lean_Expr_hasFVar(v_e_4539_);
if (v___x_4540_ == 0)
{
return v___x_4540_;
}
else
{
switch(lean_obj_tag(v_e_4539_))
{
case 7:
{
lean_object* v_binderType_4546_; lean_object* v_body_4547_; 
v_binderType_4546_ = lean_ctor_get(v_e_4539_, 1);
v_body_4547_ = lean_ctor_get(v_e_4539_, 2);
v_d_4542_ = v_binderType_4546_;
v_b_4543_ = v_body_4547_;
goto v___jp_4541_;
}
case 6:
{
lean_object* v_binderType_4548_; lean_object* v_body_4549_; 
v_binderType_4548_ = lean_ctor_get(v_e_4539_, 1);
v_body_4549_ = lean_ctor_get(v_e_4539_, 2);
v_d_4542_ = v_binderType_4548_;
v_b_4543_ = v_body_4549_;
goto v___jp_4541_;
}
case 10:
{
lean_object* v_expr_4550_; 
v_expr_4550_ = lean_ctor_get(v_e_4539_, 1);
v_e_4539_ = v_expr_4550_;
goto _start;
}
case 8:
{
lean_object* v_type_4552_; lean_object* v_value_4553_; lean_object* v_body_4554_; uint8_t v___x_4555_; 
v_type_4552_ = lean_ctor_get(v_e_4539_, 1);
v_value_4553_ = lean_ctor_get(v_e_4539_, 2);
v_body_4554_ = lean_ctor_get(v_e_4539_, 3);
v___x_4555_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4538_, v_type_4552_);
if (v___x_4555_ == 0)
{
uint8_t v___x_4556_; 
v___x_4556_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4538_, v_value_4553_);
if (v___x_4556_ == 0)
{
v_e_4539_ = v_body_4554_;
goto _start;
}
else
{
return v___x_4540_;
}
}
else
{
return v___x_4540_;
}
}
case 5:
{
lean_object* v_fn_4558_; lean_object* v_arg_4559_; uint8_t v___x_4560_; 
v_fn_4558_ = lean_ctor_get(v_e_4539_, 0);
v_arg_4559_ = lean_ctor_get(v_e_4539_, 1);
v___x_4560_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4538_, v_fn_4558_);
if (v___x_4560_ == 0)
{
v_e_4539_ = v_arg_4559_;
goto _start;
}
else
{
return v___x_4540_;
}
}
case 11:
{
lean_object* v_struct_4562_; 
v_struct_4562_ = lean_ctor_get(v_e_4539_, 2);
v_e_4539_ = v_struct_4562_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4564_; lean_object* v___x_4565_; uint8_t v___x_4566_; 
v_fvarId_4564_ = lean_ctor_get(v_e_4539_, 0);
v___x_4565_ = l_Lean_Expr_fvarId_x21(v___x_4538_);
v___x_4566_ = l_Lean_instBEqFVarId_beq(v_fvarId_4564_, v___x_4565_);
lean_dec(v___x_4565_);
return v___x_4566_;
}
default: 
{
uint8_t v___x_4567_; 
v___x_4567_ = 0;
return v___x_4567_;
}
}
}
v___jp_4541_:
{
uint8_t v___x_4544_; 
v___x_4544_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4538_, v_d_4542_);
if (v___x_4544_ == 0)
{
v_e_4539_ = v_b_4543_;
goto _start;
}
else
{
return v___x_4540_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1___boxed(lean_object* v___x_4568_, lean_object* v_e_4569_){
_start:
{
uint8_t v_res_4570_; lean_object* v_r_4571_; 
v_res_4570_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4568_, v_e_4569_);
lean_dec_ref(v_e_4569_);
lean_dec_ref(v___x_4568_);
v_r_4571_ = lean_box(v_res_4570_);
return v_r_4571_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4573_; lean_object* v___x_4574_; 
v___x_4573_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__0));
v___x_4574_ = l_Lean_stringToMessageData(v___x_4573_);
return v___x_4574_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4576_; lean_object* v___x_4577_; 
v___x_4576_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__2));
v___x_4577_ = l_Lean_stringToMessageData(v___x_4576_);
return v___x_4577_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_4579_; lean_object* v___x_4580_; 
v___x_4579_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__4));
v___x_4580_ = l_Lean_stringToMessageData(v___x_4579_);
return v___x_4580_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(lean_object* v_a_4581_, lean_object* v_termAlt_4582_, lean_object* v_a_4583_, lean_object* v_b_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_){
_start:
{
lean_object* v_array_4590_; lean_object* v_start_4591_; lean_object* v_stop_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4620_; 
v_array_4590_ = lean_ctor_get(v_a_4583_, 0);
v_start_4591_ = lean_ctor_get(v_a_4583_, 1);
v_stop_4592_ = lean_ctor_get(v_a_4583_, 2);
v_isSharedCheck_4620_ = !lean_is_exclusive(v_a_4583_);
if (v_isSharedCheck_4620_ == 0)
{
v___x_4594_ = v_a_4583_;
v_isShared_4595_ = v_isSharedCheck_4620_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_stop_4592_);
lean_inc(v_start_4591_);
lean_inc(v_array_4590_);
lean_dec(v_a_4583_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4620_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
uint8_t v___x_4596_; 
v___x_4596_ = lean_nat_dec_lt(v_start_4591_, v_stop_4592_);
if (v___x_4596_ == 0)
{
lean_object* v___x_4597_; 
lean_del_object(v___x_4594_);
lean_dec(v_stop_4592_);
lean_dec(v_start_4591_);
lean_dec_ref(v_array_4590_);
lean_dec_ref(v_termAlt_4582_);
lean_dec_ref(v_a_4581_);
v___x_4597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4597_, 0, v_b_4584_);
return v___x_4597_;
}
else
{
lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4602_; 
v___x_4598_ = lean_box(0);
v___x_4599_ = lean_unsigned_to_nat(1u);
v___x_4600_ = lean_nat_add(v_start_4591_, v___x_4599_);
lean_inc_ref(v_array_4590_);
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 1, v___x_4600_);
v___x_4602_ = v___x_4594_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v_array_4590_);
lean_ctor_set(v_reuseFailAlloc_4619_, 1, v___x_4600_);
lean_ctor_set(v_reuseFailAlloc_4619_, 2, v_stop_4592_);
v___x_4602_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
lean_object* v___x_4603_; uint8_t v___x_4604_; 
v___x_4603_ = lean_array_fget(v_array_4590_, v_start_4591_);
lean_dec(v_start_4591_);
lean_dec_ref(v_array_4590_);
v___x_4604_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4603_, v_a_4581_);
if (v___x_4604_ == 0)
{
lean_dec(v___x_4603_);
v_a_4583_ = v___x_4602_;
v_b_4584_ = v___x_4598_;
goto _start;
}
else
{
lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; 
v___x_4606_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1);
lean_inc_ref(v_a_4581_);
v___x_4607_ = l_Lean_MessageData_ofExpr(v_a_4581_);
v___x_4608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4608_, 0, v___x_4606_);
lean_ctor_set(v___x_4608_, 1, v___x_4607_);
v___x_4609_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3);
v___x_4610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4610_, 0, v___x_4608_);
lean_ctor_set(v___x_4610_, 1, v___x_4609_);
lean_inc_ref(v_termAlt_4582_);
v___x_4611_ = l_Lean_MessageData_ofExpr(v_termAlt_4582_);
v___x_4612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4612_, 0, v___x_4610_);
lean_ctor_set(v___x_4612_, 1, v___x_4611_);
v___x_4613_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5);
v___x_4614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4614_, 0, v___x_4612_);
lean_ctor_set(v___x_4614_, 1, v___x_4613_);
v___x_4615_ = l_Lean_MessageData_ofExpr(v___x_4603_);
v___x_4616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4616_, 0, v___x_4614_);
lean_ctor_set(v___x_4616_, 1, v___x_4615_);
v___x_4617_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_4616_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_);
if (lean_obj_tag(v___x_4617_) == 0)
{
lean_dec_ref(v___x_4617_);
v_a_4583_ = v___x_4602_;
v_b_4584_ = v___x_4598_;
goto _start;
}
else
{
lean_dec_ref(v___x_4602_);
lean_dec_ref(v_termAlt_4582_);
lean_dec_ref(v_a_4581_);
return v___x_4617_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___boxed(lean_object* v_a_4621_, lean_object* v_termAlt_4622_, lean_object* v_a_4623_, lean_object* v_b_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_){
_start:
{
lean_object* v_res_4630_; 
v_res_4630_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_4621_, v_termAlt_4622_, v_a_4623_, v_b_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_);
lean_dec(v___y_4628_);
lean_dec_ref(v___y_4627_);
lean_dec(v___y_4626_);
lean_dec_ref(v___y_4625_);
return v_res_4630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(lean_object* v_nExtra_4631_, lean_object* v_v_4632_, uint8_t v___x_4633_, uint8_t v___x_4634_, uint8_t v___x_4635_, lean_object* v_xs_4636_, lean_object* v_termAltBody_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_){
_start:
{
lean_object* v___x_4643_; 
lean_inc(v___y_4641_);
lean_inc_ref(v___y_4640_);
lean_inc(v___y_4639_);
lean_inc_ref(v___y_4638_);
v___x_4643_ = lean_infer_type(v_termAltBody_4637_, v___y_4638_, v___y_4639_, v___y_4640_, v___y_4641_);
if (lean_obj_tag(v___x_4643_) == 0)
{
lean_object* v_a_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; 
v_a_4644_ = lean_ctor_get(v___x_4643_, 0);
lean_inc(v_a_4644_);
lean_dec_ref(v___x_4643_);
v___x_4645_ = lean_array_get_size(v_xs_4636_);
v___x_4646_ = lean_nat_sub(v___x_4645_, v_nExtra_4631_);
v___x_4647_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_4646_);
lean_inc_ref(v_xs_4636_);
v___x_4648_ = l_Array_toSubarray___redArg(v_xs_4636_, v___x_4647_, v___x_4646_);
v___x_4649_ = l_Array_toSubarray___redArg(v_xs_4636_, v___x_4646_, v___x_4645_);
v___x_4650_ = lean_box(0);
lean_inc(v_a_4644_);
v___x_4651_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_4644_, v_v_4632_, v___x_4649_, v___x_4650_, v___y_4638_, v___y_4639_, v___y_4640_, v___y_4641_);
if (lean_obj_tag(v___x_4651_) == 0)
{
lean_object* v___x_4652_; lean_object* v___x_4653_; 
lean_dec_ref(v___x_4651_);
v___x_4652_ = l_Subarray_copy___redArg(v___x_4648_);
v___x_4653_ = l_Lean_Meta_mkLambdaFVars(v___x_4652_, v_a_4644_, v___x_4633_, v___x_4634_, v___x_4633_, v___x_4634_, v___x_4635_, v___y_4638_, v___y_4639_, v___y_4640_, v___y_4641_);
lean_dec(v___y_4641_);
lean_dec_ref(v___y_4640_);
lean_dec(v___y_4639_);
lean_dec_ref(v___y_4638_);
lean_dec_ref(v___x_4652_);
return v___x_4653_;
}
else
{
lean_object* v_a_4654_; lean_object* v___x_4656_; uint8_t v_isShared_4657_; uint8_t v_isSharedCheck_4661_; 
lean_dec_ref(v___x_4648_);
lean_dec(v_a_4644_);
lean_dec(v___y_4641_);
lean_dec_ref(v___y_4640_);
lean_dec(v___y_4639_);
lean_dec_ref(v___y_4638_);
v_a_4654_ = lean_ctor_get(v___x_4651_, 0);
v_isSharedCheck_4661_ = !lean_is_exclusive(v___x_4651_);
if (v_isSharedCheck_4661_ == 0)
{
v___x_4656_ = v___x_4651_;
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
else
{
lean_inc(v_a_4654_);
lean_dec(v___x_4651_);
v___x_4656_ = lean_box(0);
v_isShared_4657_ = v_isSharedCheck_4661_;
goto v_resetjp_4655_;
}
v_resetjp_4655_:
{
lean_object* v___x_4659_; 
if (v_isShared_4657_ == 0)
{
v___x_4659_ = v___x_4656_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4660_; 
v_reuseFailAlloc_4660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4660_, 0, v_a_4654_);
v___x_4659_ = v_reuseFailAlloc_4660_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
return v___x_4659_;
}
}
}
}
else
{
lean_dec(v___y_4641_);
lean_dec_ref(v___y_4640_);
lean_dec(v___y_4639_);
lean_dec_ref(v___y_4638_);
lean_dec_ref(v_xs_4636_);
lean_dec(v_v_4632_);
return v___x_4643_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed(lean_object* v_nExtra_4662_, lean_object* v_v_4663_, lean_object* v___x_4664_, lean_object* v___x_4665_, lean_object* v___x_4666_, lean_object* v_xs_4667_, lean_object* v_termAltBody_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_){
_start:
{
uint8_t v___x_32832__boxed_4674_; uint8_t v___x_32833__boxed_4675_; uint8_t v___x_32834__boxed_4676_; lean_object* v_res_4677_; 
v___x_32832__boxed_4674_ = lean_unbox(v___x_4664_);
v___x_32833__boxed_4675_ = lean_unbox(v___x_4665_);
v___x_32834__boxed_4676_ = lean_unbox(v___x_4666_);
v_res_4677_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(v_nExtra_4662_, v_v_4663_, v___x_32832__boxed_4674_, v___x_32833__boxed_4675_, v___x_32834__boxed_4676_, v_xs_4667_, v_termAltBody_4668_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_);
lean_dec(v_nExtra_4662_);
return v_res_4677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(lean_object* v_nExtra_4678_, size_t v_sz_4679_, size_t v_i_4680_, lean_object* v_bs_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_){
_start:
{
uint8_t v___x_4687_; 
v___x_4687_ = lean_usize_dec_lt(v_i_4680_, v_sz_4679_);
if (v___x_4687_ == 0)
{
lean_object* v___x_4688_; 
lean_dec(v___y_4685_);
lean_dec_ref(v___y_4684_);
lean_dec(v___y_4683_);
lean_dec_ref(v___y_4682_);
lean_dec(v_nExtra_4678_);
v___x_4688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4688_, 0, v_bs_4681_);
return v___x_4688_;
}
else
{
uint8_t v___x_4689_; uint8_t v___x_4690_; lean_object* v_v_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___f_4695_; lean_object* v___x_4696_; 
v___x_4689_ = 0;
v___x_4690_ = 1;
v_v_4691_ = lean_array_uget_borrowed(v_bs_4681_, v_i_4680_);
v___x_4692_ = lean_box(v___x_4689_);
v___x_4693_ = lean_box(v___x_4687_);
v___x_4694_ = lean_box(v___x_4690_);
lean_inc(v_v_4691_);
lean_inc(v_nExtra_4678_);
v___f_4695_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4695_, 0, v_nExtra_4678_);
lean_closure_set(v___f_4695_, 1, v_v_4691_);
lean_closure_set(v___f_4695_, 2, v___x_4692_);
lean_closure_set(v___f_4695_, 3, v___x_4693_);
lean_closure_set(v___f_4695_, 4, v___x_4694_);
lean_inc(v___y_4685_);
lean_inc_ref(v___y_4684_);
lean_inc(v___y_4683_);
lean_inc_ref(v___y_4682_);
lean_inc(v_v_4691_);
v___x_4696_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_v_4691_, v___f_4695_, v___x_4689_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_);
if (lean_obj_tag(v___x_4696_) == 0)
{
lean_object* v_a_4697_; lean_object* v___x_4698_; lean_object* v_bs_x27_4699_; size_t v___x_4700_; size_t v___x_4701_; lean_object* v___x_4702_; 
v_a_4697_ = lean_ctor_get(v___x_4696_, 0);
lean_inc(v_a_4697_);
lean_dec_ref(v___x_4696_);
v___x_4698_ = lean_unsigned_to_nat(0u);
v_bs_x27_4699_ = lean_array_uset(v_bs_4681_, v_i_4680_, v___x_4698_);
v___x_4700_ = ((size_t)1ULL);
v___x_4701_ = lean_usize_add(v_i_4680_, v___x_4700_);
v___x_4702_ = lean_array_uset(v_bs_x27_4699_, v_i_4680_, v_a_4697_);
v_i_4680_ = v___x_4701_;
v_bs_4681_ = v___x_4702_;
goto _start;
}
else
{
lean_object* v_a_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4711_; 
lean_dec(v___y_4685_);
lean_dec_ref(v___y_4684_);
lean_dec(v___y_4683_);
lean_dec_ref(v___y_4682_);
lean_dec_ref(v_bs_4681_);
lean_dec(v_nExtra_4678_);
v_a_4704_ = lean_ctor_get(v___x_4696_, 0);
v_isSharedCheck_4711_ = !lean_is_exclusive(v___x_4696_);
if (v_isSharedCheck_4711_ == 0)
{
v___x_4706_ = v___x_4696_;
v_isShared_4707_ = v_isSharedCheck_4711_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_a_4704_);
lean_dec(v___x_4696_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4711_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v___x_4709_; 
if (v_isShared_4707_ == 0)
{
v___x_4709_ = v___x_4706_;
goto v_reusejp_4708_;
}
else
{
lean_object* v_reuseFailAlloc_4710_; 
v_reuseFailAlloc_4710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4710_, 0, v_a_4704_);
v___x_4709_ = v_reuseFailAlloc_4710_;
goto v_reusejp_4708_;
}
v_reusejp_4708_:
{
return v___x_4709_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___boxed(lean_object* v_nExtra_4712_, lean_object* v_sz_4713_, lean_object* v_i_4714_, lean_object* v_bs_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_){
_start:
{
size_t v_sz_boxed_4721_; size_t v_i_boxed_4722_; lean_object* v_res_4723_; 
v_sz_boxed_4721_ = lean_unbox_usize(v_sz_4713_);
lean_dec(v_sz_4713_);
v_i_boxed_4722_ = lean_unbox_usize(v_i_4714_);
lean_dec(v_i_4714_);
v_res_4723_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(v_nExtra_4712_, v_sz_boxed_4721_, v_i_boxed_4722_, v_bs_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_);
return v_res_4723_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0(void){
_start:
{
lean_object* v___x_4724_; lean_object* v___x_4725_; 
v___x_4724_ = lean_box(0);
v___x_4725_ = l_Lean_Expr_sort___override(v___x_4724_);
return v___x_4725_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1(void){
_start:
{
lean_object* v___x_4726_; lean_object* v___x_4727_; 
v___x_4726_ = lean_box(0);
v___x_4727_ = l_Lean_Level_succ___override(v___x_4726_);
return v___x_4727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3(lean_object* v_nExtra_4728_, uint8_t v___x_4729_, uint8_t v___x_4730_, lean_object* v_alts_4731_, lean_object* v_toMatcherInfo_4732_, lean_object* v_matcherName_4733_, lean_object* v_params_4734_, lean_object* v_matcherLevels_4735_, lean_object* v_motiveArgs_4736_, lean_object* v_body_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_){
_start:
{
lean_object* v___x_4743_; 
lean_inc(v___y_4741_);
lean_inc_ref(v___y_4740_);
lean_inc(v___y_4739_);
lean_inc_ref(v___y_4738_);
lean_inc(v_nExtra_4728_);
v___x_4743_ = l_Lean_Meta_arrowDomainsN(v_nExtra_4728_, v_body_4737_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_);
if (lean_obj_tag(v___x_4743_) == 0)
{
lean_object* v_a_4744_; lean_object* v___x_4745_; uint8_t v___x_4746_; lean_object* v___x_4747_; 
v_a_4744_ = lean_ctor_get(v___x_4743_, 0);
lean_inc(v_a_4744_);
lean_dec_ref(v___x_4743_);
v___x_4745_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0, &l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0);
v___x_4746_ = 1;
v___x_4747_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_4736_, v___x_4745_, v___x_4729_, v___x_4730_, v___x_4729_, v___x_4730_, v___x_4746_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_);
if (lean_obj_tag(v___x_4747_) == 0)
{
lean_object* v_a_4748_; size_t v_sz_4749_; size_t v___x_4750_; lean_object* v___x_4751_; 
v_a_4748_ = lean_ctor_get(v___x_4747_, 0);
lean_inc(v_a_4748_);
lean_dec_ref(v___x_4747_);
v_sz_4749_ = lean_array_size(v_alts_4731_);
v___x_4750_ = ((size_t)0ULL);
lean_inc(v___y_4741_);
lean_inc_ref(v___y_4740_);
v___x_4751_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(v_nExtra_4728_, v_sz_4749_, v___x_4750_, v_alts_4731_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_);
if (lean_obj_tag(v___x_4751_) == 0)
{
lean_object* v_a_4752_; lean_object* v_matcherLevels_4754_; lean_object* v___y_4755_; lean_object* v___y_4756_; lean_object* v_uElimPos_x3f_4761_; 
v_a_4752_ = lean_ctor_get(v___x_4751_, 0);
lean_inc(v_a_4752_);
lean_dec_ref(v___x_4751_);
v_uElimPos_x3f_4761_ = lean_ctor_get(v_toMatcherInfo_4732_, 3);
if (lean_obj_tag(v_uElimPos_x3f_4761_) == 0)
{
v_matcherLevels_4754_ = v_matcherLevels_4735_;
v___y_4755_ = v___y_4740_;
v___y_4756_ = v___y_4741_;
goto v___jp_4753_;
}
else
{
lean_object* v_val_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; 
v_val_4762_ = lean_ctor_get(v_uElimPos_x3f_4761_, 0);
v___x_4763_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1, &l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1);
v___x_4764_ = lean_array_set(v_matcherLevels_4735_, v_val_4762_, v___x_4763_);
v_matcherLevels_4754_ = v___x_4764_;
v___y_4755_ = v___y_4740_;
v___y_4756_ = v___y_4741_;
goto v___jp_4753_;
}
v___jp_4753_:
{
lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; 
v___x_4757_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_4758_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4758_, 0, v_toMatcherInfo_4732_);
lean_ctor_set(v___x_4758_, 1, v_matcherName_4733_);
lean_ctor_set(v___x_4758_, 2, v_matcherLevels_4754_);
lean_ctor_set(v___x_4758_, 3, v_params_4734_);
lean_ctor_set(v___x_4758_, 4, v_a_4748_);
lean_ctor_set(v___x_4758_, 5, v_motiveArgs_4736_);
lean_ctor_set(v___x_4758_, 6, v_a_4752_);
lean_ctor_set(v___x_4758_, 7, v___x_4757_);
v___x_4759_ = l_Lean_Meta_MatcherApp_toExpr(v___x_4758_);
v___x_4760_ = l_Lean_mkArrowN(v_a_4744_, v___x_4759_, v___y_4755_, v___y_4756_);
lean_dec(v_a_4744_);
return v___x_4760_;
}
}
else
{
lean_object* v_a_4765_; lean_object* v___x_4767_; uint8_t v_isShared_4768_; uint8_t v_isSharedCheck_4772_; 
lean_dec(v_a_4748_);
lean_dec(v_a_4744_);
lean_dec(v___y_4741_);
lean_dec_ref(v___y_4740_);
lean_dec_ref(v_motiveArgs_4736_);
lean_dec_ref(v_matcherLevels_4735_);
lean_dec_ref(v_params_4734_);
lean_dec(v_matcherName_4733_);
lean_dec_ref(v_toMatcherInfo_4732_);
v_a_4765_ = lean_ctor_get(v___x_4751_, 0);
v_isSharedCheck_4772_ = !lean_is_exclusive(v___x_4751_);
if (v_isSharedCheck_4772_ == 0)
{
v___x_4767_ = v___x_4751_;
v_isShared_4768_ = v_isSharedCheck_4772_;
goto v_resetjp_4766_;
}
else
{
lean_inc(v_a_4765_);
lean_dec(v___x_4751_);
v___x_4767_ = lean_box(0);
v_isShared_4768_ = v_isSharedCheck_4772_;
goto v_resetjp_4766_;
}
v_resetjp_4766_:
{
lean_object* v___x_4770_; 
if (v_isShared_4768_ == 0)
{
v___x_4770_ = v___x_4767_;
goto v_reusejp_4769_;
}
else
{
lean_object* v_reuseFailAlloc_4771_; 
v_reuseFailAlloc_4771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4771_, 0, v_a_4765_);
v___x_4770_ = v_reuseFailAlloc_4771_;
goto v_reusejp_4769_;
}
v_reusejp_4769_:
{
return v___x_4770_;
}
}
}
}
else
{
lean_dec(v_a_4744_);
lean_dec(v___y_4741_);
lean_dec_ref(v___y_4740_);
lean_dec(v___y_4739_);
lean_dec_ref(v___y_4738_);
lean_dec_ref(v_motiveArgs_4736_);
lean_dec_ref(v_matcherLevels_4735_);
lean_dec_ref(v_params_4734_);
lean_dec(v_matcherName_4733_);
lean_dec_ref(v_toMatcherInfo_4732_);
lean_dec_ref(v_alts_4731_);
lean_dec(v_nExtra_4728_);
return v___x_4747_;
}
}
else
{
lean_object* v_a_4773_; lean_object* v___x_4775_; uint8_t v_isShared_4776_; uint8_t v_isSharedCheck_4780_; 
lean_dec(v___y_4741_);
lean_dec_ref(v___y_4740_);
lean_dec(v___y_4739_);
lean_dec_ref(v___y_4738_);
lean_dec_ref(v_motiveArgs_4736_);
lean_dec_ref(v_matcherLevels_4735_);
lean_dec_ref(v_params_4734_);
lean_dec(v_matcherName_4733_);
lean_dec_ref(v_toMatcherInfo_4732_);
lean_dec_ref(v_alts_4731_);
lean_dec(v_nExtra_4728_);
v_a_4773_ = lean_ctor_get(v___x_4743_, 0);
v_isSharedCheck_4780_ = !lean_is_exclusive(v___x_4743_);
if (v_isSharedCheck_4780_ == 0)
{
v___x_4775_ = v___x_4743_;
v_isShared_4776_ = v_isSharedCheck_4780_;
goto v_resetjp_4774_;
}
else
{
lean_inc(v_a_4773_);
lean_dec(v___x_4743_);
v___x_4775_ = lean_box(0);
v_isShared_4776_ = v_isSharedCheck_4780_;
goto v_resetjp_4774_;
}
v_resetjp_4774_:
{
lean_object* v___x_4778_; 
if (v_isShared_4776_ == 0)
{
v___x_4778_ = v___x_4775_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4779_; 
v_reuseFailAlloc_4779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4779_, 0, v_a_4773_);
v___x_4778_ = v_reuseFailAlloc_4779_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
return v___x_4778_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed(lean_object* v_nExtra_4781_, lean_object* v___x_4782_, lean_object* v___x_4783_, lean_object* v_alts_4784_, lean_object* v_toMatcherInfo_4785_, lean_object* v_matcherName_4786_, lean_object* v_params_4787_, lean_object* v_matcherLevels_4788_, lean_object* v_motiveArgs_4789_, lean_object* v_body_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_){
_start:
{
uint8_t v___x_32967__boxed_4796_; uint8_t v___x_32968__boxed_4797_; lean_object* v_res_4798_; 
v___x_32967__boxed_4796_ = lean_unbox(v___x_4782_);
v___x_32968__boxed_4797_ = lean_unbox(v___x_4783_);
v_res_4798_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__3(v_nExtra_4781_, v___x_32967__boxed_4796_, v___x_32968__boxed_4797_, v_alts_4784_, v_toMatcherInfo_4785_, v_matcherName_4786_, v_params_4787_, v_matcherLevels_4788_, v_motiveArgs_4789_, v_body_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_);
return v_res_4798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(lean_object* v_k_4799_, lean_object* v_ys_4800_, lean_object* v_args_4801_, lean_object* v___mask_4802_, lean_object* v___bodyType_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_){
_start:
{
lean_object* v___x_4809_; 
v___x_4809_ = lean_apply_7(v_k_4799_, v_ys_4800_, v_args_4801_, v___y_4804_, v___y_4805_, v___y_4806_, v___y_4807_, lean_box(0));
return v___x_4809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed(lean_object* v_k_4810_, lean_object* v_ys_4811_, lean_object* v_args_4812_, lean_object* v___mask_4813_, lean_object* v___bodyType_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_){
_start:
{
lean_object* v_res_4820_; 
v_res_4820_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(v_k_4810_, v_ys_4811_, v_args_4812_, v___mask_4813_, v___bodyType_4814_, v___y_4815_, v___y_4816_, v___y_4817_, v___y_4818_);
lean_dec_ref(v___bodyType_4814_);
lean_dec_ref(v___mask_4813_);
return v_res_4820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(lean_object* v_origAltType_4821_, lean_object* v_altInfo_4822_, lean_object* v_k_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_){
_start:
{
lean_object* v___f_4829_; lean_object* v___x_4830_; 
v___f_4829_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_4829_, 0, v_k_4823_);
v___x_4830_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_origAltType_4821_, v_altInfo_4822_, v___f_4829_, v___y_4824_, v___y_4825_, v___y_4826_, v___y_4827_);
if (lean_obj_tag(v___x_4830_) == 0)
{
lean_object* v_a_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4838_; 
v_a_4831_ = lean_ctor_get(v___x_4830_, 0);
v_isSharedCheck_4838_ = !lean_is_exclusive(v___x_4830_);
if (v_isSharedCheck_4838_ == 0)
{
v___x_4833_ = v___x_4830_;
v_isShared_4834_ = v_isSharedCheck_4838_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_a_4831_);
lean_dec(v___x_4830_);
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
v_reuseFailAlloc_4837_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4846_; 
v_a_4839_ = lean_ctor_get(v___x_4830_, 0);
v_isSharedCheck_4846_ = !lean_is_exclusive(v___x_4830_);
if (v_isSharedCheck_4846_ == 0)
{
v___x_4841_ = v___x_4830_;
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_a_4839_);
lean_dec(v___x_4830_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___boxed(lean_object* v_origAltType_4847_, lean_object* v_altInfo_4848_, lean_object* v_k_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_){
_start:
{
lean_object* v_res_4855_; 
v_res_4855_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v_origAltType_4847_, v_altInfo_4848_, v_k_4849_, v___y_4850_, v___y_4851_, v___y_4852_, v___y_4853_);
return v_res_4855_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(lean_object* v___x_4856_, lean_object* v___x_4857_, lean_object* v___f_4858_, lean_object* v_fst_4859_, lean_object* v___x_4860_, lean_object* v___x_4861_, lean_object* v___x_4862_, lean_object* v___x_4863_, lean_object* v___x_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_){
_start:
{
lean_object* v___x_4870_; 
v___x_4870_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v___x_4856_, v___x_4857_, v___f_4858_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_);
if (lean_obj_tag(v___x_4870_) == 0)
{
lean_object* v_a_4871_; lean_object* v___x_4873_; uint8_t v_isShared_4874_; uint8_t v_isSharedCheck_4885_; 
v_a_4871_ = lean_ctor_get(v___x_4870_, 0);
v_isSharedCheck_4885_ = !lean_is_exclusive(v___x_4870_);
if (v_isSharedCheck_4885_ == 0)
{
v___x_4873_ = v___x_4870_;
v_isShared_4874_ = v_isSharedCheck_4885_;
goto v_resetjp_4872_;
}
else
{
lean_inc(v_a_4871_);
lean_dec(v___x_4870_);
v___x_4873_ = lean_box(0);
v_isShared_4874_ = v_isSharedCheck_4885_;
goto v_resetjp_4872_;
}
v_resetjp_4872_:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4883_; 
v___x_4875_ = lean_array_push(v_fst_4859_, v_a_4871_);
v___x_4876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4876_, 0, v___x_4860_);
lean_ctor_set(v___x_4876_, 1, v___x_4861_);
v___x_4877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4862_);
lean_ctor_set(v___x_4877_, 1, v___x_4876_);
v___x_4878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4878_, 0, v___x_4863_);
lean_ctor_set(v___x_4878_, 1, v___x_4877_);
v___x_4879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4879_, 0, v___x_4864_);
lean_ctor_set(v___x_4879_, 1, v___x_4878_);
v___x_4880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4880_, 0, v___x_4875_);
lean_ctor_set(v___x_4880_, 1, v___x_4879_);
v___x_4881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4881_, 0, v___x_4880_);
if (v_isShared_4874_ == 0)
{
lean_ctor_set(v___x_4873_, 0, v___x_4881_);
v___x_4883_ = v___x_4873_;
goto v_reusejp_4882_;
}
else
{
lean_object* v_reuseFailAlloc_4884_; 
v_reuseFailAlloc_4884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4884_, 0, v___x_4881_);
v___x_4883_ = v_reuseFailAlloc_4884_;
goto v_reusejp_4882_;
}
v_reusejp_4882_:
{
return v___x_4883_;
}
}
}
else
{
lean_object* v_a_4886_; lean_object* v___x_4888_; uint8_t v_isShared_4889_; uint8_t v_isSharedCheck_4893_; 
lean_dec_ref(v___x_4864_);
lean_dec_ref(v___x_4863_);
lean_dec_ref(v___x_4862_);
lean_dec_ref(v___x_4861_);
lean_dec_ref(v___x_4860_);
lean_dec(v_fst_4859_);
v_a_4886_ = lean_ctor_get(v___x_4870_, 0);
v_isSharedCheck_4893_ = !lean_is_exclusive(v___x_4870_);
if (v_isSharedCheck_4893_ == 0)
{
v___x_4888_ = v___x_4870_;
v_isShared_4889_ = v_isSharedCheck_4893_;
goto v_resetjp_4887_;
}
else
{
lean_inc(v_a_4886_);
lean_dec(v___x_4870_);
v___x_4888_ = lean_box(0);
v_isShared_4889_ = v_isSharedCheck_4893_;
goto v_resetjp_4887_;
}
v_resetjp_4887_:
{
lean_object* v___x_4891_; 
if (v_isShared_4889_ == 0)
{
v___x_4891_ = v___x_4888_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v_a_4886_);
v___x_4891_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
return v___x_4891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed(lean_object* v___x_4894_, lean_object* v___x_4895_, lean_object* v___f_4896_, lean_object* v_fst_4897_, lean_object* v___x_4898_, lean_object* v___x_4899_, lean_object* v___x_4900_, lean_object* v___x_4901_, lean_object* v___x_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_){
_start:
{
lean_object* v_res_4908_; 
v_res_4908_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(v___x_4894_, v___x_4895_, v___f_4896_, v_fst_4897_, v___x_4898_, v___x_4899_, v___x_4900_, v___x_4901_, v___x_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_);
return v_res_4908_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0(void){
_start:
{
lean_object* v___x_4909_; 
v___x_4909_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_4909_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(lean_object* v_msg_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_){
_start:
{
lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v_toApplicative_4922_; lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4983_; 
v___x_4920_ = lean_obj_once(&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0, &l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0_once, _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0);
v___x_4921_ = l_ReaderT_instMonad___redArg(v___x_4920_);
v_toApplicative_4922_ = lean_ctor_get(v___x_4921_, 0);
v_isSharedCheck_4983_ = !lean_is_exclusive(v___x_4921_);
if (v_isSharedCheck_4983_ == 0)
{
lean_object* v_unused_4984_; 
v_unused_4984_ = lean_ctor_get(v___x_4921_, 1);
lean_dec(v_unused_4984_);
v___x_4924_ = v___x_4921_;
v_isShared_4925_ = v_isSharedCheck_4983_;
goto v_resetjp_4923_;
}
else
{
lean_inc(v_toApplicative_4922_);
lean_dec(v___x_4921_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4983_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
lean_object* v_toFunctor_4926_; lean_object* v_toSeq_4927_; lean_object* v_toSeqLeft_4928_; lean_object* v_toSeqRight_4929_; lean_object* v___x_4931_; uint8_t v_isShared_4932_; uint8_t v_isSharedCheck_4981_; 
v_toFunctor_4926_ = lean_ctor_get(v_toApplicative_4922_, 0);
v_toSeq_4927_ = lean_ctor_get(v_toApplicative_4922_, 2);
v_toSeqLeft_4928_ = lean_ctor_get(v_toApplicative_4922_, 3);
v_toSeqRight_4929_ = lean_ctor_get(v_toApplicative_4922_, 4);
v_isSharedCheck_4981_ = !lean_is_exclusive(v_toApplicative_4922_);
if (v_isSharedCheck_4981_ == 0)
{
lean_object* v_unused_4982_; 
v_unused_4982_ = lean_ctor_get(v_toApplicative_4922_, 1);
lean_dec(v_unused_4982_);
v___x_4931_ = v_toApplicative_4922_;
v_isShared_4932_ = v_isSharedCheck_4981_;
goto v_resetjp_4930_;
}
else
{
lean_inc(v_toSeqRight_4929_);
lean_inc(v_toSeqLeft_4928_);
lean_inc(v_toSeq_4927_);
lean_inc(v_toFunctor_4926_);
lean_dec(v_toApplicative_4922_);
v___x_4931_ = lean_box(0);
v_isShared_4932_ = v_isSharedCheck_4981_;
goto v_resetjp_4930_;
}
v_resetjp_4930_:
{
lean_object* v___f_4933_; lean_object* v___f_4934_; lean_object* v___f_4935_; lean_object* v___f_4936_; lean_object* v___x_4937_; lean_object* v___f_4938_; lean_object* v___f_4939_; lean_object* v___f_4940_; lean_object* v___x_4942_; 
v___f_4933_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__1));
v___f_4934_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__2));
lean_inc_ref(v_toFunctor_4926_);
v___f_4935_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4935_, 0, v_toFunctor_4926_);
v___f_4936_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4936_, 0, v_toFunctor_4926_);
v___x_4937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4937_, 0, v___f_4935_);
lean_ctor_set(v___x_4937_, 1, v___f_4936_);
v___f_4938_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4938_, 0, v_toSeqRight_4929_);
v___f_4939_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4939_, 0, v_toSeqLeft_4928_);
v___f_4940_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4940_, 0, v_toSeq_4927_);
if (v_isShared_4932_ == 0)
{
lean_ctor_set(v___x_4931_, 4, v___f_4938_);
lean_ctor_set(v___x_4931_, 3, v___f_4939_);
lean_ctor_set(v___x_4931_, 2, v___f_4940_);
lean_ctor_set(v___x_4931_, 1, v___f_4933_);
lean_ctor_set(v___x_4931_, 0, v___x_4937_);
v___x_4942_ = v___x_4931_;
goto v_reusejp_4941_;
}
else
{
lean_object* v_reuseFailAlloc_4980_; 
v_reuseFailAlloc_4980_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4980_, 0, v___x_4937_);
lean_ctor_set(v_reuseFailAlloc_4980_, 1, v___f_4933_);
lean_ctor_set(v_reuseFailAlloc_4980_, 2, v___f_4940_);
lean_ctor_set(v_reuseFailAlloc_4980_, 3, v___f_4939_);
lean_ctor_set(v_reuseFailAlloc_4980_, 4, v___f_4938_);
v___x_4942_ = v_reuseFailAlloc_4980_;
goto v_reusejp_4941_;
}
v_reusejp_4941_:
{
lean_object* v___x_4944_; 
if (v_isShared_4925_ == 0)
{
lean_ctor_set(v___x_4924_, 1, v___f_4934_);
lean_ctor_set(v___x_4924_, 0, v___x_4942_);
v___x_4944_ = v___x_4924_;
goto v_reusejp_4943_;
}
else
{
lean_object* v_reuseFailAlloc_4979_; 
v_reuseFailAlloc_4979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4979_, 0, v___x_4942_);
lean_ctor_set(v_reuseFailAlloc_4979_, 1, v___f_4934_);
v___x_4944_ = v_reuseFailAlloc_4979_;
goto v_reusejp_4943_;
}
v_reusejp_4943_:
{
lean_object* v___x_4945_; lean_object* v_toApplicative_4946_; lean_object* v___x_4948_; uint8_t v_isShared_4949_; uint8_t v_isSharedCheck_4977_; 
v___x_4945_ = l_ReaderT_instMonad___redArg(v___x_4944_);
v_toApplicative_4946_ = lean_ctor_get(v___x_4945_, 0);
v_isSharedCheck_4977_ = !lean_is_exclusive(v___x_4945_);
if (v_isSharedCheck_4977_ == 0)
{
lean_object* v_unused_4978_; 
v_unused_4978_ = lean_ctor_get(v___x_4945_, 1);
lean_dec(v_unused_4978_);
v___x_4948_ = v___x_4945_;
v_isShared_4949_ = v_isSharedCheck_4977_;
goto v_resetjp_4947_;
}
else
{
lean_inc(v_toApplicative_4946_);
lean_dec(v___x_4945_);
v___x_4948_ = lean_box(0);
v_isShared_4949_ = v_isSharedCheck_4977_;
goto v_resetjp_4947_;
}
v_resetjp_4947_:
{
lean_object* v_toFunctor_4950_; lean_object* v_toSeq_4951_; lean_object* v_toSeqLeft_4952_; lean_object* v_toSeqRight_4953_; lean_object* v___x_4955_; uint8_t v_isShared_4956_; uint8_t v_isSharedCheck_4975_; 
v_toFunctor_4950_ = lean_ctor_get(v_toApplicative_4946_, 0);
v_toSeq_4951_ = lean_ctor_get(v_toApplicative_4946_, 2);
v_toSeqLeft_4952_ = lean_ctor_get(v_toApplicative_4946_, 3);
v_toSeqRight_4953_ = lean_ctor_get(v_toApplicative_4946_, 4);
v_isSharedCheck_4975_ = !lean_is_exclusive(v_toApplicative_4946_);
if (v_isSharedCheck_4975_ == 0)
{
lean_object* v_unused_4976_; 
v_unused_4976_ = lean_ctor_get(v_toApplicative_4946_, 1);
lean_dec(v_unused_4976_);
v___x_4955_ = v_toApplicative_4946_;
v_isShared_4956_ = v_isSharedCheck_4975_;
goto v_resetjp_4954_;
}
else
{
lean_inc(v_toSeqRight_4953_);
lean_inc(v_toSeqLeft_4952_);
lean_inc(v_toSeq_4951_);
lean_inc(v_toFunctor_4950_);
lean_dec(v_toApplicative_4946_);
v___x_4955_ = lean_box(0);
v_isShared_4956_ = v_isSharedCheck_4975_;
goto v_resetjp_4954_;
}
v_resetjp_4954_:
{
lean_object* v___f_4957_; lean_object* v___f_4958_; lean_object* v___f_4959_; lean_object* v___f_4960_; lean_object* v___x_4961_; lean_object* v___f_4962_; lean_object* v___f_4963_; lean_object* v___f_4964_; lean_object* v___x_4966_; 
v___f_4957_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3));
v___f_4958_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4));
lean_inc_ref(v_toFunctor_4950_);
v___f_4959_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4959_, 0, v_toFunctor_4950_);
v___f_4960_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4960_, 0, v_toFunctor_4950_);
v___x_4961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4961_, 0, v___f_4959_);
lean_ctor_set(v___x_4961_, 1, v___f_4960_);
v___f_4962_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4962_, 0, v_toSeqRight_4953_);
v___f_4963_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4963_, 0, v_toSeqLeft_4952_);
v___f_4964_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4964_, 0, v_toSeq_4951_);
if (v_isShared_4956_ == 0)
{
lean_ctor_set(v___x_4955_, 4, v___f_4962_);
lean_ctor_set(v___x_4955_, 3, v___f_4963_);
lean_ctor_set(v___x_4955_, 2, v___f_4964_);
lean_ctor_set(v___x_4955_, 1, v___f_4957_);
lean_ctor_set(v___x_4955_, 0, v___x_4961_);
v___x_4966_ = v___x_4955_;
goto v_reusejp_4965_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v___x_4961_);
lean_ctor_set(v_reuseFailAlloc_4974_, 1, v___f_4957_);
lean_ctor_set(v_reuseFailAlloc_4974_, 2, v___f_4964_);
lean_ctor_set(v_reuseFailAlloc_4974_, 3, v___f_4963_);
lean_ctor_set(v_reuseFailAlloc_4974_, 4, v___f_4962_);
v___x_4966_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4965_;
}
v_reusejp_4965_:
{
lean_object* v___x_4968_; 
if (v_isShared_4949_ == 0)
{
lean_ctor_set(v___x_4948_, 1, v___f_4958_);
lean_ctor_set(v___x_4948_, 0, v___x_4966_);
v___x_4968_ = v___x_4948_;
goto v_reusejp_4967_;
}
else
{
lean_object* v_reuseFailAlloc_4973_; 
v_reuseFailAlloc_4973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4973_, 0, v___x_4966_);
lean_ctor_set(v_reuseFailAlloc_4973_, 1, v___f_4958_);
v___x_4968_ = v_reuseFailAlloc_4973_;
goto v_reusejp_4967_;
}
v_reusejp_4967_:
{
lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_27692__overap_4971_; lean_object* v___x_4972_; 
v___x_4969_ = l_Lean_instInhabitedExpr;
v___x_4970_ = l_instInhabitedOfMonad___redArg(v___x_4968_, v___x_4969_);
v___x_27692__overap_4971_ = lean_panic_fn(v___x_4970_, v_msg_4914_);
v___x_4972_ = lean_apply_5(v___x_27692__overap_4971_, v___y_4915_, v___y_4916_, v___y_4917_, v___y_4918_, lean_box(0));
return v___x_4972_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___boxed(lean_object* v_msg_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_){
_start:
{
lean_object* v_res_4991_; 
v_res_4991_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(v_msg_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_);
return v_res_4991_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(lean_object* v_args_4992_, lean_object* v_ys3_4993_, lean_object* v_onAlt_4994_, lean_object* v_a_4995_, lean_object* v_ys_4996_, lean_object* v_ys2_4997_, uint8_t v___x_4998_, uint8_t v_useSplitter_4999_, lean_object* v___x_5000_, lean_object* v_ys4_5001_, lean_object* v_altType_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_){
_start:
{
lean_object* v___x_5008_; lean_object* v___y_5010_; lean_object* v___x_5019_; 
v___x_5008_ = l_Array_append___redArg(v_args_4992_, v_ys3_4993_);
lean_inc(v___y_5006_);
lean_inc_ref(v___y_5005_);
lean_inc(v___y_5004_);
lean_inc_ref(v___y_5003_);
v___x_5019_ = l_Lean_Meta_instantiateLambda(v___x_5000_, v___x_5008_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5019_) == 0)
{
v___y_5010_ = v___x_5019_;
goto v___jp_5009_;
}
else
{
lean_object* v_a_5020_; uint8_t v___y_5022_; uint8_t v___x_5025_; 
v_a_5020_ = lean_ctor_get(v___x_5019_, 0);
lean_inc(v_a_5020_);
v___x_5025_ = l_Lean_Exception_isInterrupt(v_a_5020_);
if (v___x_5025_ == 0)
{
uint8_t v___x_5026_; 
v___x_5026_ = l_Lean_Exception_isRuntime(v_a_5020_);
v___y_5022_ = v___x_5026_;
goto v___jp_5021_;
}
else
{
lean_dec(v_a_5020_);
v___y_5022_ = v___x_5025_;
goto v___jp_5021_;
}
v___jp_5021_:
{
if (v___y_5022_ == 0)
{
lean_object* v___x_5023_; lean_object* v___x_5024_; 
lean_dec_ref(v___x_5019_);
v___x_5023_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2);
v___x_5024_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_5023_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
v___y_5010_ = v___x_5024_;
goto v___jp_5009_;
}
else
{
v___y_5010_ = v___x_5019_;
goto v___jp_5009_;
}
}
}
v___jp_5009_:
{
if (lean_obj_tag(v___y_5010_) == 0)
{
lean_object* v_a_5011_; lean_object* v___x_5012_; 
v_a_5011_ = lean_ctor_get(v___y_5010_, 0);
lean_inc(v_a_5011_);
lean_dec_ref(v___y_5010_);
lean_inc(v___y_5006_);
lean_inc_ref(v___y_5005_);
lean_inc(v___y_5004_);
lean_inc_ref(v___y_5003_);
v___x_5012_ = lean_apply_9(v_onAlt_4994_, v_a_4995_, v_altType_5002_, v___x_5008_, v_a_5011_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_, lean_box(0));
if (lean_obj_tag(v___x_5012_) == 0)
{
lean_object* v_a_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; uint8_t v___x_5017_; lean_object* v___x_5018_; 
v_a_5013_ = lean_ctor_get(v___x_5012_, 0);
lean_inc(v_a_5013_);
lean_dec_ref(v___x_5012_);
v___x_5014_ = l_Array_append___redArg(v_ys_4996_, v_ys2_4997_);
v___x_5015_ = l_Array_append___redArg(v___x_5014_, v_ys3_4993_);
v___x_5016_ = l_Array_append___redArg(v___x_5015_, v_ys4_5001_);
v___x_5017_ = 1;
v___x_5018_ = l_Lean_Meta_mkLambdaFVars(v___x_5016_, v_a_5013_, v___x_4998_, v_useSplitter_4999_, v___x_4998_, v_useSplitter_4999_, v___x_5017_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
lean_dec(v___y_5006_);
lean_dec_ref(v___y_5005_);
lean_dec(v___y_5004_);
lean_dec_ref(v___y_5003_);
lean_dec_ref(v___x_5016_);
return v___x_5018_;
}
else
{
lean_dec(v___y_5006_);
lean_dec_ref(v___y_5005_);
lean_dec(v___y_5004_);
lean_dec_ref(v___y_5003_);
lean_dec_ref(v_ys_4996_);
return v___x_5012_;
}
}
else
{
lean_dec_ref(v___x_5008_);
lean_dec(v___y_5006_);
lean_dec_ref(v___y_5005_);
lean_dec(v___y_5004_);
lean_dec_ref(v___y_5003_);
lean_dec_ref(v_altType_5002_);
lean_dec_ref(v_ys_4996_);
lean_dec(v_a_4995_);
lean_dec_ref(v_onAlt_4994_);
return v___y_5010_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed(lean_object* v_args_5027_, lean_object* v_ys3_5028_, lean_object* v_onAlt_5029_, lean_object* v_a_5030_, lean_object* v_ys_5031_, lean_object* v_ys2_5032_, lean_object* v___x_5033_, lean_object* v_useSplitter_5034_, lean_object* v___x_5035_, lean_object* v_ys4_5036_, lean_object* v_altType_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_){
_start:
{
uint8_t v___x_33359__boxed_5043_; uint8_t v_useSplitter_boxed_5044_; lean_object* v_res_5045_; 
v___x_33359__boxed_5043_ = lean_unbox(v___x_5033_);
v_useSplitter_boxed_5044_ = lean_unbox(v_useSplitter_5034_);
v_res_5045_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(v_args_5027_, v_ys3_5028_, v_onAlt_5029_, v_a_5030_, v_ys_5031_, v_ys2_5032_, v___x_33359__boxed_5043_, v_useSplitter_boxed_5044_, v___x_5035_, v_ys4_5036_, v_altType_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_);
lean_dec_ref(v_ys4_5036_);
lean_dec_ref(v_ys2_5032_);
lean_dec_ref(v_ys3_5028_);
return v_res_5045_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(lean_object* v_args_5046_, lean_object* v_onAlt_5047_, lean_object* v_a_5048_, lean_object* v_ys_5049_, lean_object* v_ys2_5050_, uint8_t v___x_5051_, uint8_t v_useSplitter_5052_, lean_object* v___x_5053_, lean_object* v_extraEqualities_5054_, lean_object* v_ys3_5055_, lean_object* v_altType_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_){
_start:
{
lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___f_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; 
v___x_5062_ = lean_box(v___x_5051_);
v___x_5063_ = lean_box(v_useSplitter_5052_);
v___f_5064_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed), 16, 9);
lean_closure_set(v___f_5064_, 0, v_args_5046_);
lean_closure_set(v___f_5064_, 1, v_ys3_5055_);
lean_closure_set(v___f_5064_, 2, v_onAlt_5047_);
lean_closure_set(v___f_5064_, 3, v_a_5048_);
lean_closure_set(v___f_5064_, 4, v_ys_5049_);
lean_closure_set(v___f_5064_, 5, v_ys2_5050_);
lean_closure_set(v___f_5064_, 6, v___x_5062_);
lean_closure_set(v___f_5064_, 7, v___x_5063_);
lean_closure_set(v___f_5064_, 8, v___x_5053_);
v___x_5065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5065_, 0, v_extraEqualities_5054_);
v___x_5066_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_5056_, v___x_5065_, v___f_5064_, v___x_5051_, v___x_5051_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_);
return v___x_5066_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed(lean_object* v_args_5067_, lean_object* v_onAlt_5068_, lean_object* v_a_5069_, lean_object* v_ys_5070_, lean_object* v_ys2_5071_, lean_object* v___x_5072_, lean_object* v_useSplitter_5073_, lean_object* v___x_5074_, lean_object* v_extraEqualities_5075_, lean_object* v_ys3_5076_, lean_object* v_altType_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_){
_start:
{
uint8_t v___x_33422__boxed_5083_; uint8_t v_useSplitter_boxed_5084_; lean_object* v_res_5085_; 
v___x_33422__boxed_5083_ = lean_unbox(v___x_5072_);
v_useSplitter_boxed_5084_ = lean_unbox(v_useSplitter_5073_);
v_res_5085_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(v_args_5067_, v_onAlt_5068_, v_a_5069_, v_ys_5070_, v_ys2_5071_, v___x_33422__boxed_5083_, v_useSplitter_boxed_5084_, v___x_5074_, v_extraEqualities_5075_, v_ys3_5076_, v_altType_5077_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_);
return v_res_5085_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(lean_object* v_args_5086_, lean_object* v_onAlt_5087_, lean_object* v_a_5088_, lean_object* v_ys_5089_, uint8_t v___x_5090_, uint8_t v_useSplitter_5091_, lean_object* v___x_5092_, lean_object* v_extraEqualities_5093_, lean_object* v_numDiscrEqs_5094_, lean_object* v_ys2_5095_, lean_object* v_altType_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_){
_start:
{
lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___f_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; 
v___x_5102_ = lean_box(v___x_5090_);
v___x_5103_ = lean_box(v_useSplitter_5091_);
v___f_5104_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_5104_, 0, v_args_5086_);
lean_closure_set(v___f_5104_, 1, v_onAlt_5087_);
lean_closure_set(v___f_5104_, 2, v_a_5088_);
lean_closure_set(v___f_5104_, 3, v_ys_5089_);
lean_closure_set(v___f_5104_, 4, v_ys2_5095_);
lean_closure_set(v___f_5104_, 5, v___x_5102_);
lean_closure_set(v___f_5104_, 6, v___x_5103_);
lean_closure_set(v___f_5104_, 7, v___x_5092_);
lean_closure_set(v___f_5104_, 8, v_extraEqualities_5093_);
v___x_5105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5105_, 0, v_numDiscrEqs_5094_);
v___x_5106_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_5096_, v___x_5105_, v___f_5104_, v___x_5090_, v___x_5090_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_);
return v___x_5106_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed(lean_object* v_args_5107_, lean_object* v_onAlt_5108_, lean_object* v_a_5109_, lean_object* v_ys_5110_, lean_object* v___x_5111_, lean_object* v_useSplitter_5112_, lean_object* v___x_5113_, lean_object* v_extraEqualities_5114_, lean_object* v_numDiscrEqs_5115_, lean_object* v_ys2_5116_, lean_object* v_altType_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_){
_start:
{
uint8_t v___x_33453__boxed_5123_; uint8_t v_useSplitter_boxed_5124_; lean_object* v_res_5125_; 
v___x_33453__boxed_5123_ = lean_unbox(v___x_5111_);
v_useSplitter_boxed_5124_ = lean_unbox(v_useSplitter_5112_);
v_res_5125_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(v_args_5107_, v_onAlt_5108_, v_a_5109_, v_ys_5110_, v___x_33453__boxed_5123_, v_useSplitter_boxed_5124_, v___x_5113_, v_extraEqualities_5114_, v_numDiscrEqs_5115_, v_ys2_5116_, v_altType_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
return v_res_5125_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(lean_object* v___x_5126_, lean_object* v___x_5127_, lean_object* v_onAlt_5128_, lean_object* v_a_5129_, uint8_t v___x_5130_, uint8_t v_useSplitter_5131_, lean_object* v___x_5132_, lean_object* v_extraEqualities_5133_, lean_object* v_numDiscrEqs_5134_, uint8_t v_hasUnitThunk_5135_, lean_object* v___x_5136_, lean_object* v_ys_5137_, lean_object* v_args_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_){
_start:
{
lean_object* v_numFields_5144_; lean_object* v_numOverlaps_5145_; uint8_t v_hasUnitThunk_5146_; lean_object* v___x_5147_; uint8_t v___x_5148_; 
v_numFields_5144_ = lean_ctor_get(v___x_5126_, 0);
v_numOverlaps_5145_ = lean_ctor_get(v___x_5126_, 1);
v_hasUnitThunk_5146_ = lean_ctor_get_uint8(v___x_5126_, sizeof(void*)*2);
v___x_5147_ = lean_array_get_size(v_ys_5137_);
v___x_5148_ = lean_nat_dec_eq(v___x_5147_, v_numFields_5144_);
if (v___x_5148_ == 0)
{
lean_object* v___x_5149_; lean_object* v___x_5150_; 
lean_dec_ref(v_args_5138_);
lean_dec_ref(v_ys_5137_);
lean_dec(v_numDiscrEqs_5134_);
lean_dec(v_extraEqualities_5133_);
lean_dec_ref(v___x_5132_);
lean_dec(v_a_5129_);
lean_dec_ref(v_onAlt_5128_);
lean_dec_ref(v___x_5127_);
v___x_5149_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3);
v___x_5150_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(v___x_5149_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_);
return v___x_5150_;
}
else
{
lean_object* v___x_5151_; 
lean_inc(v___y_5142_);
lean_inc_ref(v___y_5141_);
lean_inc(v___y_5140_);
lean_inc_ref(v___y_5139_);
v___x_5151_ = l_Lean_Meta_instantiateForall(v___x_5127_, v_ys_5137_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_);
if (lean_obj_tag(v___x_5151_) == 0)
{
lean_object* v_a_5152_; lean_object* v___x_5154_; uint8_t v_isShared_5155_; uint8_t v_isSharedCheck_5181_; 
v_a_5152_ = lean_ctor_get(v___x_5151_, 0);
v_isSharedCheck_5181_ = !lean_is_exclusive(v___x_5151_);
if (v_isSharedCheck_5181_ == 0)
{
v___x_5154_ = v___x_5151_;
v_isShared_5155_ = v_isSharedCheck_5181_;
goto v_resetjp_5153_;
}
else
{
lean_inc(v_a_5152_);
lean_dec(v___x_5151_);
v___x_5154_ = lean_box(0);
v_isShared_5155_ = v_isSharedCheck_5181_;
goto v_resetjp_5153_;
}
v_resetjp_5153_:
{
lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___f_5158_; lean_object* v_altType_5160_; lean_object* v___y_5161_; lean_object* v___y_5162_; lean_object* v___y_5163_; lean_object* v___y_5164_; 
v___x_5156_ = lean_box(v___x_5130_);
v___x_5157_ = lean_box(v_useSplitter_5131_);
v___f_5158_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed), 16, 9);
lean_closure_set(v___f_5158_, 0, v_args_5138_);
lean_closure_set(v___f_5158_, 1, v_onAlt_5128_);
lean_closure_set(v___f_5158_, 2, v_a_5129_);
lean_closure_set(v___f_5158_, 3, v_ys_5137_);
lean_closure_set(v___f_5158_, 4, v___x_5156_);
lean_closure_set(v___f_5158_, 5, v___x_5157_);
lean_closure_set(v___f_5158_, 6, v___x_5132_);
lean_closure_set(v___f_5158_, 7, v_extraEqualities_5133_);
lean_closure_set(v___f_5158_, 8, v_numDiscrEqs_5134_);
if (v_hasUnitThunk_5135_ == 0)
{
v_altType_5160_ = v_a_5152_;
v___y_5161_ = v___y_5139_;
v___y_5162_ = v___y_5140_;
v___y_5163_ = v___y_5141_;
v___y_5164_ = v___y_5142_;
goto v___jp_5159_;
}
else
{
lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; 
v___x_5176_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2);
v___x_5177_ = lean_mk_empty_array_with_capacity(v___x_5136_);
v___x_5178_ = lean_array_push(v___x_5177_, v___x_5176_);
lean_inc(v___y_5142_);
lean_inc_ref(v___y_5141_);
lean_inc(v___y_5140_);
lean_inc_ref(v___y_5139_);
v___x_5179_ = l_Lean_Meta_instantiateForall(v_a_5152_, v___x_5178_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_);
lean_dec_ref(v___x_5178_);
if (lean_obj_tag(v___x_5179_) == 0)
{
lean_object* v_a_5180_; 
v_a_5180_ = lean_ctor_get(v___x_5179_, 0);
lean_inc(v_a_5180_);
lean_dec_ref(v___x_5179_);
v_altType_5160_ = v_a_5180_;
v___y_5161_ = v___y_5139_;
v___y_5162_ = v___y_5140_;
v___y_5163_ = v___y_5141_;
v___y_5164_ = v___y_5142_;
goto v___jp_5159_;
}
else
{
lean_dec_ref(v___f_5158_);
lean_del_object(v___x_5154_);
lean_dec(v___y_5142_);
lean_dec_ref(v___y_5141_);
lean_dec(v___y_5140_);
lean_dec_ref(v___y_5139_);
return v___x_5179_;
}
}
v___jp_5159_:
{
lean_object* v___x_5166_; 
lean_inc(v_numOverlaps_5145_);
if (v_isShared_5155_ == 0)
{
lean_ctor_set_tag(v___x_5154_, 1);
lean_ctor_set(v___x_5154_, 0, v_numOverlaps_5145_);
v___x_5166_ = v___x_5154_;
goto v_reusejp_5165_;
}
else
{
lean_object* v_reuseFailAlloc_5175_; 
v_reuseFailAlloc_5175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5175_, 0, v_numOverlaps_5145_);
v___x_5166_ = v_reuseFailAlloc_5175_;
goto v_reusejp_5165_;
}
v_reusejp_5165_:
{
lean_object* v___x_5167_; 
lean_inc(v___y_5164_);
lean_inc_ref(v___y_5163_);
lean_inc(v___y_5162_);
lean_inc_ref(v___y_5161_);
v___x_5167_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_5160_, v___x_5166_, v___f_5158_, v___x_5130_, v___x_5130_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_);
if (lean_obj_tag(v___x_5167_) == 0)
{
if (v_hasUnitThunk_5146_ == 0)
{
lean_dec(v___y_5164_);
lean_dec_ref(v___y_5163_);
lean_dec(v___y_5162_);
lean_dec_ref(v___y_5161_);
return v___x_5167_;
}
else
{
lean_object* v_a_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; lean_object* v___x_5174_; 
v_a_5168_ = lean_ctor_get(v___x_5167_, 0);
lean_inc(v_a_5168_);
lean_dec_ref(v___x_5167_);
v___x_5169_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__2));
v___x_5170_ = lean_unsigned_to_nat(2u);
v___x_5171_ = lean_mk_empty_array_with_capacity(v___x_5170_);
lean_dec_ref(v___x_5171_);
v___x_5172_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__6);
v___x_5173_ = lean_array_push(v___x_5172_, v_a_5168_);
v___x_5174_ = l_Lean_Meta_mkAppM(v___x_5169_, v___x_5173_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_);
return v___x_5174_;
}
}
else
{
lean_dec(v___y_5164_);
lean_dec_ref(v___y_5163_);
lean_dec(v___y_5162_);
lean_dec_ref(v___y_5161_);
return v___x_5167_;
}
}
}
}
}
else
{
lean_dec(v___y_5142_);
lean_dec_ref(v___y_5141_);
lean_dec(v___y_5140_);
lean_dec_ref(v___y_5139_);
lean_dec_ref(v_args_5138_);
lean_dec_ref(v_ys_5137_);
lean_dec(v_numDiscrEqs_5134_);
lean_dec(v_extraEqualities_5133_);
lean_dec_ref(v___x_5132_);
lean_dec(v_a_5129_);
lean_dec_ref(v_onAlt_5128_);
return v___x_5151_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_5182_ = _args[0];
lean_object* v___x_5183_ = _args[1];
lean_object* v_onAlt_5184_ = _args[2];
lean_object* v_a_5185_ = _args[3];
lean_object* v___x_5186_ = _args[4];
lean_object* v_useSplitter_5187_ = _args[5];
lean_object* v___x_5188_ = _args[6];
lean_object* v_extraEqualities_5189_ = _args[7];
lean_object* v_numDiscrEqs_5190_ = _args[8];
lean_object* v_hasUnitThunk_5191_ = _args[9];
lean_object* v___x_5192_ = _args[10];
lean_object* v_ys_5193_ = _args[11];
lean_object* v_args_5194_ = _args[12];
lean_object* v___y_5195_ = _args[13];
lean_object* v___y_5196_ = _args[14];
lean_object* v___y_5197_ = _args[15];
lean_object* v___y_5198_ = _args[16];
lean_object* v___y_5199_ = _args[17];
_start:
{
uint8_t v___x_33518__boxed_5200_; uint8_t v_useSplitter_boxed_5201_; uint8_t v_hasUnitThunk_boxed_5202_; lean_object* v_res_5203_; 
v___x_33518__boxed_5200_ = lean_unbox(v___x_5186_);
v_useSplitter_boxed_5201_ = lean_unbox(v_useSplitter_5187_);
v_hasUnitThunk_boxed_5202_ = lean_unbox(v_hasUnitThunk_5191_);
v_res_5203_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(v___x_5182_, v___x_5183_, v_onAlt_5184_, v_a_5185_, v___x_33518__boxed_5200_, v_useSplitter_boxed_5201_, v___x_5188_, v_extraEqualities_5189_, v_numDiscrEqs_5190_, v_hasUnitThunk_boxed_5202_, v___x_5192_, v_ys_5193_, v_args_5194_, v___y_5195_, v___y_5196_, v___y_5197_, v___y_5198_);
lean_dec(v___x_5192_);
lean_dec_ref(v___x_5182_);
return v_res_5203_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(lean_object* v___x_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_){
_start:
{
lean_object* v___x_5210_; 
v___x_5210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5210_, 0, v___x_5204_);
return v___x_5210_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed(lean_object* v___x_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_){
_start:
{
lean_object* v_res_5217_; 
v_res_5217_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(v___x_5211_, v___y_5212_, v___y_5213_, v___y_5214_, v___y_5215_);
lean_dec(v___y_5215_);
lean_dec_ref(v___y_5214_);
lean_dec(v___y_5213_);
lean_dec_ref(v___y_5212_);
return v_res_5217_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(lean_object* v_msg_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_){
_start:
{
lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v_toApplicative_5226_; lean_object* v___x_5228_; uint8_t v_isShared_5229_; uint8_t v_isSharedCheck_5287_; 
v___x_5224_ = lean_obj_once(&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0, &l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0_once, _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0);
v___x_5225_ = l_ReaderT_instMonad___redArg(v___x_5224_);
v_toApplicative_5226_ = lean_ctor_get(v___x_5225_, 0);
v_isSharedCheck_5287_ = !lean_is_exclusive(v___x_5225_);
if (v_isSharedCheck_5287_ == 0)
{
lean_object* v_unused_5288_; 
v_unused_5288_ = lean_ctor_get(v___x_5225_, 1);
lean_dec(v_unused_5288_);
v___x_5228_ = v___x_5225_;
v_isShared_5229_ = v_isSharedCheck_5287_;
goto v_resetjp_5227_;
}
else
{
lean_inc(v_toApplicative_5226_);
lean_dec(v___x_5225_);
v___x_5228_ = lean_box(0);
v_isShared_5229_ = v_isSharedCheck_5287_;
goto v_resetjp_5227_;
}
v_resetjp_5227_:
{
lean_object* v_toFunctor_5230_; lean_object* v_toSeq_5231_; lean_object* v_toSeqLeft_5232_; lean_object* v_toSeqRight_5233_; lean_object* v___x_5235_; uint8_t v_isShared_5236_; uint8_t v_isSharedCheck_5285_; 
v_toFunctor_5230_ = lean_ctor_get(v_toApplicative_5226_, 0);
v_toSeq_5231_ = lean_ctor_get(v_toApplicative_5226_, 2);
v_toSeqLeft_5232_ = lean_ctor_get(v_toApplicative_5226_, 3);
v_toSeqRight_5233_ = lean_ctor_get(v_toApplicative_5226_, 4);
v_isSharedCheck_5285_ = !lean_is_exclusive(v_toApplicative_5226_);
if (v_isSharedCheck_5285_ == 0)
{
lean_object* v_unused_5286_; 
v_unused_5286_ = lean_ctor_get(v_toApplicative_5226_, 1);
lean_dec(v_unused_5286_);
v___x_5235_ = v_toApplicative_5226_;
v_isShared_5236_ = v_isSharedCheck_5285_;
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
v_isShared_5236_ = v_isSharedCheck_5285_;
goto v_resetjp_5234_;
}
v_resetjp_5234_:
{
lean_object* v___f_5237_; lean_object* v___f_5238_; lean_object* v___f_5239_; lean_object* v___f_5240_; lean_object* v___x_5241_; lean_object* v___f_5242_; lean_object* v___f_5243_; lean_object* v___f_5244_; lean_object* v___x_5246_; 
v___f_5237_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__1));
v___f_5238_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__2));
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
lean_object* v_reuseFailAlloc_5284_; 
v_reuseFailAlloc_5284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5284_, 0, v___x_5241_);
lean_ctor_set(v_reuseFailAlloc_5284_, 1, v___f_5237_);
lean_ctor_set(v_reuseFailAlloc_5284_, 2, v___f_5244_);
lean_ctor_set(v_reuseFailAlloc_5284_, 3, v___f_5243_);
lean_ctor_set(v_reuseFailAlloc_5284_, 4, v___f_5242_);
v___x_5246_ = v_reuseFailAlloc_5284_;
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
lean_object* v_reuseFailAlloc_5283_; 
v_reuseFailAlloc_5283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5283_, 0, v___x_5246_);
lean_ctor_set(v_reuseFailAlloc_5283_, 1, v___f_5238_);
v___x_5248_ = v_reuseFailAlloc_5283_;
goto v_reusejp_5247_;
}
v_reusejp_5247_:
{
lean_object* v___x_5249_; lean_object* v_toApplicative_5250_; lean_object* v___x_5252_; uint8_t v_isShared_5253_; uint8_t v_isSharedCheck_5281_; 
v___x_5249_ = l_ReaderT_instMonad___redArg(v___x_5248_);
v_toApplicative_5250_ = lean_ctor_get(v___x_5249_, 0);
v_isSharedCheck_5281_ = !lean_is_exclusive(v___x_5249_);
if (v_isSharedCheck_5281_ == 0)
{
lean_object* v_unused_5282_; 
v_unused_5282_ = lean_ctor_get(v___x_5249_, 1);
lean_dec(v_unused_5282_);
v___x_5252_ = v___x_5249_;
v_isShared_5253_ = v_isSharedCheck_5281_;
goto v_resetjp_5251_;
}
else
{
lean_inc(v_toApplicative_5250_);
lean_dec(v___x_5249_);
v___x_5252_ = lean_box(0);
v_isShared_5253_ = v_isSharedCheck_5281_;
goto v_resetjp_5251_;
}
v_resetjp_5251_:
{
lean_object* v_toFunctor_5254_; lean_object* v_toSeq_5255_; lean_object* v_toSeqLeft_5256_; lean_object* v_toSeqRight_5257_; lean_object* v___x_5259_; uint8_t v_isShared_5260_; uint8_t v_isSharedCheck_5279_; 
v_toFunctor_5254_ = lean_ctor_get(v_toApplicative_5250_, 0);
v_toSeq_5255_ = lean_ctor_get(v_toApplicative_5250_, 2);
v_toSeqLeft_5256_ = lean_ctor_get(v_toApplicative_5250_, 3);
v_toSeqRight_5257_ = lean_ctor_get(v_toApplicative_5250_, 4);
v_isSharedCheck_5279_ = !lean_is_exclusive(v_toApplicative_5250_);
if (v_isSharedCheck_5279_ == 0)
{
lean_object* v_unused_5280_; 
v_unused_5280_ = lean_ctor_get(v_toApplicative_5250_, 1);
lean_dec(v_unused_5280_);
v___x_5259_ = v_toApplicative_5250_;
v_isShared_5260_ = v_isSharedCheck_5279_;
goto v_resetjp_5258_;
}
else
{
lean_inc(v_toSeqRight_5257_);
lean_inc(v_toSeqLeft_5256_);
lean_inc(v_toSeq_5255_);
lean_inc(v_toFunctor_5254_);
lean_dec(v_toApplicative_5250_);
v___x_5259_ = lean_box(0);
v_isShared_5260_ = v_isSharedCheck_5279_;
goto v_resetjp_5258_;
}
v_resetjp_5258_:
{
lean_object* v___f_5261_; lean_object* v___f_5262_; lean_object* v___f_5263_; lean_object* v___f_5264_; lean_object* v___x_5265_; lean_object* v___f_5266_; lean_object* v___f_5267_; lean_object* v___f_5268_; lean_object* v___x_5270_; 
v___f_5261_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3));
v___f_5262_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4));
lean_inc_ref(v_toFunctor_5254_);
v___f_5263_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5263_, 0, v_toFunctor_5254_);
v___f_5264_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5264_, 0, v_toFunctor_5254_);
v___x_5265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5265_, 0, v___f_5263_);
lean_ctor_set(v___x_5265_, 1, v___f_5264_);
v___f_5266_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5266_, 0, v_toSeqRight_5257_);
v___f_5267_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5267_, 0, v_toSeqLeft_5256_);
v___f_5268_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5268_, 0, v_toSeq_5255_);
if (v_isShared_5260_ == 0)
{
lean_ctor_set(v___x_5259_, 4, v___f_5266_);
lean_ctor_set(v___x_5259_, 3, v___f_5267_);
lean_ctor_set(v___x_5259_, 2, v___f_5268_);
lean_ctor_set(v___x_5259_, 1, v___f_5261_);
lean_ctor_set(v___x_5259_, 0, v___x_5265_);
v___x_5270_ = v___x_5259_;
goto v_reusejp_5269_;
}
else
{
lean_object* v_reuseFailAlloc_5278_; 
v_reuseFailAlloc_5278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5278_, 0, v___x_5265_);
lean_ctor_set(v_reuseFailAlloc_5278_, 1, v___f_5261_);
lean_ctor_set(v_reuseFailAlloc_5278_, 2, v___f_5268_);
lean_ctor_set(v_reuseFailAlloc_5278_, 3, v___f_5267_);
lean_ctor_set(v_reuseFailAlloc_5278_, 4, v___f_5266_);
v___x_5270_ = v_reuseFailAlloc_5278_;
goto v_reusejp_5269_;
}
v_reusejp_5269_:
{
lean_object* v___x_5272_; 
if (v_isShared_5253_ == 0)
{
lean_ctor_set(v___x_5252_, 1, v___f_5262_);
lean_ctor_set(v___x_5252_, 0, v___x_5270_);
v___x_5272_ = v___x_5252_;
goto v_reusejp_5271_;
}
else
{
lean_object* v_reuseFailAlloc_5277_; 
v_reuseFailAlloc_5277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5277_, 0, v___x_5270_);
lean_ctor_set(v_reuseFailAlloc_5277_, 1, v___f_5262_);
v___x_5272_ = v_reuseFailAlloc_5277_;
goto v_reusejp_5271_;
}
v_reusejp_5271_:
{
lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_27680__overap_5275_; lean_object* v___x_5276_; 
v___x_5273_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7);
v___x_5274_ = l_instInhabitedOfMonad___redArg(v___x_5272_, v___x_5273_);
v___x_27680__overap_5275_ = lean_panic_fn(v___x_5274_, v_msg_5218_);
v___x_5276_ = lean_apply_5(v___x_27680__overap_5275_, v___y_5219_, v___y_5220_, v___y_5221_, v___y_5222_, lean_box(0));
return v___x_5276_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed(lean_object* v_msg_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_){
_start:
{
lean_object* v_res_5295_; 
v_res_5295_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(v_msg_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_);
return v_res_5295_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(lean_object* v_upperBound_5296_, lean_object* v_onAlt_5297_, uint8_t v_useSplitter_5298_, lean_object* v_extraEqualities_5299_, lean_object* v_numDiscrEqs_5300_, lean_object* v_a_5301_, lean_object* v_b_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_){
_start:
{
lean_object* v___y_5309_; uint8_t v___x_5332_; 
v___x_5332_ = lean_nat_dec_lt(v_a_5301_, v_upperBound_5296_);
if (v___x_5332_ == 0)
{
lean_object* v___x_5333_; 
lean_dec(v___y_5306_);
lean_dec_ref(v___y_5305_);
lean_dec(v___y_5304_);
lean_dec_ref(v___y_5303_);
lean_dec(v_a_5301_);
lean_dec(v_numDiscrEqs_5300_);
lean_dec(v_extraEqualities_5299_);
lean_dec_ref(v_onAlt_5297_);
v___x_5333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5333_, 0, v_b_5302_);
return v___x_5333_;
}
else
{
lean_object* v_snd_5334_; lean_object* v_snd_5335_; lean_object* v_snd_5336_; lean_object* v_snd_5337_; lean_object* v_snd_5338_; lean_object* v_fst_5339_; lean_object* v___x_5341_; uint8_t v_isShared_5342_; uint8_t v_isSharedCheck_5545_; 
v_snd_5334_ = lean_ctor_get(v_b_5302_, 1);
lean_inc(v_snd_5334_);
v_snd_5335_ = lean_ctor_get(v_snd_5334_, 1);
lean_inc(v_snd_5335_);
v_snd_5336_ = lean_ctor_get(v_snd_5335_, 1);
lean_inc(v_snd_5336_);
v_snd_5337_ = lean_ctor_get(v_snd_5336_, 1);
lean_inc(v_snd_5337_);
v_snd_5338_ = lean_ctor_get(v_snd_5337_, 1);
lean_inc(v_snd_5338_);
v_fst_5339_ = lean_ctor_get(v_b_5302_, 0);
v_isSharedCheck_5545_ = !lean_is_exclusive(v_b_5302_);
if (v_isSharedCheck_5545_ == 0)
{
lean_object* v_unused_5546_; 
v_unused_5546_ = lean_ctor_get(v_b_5302_, 1);
lean_dec(v_unused_5546_);
v___x_5341_ = v_b_5302_;
v_isShared_5342_ = v_isSharedCheck_5545_;
goto v_resetjp_5340_;
}
else
{
lean_inc(v_fst_5339_);
lean_dec(v_b_5302_);
v___x_5341_ = lean_box(0);
v_isShared_5342_ = v_isSharedCheck_5545_;
goto v_resetjp_5340_;
}
v_resetjp_5340_:
{
lean_object* v_fst_5343_; lean_object* v___x_5345_; uint8_t v_isShared_5346_; uint8_t v_isSharedCheck_5543_; 
v_fst_5343_ = lean_ctor_get(v_snd_5334_, 0);
v_isSharedCheck_5543_ = !lean_is_exclusive(v_snd_5334_);
if (v_isSharedCheck_5543_ == 0)
{
lean_object* v_unused_5544_; 
v_unused_5544_ = lean_ctor_get(v_snd_5334_, 1);
lean_dec(v_unused_5544_);
v___x_5345_ = v_snd_5334_;
v_isShared_5346_ = v_isSharedCheck_5543_;
goto v_resetjp_5344_;
}
else
{
lean_inc(v_fst_5343_);
lean_dec(v_snd_5334_);
v___x_5345_ = lean_box(0);
v_isShared_5346_ = v_isSharedCheck_5543_;
goto v_resetjp_5344_;
}
v_resetjp_5344_:
{
lean_object* v_fst_5347_; lean_object* v___x_5349_; uint8_t v_isShared_5350_; uint8_t v_isSharedCheck_5541_; 
v_fst_5347_ = lean_ctor_get(v_snd_5335_, 0);
v_isSharedCheck_5541_ = !lean_is_exclusive(v_snd_5335_);
if (v_isSharedCheck_5541_ == 0)
{
lean_object* v_unused_5542_; 
v_unused_5542_ = lean_ctor_get(v_snd_5335_, 1);
lean_dec(v_unused_5542_);
v___x_5349_ = v_snd_5335_;
v_isShared_5350_ = v_isSharedCheck_5541_;
goto v_resetjp_5348_;
}
else
{
lean_inc(v_fst_5347_);
lean_dec(v_snd_5335_);
v___x_5349_ = lean_box(0);
v_isShared_5350_ = v_isSharedCheck_5541_;
goto v_resetjp_5348_;
}
v_resetjp_5348_:
{
lean_object* v_fst_5351_; lean_object* v___x_5353_; uint8_t v_isShared_5354_; uint8_t v_isSharedCheck_5539_; 
v_fst_5351_ = lean_ctor_get(v_snd_5336_, 0);
v_isSharedCheck_5539_ = !lean_is_exclusive(v_snd_5336_);
if (v_isSharedCheck_5539_ == 0)
{
lean_object* v_unused_5540_; 
v_unused_5540_ = lean_ctor_get(v_snd_5336_, 1);
lean_dec(v_unused_5540_);
v___x_5353_ = v_snd_5336_;
v_isShared_5354_ = v_isSharedCheck_5539_;
goto v_resetjp_5352_;
}
else
{
lean_inc(v_fst_5351_);
lean_dec(v_snd_5336_);
v___x_5353_ = lean_box(0);
v_isShared_5354_ = v_isSharedCheck_5539_;
goto v_resetjp_5352_;
}
v_resetjp_5352_:
{
lean_object* v_fst_5355_; lean_object* v___x_5357_; uint8_t v_isShared_5358_; uint8_t v_isSharedCheck_5537_; 
v_fst_5355_ = lean_ctor_get(v_snd_5337_, 0);
v_isSharedCheck_5537_ = !lean_is_exclusive(v_snd_5337_);
if (v_isSharedCheck_5537_ == 0)
{
lean_object* v_unused_5538_; 
v_unused_5538_ = lean_ctor_get(v_snd_5337_, 1);
lean_dec(v_unused_5538_);
v___x_5357_ = v_snd_5337_;
v_isShared_5358_ = v_isSharedCheck_5537_;
goto v_resetjp_5356_;
}
else
{
lean_inc(v_fst_5355_);
lean_dec(v_snd_5337_);
v___x_5357_ = lean_box(0);
v_isShared_5358_ = v_isSharedCheck_5537_;
goto v_resetjp_5356_;
}
v_resetjp_5356_:
{
lean_object* v_array_5359_; lean_object* v_start_5360_; lean_object* v_stop_5361_; uint8_t v___x_5362_; 
v_array_5359_ = lean_ctor_get(v_snd_5338_, 0);
v_start_5360_ = lean_ctor_get(v_snd_5338_, 1);
v_stop_5361_ = lean_ctor_get(v_snd_5338_, 2);
v___x_5362_ = lean_nat_dec_lt(v_start_5360_, v_stop_5361_);
if (v___x_5362_ == 0)
{
lean_object* v___x_5364_; 
if (v_isShared_5358_ == 0)
{
v___x_5364_ = v___x_5357_;
goto v_reusejp_5363_;
}
else
{
lean_object* v_reuseFailAlloc_5379_; 
v_reuseFailAlloc_5379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5379_, 0, v_fst_5355_);
lean_ctor_set(v_reuseFailAlloc_5379_, 1, v_snd_5338_);
v___x_5364_ = v_reuseFailAlloc_5379_;
goto v_reusejp_5363_;
}
v_reusejp_5363_:
{
lean_object* v___x_5366_; 
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 1, v___x_5364_);
v___x_5366_ = v___x_5353_;
goto v_reusejp_5365_;
}
else
{
lean_object* v_reuseFailAlloc_5378_; 
v_reuseFailAlloc_5378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5378_, 0, v_fst_5351_);
lean_ctor_set(v_reuseFailAlloc_5378_, 1, v___x_5364_);
v___x_5366_ = v_reuseFailAlloc_5378_;
goto v_reusejp_5365_;
}
v_reusejp_5365_:
{
lean_object* v___x_5368_; 
if (v_isShared_5350_ == 0)
{
lean_ctor_set(v___x_5349_, 1, v___x_5366_);
v___x_5368_ = v___x_5349_;
goto v_reusejp_5367_;
}
else
{
lean_object* v_reuseFailAlloc_5377_; 
v_reuseFailAlloc_5377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5377_, 0, v_fst_5347_);
lean_ctor_set(v_reuseFailAlloc_5377_, 1, v___x_5366_);
v___x_5368_ = v_reuseFailAlloc_5377_;
goto v_reusejp_5367_;
}
v_reusejp_5367_:
{
lean_object* v___x_5370_; 
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 1, v___x_5368_);
v___x_5370_ = v___x_5345_;
goto v_reusejp_5369_;
}
else
{
lean_object* v_reuseFailAlloc_5376_; 
v_reuseFailAlloc_5376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5376_, 0, v_fst_5343_);
lean_ctor_set(v_reuseFailAlloc_5376_, 1, v___x_5368_);
v___x_5370_ = v_reuseFailAlloc_5376_;
goto v_reusejp_5369_;
}
v_reusejp_5369_:
{
lean_object* v___x_5372_; 
if (v_isShared_5342_ == 0)
{
lean_ctor_set(v___x_5341_, 1, v___x_5370_);
v___x_5372_ = v___x_5341_;
goto v_reusejp_5371_;
}
else
{
lean_object* v_reuseFailAlloc_5375_; 
v_reuseFailAlloc_5375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5375_, 0, v_fst_5339_);
lean_ctor_set(v_reuseFailAlloc_5375_, 1, v___x_5370_);
v___x_5372_ = v_reuseFailAlloc_5375_;
goto v_reusejp_5371_;
}
v_reusejp_5371_:
{
lean_object* v___x_5373_; lean_object* v___f_5374_; 
v___x_5373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5373_, 0, v___x_5372_);
v___f_5374_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5374_, 0, v___x_5373_);
v___y_5309_ = v___f_5374_;
goto v___jp_5308_;
}
}
}
}
}
}
else
{
lean_object* v___x_5381_; uint8_t v_isShared_5382_; uint8_t v_isSharedCheck_5533_; 
lean_inc(v_stop_5361_);
lean_inc(v_start_5360_);
lean_inc_ref(v_array_5359_);
v_isSharedCheck_5533_ = !lean_is_exclusive(v_snd_5338_);
if (v_isSharedCheck_5533_ == 0)
{
lean_object* v_unused_5534_; lean_object* v_unused_5535_; lean_object* v_unused_5536_; 
v_unused_5534_ = lean_ctor_get(v_snd_5338_, 2);
lean_dec(v_unused_5534_);
v_unused_5535_ = lean_ctor_get(v_snd_5338_, 1);
lean_dec(v_unused_5535_);
v_unused_5536_ = lean_ctor_get(v_snd_5338_, 0);
lean_dec(v_unused_5536_);
v___x_5381_ = v_snd_5338_;
v_isShared_5382_ = v_isSharedCheck_5533_;
goto v_resetjp_5380_;
}
else
{
lean_dec(v_snd_5338_);
v___x_5381_ = lean_box(0);
v_isShared_5382_ = v_isSharedCheck_5533_;
goto v_resetjp_5380_;
}
v_resetjp_5380_:
{
lean_object* v_array_5383_; lean_object* v_start_5384_; lean_object* v_stop_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5390_; 
v_array_5383_ = lean_ctor_get(v_fst_5355_, 0);
v_start_5384_ = lean_ctor_get(v_fst_5355_, 1);
v_stop_5385_ = lean_ctor_get(v_fst_5355_, 2);
v___x_5386_ = lean_array_fget(v_array_5359_, v_start_5360_);
v___x_5387_ = lean_unsigned_to_nat(1u);
v___x_5388_ = lean_nat_add(v_start_5360_, v___x_5387_);
lean_dec(v_start_5360_);
if (v_isShared_5382_ == 0)
{
lean_ctor_set(v___x_5381_, 1, v___x_5388_);
v___x_5390_ = v___x_5381_;
goto v_reusejp_5389_;
}
else
{
lean_object* v_reuseFailAlloc_5532_; 
v_reuseFailAlloc_5532_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5532_, 0, v_array_5359_);
lean_ctor_set(v_reuseFailAlloc_5532_, 1, v___x_5388_);
lean_ctor_set(v_reuseFailAlloc_5532_, 2, v_stop_5361_);
v___x_5390_ = v_reuseFailAlloc_5532_;
goto v_reusejp_5389_;
}
v_reusejp_5389_:
{
uint8_t v___x_5391_; 
v___x_5391_ = lean_nat_dec_lt(v_start_5384_, v_stop_5385_);
if (v___x_5391_ == 0)
{
lean_object* v___x_5393_; 
lean_dec(v___x_5386_);
if (v_isShared_5358_ == 0)
{
lean_ctor_set(v___x_5357_, 1, v___x_5390_);
v___x_5393_ = v___x_5357_;
goto v_reusejp_5392_;
}
else
{
lean_object* v_reuseFailAlloc_5408_; 
v_reuseFailAlloc_5408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5408_, 0, v_fst_5355_);
lean_ctor_set(v_reuseFailAlloc_5408_, 1, v___x_5390_);
v___x_5393_ = v_reuseFailAlloc_5408_;
goto v_reusejp_5392_;
}
v_reusejp_5392_:
{
lean_object* v___x_5395_; 
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 1, v___x_5393_);
v___x_5395_ = v___x_5353_;
goto v_reusejp_5394_;
}
else
{
lean_object* v_reuseFailAlloc_5407_; 
v_reuseFailAlloc_5407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5407_, 0, v_fst_5351_);
lean_ctor_set(v_reuseFailAlloc_5407_, 1, v___x_5393_);
v___x_5395_ = v_reuseFailAlloc_5407_;
goto v_reusejp_5394_;
}
v_reusejp_5394_:
{
lean_object* v___x_5397_; 
if (v_isShared_5350_ == 0)
{
lean_ctor_set(v___x_5349_, 1, v___x_5395_);
v___x_5397_ = v___x_5349_;
goto v_reusejp_5396_;
}
else
{
lean_object* v_reuseFailAlloc_5406_; 
v_reuseFailAlloc_5406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5406_, 0, v_fst_5347_);
lean_ctor_set(v_reuseFailAlloc_5406_, 1, v___x_5395_);
v___x_5397_ = v_reuseFailAlloc_5406_;
goto v_reusejp_5396_;
}
v_reusejp_5396_:
{
lean_object* v___x_5399_; 
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 1, v___x_5397_);
v___x_5399_ = v___x_5345_;
goto v_reusejp_5398_;
}
else
{
lean_object* v_reuseFailAlloc_5405_; 
v_reuseFailAlloc_5405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5405_, 0, v_fst_5343_);
lean_ctor_set(v_reuseFailAlloc_5405_, 1, v___x_5397_);
v___x_5399_ = v_reuseFailAlloc_5405_;
goto v_reusejp_5398_;
}
v_reusejp_5398_:
{
lean_object* v___x_5401_; 
if (v_isShared_5342_ == 0)
{
lean_ctor_set(v___x_5341_, 1, v___x_5399_);
v___x_5401_ = v___x_5341_;
goto v_reusejp_5400_;
}
else
{
lean_object* v_reuseFailAlloc_5404_; 
v_reuseFailAlloc_5404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5404_, 0, v_fst_5339_);
lean_ctor_set(v_reuseFailAlloc_5404_, 1, v___x_5399_);
v___x_5401_ = v_reuseFailAlloc_5404_;
goto v_reusejp_5400_;
}
v_reusejp_5400_:
{
lean_object* v___x_5402_; lean_object* v___f_5403_; 
v___x_5402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5402_, 0, v___x_5401_);
v___f_5403_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5403_, 0, v___x_5402_);
v___y_5309_ = v___f_5403_;
goto v___jp_5308_;
}
}
}
}
}
}
else
{
lean_object* v___x_5410_; uint8_t v_isShared_5411_; uint8_t v_isSharedCheck_5528_; 
lean_inc(v_stop_5385_);
lean_inc(v_start_5384_);
lean_inc_ref(v_array_5383_);
v_isSharedCheck_5528_ = !lean_is_exclusive(v_fst_5355_);
if (v_isSharedCheck_5528_ == 0)
{
lean_object* v_unused_5529_; lean_object* v_unused_5530_; lean_object* v_unused_5531_; 
v_unused_5529_ = lean_ctor_get(v_fst_5355_, 2);
lean_dec(v_unused_5529_);
v_unused_5530_ = lean_ctor_get(v_fst_5355_, 1);
lean_dec(v_unused_5530_);
v_unused_5531_ = lean_ctor_get(v_fst_5355_, 0);
lean_dec(v_unused_5531_);
v___x_5410_ = v_fst_5355_;
v_isShared_5411_ = v_isSharedCheck_5528_;
goto v_resetjp_5409_;
}
else
{
lean_dec(v_fst_5355_);
v___x_5410_ = lean_box(0);
v_isShared_5411_ = v_isSharedCheck_5528_;
goto v_resetjp_5409_;
}
v_resetjp_5409_:
{
lean_object* v_array_5412_; lean_object* v_start_5413_; lean_object* v_stop_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5418_; 
v_array_5412_ = lean_ctor_get(v_fst_5351_, 0);
v_start_5413_ = lean_ctor_get(v_fst_5351_, 1);
v_stop_5414_ = lean_ctor_get(v_fst_5351_, 2);
v___x_5415_ = lean_array_fget(v_array_5383_, v_start_5384_);
v___x_5416_ = lean_nat_add(v_start_5384_, v___x_5387_);
lean_dec(v_start_5384_);
if (v_isShared_5411_ == 0)
{
lean_ctor_set(v___x_5410_, 1, v___x_5416_);
v___x_5418_ = v___x_5410_;
goto v_reusejp_5417_;
}
else
{
lean_object* v_reuseFailAlloc_5527_; 
v_reuseFailAlloc_5527_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5527_, 0, v_array_5383_);
lean_ctor_set(v_reuseFailAlloc_5527_, 1, v___x_5416_);
lean_ctor_set(v_reuseFailAlloc_5527_, 2, v_stop_5385_);
v___x_5418_ = v_reuseFailAlloc_5527_;
goto v_reusejp_5417_;
}
v_reusejp_5417_:
{
uint8_t v___x_5419_; 
v___x_5419_ = lean_nat_dec_lt(v_start_5413_, v_stop_5414_);
if (v___x_5419_ == 0)
{
lean_object* v___x_5421_; 
lean_dec(v___x_5415_);
lean_dec(v___x_5386_);
if (v_isShared_5358_ == 0)
{
lean_ctor_set(v___x_5357_, 1, v___x_5390_);
lean_ctor_set(v___x_5357_, 0, v___x_5418_);
v___x_5421_ = v___x_5357_;
goto v_reusejp_5420_;
}
else
{
lean_object* v_reuseFailAlloc_5436_; 
v_reuseFailAlloc_5436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5436_, 0, v___x_5418_);
lean_ctor_set(v_reuseFailAlloc_5436_, 1, v___x_5390_);
v___x_5421_ = v_reuseFailAlloc_5436_;
goto v_reusejp_5420_;
}
v_reusejp_5420_:
{
lean_object* v___x_5423_; 
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 1, v___x_5421_);
v___x_5423_ = v___x_5353_;
goto v_reusejp_5422_;
}
else
{
lean_object* v_reuseFailAlloc_5435_; 
v_reuseFailAlloc_5435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_fst_5351_);
lean_ctor_set(v_reuseFailAlloc_5435_, 1, v___x_5421_);
v___x_5423_ = v_reuseFailAlloc_5435_;
goto v_reusejp_5422_;
}
v_reusejp_5422_:
{
lean_object* v___x_5425_; 
if (v_isShared_5350_ == 0)
{
lean_ctor_set(v___x_5349_, 1, v___x_5423_);
v___x_5425_ = v___x_5349_;
goto v_reusejp_5424_;
}
else
{
lean_object* v_reuseFailAlloc_5434_; 
v_reuseFailAlloc_5434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5434_, 0, v_fst_5347_);
lean_ctor_set(v_reuseFailAlloc_5434_, 1, v___x_5423_);
v___x_5425_ = v_reuseFailAlloc_5434_;
goto v_reusejp_5424_;
}
v_reusejp_5424_:
{
lean_object* v___x_5427_; 
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 1, v___x_5425_);
v___x_5427_ = v___x_5345_;
goto v_reusejp_5426_;
}
else
{
lean_object* v_reuseFailAlloc_5433_; 
v_reuseFailAlloc_5433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5433_, 0, v_fst_5343_);
lean_ctor_set(v_reuseFailAlloc_5433_, 1, v___x_5425_);
v___x_5427_ = v_reuseFailAlloc_5433_;
goto v_reusejp_5426_;
}
v_reusejp_5426_:
{
lean_object* v___x_5429_; 
if (v_isShared_5342_ == 0)
{
lean_ctor_set(v___x_5341_, 1, v___x_5427_);
v___x_5429_ = v___x_5341_;
goto v_reusejp_5428_;
}
else
{
lean_object* v_reuseFailAlloc_5432_; 
v_reuseFailAlloc_5432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5432_, 0, v_fst_5339_);
lean_ctor_set(v_reuseFailAlloc_5432_, 1, v___x_5427_);
v___x_5429_ = v_reuseFailAlloc_5432_;
goto v_reusejp_5428_;
}
v_reusejp_5428_:
{
lean_object* v___x_5430_; lean_object* v___f_5431_; 
v___x_5430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5430_, 0, v___x_5429_);
v___f_5431_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5431_, 0, v___x_5430_);
v___y_5309_ = v___f_5431_;
goto v___jp_5308_;
}
}
}
}
}
}
else
{
lean_object* v___x_5438_; uint8_t v_isShared_5439_; uint8_t v_isSharedCheck_5523_; 
lean_inc(v_stop_5414_);
lean_inc(v_start_5413_);
lean_inc_ref(v_array_5412_);
v_isSharedCheck_5523_ = !lean_is_exclusive(v_fst_5351_);
if (v_isSharedCheck_5523_ == 0)
{
lean_object* v_unused_5524_; lean_object* v_unused_5525_; lean_object* v_unused_5526_; 
v_unused_5524_ = lean_ctor_get(v_fst_5351_, 2);
lean_dec(v_unused_5524_);
v_unused_5525_ = lean_ctor_get(v_fst_5351_, 1);
lean_dec(v_unused_5525_);
v_unused_5526_ = lean_ctor_get(v_fst_5351_, 0);
lean_dec(v_unused_5526_);
v___x_5438_ = v_fst_5351_;
v_isShared_5439_ = v_isSharedCheck_5523_;
goto v_resetjp_5437_;
}
else
{
lean_dec(v_fst_5351_);
v___x_5438_ = lean_box(0);
v_isShared_5439_ = v_isSharedCheck_5523_;
goto v_resetjp_5437_;
}
v_resetjp_5437_:
{
lean_object* v_array_5440_; lean_object* v_start_5441_; lean_object* v_stop_5442_; lean_object* v___x_5443_; lean_object* v___x_5444_; lean_object* v___x_5446_; 
v_array_5440_ = lean_ctor_get(v_fst_5347_, 0);
v_start_5441_ = lean_ctor_get(v_fst_5347_, 1);
v_stop_5442_ = lean_ctor_get(v_fst_5347_, 2);
v___x_5443_ = lean_array_fget(v_array_5412_, v_start_5413_);
v___x_5444_ = lean_nat_add(v_start_5413_, v___x_5387_);
lean_dec(v_start_5413_);
if (v_isShared_5439_ == 0)
{
lean_ctor_set(v___x_5438_, 1, v___x_5444_);
v___x_5446_ = v___x_5438_;
goto v_reusejp_5445_;
}
else
{
lean_object* v_reuseFailAlloc_5522_; 
v_reuseFailAlloc_5522_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5522_, 0, v_array_5412_);
lean_ctor_set(v_reuseFailAlloc_5522_, 1, v___x_5444_);
lean_ctor_set(v_reuseFailAlloc_5522_, 2, v_stop_5414_);
v___x_5446_ = v_reuseFailAlloc_5522_;
goto v_reusejp_5445_;
}
v_reusejp_5445_:
{
uint8_t v___x_5447_; 
v___x_5447_ = lean_nat_dec_lt(v_start_5441_, v_stop_5442_);
if (v___x_5447_ == 0)
{
lean_object* v___x_5449_; 
lean_dec(v___x_5443_);
lean_dec(v___x_5415_);
lean_dec(v___x_5386_);
if (v_isShared_5358_ == 0)
{
lean_ctor_set(v___x_5357_, 1, v___x_5390_);
lean_ctor_set(v___x_5357_, 0, v___x_5418_);
v___x_5449_ = v___x_5357_;
goto v_reusejp_5448_;
}
else
{
lean_object* v_reuseFailAlloc_5464_; 
v_reuseFailAlloc_5464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5464_, 0, v___x_5418_);
lean_ctor_set(v_reuseFailAlloc_5464_, 1, v___x_5390_);
v___x_5449_ = v_reuseFailAlloc_5464_;
goto v_reusejp_5448_;
}
v_reusejp_5448_:
{
lean_object* v___x_5451_; 
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 1, v___x_5449_);
lean_ctor_set(v___x_5353_, 0, v___x_5446_);
v___x_5451_ = v___x_5353_;
goto v_reusejp_5450_;
}
else
{
lean_object* v_reuseFailAlloc_5463_; 
v_reuseFailAlloc_5463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5463_, 0, v___x_5446_);
lean_ctor_set(v_reuseFailAlloc_5463_, 1, v___x_5449_);
v___x_5451_ = v_reuseFailAlloc_5463_;
goto v_reusejp_5450_;
}
v_reusejp_5450_:
{
lean_object* v___x_5453_; 
if (v_isShared_5350_ == 0)
{
lean_ctor_set(v___x_5349_, 1, v___x_5451_);
v___x_5453_ = v___x_5349_;
goto v_reusejp_5452_;
}
else
{
lean_object* v_reuseFailAlloc_5462_; 
v_reuseFailAlloc_5462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5462_, 0, v_fst_5347_);
lean_ctor_set(v_reuseFailAlloc_5462_, 1, v___x_5451_);
v___x_5453_ = v_reuseFailAlloc_5462_;
goto v_reusejp_5452_;
}
v_reusejp_5452_:
{
lean_object* v___x_5455_; 
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 1, v___x_5453_);
v___x_5455_ = v___x_5345_;
goto v_reusejp_5454_;
}
else
{
lean_object* v_reuseFailAlloc_5461_; 
v_reuseFailAlloc_5461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5461_, 0, v_fst_5343_);
lean_ctor_set(v_reuseFailAlloc_5461_, 1, v___x_5453_);
v___x_5455_ = v_reuseFailAlloc_5461_;
goto v_reusejp_5454_;
}
v_reusejp_5454_:
{
lean_object* v___x_5457_; 
if (v_isShared_5342_ == 0)
{
lean_ctor_set(v___x_5341_, 1, v___x_5455_);
v___x_5457_ = v___x_5341_;
goto v_reusejp_5456_;
}
else
{
lean_object* v_reuseFailAlloc_5460_; 
v_reuseFailAlloc_5460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5460_, 0, v_fst_5339_);
lean_ctor_set(v_reuseFailAlloc_5460_, 1, v___x_5455_);
v___x_5457_ = v_reuseFailAlloc_5460_;
goto v_reusejp_5456_;
}
v_reusejp_5456_:
{
lean_object* v___x_5458_; lean_object* v___f_5459_; 
v___x_5458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5458_, 0, v___x_5457_);
v___f_5459_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5459_, 0, v___x_5458_);
v___y_5309_ = v___f_5459_;
goto v___jp_5308_;
}
}
}
}
}
}
else
{
lean_object* v___x_5466_; uint8_t v_isShared_5467_; uint8_t v_isSharedCheck_5518_; 
lean_inc(v_stop_5442_);
lean_inc(v_start_5441_);
lean_inc_ref(v_array_5440_);
v_isSharedCheck_5518_ = !lean_is_exclusive(v_fst_5347_);
if (v_isSharedCheck_5518_ == 0)
{
lean_object* v_unused_5519_; lean_object* v_unused_5520_; lean_object* v_unused_5521_; 
v_unused_5519_ = lean_ctor_get(v_fst_5347_, 2);
lean_dec(v_unused_5519_);
v_unused_5520_ = lean_ctor_get(v_fst_5347_, 1);
lean_dec(v_unused_5520_);
v_unused_5521_ = lean_ctor_get(v_fst_5347_, 0);
lean_dec(v_unused_5521_);
v___x_5466_ = v_fst_5347_;
v_isShared_5467_ = v_isSharedCheck_5518_;
goto v_resetjp_5465_;
}
else
{
lean_dec(v_fst_5347_);
v___x_5466_ = lean_box(0);
v_isShared_5467_ = v_isSharedCheck_5518_;
goto v_resetjp_5465_;
}
v_resetjp_5465_:
{
lean_object* v_array_5468_; lean_object* v_start_5469_; lean_object* v_stop_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; lean_object* v___x_5474_; 
v_array_5468_ = lean_ctor_get(v_fst_5343_, 0);
v_start_5469_ = lean_ctor_get(v_fst_5343_, 1);
v_stop_5470_ = lean_ctor_get(v_fst_5343_, 2);
v___x_5471_ = lean_array_fget(v_array_5440_, v_start_5441_);
v___x_5472_ = lean_nat_add(v_start_5441_, v___x_5387_);
lean_dec(v_start_5441_);
if (v_isShared_5467_ == 0)
{
lean_ctor_set(v___x_5466_, 1, v___x_5472_);
v___x_5474_ = v___x_5466_;
goto v_reusejp_5473_;
}
else
{
lean_object* v_reuseFailAlloc_5517_; 
v_reuseFailAlloc_5517_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5517_, 0, v_array_5440_);
lean_ctor_set(v_reuseFailAlloc_5517_, 1, v___x_5472_);
lean_ctor_set(v_reuseFailAlloc_5517_, 2, v_stop_5442_);
v___x_5474_ = v_reuseFailAlloc_5517_;
goto v_reusejp_5473_;
}
v_reusejp_5473_:
{
uint8_t v___x_5475_; 
v___x_5475_ = lean_nat_dec_lt(v_start_5469_, v_stop_5470_);
if (v___x_5475_ == 0)
{
lean_object* v___x_5477_; 
lean_dec(v___x_5471_);
lean_dec(v___x_5443_);
lean_dec(v___x_5415_);
lean_dec(v___x_5386_);
if (v_isShared_5358_ == 0)
{
lean_ctor_set(v___x_5357_, 1, v___x_5390_);
lean_ctor_set(v___x_5357_, 0, v___x_5418_);
v___x_5477_ = v___x_5357_;
goto v_reusejp_5476_;
}
else
{
lean_object* v_reuseFailAlloc_5492_; 
v_reuseFailAlloc_5492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5492_, 0, v___x_5418_);
lean_ctor_set(v_reuseFailAlloc_5492_, 1, v___x_5390_);
v___x_5477_ = v_reuseFailAlloc_5492_;
goto v_reusejp_5476_;
}
v_reusejp_5476_:
{
lean_object* v___x_5479_; 
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 1, v___x_5477_);
lean_ctor_set(v___x_5353_, 0, v___x_5446_);
v___x_5479_ = v___x_5353_;
goto v_reusejp_5478_;
}
else
{
lean_object* v_reuseFailAlloc_5491_; 
v_reuseFailAlloc_5491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5491_, 0, v___x_5446_);
lean_ctor_set(v_reuseFailAlloc_5491_, 1, v___x_5477_);
v___x_5479_ = v_reuseFailAlloc_5491_;
goto v_reusejp_5478_;
}
v_reusejp_5478_:
{
lean_object* v___x_5481_; 
if (v_isShared_5350_ == 0)
{
lean_ctor_set(v___x_5349_, 1, v___x_5479_);
lean_ctor_set(v___x_5349_, 0, v___x_5474_);
v___x_5481_ = v___x_5349_;
goto v_reusejp_5480_;
}
else
{
lean_object* v_reuseFailAlloc_5490_; 
v_reuseFailAlloc_5490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5490_, 0, v___x_5474_);
lean_ctor_set(v_reuseFailAlloc_5490_, 1, v___x_5479_);
v___x_5481_ = v_reuseFailAlloc_5490_;
goto v_reusejp_5480_;
}
v_reusejp_5480_:
{
lean_object* v___x_5483_; 
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 1, v___x_5481_);
v___x_5483_ = v___x_5345_;
goto v_reusejp_5482_;
}
else
{
lean_object* v_reuseFailAlloc_5489_; 
v_reuseFailAlloc_5489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5489_, 0, v_fst_5343_);
lean_ctor_set(v_reuseFailAlloc_5489_, 1, v___x_5481_);
v___x_5483_ = v_reuseFailAlloc_5489_;
goto v_reusejp_5482_;
}
v_reusejp_5482_:
{
lean_object* v___x_5485_; 
if (v_isShared_5342_ == 0)
{
lean_ctor_set(v___x_5341_, 1, v___x_5483_);
v___x_5485_ = v___x_5341_;
goto v_reusejp_5484_;
}
else
{
lean_object* v_reuseFailAlloc_5488_; 
v_reuseFailAlloc_5488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5488_, 0, v_fst_5339_);
lean_ctor_set(v_reuseFailAlloc_5488_, 1, v___x_5483_);
v___x_5485_ = v_reuseFailAlloc_5488_;
goto v_reusejp_5484_;
}
v_reusejp_5484_:
{
lean_object* v___x_5486_; lean_object* v___f_5487_; 
v___x_5486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5486_, 0, v___x_5485_);
v___f_5487_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5487_, 0, v___x_5486_);
v___y_5309_ = v___f_5487_;
goto v___jp_5308_;
}
}
}
}
}
}
else
{
lean_object* v___x_5494_; uint8_t v_isShared_5495_; uint8_t v_isSharedCheck_5513_; 
lean_inc(v_stop_5470_);
lean_inc(v_start_5469_);
lean_inc_ref(v_array_5468_);
lean_del_object(v___x_5357_);
lean_del_object(v___x_5353_);
lean_del_object(v___x_5349_);
lean_del_object(v___x_5345_);
lean_del_object(v___x_5341_);
v_isSharedCheck_5513_ = !lean_is_exclusive(v_fst_5343_);
if (v_isSharedCheck_5513_ == 0)
{
lean_object* v_unused_5514_; lean_object* v_unused_5515_; lean_object* v_unused_5516_; 
v_unused_5514_ = lean_ctor_get(v_fst_5343_, 2);
lean_dec(v_unused_5514_);
v_unused_5515_ = lean_ctor_get(v_fst_5343_, 1);
lean_dec(v_unused_5515_);
v_unused_5516_ = lean_ctor_get(v_fst_5343_, 0);
lean_dec(v_unused_5516_);
v___x_5494_ = v_fst_5343_;
v_isShared_5495_ = v_isSharedCheck_5513_;
goto v_resetjp_5493_;
}
else
{
lean_dec(v_fst_5343_);
v___x_5494_ = lean_box(0);
v_isShared_5495_ = v_isSharedCheck_5513_;
goto v_resetjp_5493_;
}
v_resetjp_5493_:
{
lean_object* v_numOverlaps_5496_; uint8_t v_hasUnitThunk_5497_; lean_object* v___x_5498_; uint8_t v___x_5499_; 
v_numOverlaps_5496_ = lean_ctor_get(v___x_5471_, 1);
v_hasUnitThunk_5497_ = lean_ctor_get_uint8(v___x_5471_, sizeof(void*)*2);
v___x_5498_ = lean_unsigned_to_nat(0u);
v___x_5499_ = lean_nat_dec_eq(v_numOverlaps_5496_, v___x_5498_);
if (v___x_5499_ == 0)
{
lean_object* v___x_5500_; lean_object* v___x_5501_; 
lean_del_object(v___x_5494_);
lean_dec_ref(v___x_5474_);
lean_dec(v___x_5471_);
lean_dec(v_stop_5470_);
lean_dec(v_start_5469_);
lean_dec_ref(v_array_5468_);
lean_dec_ref(v___x_5446_);
lean_dec(v___x_5443_);
lean_dec_ref(v___x_5418_);
lean_dec(v___x_5415_);
lean_dec_ref(v___x_5390_);
lean_dec(v___x_5386_);
lean_dec(v_fst_5339_);
v___x_5500_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9);
v___x_5501_ = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed), 6, 1);
lean_closure_set(v___x_5501_, 0, v___x_5500_);
v___y_5309_ = v___x_5501_;
goto v___jp_5308_;
}
else
{
uint8_t v___x_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; lean_object* v___f_5507_; lean_object* v___x_5508_; lean_object* v___x_5510_; 
v___x_5502_ = 0;
v___x_5503_ = lean_array_fget_borrowed(v_array_5468_, v_start_5469_);
v___x_5504_ = lean_box(v___x_5502_);
v___x_5505_ = lean_box(v_useSplitter_5298_);
v___x_5506_ = lean_box(v_hasUnitThunk_5497_);
lean_inc(v_numDiscrEqs_5300_);
lean_inc(v_extraEqualities_5299_);
lean_inc(v___x_5503_);
lean_inc(v_a_5301_);
lean_inc_ref(v_onAlt_5297_);
v___f_5507_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed), 18, 11);
lean_closure_set(v___f_5507_, 0, v___x_5443_);
lean_closure_set(v___f_5507_, 1, v___x_5386_);
lean_closure_set(v___f_5507_, 2, v_onAlt_5297_);
lean_closure_set(v___f_5507_, 3, v_a_5301_);
lean_closure_set(v___f_5507_, 4, v___x_5504_);
lean_closure_set(v___f_5507_, 5, v___x_5505_);
lean_closure_set(v___f_5507_, 6, v___x_5503_);
lean_closure_set(v___f_5507_, 7, v_extraEqualities_5299_);
lean_closure_set(v___f_5507_, 8, v_numDiscrEqs_5300_);
lean_closure_set(v___f_5507_, 9, v___x_5506_);
lean_closure_set(v___f_5507_, 10, v___x_5387_);
v___x_5508_ = lean_nat_add(v_start_5469_, v___x_5387_);
lean_dec(v_start_5469_);
if (v_isShared_5495_ == 0)
{
lean_ctor_set(v___x_5494_, 1, v___x_5508_);
v___x_5510_ = v___x_5494_;
goto v_reusejp_5509_;
}
else
{
lean_object* v_reuseFailAlloc_5512_; 
v_reuseFailAlloc_5512_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5512_, 0, v_array_5468_);
lean_ctor_set(v_reuseFailAlloc_5512_, 1, v___x_5508_);
lean_ctor_set(v_reuseFailAlloc_5512_, 2, v_stop_5470_);
v___x_5510_ = v_reuseFailAlloc_5512_;
goto v_reusejp_5509_;
}
v_reusejp_5509_:
{
lean_object* v___f_5511_; 
v___f_5511_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed), 14, 9);
lean_closure_set(v___f_5511_, 0, v___x_5415_);
lean_closure_set(v___f_5511_, 1, v___x_5471_);
lean_closure_set(v___f_5511_, 2, v___f_5507_);
lean_closure_set(v___f_5511_, 3, v_fst_5339_);
lean_closure_set(v___f_5511_, 4, v___x_5418_);
lean_closure_set(v___f_5511_, 5, v___x_5390_);
lean_closure_set(v___f_5511_, 6, v___x_5446_);
lean_closure_set(v___f_5511_, 7, v___x_5474_);
lean_closure_set(v___f_5511_, 8, v___x_5510_);
v___y_5309_ = v___f_5511_;
goto v___jp_5308_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_5308_:
{
lean_object* v___x_5310_; 
lean_inc(v___y_5306_);
lean_inc_ref(v___y_5305_);
lean_inc(v___y_5304_);
lean_inc_ref(v___y_5303_);
v___x_5310_ = lean_apply_5(v___y_5309_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, lean_box(0));
if (lean_obj_tag(v___x_5310_) == 0)
{
lean_object* v_a_5311_; lean_object* v___x_5313_; uint8_t v_isShared_5314_; uint8_t v_isSharedCheck_5323_; 
v_a_5311_ = lean_ctor_get(v___x_5310_, 0);
v_isSharedCheck_5323_ = !lean_is_exclusive(v___x_5310_);
if (v_isSharedCheck_5323_ == 0)
{
v___x_5313_ = v___x_5310_;
v_isShared_5314_ = v_isSharedCheck_5323_;
goto v_resetjp_5312_;
}
else
{
lean_inc(v_a_5311_);
lean_dec(v___x_5310_);
v___x_5313_ = lean_box(0);
v_isShared_5314_ = v_isSharedCheck_5323_;
goto v_resetjp_5312_;
}
v_resetjp_5312_:
{
if (lean_obj_tag(v_a_5311_) == 0)
{
lean_object* v_a_5315_; lean_object* v___x_5317_; 
lean_dec(v___y_5306_);
lean_dec_ref(v___y_5305_);
lean_dec(v___y_5304_);
lean_dec_ref(v___y_5303_);
lean_dec(v_a_5301_);
lean_dec(v_numDiscrEqs_5300_);
lean_dec(v_extraEqualities_5299_);
lean_dec_ref(v_onAlt_5297_);
v_a_5315_ = lean_ctor_get(v_a_5311_, 0);
lean_inc(v_a_5315_);
lean_dec_ref(v_a_5311_);
if (v_isShared_5314_ == 0)
{
lean_ctor_set(v___x_5313_, 0, v_a_5315_);
v___x_5317_ = v___x_5313_;
goto v_reusejp_5316_;
}
else
{
lean_object* v_reuseFailAlloc_5318_; 
v_reuseFailAlloc_5318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5318_, 0, v_a_5315_);
v___x_5317_ = v_reuseFailAlloc_5318_;
goto v_reusejp_5316_;
}
v_reusejp_5316_:
{
return v___x_5317_;
}
}
else
{
lean_object* v_a_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; 
lean_del_object(v___x_5313_);
v_a_5319_ = lean_ctor_get(v_a_5311_, 0);
lean_inc(v_a_5319_);
lean_dec_ref(v_a_5311_);
v___x_5320_ = lean_unsigned_to_nat(1u);
v___x_5321_ = lean_nat_add(v_a_5301_, v___x_5320_);
lean_dec(v_a_5301_);
v_a_5301_ = v___x_5321_;
v_b_5302_ = v_a_5319_;
goto _start;
}
}
}
else
{
lean_object* v_a_5324_; lean_object* v___x_5326_; uint8_t v_isShared_5327_; uint8_t v_isSharedCheck_5331_; 
lean_dec(v___y_5306_);
lean_dec_ref(v___y_5305_);
lean_dec(v___y_5304_);
lean_dec_ref(v___y_5303_);
lean_dec(v_a_5301_);
lean_dec(v_numDiscrEqs_5300_);
lean_dec(v_extraEqualities_5299_);
lean_dec_ref(v_onAlt_5297_);
v_a_5324_ = lean_ctor_get(v___x_5310_, 0);
v_isSharedCheck_5331_ = !lean_is_exclusive(v___x_5310_);
if (v_isSharedCheck_5331_ == 0)
{
v___x_5326_ = v___x_5310_;
v_isShared_5327_ = v_isSharedCheck_5331_;
goto v_resetjp_5325_;
}
else
{
lean_inc(v_a_5324_);
lean_dec(v___x_5310_);
v___x_5326_ = lean_box(0);
v_isShared_5327_ = v_isSharedCheck_5331_;
goto v_resetjp_5325_;
}
v_resetjp_5325_:
{
lean_object* v___x_5329_; 
if (v_isShared_5327_ == 0)
{
v___x_5329_ = v___x_5326_;
goto v_reusejp_5328_;
}
else
{
lean_object* v_reuseFailAlloc_5330_; 
v_reuseFailAlloc_5330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5330_, 0, v_a_5324_);
v___x_5329_ = v_reuseFailAlloc_5330_;
goto v_reusejp_5328_;
}
v_reusejp_5328_:
{
return v___x_5329_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___boxed(lean_object* v_upperBound_5547_, lean_object* v_onAlt_5548_, lean_object* v_useSplitter_5549_, lean_object* v_extraEqualities_5550_, lean_object* v_numDiscrEqs_5551_, lean_object* v_a_5552_, lean_object* v_b_5553_, lean_object* v___y_5554_, lean_object* v___y_5555_, lean_object* v___y_5556_, lean_object* v___y_5557_, lean_object* v___y_5558_){
_start:
{
uint8_t v_useSplitter_boxed_5559_; lean_object* v_res_5560_; 
v_useSplitter_boxed_5559_ = lean_unbox(v_useSplitter_5549_);
v_res_5560_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v_upperBound_5547_, v_onAlt_5548_, v_useSplitter_boxed_5559_, v_extraEqualities_5550_, v_numDiscrEqs_5551_, v_a_5552_, v_b_5553_, v___y_5554_, v___y_5555_, v___y_5556_, v___y_5557_);
lean_dec(v_upperBound_5547_);
return v_res_5560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(uint8_t v_addEqualities_5561_, lean_object* v_as_5562_, size_t v_sz_5563_, size_t v_i_5564_, lean_object* v_b_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_, lean_object* v___y_5568_, lean_object* v___y_5569_){
_start:
{
lean_object* v_a_5572_; uint8_t v___x_5576_; 
v___x_5576_ = lean_usize_dec_lt(v_i_5564_, v_sz_5563_);
if (v___x_5576_ == 0)
{
lean_object* v___x_5577_; 
lean_dec(v___y_5569_);
lean_dec_ref(v___y_5568_);
lean_dec(v___y_5567_);
lean_dec_ref(v___y_5566_);
v___x_5577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5577_, 0, v_b_5565_);
return v___x_5577_;
}
else
{
lean_object* v_snd_5578_; lean_object* v_snd_5579_; lean_object* v_snd_5580_; lean_object* v_snd_5581_; lean_object* v_fst_5582_; lean_object* v___x_5584_; uint8_t v_isShared_5585_; uint8_t v_isSharedCheck_5728_; 
v_snd_5578_ = lean_ctor_get(v_b_5565_, 1);
lean_inc(v_snd_5578_);
v_snd_5579_ = lean_ctor_get(v_snd_5578_, 1);
lean_inc(v_snd_5579_);
v_snd_5580_ = lean_ctor_get(v_snd_5579_, 1);
lean_inc(v_snd_5580_);
v_snd_5581_ = lean_ctor_get(v_snd_5580_, 1);
lean_inc(v_snd_5581_);
v_fst_5582_ = lean_ctor_get(v_b_5565_, 0);
v_isSharedCheck_5728_ = !lean_is_exclusive(v_b_5565_);
if (v_isSharedCheck_5728_ == 0)
{
lean_object* v_unused_5729_; 
v_unused_5729_ = lean_ctor_get(v_b_5565_, 1);
lean_dec(v_unused_5729_);
v___x_5584_ = v_b_5565_;
v_isShared_5585_ = v_isSharedCheck_5728_;
goto v_resetjp_5583_;
}
else
{
lean_inc(v_fst_5582_);
lean_dec(v_b_5565_);
v___x_5584_ = lean_box(0);
v_isShared_5585_ = v_isSharedCheck_5728_;
goto v_resetjp_5583_;
}
v_resetjp_5583_:
{
lean_object* v_fst_5586_; lean_object* v___x_5588_; uint8_t v_isShared_5589_; uint8_t v_isSharedCheck_5726_; 
v_fst_5586_ = lean_ctor_get(v_snd_5578_, 0);
v_isSharedCheck_5726_ = !lean_is_exclusive(v_snd_5578_);
if (v_isSharedCheck_5726_ == 0)
{
lean_object* v_unused_5727_; 
v_unused_5727_ = lean_ctor_get(v_snd_5578_, 1);
lean_dec(v_unused_5727_);
v___x_5588_ = v_snd_5578_;
v_isShared_5589_ = v_isSharedCheck_5726_;
goto v_resetjp_5587_;
}
else
{
lean_inc(v_fst_5586_);
lean_dec(v_snd_5578_);
v___x_5588_ = lean_box(0);
v_isShared_5589_ = v_isSharedCheck_5726_;
goto v_resetjp_5587_;
}
v_resetjp_5587_:
{
lean_object* v_fst_5590_; lean_object* v___x_5592_; uint8_t v_isShared_5593_; uint8_t v_isSharedCheck_5724_; 
v_fst_5590_ = lean_ctor_get(v_snd_5579_, 0);
v_isSharedCheck_5724_ = !lean_is_exclusive(v_snd_5579_);
if (v_isSharedCheck_5724_ == 0)
{
lean_object* v_unused_5725_; 
v_unused_5725_ = lean_ctor_get(v_snd_5579_, 1);
lean_dec(v_unused_5725_);
v___x_5592_ = v_snd_5579_;
v_isShared_5593_ = v_isSharedCheck_5724_;
goto v_resetjp_5591_;
}
else
{
lean_inc(v_fst_5590_);
lean_dec(v_snd_5579_);
v___x_5592_ = lean_box(0);
v_isShared_5593_ = v_isSharedCheck_5724_;
goto v_resetjp_5591_;
}
v_resetjp_5591_:
{
lean_object* v_fst_5594_; lean_object* v___x_5596_; uint8_t v_isShared_5597_; uint8_t v_isSharedCheck_5722_; 
v_fst_5594_ = lean_ctor_get(v_snd_5580_, 0);
v_isSharedCheck_5722_ = !lean_is_exclusive(v_snd_5580_);
if (v_isSharedCheck_5722_ == 0)
{
lean_object* v_unused_5723_; 
v_unused_5723_ = lean_ctor_get(v_snd_5580_, 1);
lean_dec(v_unused_5723_);
v___x_5596_ = v_snd_5580_;
v_isShared_5597_ = v_isSharedCheck_5722_;
goto v_resetjp_5595_;
}
else
{
lean_inc(v_fst_5594_);
lean_dec(v_snd_5580_);
v___x_5596_ = lean_box(0);
v_isShared_5597_ = v_isSharedCheck_5722_;
goto v_resetjp_5595_;
}
v_resetjp_5595_:
{
lean_object* v_array_5598_; lean_object* v_start_5599_; lean_object* v_stop_5600_; uint8_t v___x_5601_; 
v_array_5598_ = lean_ctor_get(v_snd_5581_, 0);
v_start_5599_ = lean_ctor_get(v_snd_5581_, 1);
v_stop_5600_ = lean_ctor_get(v_snd_5581_, 2);
v___x_5601_ = lean_nat_dec_lt(v_start_5599_, v_stop_5600_);
if (v___x_5601_ == 0)
{
lean_object* v___x_5603_; 
lean_dec(v___y_5569_);
lean_dec_ref(v___y_5568_);
lean_dec(v___y_5567_);
lean_dec_ref(v___y_5566_);
if (v_isShared_5597_ == 0)
{
v___x_5603_ = v___x_5596_;
goto v_reusejp_5602_;
}
else
{
lean_object* v_reuseFailAlloc_5614_; 
v_reuseFailAlloc_5614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5614_, 0, v_fst_5594_);
lean_ctor_set(v_reuseFailAlloc_5614_, 1, v_snd_5581_);
v___x_5603_ = v_reuseFailAlloc_5614_;
goto v_reusejp_5602_;
}
v_reusejp_5602_:
{
lean_object* v___x_5605_; 
if (v_isShared_5593_ == 0)
{
lean_ctor_set(v___x_5592_, 1, v___x_5603_);
v___x_5605_ = v___x_5592_;
goto v_reusejp_5604_;
}
else
{
lean_object* v_reuseFailAlloc_5613_; 
v_reuseFailAlloc_5613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5613_, 0, v_fst_5590_);
lean_ctor_set(v_reuseFailAlloc_5613_, 1, v___x_5603_);
v___x_5605_ = v_reuseFailAlloc_5613_;
goto v_reusejp_5604_;
}
v_reusejp_5604_:
{
lean_object* v___x_5607_; 
if (v_isShared_5589_ == 0)
{
lean_ctor_set(v___x_5588_, 1, v___x_5605_);
v___x_5607_ = v___x_5588_;
goto v_reusejp_5606_;
}
else
{
lean_object* v_reuseFailAlloc_5612_; 
v_reuseFailAlloc_5612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5612_, 0, v_fst_5586_);
lean_ctor_set(v_reuseFailAlloc_5612_, 1, v___x_5605_);
v___x_5607_ = v_reuseFailAlloc_5612_;
goto v_reusejp_5606_;
}
v_reusejp_5606_:
{
lean_object* v___x_5609_; 
if (v_isShared_5585_ == 0)
{
lean_ctor_set(v___x_5584_, 1, v___x_5607_);
v___x_5609_ = v___x_5584_;
goto v_reusejp_5608_;
}
else
{
lean_object* v_reuseFailAlloc_5611_; 
v_reuseFailAlloc_5611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5611_, 0, v_fst_5582_);
lean_ctor_set(v_reuseFailAlloc_5611_, 1, v___x_5607_);
v___x_5609_ = v_reuseFailAlloc_5611_;
goto v_reusejp_5608_;
}
v_reusejp_5608_:
{
lean_object* v___x_5610_; 
v___x_5610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5610_, 0, v___x_5609_);
return v___x_5610_;
}
}
}
}
}
else
{
lean_object* v___x_5616_; uint8_t v_isShared_5617_; uint8_t v_isSharedCheck_5718_; 
lean_inc(v_stop_5600_);
lean_inc(v_start_5599_);
lean_inc_ref(v_array_5598_);
v_isSharedCheck_5718_ = !lean_is_exclusive(v_snd_5581_);
if (v_isSharedCheck_5718_ == 0)
{
lean_object* v_unused_5719_; lean_object* v_unused_5720_; lean_object* v_unused_5721_; 
v_unused_5719_ = lean_ctor_get(v_snd_5581_, 2);
lean_dec(v_unused_5719_);
v_unused_5720_ = lean_ctor_get(v_snd_5581_, 1);
lean_dec(v_unused_5720_);
v_unused_5721_ = lean_ctor_get(v_snd_5581_, 0);
lean_dec(v_unused_5721_);
v___x_5616_ = v_snd_5581_;
v_isShared_5617_ = v_isSharedCheck_5718_;
goto v_resetjp_5615_;
}
else
{
lean_dec(v_snd_5581_);
v___x_5616_ = lean_box(0);
v_isShared_5617_ = v_isSharedCheck_5718_;
goto v_resetjp_5615_;
}
v_resetjp_5615_:
{
lean_object* v_array_5618_; lean_object* v_start_5619_; lean_object* v_stop_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5625_; 
v_array_5618_ = lean_ctor_get(v_fst_5594_, 0);
v_start_5619_ = lean_ctor_get(v_fst_5594_, 1);
v_stop_5620_ = lean_ctor_get(v_fst_5594_, 2);
v___x_5621_ = lean_array_fget(v_array_5598_, v_start_5599_);
v___x_5622_ = lean_unsigned_to_nat(1u);
v___x_5623_ = lean_nat_add(v_start_5599_, v___x_5622_);
lean_dec(v_start_5599_);
if (v_isShared_5617_ == 0)
{
lean_ctor_set(v___x_5616_, 1, v___x_5623_);
v___x_5625_ = v___x_5616_;
goto v_reusejp_5624_;
}
else
{
lean_object* v_reuseFailAlloc_5717_; 
v_reuseFailAlloc_5717_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5717_, 0, v_array_5598_);
lean_ctor_set(v_reuseFailAlloc_5717_, 1, v___x_5623_);
lean_ctor_set(v_reuseFailAlloc_5717_, 2, v_stop_5600_);
v___x_5625_ = v_reuseFailAlloc_5717_;
goto v_reusejp_5624_;
}
v_reusejp_5624_:
{
uint8_t v___x_5626_; 
v___x_5626_ = lean_nat_dec_lt(v_start_5619_, v_stop_5620_);
if (v___x_5626_ == 0)
{
lean_object* v___x_5628_; 
lean_dec(v___x_5621_);
lean_dec(v___y_5569_);
lean_dec_ref(v___y_5568_);
lean_dec(v___y_5567_);
lean_dec_ref(v___y_5566_);
if (v_isShared_5597_ == 0)
{
lean_ctor_set(v___x_5596_, 1, v___x_5625_);
v___x_5628_ = v___x_5596_;
goto v_reusejp_5627_;
}
else
{
lean_object* v_reuseFailAlloc_5639_; 
v_reuseFailAlloc_5639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5639_, 0, v_fst_5594_);
lean_ctor_set(v_reuseFailAlloc_5639_, 1, v___x_5625_);
v___x_5628_ = v_reuseFailAlloc_5639_;
goto v_reusejp_5627_;
}
v_reusejp_5627_:
{
lean_object* v___x_5630_; 
if (v_isShared_5593_ == 0)
{
lean_ctor_set(v___x_5592_, 1, v___x_5628_);
v___x_5630_ = v___x_5592_;
goto v_reusejp_5629_;
}
else
{
lean_object* v_reuseFailAlloc_5638_; 
v_reuseFailAlloc_5638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5638_, 0, v_fst_5590_);
lean_ctor_set(v_reuseFailAlloc_5638_, 1, v___x_5628_);
v___x_5630_ = v_reuseFailAlloc_5638_;
goto v_reusejp_5629_;
}
v_reusejp_5629_:
{
lean_object* v___x_5632_; 
if (v_isShared_5589_ == 0)
{
lean_ctor_set(v___x_5588_, 1, v___x_5630_);
v___x_5632_ = v___x_5588_;
goto v_reusejp_5631_;
}
else
{
lean_object* v_reuseFailAlloc_5637_; 
v_reuseFailAlloc_5637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5637_, 0, v_fst_5586_);
lean_ctor_set(v_reuseFailAlloc_5637_, 1, v___x_5630_);
v___x_5632_ = v_reuseFailAlloc_5637_;
goto v_reusejp_5631_;
}
v_reusejp_5631_:
{
lean_object* v___x_5634_; 
if (v_isShared_5585_ == 0)
{
lean_ctor_set(v___x_5584_, 1, v___x_5632_);
v___x_5634_ = v___x_5584_;
goto v_reusejp_5633_;
}
else
{
lean_object* v_reuseFailAlloc_5636_; 
v_reuseFailAlloc_5636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5636_, 0, v_fst_5582_);
lean_ctor_set(v_reuseFailAlloc_5636_, 1, v___x_5632_);
v___x_5634_ = v_reuseFailAlloc_5636_;
goto v_reusejp_5633_;
}
v_reusejp_5633_:
{
lean_object* v___x_5635_; 
v___x_5635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5635_, 0, v___x_5634_);
return v___x_5635_;
}
}
}
}
}
else
{
lean_object* v___x_5641_; uint8_t v_isShared_5642_; uint8_t v_isSharedCheck_5713_; 
lean_inc(v_stop_5620_);
lean_inc(v_start_5619_);
lean_inc_ref(v_array_5618_);
v_isSharedCheck_5713_ = !lean_is_exclusive(v_fst_5594_);
if (v_isSharedCheck_5713_ == 0)
{
lean_object* v_unused_5714_; lean_object* v_unused_5715_; lean_object* v_unused_5716_; 
v_unused_5714_ = lean_ctor_get(v_fst_5594_, 2);
lean_dec(v_unused_5714_);
v_unused_5715_ = lean_ctor_get(v_fst_5594_, 1);
lean_dec(v_unused_5715_);
v_unused_5716_ = lean_ctor_get(v_fst_5594_, 0);
lean_dec(v_unused_5716_);
v___x_5641_ = v_fst_5594_;
v_isShared_5642_ = v_isSharedCheck_5713_;
goto v_resetjp_5640_;
}
else
{
lean_dec(v_fst_5594_);
v___x_5641_ = lean_box(0);
v_isShared_5642_ = v_isSharedCheck_5713_;
goto v_resetjp_5640_;
}
v_resetjp_5640_:
{
lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5646_; 
v___x_5643_ = lean_array_fget(v_array_5618_, v_start_5619_);
v___x_5644_ = lean_nat_add(v_start_5619_, v___x_5622_);
lean_dec(v_start_5619_);
if (v_isShared_5642_ == 0)
{
lean_ctor_set(v___x_5641_, 1, v___x_5644_);
v___x_5646_ = v___x_5641_;
goto v_reusejp_5645_;
}
else
{
lean_object* v_reuseFailAlloc_5712_; 
v_reuseFailAlloc_5712_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5712_, 0, v_array_5618_);
lean_ctor_set(v_reuseFailAlloc_5712_, 1, v___x_5644_);
lean_ctor_set(v_reuseFailAlloc_5712_, 2, v_stop_5620_);
v___x_5646_ = v_reuseFailAlloc_5712_;
goto v_reusejp_5645_;
}
v_reusejp_5645_:
{
if (v_addEqualities_5561_ == 0)
{
lean_dec(v___x_5643_);
goto v___jp_5647_;
}
else
{
if (lean_obj_tag(v___x_5621_) == 0)
{
lean_object* v_a_5663_; lean_object* v___x_5664_; 
lean_del_object(v___x_5596_);
lean_del_object(v___x_5592_);
lean_del_object(v___x_5588_);
lean_del_object(v___x_5584_);
v_a_5663_ = lean_array_uget_borrowed(v_as_5562_, v_i_5564_);
lean_inc(v___y_5569_);
lean_inc_ref(v___y_5568_);
lean_inc(v___y_5567_);
lean_inc_ref(v___y_5566_);
lean_inc(v_a_5663_);
v___x_5664_ = l_Lean_Meta_isProof(v_a_5663_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_);
if (lean_obj_tag(v___x_5664_) == 0)
{
lean_object* v_a_5665_; uint8_t v___x_5666_; 
v_a_5665_ = lean_ctor_get(v___x_5664_, 0);
lean_inc(v_a_5665_);
lean_dec_ref(v___x_5664_);
v___x_5666_ = lean_unbox(v_a_5665_);
lean_dec(v_a_5665_);
if (v___x_5666_ == 0)
{
lean_object* v___x_5667_; 
lean_inc(v___y_5569_);
lean_inc_ref(v___y_5568_);
lean_inc(v___y_5567_);
lean_inc_ref(v___y_5566_);
lean_inc(v_a_5663_);
v___x_5667_ = l_Lean_Meta_mkEqHEq(v___x_5643_, v_a_5663_, v___y_5566_, v___y_5567_, v___y_5568_, v___y_5569_);
if (lean_obj_tag(v___x_5667_) == 0)
{
lean_object* v_a_5668_; lean_object* v___x_5669_; 
v_a_5668_ = lean_ctor_get(v___x_5667_, 0);
lean_inc(v_a_5668_);
lean_dec_ref(v___x_5667_);
lean_inc(v___y_5569_);
lean_inc_ref(v___y_5568_);
lean_inc(v_a_5668_);
v___x_5669_ = l_Lean_mkArrow(v_a_5668_, v_fst_5582_, v___y_5568_, v___y_5569_);
if (lean_obj_tag(v___x_5669_) == 0)
{
lean_object* v_a_5670_; uint8_t v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; 
v_a_5670_ = lean_ctor_get(v___x_5669_, 0);
lean_inc(v_a_5670_);
lean_dec_ref(v___x_5669_);
v___x_5671_ = l_Lean_Expr_isHEq(v_a_5668_);
lean_dec(v_a_5668_);
v___x_5672_ = lean_box(v___x_5671_);
v___x_5673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5673_, 0, v___x_5672_);
v___x_5674_ = lean_array_push(v_fst_5586_, v___x_5673_);
v___x_5675_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9___closed__0));
v___x_5676_ = lean_array_push(v_fst_5590_, v___x_5675_);
v___x_5677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5677_, 0, v___x_5646_);
lean_ctor_set(v___x_5677_, 1, v___x_5625_);
v___x_5678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5678_, 0, v___x_5676_);
lean_ctor_set(v___x_5678_, 1, v___x_5677_);
v___x_5679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5679_, 0, v___x_5674_);
lean_ctor_set(v___x_5679_, 1, v___x_5678_);
v___x_5680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5680_, 0, v_a_5670_);
lean_ctor_set(v___x_5680_, 1, v___x_5679_);
v_a_5572_ = v___x_5680_;
goto v___jp_5571_;
}
else
{
lean_object* v_a_5681_; lean_object* v___x_5683_; uint8_t v_isShared_5684_; uint8_t v_isSharedCheck_5688_; 
lean_dec(v_a_5668_);
lean_dec_ref(v___x_5646_);
lean_dec_ref(v___x_5625_);
lean_dec(v_fst_5590_);
lean_dec(v_fst_5586_);
lean_dec(v___y_5569_);
lean_dec_ref(v___y_5568_);
lean_dec(v___y_5567_);
lean_dec_ref(v___y_5566_);
v_a_5681_ = lean_ctor_get(v___x_5669_, 0);
v_isSharedCheck_5688_ = !lean_is_exclusive(v___x_5669_);
if (v_isSharedCheck_5688_ == 0)
{
v___x_5683_ = v___x_5669_;
v_isShared_5684_ = v_isSharedCheck_5688_;
goto v_resetjp_5682_;
}
else
{
lean_inc(v_a_5681_);
lean_dec(v___x_5669_);
v___x_5683_ = lean_box(0);
v_isShared_5684_ = v_isSharedCheck_5688_;
goto v_resetjp_5682_;
}
v_resetjp_5682_:
{
lean_object* v___x_5686_; 
if (v_isShared_5684_ == 0)
{
v___x_5686_ = v___x_5683_;
goto v_reusejp_5685_;
}
else
{
lean_object* v_reuseFailAlloc_5687_; 
v_reuseFailAlloc_5687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5687_, 0, v_a_5681_);
v___x_5686_ = v_reuseFailAlloc_5687_;
goto v_reusejp_5685_;
}
v_reusejp_5685_:
{
return v___x_5686_;
}
}
}
}
else
{
lean_object* v_a_5689_; lean_object* v___x_5691_; uint8_t v_isShared_5692_; uint8_t v_isSharedCheck_5696_; 
lean_dec_ref(v___x_5646_);
lean_dec_ref(v___x_5625_);
lean_dec(v_fst_5590_);
lean_dec(v_fst_5586_);
lean_dec(v_fst_5582_);
lean_dec(v___y_5569_);
lean_dec_ref(v___y_5568_);
lean_dec(v___y_5567_);
lean_dec_ref(v___y_5566_);
v_a_5689_ = lean_ctor_get(v___x_5667_, 0);
v_isSharedCheck_5696_ = !lean_is_exclusive(v___x_5667_);
if (v_isSharedCheck_5696_ == 0)
{
v___x_5691_ = v___x_5667_;
v_isShared_5692_ = v_isSharedCheck_5696_;
goto v_resetjp_5690_;
}
else
{
lean_inc(v_a_5689_);
lean_dec(v___x_5667_);
v___x_5691_ = lean_box(0);
v_isShared_5692_ = v_isSharedCheck_5696_;
goto v_resetjp_5690_;
}
v_resetjp_5690_:
{
lean_object* v___x_5694_; 
if (v_isShared_5692_ == 0)
{
v___x_5694_ = v___x_5691_;
goto v_reusejp_5693_;
}
else
{
lean_object* v_reuseFailAlloc_5695_; 
v_reuseFailAlloc_5695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5695_, 0, v_a_5689_);
v___x_5694_ = v_reuseFailAlloc_5695_;
goto v_reusejp_5693_;
}
v_reusejp_5693_:
{
return v___x_5694_;
}
}
}
}
else
{
lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; 
lean_dec(v___x_5643_);
v___x_5697_ = lean_box(0);
v___x_5698_ = lean_array_push(v_fst_5586_, v___x_5697_);
v___x_5699_ = lean_array_push(v_fst_5590_, v___x_5621_);
v___x_5700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5700_, 0, v___x_5646_);
lean_ctor_set(v___x_5700_, 1, v___x_5625_);
v___x_5701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5701_, 0, v___x_5699_);
lean_ctor_set(v___x_5701_, 1, v___x_5700_);
v___x_5702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5702_, 0, v___x_5698_);
lean_ctor_set(v___x_5702_, 1, v___x_5701_);
v___x_5703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5703_, 0, v_fst_5582_);
lean_ctor_set(v___x_5703_, 1, v___x_5702_);
v_a_5572_ = v___x_5703_;
goto v___jp_5571_;
}
}
else
{
lean_object* v_a_5704_; lean_object* v___x_5706_; uint8_t v_isShared_5707_; uint8_t v_isSharedCheck_5711_; 
lean_dec_ref(v___x_5646_);
lean_dec(v___x_5643_);
lean_dec_ref(v___x_5625_);
lean_dec(v_fst_5590_);
lean_dec(v_fst_5586_);
lean_dec(v_fst_5582_);
lean_dec(v___y_5569_);
lean_dec_ref(v___y_5568_);
lean_dec(v___y_5567_);
lean_dec_ref(v___y_5566_);
v_a_5704_ = lean_ctor_get(v___x_5664_, 0);
v_isSharedCheck_5711_ = !lean_is_exclusive(v___x_5664_);
if (v_isSharedCheck_5711_ == 0)
{
v___x_5706_ = v___x_5664_;
v_isShared_5707_ = v_isSharedCheck_5711_;
goto v_resetjp_5705_;
}
else
{
lean_inc(v_a_5704_);
lean_dec(v___x_5664_);
v___x_5706_ = lean_box(0);
v_isShared_5707_ = v_isSharedCheck_5711_;
goto v_resetjp_5705_;
}
v_resetjp_5705_:
{
lean_object* v___x_5709_; 
if (v_isShared_5707_ == 0)
{
v___x_5709_ = v___x_5706_;
goto v_reusejp_5708_;
}
else
{
lean_object* v_reuseFailAlloc_5710_; 
v_reuseFailAlloc_5710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5710_, 0, v_a_5704_);
v___x_5709_ = v_reuseFailAlloc_5710_;
goto v_reusejp_5708_;
}
v_reusejp_5708_:
{
return v___x_5709_;
}
}
}
}
else
{
lean_dec(v___x_5643_);
goto v___jp_5647_;
}
}
v___jp_5647_:
{
lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5652_; 
v___x_5648_ = lean_box(0);
v___x_5649_ = lean_array_push(v_fst_5586_, v___x_5648_);
v___x_5650_ = lean_array_push(v_fst_5590_, v___x_5621_);
if (v_isShared_5597_ == 0)
{
lean_ctor_set(v___x_5596_, 1, v___x_5625_);
lean_ctor_set(v___x_5596_, 0, v___x_5646_);
v___x_5652_ = v___x_5596_;
goto v_reusejp_5651_;
}
else
{
lean_object* v_reuseFailAlloc_5662_; 
v_reuseFailAlloc_5662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5662_, 0, v___x_5646_);
lean_ctor_set(v_reuseFailAlloc_5662_, 1, v___x_5625_);
v___x_5652_ = v_reuseFailAlloc_5662_;
goto v_reusejp_5651_;
}
v_reusejp_5651_:
{
lean_object* v___x_5654_; 
if (v_isShared_5593_ == 0)
{
lean_ctor_set(v___x_5592_, 1, v___x_5652_);
lean_ctor_set(v___x_5592_, 0, v___x_5650_);
v___x_5654_ = v___x_5592_;
goto v_reusejp_5653_;
}
else
{
lean_object* v_reuseFailAlloc_5661_; 
v_reuseFailAlloc_5661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5661_, 0, v___x_5650_);
lean_ctor_set(v_reuseFailAlloc_5661_, 1, v___x_5652_);
v___x_5654_ = v_reuseFailAlloc_5661_;
goto v_reusejp_5653_;
}
v_reusejp_5653_:
{
lean_object* v___x_5656_; 
if (v_isShared_5589_ == 0)
{
lean_ctor_set(v___x_5588_, 1, v___x_5654_);
lean_ctor_set(v___x_5588_, 0, v___x_5649_);
v___x_5656_ = v___x_5588_;
goto v_reusejp_5655_;
}
else
{
lean_object* v_reuseFailAlloc_5660_; 
v_reuseFailAlloc_5660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5660_, 0, v___x_5649_);
lean_ctor_set(v_reuseFailAlloc_5660_, 1, v___x_5654_);
v___x_5656_ = v_reuseFailAlloc_5660_;
goto v_reusejp_5655_;
}
v_reusejp_5655_:
{
lean_object* v___x_5658_; 
if (v_isShared_5585_ == 0)
{
lean_ctor_set(v___x_5584_, 1, v___x_5656_);
v___x_5658_ = v___x_5584_;
goto v_reusejp_5657_;
}
else
{
lean_object* v_reuseFailAlloc_5659_; 
v_reuseFailAlloc_5659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5659_, 0, v_fst_5582_);
lean_ctor_set(v_reuseFailAlloc_5659_, 1, v___x_5656_);
v___x_5658_ = v_reuseFailAlloc_5659_;
goto v_reusejp_5657_;
}
v_reusejp_5657_:
{
v_a_5572_ = v___x_5658_;
goto v___jp_5571_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_5571_:
{
size_t v___x_5573_; size_t v___x_5574_; 
v___x_5573_ = ((size_t)1ULL);
v___x_5574_ = lean_usize_add(v_i_5564_, v___x_5573_);
v_i_5564_ = v___x_5574_;
v_b_5565_ = v_a_5572_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7___boxed(lean_object* v_addEqualities_5730_, lean_object* v_as_5731_, lean_object* v_sz_5732_, lean_object* v_i_5733_, lean_object* v_b_5734_, lean_object* v___y_5735_, lean_object* v___y_5736_, lean_object* v___y_5737_, lean_object* v___y_5738_, lean_object* v___y_5739_){
_start:
{
uint8_t v_addEqualities_boxed_5740_; size_t v_sz_boxed_5741_; size_t v_i_boxed_5742_; lean_object* v_res_5743_; 
v_addEqualities_boxed_5740_ = lean_unbox(v_addEqualities_5730_);
v_sz_boxed_5741_ = lean_unbox_usize(v_sz_5732_);
lean_dec(v_sz_5732_);
v_i_boxed_5742_ = lean_unbox_usize(v_i_5733_);
lean_dec(v_i_5733_);
v_res_5743_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(v_addEqualities_boxed_5740_, v_as_5731_, v_sz_boxed_5741_, v_i_boxed_5742_, v_b_5734_, v___y_5735_, v___y_5736_, v___y_5737_, v___y_5738_);
lean_dec_ref(v_as_5731_);
return v_res_5743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(lean_object* v_onMotive_5744_, lean_object* v_toMatcherInfo_5745_, lean_object* v_a_5746_, uint8_t v_addEqualities_5747_, size_t v___x_5748_, lean_object* v_discrs_5749_, lean_object* v_motiveArgs_5750_, lean_object* v_motiveBody_5751_, lean_object* v___y_5752_, lean_object* v___y_5753_, lean_object* v___y_5754_, lean_object* v___y_5755_){
_start:
{
lean_object* v___x_5849_; lean_object* v___x_5850_; uint8_t v___x_5851_; 
v___x_5849_ = lean_array_get_size(v_motiveArgs_5750_);
v___x_5850_ = lean_array_get_size(v_discrs_5749_);
v___x_5851_ = lean_nat_dec_eq(v___x_5849_, v___x_5850_);
if (v___x_5851_ == 0)
{
lean_object* v___x_5852_; lean_object* v___x_5853_; lean_object* v___x_5854_; lean_object* v___x_5855_; lean_object* v___x_5856_; lean_object* v___x_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; lean_object* v_a_5860_; lean_object* v___x_5862_; uint8_t v_isShared_5863_; uint8_t v_isSharedCheck_5867_; 
lean_dec_ref(v_motiveBody_5751_);
lean_dec_ref(v_motiveArgs_5750_);
lean_dec_ref(v_a_5746_);
lean_dec_ref(v_toMatcherInfo_5745_);
lean_dec_ref(v_onMotive_5744_);
v___x_5852_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_5853_ = l_Nat_reprFast(v___x_5850_);
v___x_5854_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5854_, 0, v___x_5853_);
v___x_5855_ = l_Lean_MessageData_ofFormat(v___x_5854_);
v___x_5856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5856_, 0, v___x_5852_);
lean_ctor_set(v___x_5856_, 1, v___x_5855_);
v___x_5857_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_5858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5858_, 0, v___x_5856_);
lean_ctor_set(v___x_5858_, 1, v___x_5857_);
v___x_5859_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_5858_, v___y_5752_, v___y_5753_, v___y_5754_, v___y_5755_);
lean_dec(v___y_5755_);
lean_dec_ref(v___y_5754_);
lean_dec(v___y_5753_);
lean_dec_ref(v___y_5752_);
v_a_5860_ = lean_ctor_get(v___x_5859_, 0);
v_isSharedCheck_5867_ = !lean_is_exclusive(v___x_5859_);
if (v_isSharedCheck_5867_ == 0)
{
v___x_5862_ = v___x_5859_;
v_isShared_5863_ = v_isSharedCheck_5867_;
goto v_resetjp_5861_;
}
else
{
lean_inc(v_a_5860_);
lean_dec(v___x_5859_);
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
else
{
goto v___jp_5757_;
}
v___jp_5757_:
{
lean_object* v___x_5758_; 
lean_inc(v___y_5755_);
lean_inc_ref(v___y_5754_);
lean_inc(v___y_5753_);
lean_inc_ref(v___y_5752_);
lean_inc_ref(v_motiveArgs_5750_);
v___x_5758_ = lean_apply_7(v_onMotive_5744_, v_motiveArgs_5750_, v_motiveBody_5751_, v___y_5752_, v___y_5753_, v___y_5754_, v___y_5755_, lean_box(0));
if (lean_obj_tag(v___x_5758_) == 0)
{
lean_object* v_a_5759_; lean_object* v_discrInfos_5760_; lean_object* v___x_5761_; lean_object* v_addHEqualities_5762_; lean_object* v___x_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; size_t v_sz_5771_; lean_object* v___x_5772_; 
v_a_5759_ = lean_ctor_get(v___x_5758_, 0);
lean_inc(v_a_5759_);
lean_dec_ref(v___x_5758_);
v_discrInfos_5760_ = lean_ctor_get(v_toMatcherInfo_5745_, 4);
lean_inc_ref(v_discrInfos_5760_);
lean_dec_ref(v_toMatcherInfo_5745_);
v___x_5761_ = lean_unsigned_to_nat(0u);
v_addHEqualities_5762_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___closed__0));
v___x_5763_ = lean_array_get_size(v_a_5746_);
v___x_5764_ = l_Array_toSubarray___redArg(v_a_5746_, v___x_5761_, v___x_5763_);
v___x_5765_ = lean_array_get_size(v_discrInfos_5760_);
v___x_5766_ = l_Array_toSubarray___redArg(v_discrInfos_5760_, v___x_5761_, v___x_5765_);
v___x_5767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5767_, 0, v___x_5764_);
lean_ctor_set(v___x_5767_, 1, v___x_5766_);
v___x_5768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5768_, 0, v_addHEqualities_5762_);
lean_ctor_set(v___x_5768_, 1, v___x_5767_);
v___x_5769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5769_, 0, v_addHEqualities_5762_);
lean_ctor_set(v___x_5769_, 1, v___x_5768_);
v___x_5770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5770_, 0, v_a_5759_);
lean_ctor_set(v___x_5770_, 1, v___x_5769_);
v_sz_5771_ = lean_array_size(v_motiveArgs_5750_);
lean_inc(v___y_5755_);
lean_inc_ref(v___y_5754_);
lean_inc(v___y_5753_);
lean_inc_ref(v___y_5752_);
v___x_5772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(v_addEqualities_5747_, v_motiveArgs_5750_, v_sz_5771_, v___x_5748_, v___x_5770_, v___y_5752_, v___y_5753_, v___y_5754_, v___y_5755_);
if (lean_obj_tag(v___x_5772_) == 0)
{
lean_object* v_a_5773_; lean_object* v_snd_5774_; lean_object* v_snd_5775_; lean_object* v_fst_5776_; lean_object* v___x_5778_; uint8_t v_isShared_5779_; uint8_t v_isSharedCheck_5831_; 
v_a_5773_ = lean_ctor_get(v___x_5772_, 0);
lean_inc(v_a_5773_);
lean_dec_ref(v___x_5772_);
v_snd_5774_ = lean_ctor_get(v_a_5773_, 1);
lean_inc(v_snd_5774_);
v_snd_5775_ = lean_ctor_get(v_snd_5774_, 1);
lean_inc(v_snd_5775_);
v_fst_5776_ = lean_ctor_get(v_a_5773_, 0);
v_isSharedCheck_5831_ = !lean_is_exclusive(v_a_5773_);
if (v_isSharedCheck_5831_ == 0)
{
lean_object* v_unused_5832_; 
v_unused_5832_ = lean_ctor_get(v_a_5773_, 1);
lean_dec(v_unused_5832_);
v___x_5778_ = v_a_5773_;
v_isShared_5779_ = v_isSharedCheck_5831_;
goto v_resetjp_5777_;
}
else
{
lean_inc(v_fst_5776_);
lean_dec(v_a_5773_);
v___x_5778_ = lean_box(0);
v_isShared_5779_ = v_isSharedCheck_5831_;
goto v_resetjp_5777_;
}
v_resetjp_5777_:
{
lean_object* v_fst_5780_; lean_object* v___x_5782_; uint8_t v_isShared_5783_; uint8_t v_isSharedCheck_5829_; 
v_fst_5780_ = lean_ctor_get(v_snd_5774_, 0);
v_isSharedCheck_5829_ = !lean_is_exclusive(v_snd_5774_);
if (v_isSharedCheck_5829_ == 0)
{
lean_object* v_unused_5830_; 
v_unused_5830_ = lean_ctor_get(v_snd_5774_, 1);
lean_dec(v_unused_5830_);
v___x_5782_ = v_snd_5774_;
v_isShared_5783_ = v_isSharedCheck_5829_;
goto v_resetjp_5781_;
}
else
{
lean_inc(v_fst_5780_);
lean_dec(v_snd_5774_);
v___x_5782_ = lean_box(0);
v_isShared_5783_ = v_isSharedCheck_5829_;
goto v_resetjp_5781_;
}
v_resetjp_5781_:
{
lean_object* v_fst_5784_; lean_object* v___x_5786_; uint8_t v_isShared_5787_; uint8_t v_isSharedCheck_5827_; 
v_fst_5784_ = lean_ctor_get(v_snd_5775_, 0);
v_isSharedCheck_5827_ = !lean_is_exclusive(v_snd_5775_);
if (v_isSharedCheck_5827_ == 0)
{
lean_object* v_unused_5828_; 
v_unused_5828_ = lean_ctor_get(v_snd_5775_, 1);
lean_dec(v_unused_5828_);
v___x_5786_ = v_snd_5775_;
v_isShared_5787_ = v_isSharedCheck_5827_;
goto v_resetjp_5785_;
}
else
{
lean_inc(v_fst_5784_);
lean_dec(v_snd_5775_);
v___x_5786_ = lean_box(0);
v_isShared_5787_ = v_isSharedCheck_5827_;
goto v_resetjp_5785_;
}
v_resetjp_5785_:
{
uint8_t v___x_5788_; uint8_t v___x_5789_; uint8_t v___x_5790_; lean_object* v___x_5791_; 
v___x_5788_ = 0;
v___x_5789_ = 1;
v___x_5790_ = 1;
lean_inc(v_fst_5776_);
v___x_5791_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_5750_, v_fst_5776_, v___x_5788_, v___x_5789_, v___x_5788_, v___x_5789_, v___x_5790_, v___y_5752_, v___y_5753_, v___y_5754_, v___y_5755_);
lean_dec_ref(v_motiveArgs_5750_);
if (lean_obj_tag(v___x_5791_) == 0)
{
lean_object* v_a_5792_; lean_object* v___x_5793_; 
v_a_5792_ = lean_ctor_get(v___x_5791_, 0);
lean_inc(v_a_5792_);
lean_dec_ref(v___x_5791_);
v___x_5793_ = l_Lean_Meta_getLevel(v_fst_5776_, v___y_5752_, v___y_5753_, v___y_5754_, v___y_5755_);
if (lean_obj_tag(v___x_5793_) == 0)
{
lean_object* v_a_5794_; lean_object* v___x_5796_; uint8_t v_isShared_5797_; uint8_t v_isSharedCheck_5810_; 
v_a_5794_ = lean_ctor_get(v___x_5793_, 0);
v_isSharedCheck_5810_ = !lean_is_exclusive(v___x_5793_);
if (v_isSharedCheck_5810_ == 0)
{
v___x_5796_ = v___x_5793_;
v_isShared_5797_ = v_isSharedCheck_5810_;
goto v_resetjp_5795_;
}
else
{
lean_inc(v_a_5794_);
lean_dec(v___x_5793_);
v___x_5796_ = lean_box(0);
v_isShared_5797_ = v_isSharedCheck_5810_;
goto v_resetjp_5795_;
}
v_resetjp_5795_:
{
lean_object* v___x_5799_; 
if (v_isShared_5787_ == 0)
{
lean_ctor_set(v___x_5786_, 1, v_fst_5784_);
lean_ctor_set(v___x_5786_, 0, v_fst_5780_);
v___x_5799_ = v___x_5786_;
goto v_reusejp_5798_;
}
else
{
lean_object* v_reuseFailAlloc_5809_; 
v_reuseFailAlloc_5809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5809_, 0, v_fst_5780_);
lean_ctor_set(v_reuseFailAlloc_5809_, 1, v_fst_5784_);
v___x_5799_ = v_reuseFailAlloc_5809_;
goto v_reusejp_5798_;
}
v_reusejp_5798_:
{
lean_object* v___x_5801_; 
if (v_isShared_5783_ == 0)
{
lean_ctor_set(v___x_5782_, 1, v___x_5799_);
lean_ctor_set(v___x_5782_, 0, v_a_5794_);
v___x_5801_ = v___x_5782_;
goto v_reusejp_5800_;
}
else
{
lean_object* v_reuseFailAlloc_5808_; 
v_reuseFailAlloc_5808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5808_, 0, v_a_5794_);
lean_ctor_set(v_reuseFailAlloc_5808_, 1, v___x_5799_);
v___x_5801_ = v_reuseFailAlloc_5808_;
goto v_reusejp_5800_;
}
v_reusejp_5800_:
{
lean_object* v___x_5803_; 
if (v_isShared_5779_ == 0)
{
lean_ctor_set(v___x_5778_, 1, v___x_5801_);
lean_ctor_set(v___x_5778_, 0, v_a_5792_);
v___x_5803_ = v___x_5778_;
goto v_reusejp_5802_;
}
else
{
lean_object* v_reuseFailAlloc_5807_; 
v_reuseFailAlloc_5807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5807_, 0, v_a_5792_);
lean_ctor_set(v_reuseFailAlloc_5807_, 1, v___x_5801_);
v___x_5803_ = v_reuseFailAlloc_5807_;
goto v_reusejp_5802_;
}
v_reusejp_5802_:
{
lean_object* v___x_5805_; 
if (v_isShared_5797_ == 0)
{
lean_ctor_set(v___x_5796_, 0, v___x_5803_);
v___x_5805_ = v___x_5796_;
goto v_reusejp_5804_;
}
else
{
lean_object* v_reuseFailAlloc_5806_; 
v_reuseFailAlloc_5806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5806_, 0, v___x_5803_);
v___x_5805_ = v_reuseFailAlloc_5806_;
goto v_reusejp_5804_;
}
v_reusejp_5804_:
{
return v___x_5805_;
}
}
}
}
}
}
else
{
lean_object* v_a_5811_; lean_object* v___x_5813_; uint8_t v_isShared_5814_; uint8_t v_isSharedCheck_5818_; 
lean_dec(v_a_5792_);
lean_del_object(v___x_5786_);
lean_dec(v_fst_5784_);
lean_del_object(v___x_5782_);
lean_dec(v_fst_5780_);
lean_del_object(v___x_5778_);
v_a_5811_ = lean_ctor_get(v___x_5793_, 0);
v_isSharedCheck_5818_ = !lean_is_exclusive(v___x_5793_);
if (v_isSharedCheck_5818_ == 0)
{
v___x_5813_ = v___x_5793_;
v_isShared_5814_ = v_isSharedCheck_5818_;
goto v_resetjp_5812_;
}
else
{
lean_inc(v_a_5811_);
lean_dec(v___x_5793_);
v___x_5813_ = lean_box(0);
v_isShared_5814_ = v_isSharedCheck_5818_;
goto v_resetjp_5812_;
}
v_resetjp_5812_:
{
lean_object* v___x_5816_; 
if (v_isShared_5814_ == 0)
{
v___x_5816_ = v___x_5813_;
goto v_reusejp_5815_;
}
else
{
lean_object* v_reuseFailAlloc_5817_; 
v_reuseFailAlloc_5817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5817_, 0, v_a_5811_);
v___x_5816_ = v_reuseFailAlloc_5817_;
goto v_reusejp_5815_;
}
v_reusejp_5815_:
{
return v___x_5816_;
}
}
}
}
else
{
lean_object* v_a_5819_; lean_object* v___x_5821_; uint8_t v_isShared_5822_; uint8_t v_isSharedCheck_5826_; 
lean_del_object(v___x_5786_);
lean_dec(v_fst_5784_);
lean_del_object(v___x_5782_);
lean_dec(v_fst_5780_);
lean_del_object(v___x_5778_);
lean_dec(v_fst_5776_);
lean_dec(v___y_5755_);
lean_dec_ref(v___y_5754_);
lean_dec(v___y_5753_);
lean_dec_ref(v___y_5752_);
v_a_5819_ = lean_ctor_get(v___x_5791_, 0);
v_isSharedCheck_5826_ = !lean_is_exclusive(v___x_5791_);
if (v_isSharedCheck_5826_ == 0)
{
v___x_5821_ = v___x_5791_;
v_isShared_5822_ = v_isSharedCheck_5826_;
goto v_resetjp_5820_;
}
else
{
lean_inc(v_a_5819_);
lean_dec(v___x_5791_);
v___x_5821_ = lean_box(0);
v_isShared_5822_ = v_isSharedCheck_5826_;
goto v_resetjp_5820_;
}
v_resetjp_5820_:
{
lean_object* v___x_5824_; 
if (v_isShared_5822_ == 0)
{
v___x_5824_ = v___x_5821_;
goto v_reusejp_5823_;
}
else
{
lean_object* v_reuseFailAlloc_5825_; 
v_reuseFailAlloc_5825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5825_, 0, v_a_5819_);
v___x_5824_ = v_reuseFailAlloc_5825_;
goto v_reusejp_5823_;
}
v_reusejp_5823_:
{
return v___x_5824_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5833_; lean_object* v___x_5835_; uint8_t v_isShared_5836_; uint8_t v_isSharedCheck_5840_; 
lean_dec(v___y_5755_);
lean_dec_ref(v___y_5754_);
lean_dec(v___y_5753_);
lean_dec_ref(v___y_5752_);
lean_dec_ref(v_motiveArgs_5750_);
v_a_5833_ = lean_ctor_get(v___x_5772_, 0);
v_isSharedCheck_5840_ = !lean_is_exclusive(v___x_5772_);
if (v_isSharedCheck_5840_ == 0)
{
v___x_5835_ = v___x_5772_;
v_isShared_5836_ = v_isSharedCheck_5840_;
goto v_resetjp_5834_;
}
else
{
lean_inc(v_a_5833_);
lean_dec(v___x_5772_);
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
lean_object* v_a_5841_; lean_object* v___x_5843_; uint8_t v_isShared_5844_; uint8_t v_isSharedCheck_5848_; 
lean_dec(v___y_5755_);
lean_dec_ref(v___y_5754_);
lean_dec(v___y_5753_);
lean_dec_ref(v___y_5752_);
lean_dec_ref(v_motiveArgs_5750_);
lean_dec_ref(v_a_5746_);
lean_dec_ref(v_toMatcherInfo_5745_);
v_a_5841_ = lean_ctor_get(v___x_5758_, 0);
v_isSharedCheck_5848_ = !lean_is_exclusive(v___x_5758_);
if (v_isSharedCheck_5848_ == 0)
{
v___x_5843_ = v___x_5758_;
v_isShared_5844_ = v_isSharedCheck_5848_;
goto v_resetjp_5842_;
}
else
{
lean_inc(v_a_5841_);
lean_dec(v___x_5758_);
v___x_5843_ = lean_box(0);
v_isShared_5844_ = v_isSharedCheck_5848_;
goto v_resetjp_5842_;
}
v_resetjp_5842_:
{
lean_object* v___x_5846_; 
if (v_isShared_5844_ == 0)
{
v___x_5846_ = v___x_5843_;
goto v_reusejp_5845_;
}
else
{
lean_object* v_reuseFailAlloc_5847_; 
v_reuseFailAlloc_5847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5847_, 0, v_a_5841_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed(lean_object* v_onMotive_5868_, lean_object* v_toMatcherInfo_5869_, lean_object* v_a_5870_, lean_object* v_addEqualities_5871_, lean_object* v___x_5872_, lean_object* v_discrs_5873_, lean_object* v_motiveArgs_5874_, lean_object* v_motiveBody_5875_, lean_object* v___y_5876_, lean_object* v___y_5877_, lean_object* v___y_5878_, lean_object* v___y_5879_, lean_object* v___y_5880_){
_start:
{
uint8_t v_addEqualities_boxed_5881_; size_t v___x_34577__boxed_5882_; lean_object* v_res_5883_; 
v_addEqualities_boxed_5881_ = lean_unbox(v_addEqualities_5871_);
v___x_34577__boxed_5882_ = lean_unbox_usize(v___x_5872_);
lean_dec(v___x_5872_);
v_res_5883_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(v_onMotive_5868_, v_toMatcherInfo_5869_, v_a_5870_, v_addEqualities_boxed_5881_, v___x_34577__boxed_5882_, v_discrs_5873_, v_motiveArgs_5874_, v_motiveBody_5875_, v___y_5876_, v___y_5877_, v___y_5878_, v___y_5879_);
lean_dec_ref(v_discrs_5873_);
return v_res_5883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(lean_object* v_as_5884_, size_t v_sz_5885_, size_t v_i_5886_, lean_object* v_b_5887_, lean_object* v___y_5888_, lean_object* v___y_5889_, lean_object* v___y_5890_, lean_object* v___y_5891_){
_start:
{
lean_object* v_a_5894_; uint8_t v___x_5898_; 
v___x_5898_ = lean_usize_dec_lt(v_i_5886_, v_sz_5885_);
if (v___x_5898_ == 0)
{
lean_object* v___x_5899_; 
lean_dec(v___y_5891_);
lean_dec_ref(v___y_5890_);
lean_dec(v___y_5889_);
lean_dec_ref(v___y_5888_);
v___x_5899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5899_, 0, v_b_5887_);
return v___x_5899_;
}
else
{
lean_object* v_snd_5900_; lean_object* v_snd_5901_; lean_object* v_fst_5902_; lean_object* v___x_5904_; uint8_t v_isShared_5905_; uint8_t v_isSharedCheck_5962_; 
v_snd_5900_ = lean_ctor_get(v_b_5887_, 1);
lean_inc(v_snd_5900_);
v_snd_5901_ = lean_ctor_get(v_snd_5900_, 1);
lean_inc(v_snd_5901_);
v_fst_5902_ = lean_ctor_get(v_b_5887_, 0);
v_isSharedCheck_5962_ = !lean_is_exclusive(v_b_5887_);
if (v_isSharedCheck_5962_ == 0)
{
lean_object* v_unused_5963_; 
v_unused_5963_ = lean_ctor_get(v_b_5887_, 1);
lean_dec(v_unused_5963_);
v___x_5904_ = v_b_5887_;
v_isShared_5905_ = v_isSharedCheck_5962_;
goto v_resetjp_5903_;
}
else
{
lean_inc(v_fst_5902_);
lean_dec(v_b_5887_);
v___x_5904_ = lean_box(0);
v_isShared_5905_ = v_isSharedCheck_5962_;
goto v_resetjp_5903_;
}
v_resetjp_5903_:
{
lean_object* v_fst_5906_; lean_object* v___x_5908_; uint8_t v_isShared_5909_; uint8_t v_isSharedCheck_5960_; 
v_fst_5906_ = lean_ctor_get(v_snd_5900_, 0);
v_isSharedCheck_5960_ = !lean_is_exclusive(v_snd_5900_);
if (v_isSharedCheck_5960_ == 0)
{
lean_object* v_unused_5961_; 
v_unused_5961_ = lean_ctor_get(v_snd_5900_, 1);
lean_dec(v_unused_5961_);
v___x_5908_ = v_snd_5900_;
v_isShared_5909_ = v_isSharedCheck_5960_;
goto v_resetjp_5907_;
}
else
{
lean_inc(v_fst_5906_);
lean_dec(v_snd_5900_);
v___x_5908_ = lean_box(0);
v_isShared_5909_ = v_isSharedCheck_5960_;
goto v_resetjp_5907_;
}
v_resetjp_5907_:
{
lean_object* v_array_5910_; lean_object* v_start_5911_; lean_object* v_stop_5912_; uint8_t v___x_5913_; 
v_array_5910_ = lean_ctor_get(v_snd_5901_, 0);
v_start_5911_ = lean_ctor_get(v_snd_5901_, 1);
v_stop_5912_ = lean_ctor_get(v_snd_5901_, 2);
v___x_5913_ = lean_nat_dec_lt(v_start_5911_, v_stop_5912_);
if (v___x_5913_ == 0)
{
lean_object* v___x_5915_; 
lean_dec(v___y_5891_);
lean_dec_ref(v___y_5890_);
lean_dec(v___y_5889_);
lean_dec_ref(v___y_5888_);
if (v_isShared_5909_ == 0)
{
v___x_5915_ = v___x_5908_;
goto v_reusejp_5914_;
}
else
{
lean_object* v_reuseFailAlloc_5920_; 
v_reuseFailAlloc_5920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5920_, 0, v_fst_5906_);
lean_ctor_set(v_reuseFailAlloc_5920_, 1, v_snd_5901_);
v___x_5915_ = v_reuseFailAlloc_5920_;
goto v_reusejp_5914_;
}
v_reusejp_5914_:
{
lean_object* v___x_5917_; 
if (v_isShared_5905_ == 0)
{
lean_ctor_set(v___x_5904_, 1, v___x_5915_);
v___x_5917_ = v___x_5904_;
goto v_reusejp_5916_;
}
else
{
lean_object* v_reuseFailAlloc_5919_; 
v_reuseFailAlloc_5919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5919_, 0, v_fst_5902_);
lean_ctor_set(v_reuseFailAlloc_5919_, 1, v___x_5915_);
v___x_5917_ = v_reuseFailAlloc_5919_;
goto v_reusejp_5916_;
}
v_reusejp_5916_:
{
lean_object* v___x_5918_; 
v___x_5918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5918_, 0, v___x_5917_);
return v___x_5918_;
}
}
}
else
{
lean_object* v___x_5922_; uint8_t v_isShared_5923_; uint8_t v_isSharedCheck_5956_; 
lean_inc(v_stop_5912_);
lean_inc(v_start_5911_);
lean_inc_ref(v_array_5910_);
v_isSharedCheck_5956_ = !lean_is_exclusive(v_snd_5901_);
if (v_isSharedCheck_5956_ == 0)
{
lean_object* v_unused_5957_; lean_object* v_unused_5958_; lean_object* v_unused_5959_; 
v_unused_5957_ = lean_ctor_get(v_snd_5901_, 2);
lean_dec(v_unused_5957_);
v_unused_5958_ = lean_ctor_get(v_snd_5901_, 1);
lean_dec(v_unused_5958_);
v_unused_5959_ = lean_ctor_get(v_snd_5901_, 0);
lean_dec(v_unused_5959_);
v___x_5922_ = v_snd_5901_;
v_isShared_5923_ = v_isSharedCheck_5956_;
goto v_resetjp_5921_;
}
else
{
lean_dec(v_snd_5901_);
v___x_5922_ = lean_box(0);
v_isShared_5923_ = v_isSharedCheck_5956_;
goto v_resetjp_5921_;
}
v_resetjp_5921_:
{
lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5928_; 
v___x_5924_ = lean_array_fget(v_array_5910_, v_start_5911_);
v___x_5925_ = lean_unsigned_to_nat(1u);
v___x_5926_ = lean_nat_add(v_start_5911_, v___x_5925_);
lean_dec(v_start_5911_);
if (v_isShared_5923_ == 0)
{
lean_ctor_set(v___x_5922_, 1, v___x_5926_);
v___x_5928_ = v___x_5922_;
goto v_reusejp_5927_;
}
else
{
lean_object* v_reuseFailAlloc_5955_; 
v_reuseFailAlloc_5955_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5955_, 0, v_array_5910_);
lean_ctor_set(v_reuseFailAlloc_5955_, 1, v___x_5926_);
lean_ctor_set(v_reuseFailAlloc_5955_, 2, v_stop_5912_);
v___x_5928_ = v_reuseFailAlloc_5955_;
goto v_reusejp_5927_;
}
v_reusejp_5927_:
{
lean_object* v___y_5930_; 
if (lean_obj_tag(v___x_5924_) == 0)
{
lean_object* v___x_5948_; lean_object* v___x_5949_; 
lean_del_object(v___x_5908_);
lean_del_object(v___x_5904_);
v___x_5948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5948_, 0, v_fst_5906_);
lean_ctor_set(v___x_5948_, 1, v___x_5928_);
v___x_5949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5949_, 0, v_fst_5902_);
lean_ctor_set(v___x_5949_, 1, v___x_5948_);
v_a_5894_ = v___x_5949_;
goto v___jp_5893_;
}
else
{
lean_object* v_val_5950_; lean_object* v_a_5951_; uint8_t v___x_5952_; 
v_val_5950_ = lean_ctor_get(v___x_5924_, 0);
lean_inc(v_val_5950_);
lean_dec_ref(v___x_5924_);
v_a_5951_ = lean_array_uget_borrowed(v_as_5884_, v_i_5886_);
v___x_5952_ = lean_unbox(v_val_5950_);
lean_dec(v_val_5950_);
if (v___x_5952_ == 0)
{
lean_object* v___x_5953_; 
lean_inc(v___y_5891_);
lean_inc_ref(v___y_5890_);
lean_inc(v___y_5889_);
lean_inc_ref(v___y_5888_);
lean_inc(v_a_5951_);
v___x_5953_ = l_Lean_Meta_mkEqRefl(v_a_5951_, v___y_5888_, v___y_5889_, v___y_5890_, v___y_5891_);
v___y_5930_ = v___x_5953_;
goto v___jp_5929_;
}
else
{
lean_object* v___x_5954_; 
lean_inc(v___y_5891_);
lean_inc_ref(v___y_5890_);
lean_inc(v___y_5889_);
lean_inc_ref(v___y_5888_);
lean_inc(v_a_5951_);
v___x_5954_ = l_Lean_Meta_mkHEqRefl(v_a_5951_, v___y_5888_, v___y_5889_, v___y_5890_, v___y_5891_);
v___y_5930_ = v___x_5954_;
goto v___jp_5929_;
}
}
v___jp_5929_:
{
if (lean_obj_tag(v___y_5930_) == 0)
{
lean_object* v_a_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5935_; 
v_a_5931_ = lean_ctor_get(v___y_5930_, 0);
lean_inc(v_a_5931_);
lean_dec_ref(v___y_5930_);
v___x_5932_ = lean_array_push(v_fst_5902_, v_a_5931_);
v___x_5933_ = lean_nat_add(v_fst_5906_, v___x_5925_);
lean_dec(v_fst_5906_);
if (v_isShared_5909_ == 0)
{
lean_ctor_set(v___x_5908_, 1, v___x_5928_);
lean_ctor_set(v___x_5908_, 0, v___x_5933_);
v___x_5935_ = v___x_5908_;
goto v_reusejp_5934_;
}
else
{
lean_object* v_reuseFailAlloc_5939_; 
v_reuseFailAlloc_5939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5939_, 0, v___x_5933_);
lean_ctor_set(v_reuseFailAlloc_5939_, 1, v___x_5928_);
v___x_5935_ = v_reuseFailAlloc_5939_;
goto v_reusejp_5934_;
}
v_reusejp_5934_:
{
lean_object* v___x_5937_; 
if (v_isShared_5905_ == 0)
{
lean_ctor_set(v___x_5904_, 1, v___x_5935_);
lean_ctor_set(v___x_5904_, 0, v___x_5932_);
v___x_5937_ = v___x_5904_;
goto v_reusejp_5936_;
}
else
{
lean_object* v_reuseFailAlloc_5938_; 
v_reuseFailAlloc_5938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5938_, 0, v___x_5932_);
lean_ctor_set(v_reuseFailAlloc_5938_, 1, v___x_5935_);
v___x_5937_ = v_reuseFailAlloc_5938_;
goto v_reusejp_5936_;
}
v_reusejp_5936_:
{
v_a_5894_ = v___x_5937_;
goto v___jp_5893_;
}
}
}
else
{
lean_object* v_a_5940_; lean_object* v___x_5942_; uint8_t v_isShared_5943_; uint8_t v_isSharedCheck_5947_; 
lean_dec_ref(v___x_5928_);
lean_del_object(v___x_5908_);
lean_dec(v_fst_5906_);
lean_del_object(v___x_5904_);
lean_dec(v_fst_5902_);
lean_dec(v___y_5891_);
lean_dec_ref(v___y_5890_);
lean_dec(v___y_5889_);
lean_dec_ref(v___y_5888_);
v_a_5940_ = lean_ctor_get(v___y_5930_, 0);
v_isSharedCheck_5947_ = !lean_is_exclusive(v___y_5930_);
if (v_isSharedCheck_5947_ == 0)
{
v___x_5942_ = v___y_5930_;
v_isShared_5943_ = v_isSharedCheck_5947_;
goto v_resetjp_5941_;
}
else
{
lean_inc(v_a_5940_);
lean_dec(v___y_5930_);
v___x_5942_ = lean_box(0);
v_isShared_5943_ = v_isSharedCheck_5947_;
goto v_resetjp_5941_;
}
v_resetjp_5941_:
{
lean_object* v___x_5945_; 
if (v_isShared_5943_ == 0)
{
v___x_5945_ = v___x_5942_;
goto v_reusejp_5944_;
}
else
{
lean_object* v_reuseFailAlloc_5946_; 
v_reuseFailAlloc_5946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5946_, 0, v_a_5940_);
v___x_5945_ = v_reuseFailAlloc_5946_;
goto v_reusejp_5944_;
}
v_reusejp_5944_:
{
return v___x_5945_;
}
}
}
}
}
}
}
}
}
}
v___jp_5893_:
{
size_t v___x_5895_; size_t v___x_5896_; 
v___x_5895_ = ((size_t)1ULL);
v___x_5896_ = lean_usize_add(v_i_5886_, v___x_5895_);
v_i_5886_ = v___x_5896_;
v_b_5887_ = v_a_5894_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8___boxed(lean_object* v_as_5964_, lean_object* v_sz_5965_, lean_object* v_i_5966_, lean_object* v_b_5967_, lean_object* v___y_5968_, lean_object* v___y_5969_, lean_object* v___y_5970_, lean_object* v___y_5971_, lean_object* v___y_5972_){
_start:
{
size_t v_sz_boxed_5973_; size_t v_i_boxed_5974_; lean_object* v_res_5975_; 
v_sz_boxed_5973_ = lean_unbox_usize(v_sz_5965_);
lean_dec(v_sz_5965_);
v_i_boxed_5974_ = lean_unbox_usize(v_i_5966_);
lean_dec(v_i_5966_);
v_res_5975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(v_as_5964_, v_sz_boxed_5973_, v_i_boxed_5974_, v_b_5967_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_);
lean_dec_ref(v_as_5964_);
return v_res_5975_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(lean_object* v___x_5976_, lean_object* v___y_5977_, lean_object* v___y_5978_, lean_object* v___y_5979_, lean_object* v___y_5980_){
_start:
{
lean_object* v___x_5982_; 
v___x_5982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5982_, 0, v___x_5976_);
return v___x_5982_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed(lean_object* v___x_5983_, lean_object* v___y_5984_, lean_object* v___y_5985_, lean_object* v___y_5986_, lean_object* v___y_5987_, lean_object* v___y_5988_){
_start:
{
lean_object* v_res_5989_; 
v_res_5989_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(v___x_5983_, v___y_5984_, v___y_5985_, v___y_5986_, v___y_5987_);
lean_dec(v___y_5987_);
lean_dec_ref(v___y_5986_);
lean_dec(v___y_5985_);
lean_dec_ref(v___y_5984_);
return v_res_5989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(size_t v_sz_5990_, size_t v_i_5991_, lean_object* v_bs_5992_, lean_object* v___y_5993_, lean_object* v___y_5994_, lean_object* v___y_5995_){
_start:
{
uint8_t v___x_5997_; 
v___x_5997_ = lean_usize_dec_lt(v_i_5991_, v_sz_5990_);
if (v___x_5997_ == 0)
{
lean_object* v___x_5998_; 
lean_dec_ref(v___y_5993_);
v___x_5998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5998_, 0, v_bs_5992_);
return v___x_5998_;
}
else
{
lean_object* v_v_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; 
v_v_5999_ = lean_array_uget_borrowed(v_bs_5992_, v_i_5991_);
v___x_6000_ = l_Lean_Expr_fvarId_x21(v_v_5999_);
lean_inc_ref(v___y_5993_);
v___x_6001_ = l_Lean_FVarId_getUserName___redArg(v___x_6000_, v___y_5993_, v___y_5994_, v___y_5995_);
if (lean_obj_tag(v___x_6001_) == 0)
{
lean_object* v_a_6002_; lean_object* v___x_6003_; lean_object* v_bs_x27_6004_; size_t v___x_6005_; size_t v___x_6006_; lean_object* v___x_6007_; 
v_a_6002_ = lean_ctor_get(v___x_6001_, 0);
lean_inc(v_a_6002_);
lean_dec_ref(v___x_6001_);
v___x_6003_ = lean_unsigned_to_nat(0u);
v_bs_x27_6004_ = lean_array_uset(v_bs_5992_, v_i_5991_, v___x_6003_);
v___x_6005_ = ((size_t)1ULL);
v___x_6006_ = lean_usize_add(v_i_5991_, v___x_6005_);
v___x_6007_ = lean_array_uset(v_bs_x27_6004_, v_i_5991_, v_a_6002_);
v_i_5991_ = v___x_6006_;
v_bs_5992_ = v___x_6007_;
goto _start;
}
else
{
lean_object* v_a_6009_; lean_object* v___x_6011_; uint8_t v_isShared_6012_; uint8_t v_isSharedCheck_6016_; 
lean_dec_ref(v___y_5993_);
lean_dec_ref(v_bs_5992_);
v_a_6009_ = lean_ctor_get(v___x_6001_, 0);
v_isSharedCheck_6016_ = !lean_is_exclusive(v___x_6001_);
if (v_isSharedCheck_6016_ == 0)
{
v___x_6011_ = v___x_6001_;
v_isShared_6012_ = v_isSharedCheck_6016_;
goto v_resetjp_6010_;
}
else
{
lean_inc(v_a_6009_);
lean_dec(v___x_6001_);
v___x_6011_ = lean_box(0);
v_isShared_6012_ = v_isSharedCheck_6016_;
goto v_resetjp_6010_;
}
v_resetjp_6010_:
{
lean_object* v___x_6014_; 
if (v_isShared_6012_ == 0)
{
v___x_6014_ = v___x_6011_;
goto v_reusejp_6013_;
}
else
{
lean_object* v_reuseFailAlloc_6015_; 
v_reuseFailAlloc_6015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6015_, 0, v_a_6009_);
v___x_6014_ = v_reuseFailAlloc_6015_;
goto v_reusejp_6013_;
}
v_reusejp_6013_:
{
return v___x_6014_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg___boxed(lean_object* v_sz_6017_, lean_object* v_i_6018_, lean_object* v_bs_6019_, lean_object* v___y_6020_, lean_object* v___y_6021_, lean_object* v___y_6022_, lean_object* v___y_6023_){
_start:
{
size_t v_sz_boxed_6024_; size_t v_i_boxed_6025_; lean_object* v_res_6026_; 
v_sz_boxed_6024_ = lean_unbox_usize(v_sz_6017_);
lean_dec(v_sz_6017_);
v_i_boxed_6025_ = lean_unbox_usize(v_i_6018_);
lean_dec(v_i_6018_);
v_res_6026_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_boxed_6024_, v_i_boxed_6025_, v_bs_6019_, v___y_6020_, v___y_6021_, v___y_6022_);
lean_dec(v___y_6022_);
lean_dec_ref(v___y_6021_);
return v_res_6026_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(lean_object* v_xs_6027_, lean_object* v_x_6028_, lean_object* v___y_6029_, lean_object* v___y_6030_, lean_object* v___y_6031_, lean_object* v___y_6032_){
_start:
{
size_t v_sz_6034_; size_t v___x_6035_; lean_object* v___x_6036_; 
v_sz_6034_ = lean_array_size(v_xs_6027_);
v___x_6035_ = ((size_t)0ULL);
v___x_6036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_6034_, v___x_6035_, v_xs_6027_, v___y_6029_, v___y_6031_, v___y_6032_);
return v___x_6036_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3___boxed(lean_object* v_xs_6037_, lean_object* v_x_6038_, lean_object* v___y_6039_, lean_object* v___y_6040_, lean_object* v___y_6041_, lean_object* v___y_6042_, lean_object* v___y_6043_){
_start:
{
lean_object* v_res_6044_; 
v_res_6044_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(v_xs_6037_, v_x_6038_, v___y_6039_, v___y_6040_, v___y_6041_, v___y_6042_);
lean_dec(v___y_6042_);
lean_dec_ref(v___y_6041_);
lean_dec(v___y_6040_);
lean_dec_ref(v_x_6038_);
return v_res_6044_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(lean_object* v___x_6045_, lean_object* v___x_6046_, lean_object* v___f_6047_, uint8_t v___x_6048_, lean_object* v_fst_6049_, lean_object* v___x_6050_, lean_object* v___x_6051_, lean_object* v___x_6052_, lean_object* v___y_6053_, lean_object* v___y_6054_, lean_object* v___y_6055_, lean_object* v___y_6056_){
_start:
{
lean_object* v___x_6058_; 
v___x_6058_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v___x_6045_, v___x_6046_, v___f_6047_, v___x_6048_, v___x_6048_, v___y_6053_, v___y_6054_, v___y_6055_, v___y_6056_);
if (lean_obj_tag(v___x_6058_) == 0)
{
lean_object* v_a_6059_; lean_object* v___x_6061_; uint8_t v_isShared_6062_; uint8_t v_isSharedCheck_6071_; 
v_a_6059_ = lean_ctor_get(v___x_6058_, 0);
v_isSharedCheck_6071_ = !lean_is_exclusive(v___x_6058_);
if (v_isSharedCheck_6071_ == 0)
{
v___x_6061_ = v___x_6058_;
v_isShared_6062_ = v_isSharedCheck_6071_;
goto v_resetjp_6060_;
}
else
{
lean_inc(v_a_6059_);
lean_dec(v___x_6058_);
v___x_6061_ = lean_box(0);
v_isShared_6062_ = v_isSharedCheck_6071_;
goto v_resetjp_6060_;
}
v_resetjp_6060_:
{
lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6069_; 
v___x_6063_ = lean_array_push(v_fst_6049_, v_a_6059_);
v___x_6064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6064_, 0, v___x_6050_);
lean_ctor_set(v___x_6064_, 1, v___x_6051_);
v___x_6065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6065_, 0, v___x_6052_);
lean_ctor_set(v___x_6065_, 1, v___x_6064_);
v___x_6066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6066_, 0, v___x_6063_);
lean_ctor_set(v___x_6066_, 1, v___x_6065_);
v___x_6067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6067_, 0, v___x_6066_);
if (v_isShared_6062_ == 0)
{
lean_ctor_set(v___x_6061_, 0, v___x_6067_);
v___x_6069_ = v___x_6061_;
goto v_reusejp_6068_;
}
else
{
lean_object* v_reuseFailAlloc_6070_; 
v_reuseFailAlloc_6070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6070_, 0, v___x_6067_);
v___x_6069_ = v_reuseFailAlloc_6070_;
goto v_reusejp_6068_;
}
v_reusejp_6068_:
{
return v___x_6069_;
}
}
}
else
{
lean_object* v_a_6072_; lean_object* v___x_6074_; uint8_t v_isShared_6075_; uint8_t v_isSharedCheck_6079_; 
lean_dec_ref(v___x_6052_);
lean_dec_ref(v___x_6051_);
lean_dec_ref(v___x_6050_);
lean_dec(v_fst_6049_);
v_a_6072_ = lean_ctor_get(v___x_6058_, 0);
v_isSharedCheck_6079_ = !lean_is_exclusive(v___x_6058_);
if (v_isSharedCheck_6079_ == 0)
{
v___x_6074_ = v___x_6058_;
v_isShared_6075_ = v_isSharedCheck_6079_;
goto v_resetjp_6073_;
}
else
{
lean_inc(v_a_6072_);
lean_dec(v___x_6058_);
v___x_6074_ = lean_box(0);
v_isShared_6075_ = v_isSharedCheck_6079_;
goto v_resetjp_6073_;
}
v_resetjp_6073_:
{
lean_object* v___x_6077_; 
if (v_isShared_6075_ == 0)
{
v___x_6077_ = v___x_6074_;
goto v_reusejp_6076_;
}
else
{
lean_object* v_reuseFailAlloc_6078_; 
v_reuseFailAlloc_6078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6078_, 0, v_a_6072_);
v___x_6077_ = v_reuseFailAlloc_6078_;
goto v_reusejp_6076_;
}
v_reusejp_6076_:
{
return v___x_6077_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed(lean_object* v___x_6080_, lean_object* v___x_6081_, lean_object* v___f_6082_, lean_object* v___x_6083_, lean_object* v_fst_6084_, lean_object* v___x_6085_, lean_object* v___x_6086_, lean_object* v___x_6087_, lean_object* v___y_6088_, lean_object* v___y_6089_, lean_object* v___y_6090_, lean_object* v___y_6091_, lean_object* v___y_6092_){
_start:
{
uint8_t v___x_35040__boxed_6093_; lean_object* v_res_6094_; 
v___x_35040__boxed_6093_ = lean_unbox(v___x_6083_);
v_res_6094_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(v___x_6080_, v___x_6081_, v___f_6082_, v___x_35040__boxed_6093_, v_fst_6084_, v___x_6085_, v___x_6086_, v___x_6087_, v___y_6088_, v___y_6089_, v___y_6090_, v___y_6091_);
return v_res_6094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(lean_object* v_fvars_6095_, lean_object* v_names_6096_, lean_object* v_k_6097_, lean_object* v___y_6098_, lean_object* v___y_6099_, lean_object* v___y_6100_, lean_object* v___y_6101_){
_start:
{
lean_object* v___x_6103_; 
v___x_6103_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_6095_, v_names_6096_, v_k_6097_, v___y_6098_, v___y_6099_, v___y_6100_, v___y_6101_);
if (lean_obj_tag(v___x_6103_) == 0)
{
lean_object* v_a_6104_; lean_object* v___x_6106_; uint8_t v_isShared_6107_; uint8_t v_isSharedCheck_6111_; 
v_a_6104_ = lean_ctor_get(v___x_6103_, 0);
v_isSharedCheck_6111_ = !lean_is_exclusive(v___x_6103_);
if (v_isSharedCheck_6111_ == 0)
{
v___x_6106_ = v___x_6103_;
v_isShared_6107_ = v_isSharedCheck_6111_;
goto v_resetjp_6105_;
}
else
{
lean_inc(v_a_6104_);
lean_dec(v___x_6103_);
v___x_6106_ = lean_box(0);
v_isShared_6107_ = v_isSharedCheck_6111_;
goto v_resetjp_6105_;
}
v_resetjp_6105_:
{
lean_object* v___x_6109_; 
if (v_isShared_6107_ == 0)
{
v___x_6109_ = v___x_6106_;
goto v_reusejp_6108_;
}
else
{
lean_object* v_reuseFailAlloc_6110_; 
v_reuseFailAlloc_6110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6110_, 0, v_a_6104_);
v___x_6109_ = v_reuseFailAlloc_6110_;
goto v_reusejp_6108_;
}
v_reusejp_6108_:
{
return v___x_6109_;
}
}
}
else
{
lean_object* v_a_6112_; lean_object* v___x_6114_; uint8_t v_isShared_6115_; uint8_t v_isSharedCheck_6119_; 
v_a_6112_ = lean_ctor_get(v___x_6103_, 0);
v_isSharedCheck_6119_ = !lean_is_exclusive(v___x_6103_);
if (v_isSharedCheck_6119_ == 0)
{
v___x_6114_ = v___x_6103_;
v_isShared_6115_ = v_isSharedCheck_6119_;
goto v_resetjp_6113_;
}
else
{
lean_inc(v_a_6112_);
lean_dec(v___x_6103_);
v___x_6114_ = lean_box(0);
v_isShared_6115_ = v_isSharedCheck_6119_;
goto v_resetjp_6113_;
}
v_resetjp_6113_:
{
lean_object* v___x_6117_; 
if (v_isShared_6115_ == 0)
{
v___x_6117_ = v___x_6114_;
goto v_reusejp_6116_;
}
else
{
lean_object* v_reuseFailAlloc_6118_; 
v_reuseFailAlloc_6118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6118_, 0, v_a_6112_);
v___x_6117_ = v_reuseFailAlloc_6118_;
goto v_reusejp_6116_;
}
v_reusejp_6116_:
{
return v___x_6117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg___boxed(lean_object* v_fvars_6120_, lean_object* v_names_6121_, lean_object* v_k_6122_, lean_object* v___y_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_){
_start:
{
lean_object* v_res_6128_; 
v_res_6128_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_fvars_6120_, v_names_6121_, v_k_6122_, v___y_6123_, v___y_6124_, v___y_6125_, v___y_6126_);
lean_dec_ref(v_names_6121_);
lean_dec_ref(v_fvars_6120_);
return v_res_6128_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(lean_object* v___x_6129_, lean_object* v_xs_6130_, lean_object* v_onAlt_6131_, lean_object* v_a_6132_, lean_object* v_altType_6133_, lean_object* v_ys4_6134_, uint8_t v___x_6135_, uint8_t v___x_6136_, lean_object* v___y_6137_, lean_object* v___y_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_){
_start:
{
lean_object* v___x_6142_; 
lean_inc(v___y_6140_);
lean_inc_ref(v___y_6139_);
lean_inc(v___y_6138_);
lean_inc_ref(v___y_6137_);
v___x_6142_ = l_Lean_Meta_instantiateLambda(v___x_6129_, v_xs_6130_, v___y_6137_, v___y_6138_, v___y_6139_, v___y_6140_);
if (lean_obj_tag(v___x_6142_) == 0)
{
lean_object* v_a_6143_; lean_object* v___x_6144_; 
v_a_6143_ = lean_ctor_get(v___x_6142_, 0);
lean_inc(v_a_6143_);
lean_dec_ref(v___x_6142_);
lean_inc(v___y_6140_);
lean_inc_ref(v___y_6139_);
lean_inc(v___y_6138_);
lean_inc_ref(v___y_6137_);
lean_inc_ref(v_xs_6130_);
v___x_6144_ = lean_apply_9(v_onAlt_6131_, v_a_6132_, v_altType_6133_, v_xs_6130_, v_a_6143_, v___y_6137_, v___y_6138_, v___y_6139_, v___y_6140_, lean_box(0));
if (lean_obj_tag(v___x_6144_) == 0)
{
lean_object* v_a_6145_; lean_object* v___x_6146_; uint8_t v___x_6147_; lean_object* v___x_6148_; 
v_a_6145_ = lean_ctor_get(v___x_6144_, 0);
lean_inc(v_a_6145_);
lean_dec_ref(v___x_6144_);
v___x_6146_ = l_Array_append___redArg(v_xs_6130_, v_ys4_6134_);
v___x_6147_ = 1;
v___x_6148_ = l_Lean_Meta_mkLambdaFVars(v___x_6146_, v_a_6145_, v___x_6135_, v___x_6136_, v___x_6135_, v___x_6136_, v___x_6147_, v___y_6137_, v___y_6138_, v___y_6139_, v___y_6140_);
lean_dec(v___y_6140_);
lean_dec_ref(v___y_6139_);
lean_dec(v___y_6138_);
lean_dec_ref(v___y_6137_);
lean_dec_ref(v___x_6146_);
return v___x_6148_;
}
else
{
lean_dec(v___y_6140_);
lean_dec_ref(v___y_6139_);
lean_dec(v___y_6138_);
lean_dec_ref(v___y_6137_);
lean_dec_ref(v_xs_6130_);
return v___x_6144_;
}
}
else
{
lean_dec(v___y_6140_);
lean_dec_ref(v___y_6139_);
lean_dec(v___y_6138_);
lean_dec_ref(v___y_6137_);
lean_dec_ref(v_altType_6133_);
lean_dec(v_a_6132_);
lean_dec_ref(v_onAlt_6131_);
lean_dec_ref(v_xs_6130_);
return v___x_6142_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed(lean_object* v___x_6149_, lean_object* v_xs_6150_, lean_object* v_onAlt_6151_, lean_object* v_a_6152_, lean_object* v_altType_6153_, lean_object* v_ys4_6154_, lean_object* v___x_6155_, lean_object* v___x_6156_, lean_object* v___y_6157_, lean_object* v___y_6158_, lean_object* v___y_6159_, lean_object* v___y_6160_, lean_object* v___y_6161_){
_start:
{
uint8_t v___x_35167__boxed_6162_; uint8_t v___x_35168__boxed_6163_; lean_object* v_res_6164_; 
v___x_35167__boxed_6162_ = lean_unbox(v___x_6155_);
v___x_35168__boxed_6163_ = lean_unbox(v___x_6156_);
v_res_6164_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(v___x_6149_, v_xs_6150_, v_onAlt_6151_, v_a_6152_, v_altType_6153_, v_ys4_6154_, v___x_35167__boxed_6162_, v___x_35168__boxed_6163_, v___y_6157_, v___y_6158_, v___y_6159_, v___y_6160_);
lean_dec_ref(v_ys4_6154_);
return v_res_6164_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(lean_object* v___x_6165_, lean_object* v___f_6166_, uint8_t v___x_6167_, lean_object* v_xs_6168_, lean_object* v_onAlt_6169_, lean_object* v_a_6170_, uint8_t v___x_6171_, lean_object* v_ys4_6172_, lean_object* v_altType_6173_, lean_object* v___y_6174_, lean_object* v___y_6175_, lean_object* v___y_6176_, lean_object* v___y_6177_){
_start:
{
lean_object* v___x_6179_; 
lean_inc(v___y_6177_);
lean_inc_ref(v___y_6176_);
lean_inc(v___y_6175_);
lean_inc_ref(v___y_6174_);
lean_inc_ref(v___x_6165_);
v___x_6179_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v___x_6165_, v___f_6166_, v___x_6167_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_);
if (lean_obj_tag(v___x_6179_) == 0)
{
lean_object* v_a_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; lean_object* v___f_6183_; lean_object* v___x_6184_; 
v_a_6180_ = lean_ctor_get(v___x_6179_, 0);
lean_inc(v_a_6180_);
lean_dec_ref(v___x_6179_);
v___x_6181_ = lean_box(v___x_6167_);
v___x_6182_ = lean_box(v___x_6171_);
lean_inc_ref(v_xs_6168_);
v___f_6183_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed), 13, 8);
lean_closure_set(v___f_6183_, 0, v___x_6165_);
lean_closure_set(v___f_6183_, 1, v_xs_6168_);
lean_closure_set(v___f_6183_, 2, v_onAlt_6169_);
lean_closure_set(v___f_6183_, 3, v_a_6170_);
lean_closure_set(v___f_6183_, 4, v_altType_6173_);
lean_closure_set(v___f_6183_, 5, v_ys4_6172_);
lean_closure_set(v___f_6183_, 6, v___x_6181_);
lean_closure_set(v___f_6183_, 7, v___x_6182_);
v___x_6184_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_xs_6168_, v_a_6180_, v___f_6183_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_);
lean_dec(v_a_6180_);
lean_dec_ref(v_xs_6168_);
return v___x_6184_;
}
else
{
lean_object* v_a_6185_; lean_object* v___x_6187_; uint8_t v_isShared_6188_; uint8_t v_isSharedCheck_6192_; 
lean_dec(v___y_6177_);
lean_dec_ref(v___y_6176_);
lean_dec(v___y_6175_);
lean_dec_ref(v___y_6174_);
lean_dec_ref(v_altType_6173_);
lean_dec_ref(v_ys4_6172_);
lean_dec(v_a_6170_);
lean_dec_ref(v_onAlt_6169_);
lean_dec_ref(v_xs_6168_);
lean_dec_ref(v___x_6165_);
v_a_6185_ = lean_ctor_get(v___x_6179_, 0);
v_isSharedCheck_6192_ = !lean_is_exclusive(v___x_6179_);
if (v_isSharedCheck_6192_ == 0)
{
v___x_6187_ = v___x_6179_;
v_isShared_6188_ = v_isSharedCheck_6192_;
goto v_resetjp_6186_;
}
else
{
lean_inc(v_a_6185_);
lean_dec(v___x_6179_);
v___x_6187_ = lean_box(0);
v_isShared_6188_ = v_isSharedCheck_6192_;
goto v_resetjp_6186_;
}
v_resetjp_6186_:
{
lean_object* v___x_6190_; 
if (v_isShared_6188_ == 0)
{
v___x_6190_ = v___x_6187_;
goto v_reusejp_6189_;
}
else
{
lean_object* v_reuseFailAlloc_6191_; 
v_reuseFailAlloc_6191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6191_, 0, v_a_6185_);
v___x_6190_ = v_reuseFailAlloc_6191_;
goto v_reusejp_6189_;
}
v_reusejp_6189_:
{
return v___x_6190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed(lean_object* v___x_6193_, lean_object* v___f_6194_, lean_object* v___x_6195_, lean_object* v_xs_6196_, lean_object* v_onAlt_6197_, lean_object* v_a_6198_, lean_object* v___x_6199_, lean_object* v_ys4_6200_, lean_object* v_altType_6201_, lean_object* v___y_6202_, lean_object* v___y_6203_, lean_object* v___y_6204_, lean_object* v___y_6205_, lean_object* v___y_6206_){
_start:
{
uint8_t v___x_35208__boxed_6207_; uint8_t v___x_35209__boxed_6208_; lean_object* v_res_6209_; 
v___x_35208__boxed_6207_ = lean_unbox(v___x_6195_);
v___x_35209__boxed_6208_ = lean_unbox(v___x_6199_);
v_res_6209_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(v___x_6193_, v___f_6194_, v___x_35208__boxed_6207_, v_xs_6196_, v_onAlt_6197_, v_a_6198_, v___x_35209__boxed_6208_, v_ys4_6200_, v_altType_6201_, v___y_6202_, v___y_6203_, v___y_6204_, v___y_6205_);
return v_res_6209_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(lean_object* v___x_6210_, lean_object* v___f_6211_, uint8_t v___x_6212_, lean_object* v_onAlt_6213_, lean_object* v_a_6214_, uint8_t v___x_6215_, lean_object* v_extraEqualities_6216_, lean_object* v_xs_6217_, lean_object* v_altType_6218_, lean_object* v___y_6219_, lean_object* v___y_6220_, lean_object* v___y_6221_, lean_object* v___y_6222_){
_start:
{
lean_object* v___x_6224_; lean_object* v___x_6225_; lean_object* v___f_6226_; lean_object* v___x_6227_; lean_object* v___x_6228_; 
v___x_6224_ = lean_box(v___x_6212_);
v___x_6225_ = lean_box(v___x_6215_);
v___f_6226_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed), 14, 7);
lean_closure_set(v___f_6226_, 0, v___x_6210_);
lean_closure_set(v___f_6226_, 1, v___f_6211_);
lean_closure_set(v___f_6226_, 2, v___x_6224_);
lean_closure_set(v___f_6226_, 3, v_xs_6217_);
lean_closure_set(v___f_6226_, 4, v_onAlt_6213_);
lean_closure_set(v___f_6226_, 5, v_a_6214_);
lean_closure_set(v___f_6226_, 6, v___x_6225_);
v___x_6227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6227_, 0, v_extraEqualities_6216_);
v___x_6228_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_6218_, v___x_6227_, v___f_6226_, v___x_6212_, v___x_6212_, v___y_6219_, v___y_6220_, v___y_6221_, v___y_6222_);
return v___x_6228_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed(lean_object* v___x_6229_, lean_object* v___f_6230_, lean_object* v___x_6231_, lean_object* v_onAlt_6232_, lean_object* v_a_6233_, lean_object* v___x_6234_, lean_object* v_extraEqualities_6235_, lean_object* v_xs_6236_, lean_object* v_altType_6237_, lean_object* v___y_6238_, lean_object* v___y_6239_, lean_object* v___y_6240_, lean_object* v___y_6241_, lean_object* v___y_6242_){
_start:
{
uint8_t v___x_35263__boxed_6243_; uint8_t v___x_35264__boxed_6244_; lean_object* v_res_6245_; 
v___x_35263__boxed_6243_ = lean_unbox(v___x_6231_);
v___x_35264__boxed_6244_ = lean_unbox(v___x_6234_);
v_res_6245_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(v___x_6229_, v___f_6230_, v___x_35263__boxed_6243_, v_onAlt_6232_, v_a_6233_, v___x_35264__boxed_6244_, v_extraEqualities_6235_, v_xs_6236_, v_altType_6237_, v___y_6238_, v___y_6239_, v___y_6240_, v___y_6241_);
return v_res_6245_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(lean_object* v_upperBound_6247_, lean_object* v_onAlt_6248_, lean_object* v_extraEqualities_6249_, lean_object* v_a_6250_, lean_object* v_b_6251_, lean_object* v___y_6252_, lean_object* v___y_6253_, lean_object* v___y_6254_, lean_object* v___y_6255_){
_start:
{
lean_object* v___y_6258_; uint8_t v___x_6281_; 
v___x_6281_ = lean_nat_dec_lt(v_a_6250_, v_upperBound_6247_);
if (v___x_6281_ == 0)
{
lean_object* v___x_6282_; 
lean_dec(v___y_6255_);
lean_dec_ref(v___y_6254_);
lean_dec(v___y_6253_);
lean_dec_ref(v___y_6252_);
lean_dec(v_a_6250_);
lean_dec(v_extraEqualities_6249_);
lean_dec_ref(v_onAlt_6248_);
v___x_6282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6282_, 0, v_b_6251_);
return v___x_6282_;
}
else
{
lean_object* v_snd_6283_; lean_object* v_snd_6284_; lean_object* v_snd_6285_; lean_object* v_fst_6286_; lean_object* v___x_6288_; uint8_t v_isShared_6289_; uint8_t v_isSharedCheck_6392_; 
v_snd_6283_ = lean_ctor_get(v_b_6251_, 1);
lean_inc(v_snd_6283_);
v_snd_6284_ = lean_ctor_get(v_snd_6283_, 1);
lean_inc(v_snd_6284_);
v_snd_6285_ = lean_ctor_get(v_snd_6284_, 1);
lean_inc(v_snd_6285_);
v_fst_6286_ = lean_ctor_get(v_b_6251_, 0);
v_isSharedCheck_6392_ = !lean_is_exclusive(v_b_6251_);
if (v_isSharedCheck_6392_ == 0)
{
lean_object* v_unused_6393_; 
v_unused_6393_ = lean_ctor_get(v_b_6251_, 1);
lean_dec(v_unused_6393_);
v___x_6288_ = v_b_6251_;
v_isShared_6289_ = v_isSharedCheck_6392_;
goto v_resetjp_6287_;
}
else
{
lean_inc(v_fst_6286_);
lean_dec(v_b_6251_);
v___x_6288_ = lean_box(0);
v_isShared_6289_ = v_isSharedCheck_6392_;
goto v_resetjp_6287_;
}
v_resetjp_6287_:
{
lean_object* v_fst_6290_; lean_object* v___x_6292_; uint8_t v_isShared_6293_; uint8_t v_isSharedCheck_6390_; 
v_fst_6290_ = lean_ctor_get(v_snd_6283_, 0);
v_isSharedCheck_6390_ = !lean_is_exclusive(v_snd_6283_);
if (v_isSharedCheck_6390_ == 0)
{
lean_object* v_unused_6391_; 
v_unused_6391_ = lean_ctor_get(v_snd_6283_, 1);
lean_dec(v_unused_6391_);
v___x_6292_ = v_snd_6283_;
v_isShared_6293_ = v_isSharedCheck_6390_;
goto v_resetjp_6291_;
}
else
{
lean_inc(v_fst_6290_);
lean_dec(v_snd_6283_);
v___x_6292_ = lean_box(0);
v_isShared_6293_ = v_isSharedCheck_6390_;
goto v_resetjp_6291_;
}
v_resetjp_6291_:
{
lean_object* v_fst_6294_; lean_object* v___x_6296_; uint8_t v_isShared_6297_; uint8_t v_isSharedCheck_6388_; 
v_fst_6294_ = lean_ctor_get(v_snd_6284_, 0);
v_isSharedCheck_6388_ = !lean_is_exclusive(v_snd_6284_);
if (v_isSharedCheck_6388_ == 0)
{
lean_object* v_unused_6389_; 
v_unused_6389_ = lean_ctor_get(v_snd_6284_, 1);
lean_dec(v_unused_6389_);
v___x_6296_ = v_snd_6284_;
v_isShared_6297_ = v_isSharedCheck_6388_;
goto v_resetjp_6295_;
}
else
{
lean_inc(v_fst_6294_);
lean_dec(v_snd_6284_);
v___x_6296_ = lean_box(0);
v_isShared_6297_ = v_isSharedCheck_6388_;
goto v_resetjp_6295_;
}
v_resetjp_6295_:
{
lean_object* v_array_6298_; lean_object* v_start_6299_; lean_object* v_stop_6300_; uint8_t v___x_6301_; 
v_array_6298_ = lean_ctor_get(v_snd_6285_, 0);
v_start_6299_ = lean_ctor_get(v_snd_6285_, 1);
v_stop_6300_ = lean_ctor_get(v_snd_6285_, 2);
v___x_6301_ = lean_nat_dec_lt(v_start_6299_, v_stop_6300_);
if (v___x_6301_ == 0)
{
lean_object* v___x_6303_; 
if (v_isShared_6297_ == 0)
{
v___x_6303_ = v___x_6296_;
goto v_reusejp_6302_;
}
else
{
lean_object* v_reuseFailAlloc_6312_; 
v_reuseFailAlloc_6312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6312_, 0, v_fst_6294_);
lean_ctor_set(v_reuseFailAlloc_6312_, 1, v_snd_6285_);
v___x_6303_ = v_reuseFailAlloc_6312_;
goto v_reusejp_6302_;
}
v_reusejp_6302_:
{
lean_object* v___x_6305_; 
if (v_isShared_6293_ == 0)
{
lean_ctor_set(v___x_6292_, 1, v___x_6303_);
v___x_6305_ = v___x_6292_;
goto v_reusejp_6304_;
}
else
{
lean_object* v_reuseFailAlloc_6311_; 
v_reuseFailAlloc_6311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6311_, 0, v_fst_6290_);
lean_ctor_set(v_reuseFailAlloc_6311_, 1, v___x_6303_);
v___x_6305_ = v_reuseFailAlloc_6311_;
goto v_reusejp_6304_;
}
v_reusejp_6304_:
{
lean_object* v___x_6307_; 
if (v_isShared_6289_ == 0)
{
lean_ctor_set(v___x_6288_, 1, v___x_6305_);
v___x_6307_ = v___x_6288_;
goto v_reusejp_6306_;
}
else
{
lean_object* v_reuseFailAlloc_6310_; 
v_reuseFailAlloc_6310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6310_, 0, v_fst_6286_);
lean_ctor_set(v_reuseFailAlloc_6310_, 1, v___x_6305_);
v___x_6307_ = v_reuseFailAlloc_6310_;
goto v_reusejp_6306_;
}
v_reusejp_6306_:
{
lean_object* v___x_6308_; lean_object* v___f_6309_; 
v___x_6308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6308_, 0, v___x_6307_);
v___f_6309_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6309_, 0, v___x_6308_);
v___y_6258_ = v___f_6309_;
goto v___jp_6257_;
}
}
}
}
else
{
lean_object* v___x_6314_; uint8_t v_isShared_6315_; uint8_t v_isSharedCheck_6384_; 
lean_inc(v_stop_6300_);
lean_inc(v_start_6299_);
lean_inc_ref(v_array_6298_);
v_isSharedCheck_6384_ = !lean_is_exclusive(v_snd_6285_);
if (v_isSharedCheck_6384_ == 0)
{
lean_object* v_unused_6385_; lean_object* v_unused_6386_; lean_object* v_unused_6387_; 
v_unused_6385_ = lean_ctor_get(v_snd_6285_, 2);
lean_dec(v_unused_6385_);
v_unused_6386_ = lean_ctor_get(v_snd_6285_, 1);
lean_dec(v_unused_6386_);
v_unused_6387_ = lean_ctor_get(v_snd_6285_, 0);
lean_dec(v_unused_6387_);
v___x_6314_ = v_snd_6285_;
v_isShared_6315_ = v_isSharedCheck_6384_;
goto v_resetjp_6313_;
}
else
{
lean_dec(v_snd_6285_);
v___x_6314_ = lean_box(0);
v_isShared_6315_ = v_isSharedCheck_6384_;
goto v_resetjp_6313_;
}
v_resetjp_6313_:
{
lean_object* v_array_6316_; lean_object* v_start_6317_; lean_object* v_stop_6318_; lean_object* v___x_6319_; lean_object* v___x_6320_; lean_object* v___x_6321_; lean_object* v___x_6323_; 
v_array_6316_ = lean_ctor_get(v_fst_6294_, 0);
v_start_6317_ = lean_ctor_get(v_fst_6294_, 1);
v_stop_6318_ = lean_ctor_get(v_fst_6294_, 2);
v___x_6319_ = lean_array_fget(v_array_6298_, v_start_6299_);
v___x_6320_ = lean_unsigned_to_nat(1u);
v___x_6321_ = lean_nat_add(v_start_6299_, v___x_6320_);
lean_dec(v_start_6299_);
if (v_isShared_6315_ == 0)
{
lean_ctor_set(v___x_6314_, 1, v___x_6321_);
v___x_6323_ = v___x_6314_;
goto v_reusejp_6322_;
}
else
{
lean_object* v_reuseFailAlloc_6383_; 
v_reuseFailAlloc_6383_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6383_, 0, v_array_6298_);
lean_ctor_set(v_reuseFailAlloc_6383_, 1, v___x_6321_);
lean_ctor_set(v_reuseFailAlloc_6383_, 2, v_stop_6300_);
v___x_6323_ = v_reuseFailAlloc_6383_;
goto v_reusejp_6322_;
}
v_reusejp_6322_:
{
uint8_t v___x_6324_; 
v___x_6324_ = lean_nat_dec_lt(v_start_6317_, v_stop_6318_);
if (v___x_6324_ == 0)
{
lean_object* v___x_6326_; 
lean_dec(v___x_6319_);
if (v_isShared_6297_ == 0)
{
lean_ctor_set(v___x_6296_, 1, v___x_6323_);
v___x_6326_ = v___x_6296_;
goto v_reusejp_6325_;
}
else
{
lean_object* v_reuseFailAlloc_6335_; 
v_reuseFailAlloc_6335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6335_, 0, v_fst_6294_);
lean_ctor_set(v_reuseFailAlloc_6335_, 1, v___x_6323_);
v___x_6326_ = v_reuseFailAlloc_6335_;
goto v_reusejp_6325_;
}
v_reusejp_6325_:
{
lean_object* v___x_6328_; 
if (v_isShared_6293_ == 0)
{
lean_ctor_set(v___x_6292_, 1, v___x_6326_);
v___x_6328_ = v___x_6292_;
goto v_reusejp_6327_;
}
else
{
lean_object* v_reuseFailAlloc_6334_; 
v_reuseFailAlloc_6334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6334_, 0, v_fst_6290_);
lean_ctor_set(v_reuseFailAlloc_6334_, 1, v___x_6326_);
v___x_6328_ = v_reuseFailAlloc_6334_;
goto v_reusejp_6327_;
}
v_reusejp_6327_:
{
lean_object* v___x_6330_; 
if (v_isShared_6289_ == 0)
{
lean_ctor_set(v___x_6288_, 1, v___x_6328_);
v___x_6330_ = v___x_6288_;
goto v_reusejp_6329_;
}
else
{
lean_object* v_reuseFailAlloc_6333_; 
v_reuseFailAlloc_6333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6333_, 0, v_fst_6286_);
lean_ctor_set(v_reuseFailAlloc_6333_, 1, v___x_6328_);
v___x_6330_ = v_reuseFailAlloc_6333_;
goto v_reusejp_6329_;
}
v_reusejp_6329_:
{
lean_object* v___x_6331_; lean_object* v___f_6332_; 
v___x_6331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6331_, 0, v___x_6330_);
v___f_6332_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6332_, 0, v___x_6331_);
v___y_6258_ = v___f_6332_;
goto v___jp_6257_;
}
}
}
}
else
{
lean_object* v___x_6337_; uint8_t v_isShared_6338_; uint8_t v_isSharedCheck_6379_; 
lean_inc(v_stop_6318_);
lean_inc(v_start_6317_);
lean_inc_ref(v_array_6316_);
v_isSharedCheck_6379_ = !lean_is_exclusive(v_fst_6294_);
if (v_isSharedCheck_6379_ == 0)
{
lean_object* v_unused_6380_; lean_object* v_unused_6381_; lean_object* v_unused_6382_; 
v_unused_6380_ = lean_ctor_get(v_fst_6294_, 2);
lean_dec(v_unused_6380_);
v_unused_6381_ = lean_ctor_get(v_fst_6294_, 1);
lean_dec(v_unused_6381_);
v_unused_6382_ = lean_ctor_get(v_fst_6294_, 0);
lean_dec(v_unused_6382_);
v___x_6337_ = v_fst_6294_;
v_isShared_6338_ = v_isSharedCheck_6379_;
goto v_resetjp_6336_;
}
else
{
lean_dec(v_fst_6294_);
v___x_6337_ = lean_box(0);
v_isShared_6338_ = v_isSharedCheck_6379_;
goto v_resetjp_6336_;
}
v_resetjp_6336_:
{
lean_object* v_array_6339_; lean_object* v_start_6340_; lean_object* v_stop_6341_; lean_object* v___x_6342_; lean_object* v___x_6343_; lean_object* v___x_6345_; 
v_array_6339_ = lean_ctor_get(v_fst_6290_, 0);
v_start_6340_ = lean_ctor_get(v_fst_6290_, 1);
v_stop_6341_ = lean_ctor_get(v_fst_6290_, 2);
v___x_6342_ = lean_array_fget(v_array_6316_, v_start_6317_);
v___x_6343_ = lean_nat_add(v_start_6317_, v___x_6320_);
lean_dec(v_start_6317_);
if (v_isShared_6338_ == 0)
{
lean_ctor_set(v___x_6337_, 1, v___x_6343_);
v___x_6345_ = v___x_6337_;
goto v_reusejp_6344_;
}
else
{
lean_object* v_reuseFailAlloc_6378_; 
v_reuseFailAlloc_6378_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6378_, 0, v_array_6316_);
lean_ctor_set(v_reuseFailAlloc_6378_, 1, v___x_6343_);
lean_ctor_set(v_reuseFailAlloc_6378_, 2, v_stop_6318_);
v___x_6345_ = v_reuseFailAlloc_6378_;
goto v_reusejp_6344_;
}
v_reusejp_6344_:
{
uint8_t v___x_6346_; 
v___x_6346_ = lean_nat_dec_lt(v_start_6340_, v_stop_6341_);
if (v___x_6346_ == 0)
{
lean_object* v___x_6348_; 
lean_dec(v___x_6342_);
lean_dec(v___x_6319_);
if (v_isShared_6297_ == 0)
{
lean_ctor_set(v___x_6296_, 1, v___x_6323_);
lean_ctor_set(v___x_6296_, 0, v___x_6345_);
v___x_6348_ = v___x_6296_;
goto v_reusejp_6347_;
}
else
{
lean_object* v_reuseFailAlloc_6357_; 
v_reuseFailAlloc_6357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6357_, 0, v___x_6345_);
lean_ctor_set(v_reuseFailAlloc_6357_, 1, v___x_6323_);
v___x_6348_ = v_reuseFailAlloc_6357_;
goto v_reusejp_6347_;
}
v_reusejp_6347_:
{
lean_object* v___x_6350_; 
if (v_isShared_6293_ == 0)
{
lean_ctor_set(v___x_6292_, 1, v___x_6348_);
v___x_6350_ = v___x_6292_;
goto v_reusejp_6349_;
}
else
{
lean_object* v_reuseFailAlloc_6356_; 
v_reuseFailAlloc_6356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6356_, 0, v_fst_6290_);
lean_ctor_set(v_reuseFailAlloc_6356_, 1, v___x_6348_);
v___x_6350_ = v_reuseFailAlloc_6356_;
goto v_reusejp_6349_;
}
v_reusejp_6349_:
{
lean_object* v___x_6352_; 
if (v_isShared_6289_ == 0)
{
lean_ctor_set(v___x_6288_, 1, v___x_6350_);
v___x_6352_ = v___x_6288_;
goto v_reusejp_6351_;
}
else
{
lean_object* v_reuseFailAlloc_6355_; 
v_reuseFailAlloc_6355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6355_, 0, v_fst_6286_);
lean_ctor_set(v_reuseFailAlloc_6355_, 1, v___x_6350_);
v___x_6352_ = v_reuseFailAlloc_6355_;
goto v_reusejp_6351_;
}
v_reusejp_6351_:
{
lean_object* v___x_6353_; lean_object* v___f_6354_; 
v___x_6353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6353_, 0, v___x_6352_);
v___f_6354_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6354_, 0, v___x_6353_);
v___y_6258_ = v___f_6354_;
goto v___jp_6257_;
}
}
}
}
else
{
lean_object* v___x_6359_; uint8_t v_isShared_6360_; uint8_t v_isSharedCheck_6374_; 
lean_inc(v_stop_6341_);
lean_inc(v_start_6340_);
lean_inc_ref(v_array_6339_);
lean_del_object(v___x_6296_);
lean_del_object(v___x_6292_);
lean_del_object(v___x_6288_);
v_isSharedCheck_6374_ = !lean_is_exclusive(v_fst_6290_);
if (v_isSharedCheck_6374_ == 0)
{
lean_object* v_unused_6375_; lean_object* v_unused_6376_; lean_object* v_unused_6377_; 
v_unused_6375_ = lean_ctor_get(v_fst_6290_, 2);
lean_dec(v_unused_6375_);
v_unused_6376_ = lean_ctor_get(v_fst_6290_, 1);
lean_dec(v_unused_6376_);
v_unused_6377_ = lean_ctor_get(v_fst_6290_, 0);
lean_dec(v_unused_6377_);
v___x_6359_ = v_fst_6290_;
v_isShared_6360_ = v_isSharedCheck_6374_;
goto v_resetjp_6358_;
}
else
{
lean_dec(v_fst_6290_);
v___x_6359_ = lean_box(0);
v_isShared_6360_ = v_isSharedCheck_6374_;
goto v_resetjp_6358_;
}
v_resetjp_6358_:
{
lean_object* v___f_6361_; uint8_t v___x_6362_; lean_object* v___x_6363_; lean_object* v___x_6364_; lean_object* v___x_6365_; lean_object* v___f_6366_; lean_object* v___x_6367_; lean_object* v___x_6369_; 
v___f_6361_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___closed__0));
v___x_6362_ = 0;
v___x_6363_ = lean_array_fget_borrowed(v_array_6339_, v_start_6340_);
v___x_6364_ = lean_box(v___x_6362_);
v___x_6365_ = lean_box(v___x_6346_);
lean_inc(v_extraEqualities_6249_);
lean_inc(v_a_6250_);
lean_inc_ref(v_onAlt_6248_);
lean_inc(v___x_6363_);
v___f_6366_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed), 14, 7);
lean_closure_set(v___f_6366_, 0, v___x_6363_);
lean_closure_set(v___f_6366_, 1, v___f_6361_);
lean_closure_set(v___f_6366_, 2, v___x_6364_);
lean_closure_set(v___f_6366_, 3, v_onAlt_6248_);
lean_closure_set(v___f_6366_, 4, v_a_6250_);
lean_closure_set(v___f_6366_, 5, v___x_6365_);
lean_closure_set(v___f_6366_, 6, v_extraEqualities_6249_);
v___x_6367_ = lean_nat_add(v_start_6340_, v___x_6320_);
lean_dec(v_start_6340_);
if (v_isShared_6360_ == 0)
{
lean_ctor_set(v___x_6359_, 1, v___x_6367_);
v___x_6369_ = v___x_6359_;
goto v_reusejp_6368_;
}
else
{
lean_object* v_reuseFailAlloc_6373_; 
v_reuseFailAlloc_6373_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6373_, 0, v_array_6339_);
lean_ctor_set(v_reuseFailAlloc_6373_, 1, v___x_6367_);
lean_ctor_set(v_reuseFailAlloc_6373_, 2, v_stop_6341_);
v___x_6369_ = v_reuseFailAlloc_6373_;
goto v_reusejp_6368_;
}
v_reusejp_6368_:
{
lean_object* v___x_6370_; lean_object* v___x_6371_; lean_object* v___f_6372_; 
v___x_6370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6370_, 0, v___x_6342_);
v___x_6371_ = lean_box(v___x_6362_);
v___f_6372_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed), 13, 8);
lean_closure_set(v___f_6372_, 0, v___x_6319_);
lean_closure_set(v___f_6372_, 1, v___x_6370_);
lean_closure_set(v___f_6372_, 2, v___f_6366_);
lean_closure_set(v___f_6372_, 3, v___x_6371_);
lean_closure_set(v___f_6372_, 4, v_fst_6286_);
lean_closure_set(v___f_6372_, 5, v___x_6345_);
lean_closure_set(v___f_6372_, 6, v___x_6323_);
lean_closure_set(v___f_6372_, 7, v___x_6369_);
v___y_6258_ = v___f_6372_;
goto v___jp_6257_;
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_6257_:
{
lean_object* v___x_6259_; 
lean_inc(v___y_6255_);
lean_inc_ref(v___y_6254_);
lean_inc(v___y_6253_);
lean_inc_ref(v___y_6252_);
v___x_6259_ = lean_apply_5(v___y_6258_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_, lean_box(0));
if (lean_obj_tag(v___x_6259_) == 0)
{
lean_object* v_a_6260_; lean_object* v___x_6262_; uint8_t v_isShared_6263_; uint8_t v_isSharedCheck_6272_; 
v_a_6260_ = lean_ctor_get(v___x_6259_, 0);
v_isSharedCheck_6272_ = !lean_is_exclusive(v___x_6259_);
if (v_isSharedCheck_6272_ == 0)
{
v___x_6262_ = v___x_6259_;
v_isShared_6263_ = v_isSharedCheck_6272_;
goto v_resetjp_6261_;
}
else
{
lean_inc(v_a_6260_);
lean_dec(v___x_6259_);
v___x_6262_ = lean_box(0);
v_isShared_6263_ = v_isSharedCheck_6272_;
goto v_resetjp_6261_;
}
v_resetjp_6261_:
{
if (lean_obj_tag(v_a_6260_) == 0)
{
lean_object* v_a_6264_; lean_object* v___x_6266_; 
lean_dec(v___y_6255_);
lean_dec_ref(v___y_6254_);
lean_dec(v___y_6253_);
lean_dec_ref(v___y_6252_);
lean_dec(v_a_6250_);
lean_dec(v_extraEqualities_6249_);
lean_dec_ref(v_onAlt_6248_);
v_a_6264_ = lean_ctor_get(v_a_6260_, 0);
lean_inc(v_a_6264_);
lean_dec_ref(v_a_6260_);
if (v_isShared_6263_ == 0)
{
lean_ctor_set(v___x_6262_, 0, v_a_6264_);
v___x_6266_ = v___x_6262_;
goto v_reusejp_6265_;
}
else
{
lean_object* v_reuseFailAlloc_6267_; 
v_reuseFailAlloc_6267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6267_, 0, v_a_6264_);
v___x_6266_ = v_reuseFailAlloc_6267_;
goto v_reusejp_6265_;
}
v_reusejp_6265_:
{
return v___x_6266_;
}
}
else
{
lean_object* v_a_6268_; lean_object* v___x_6269_; lean_object* v___x_6270_; 
lean_del_object(v___x_6262_);
v_a_6268_ = lean_ctor_get(v_a_6260_, 0);
lean_inc(v_a_6268_);
lean_dec_ref(v_a_6260_);
v___x_6269_ = lean_unsigned_to_nat(1u);
v___x_6270_ = lean_nat_add(v_a_6250_, v___x_6269_);
lean_dec(v_a_6250_);
v_a_6250_ = v___x_6270_;
v_b_6251_ = v_a_6268_;
goto _start;
}
}
}
else
{
lean_object* v_a_6273_; lean_object* v___x_6275_; uint8_t v_isShared_6276_; uint8_t v_isSharedCheck_6280_; 
lean_dec(v___y_6255_);
lean_dec_ref(v___y_6254_);
lean_dec(v___y_6253_);
lean_dec_ref(v___y_6252_);
lean_dec(v_a_6250_);
lean_dec(v_extraEqualities_6249_);
lean_dec_ref(v_onAlt_6248_);
v_a_6273_ = lean_ctor_get(v___x_6259_, 0);
v_isSharedCheck_6280_ = !lean_is_exclusive(v___x_6259_);
if (v_isSharedCheck_6280_ == 0)
{
v___x_6275_ = v___x_6259_;
v_isShared_6276_ = v_isSharedCheck_6280_;
goto v_resetjp_6274_;
}
else
{
lean_inc(v_a_6273_);
lean_dec(v___x_6259_);
v___x_6275_ = lean_box(0);
v_isShared_6276_ = v_isSharedCheck_6280_;
goto v_resetjp_6274_;
}
v_resetjp_6274_:
{
lean_object* v___x_6278_; 
if (v_isShared_6276_ == 0)
{
v___x_6278_ = v___x_6275_;
goto v_reusejp_6277_;
}
else
{
lean_object* v_reuseFailAlloc_6279_; 
v_reuseFailAlloc_6279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6279_, 0, v_a_6273_);
v___x_6278_ = v_reuseFailAlloc_6279_;
goto v_reusejp_6277_;
}
v_reusejp_6277_:
{
return v___x_6278_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___boxed(lean_object* v_upperBound_6394_, lean_object* v_onAlt_6395_, lean_object* v_extraEqualities_6396_, lean_object* v_a_6397_, lean_object* v_b_6398_, lean_object* v___y_6399_, lean_object* v___y_6400_, lean_object* v___y_6401_, lean_object* v___y_6402_, lean_object* v___y_6403_){
_start:
{
lean_object* v_res_6404_; 
v_res_6404_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v_upperBound_6394_, v_onAlt_6395_, v_extraEqualities_6396_, v_a_6397_, v_b_6398_, v___y_6399_, v___y_6400_, v___y_6401_, v___y_6402_);
lean_dec(v_upperBound_6394_);
return v_res_6404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(lean_object* v_onParams_6405_, size_t v_sz_6406_, size_t v_i_6407_, lean_object* v_bs_6408_, lean_object* v___y_6409_, lean_object* v___y_6410_, lean_object* v___y_6411_, lean_object* v___y_6412_){
_start:
{
uint8_t v___x_6414_; 
v___x_6414_ = lean_usize_dec_lt(v_i_6407_, v_sz_6406_);
if (v___x_6414_ == 0)
{
lean_object* v___x_6415_; 
lean_dec(v___y_6412_);
lean_dec_ref(v___y_6411_);
lean_dec(v___y_6410_);
lean_dec_ref(v___y_6409_);
lean_dec_ref(v_onParams_6405_);
v___x_6415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6415_, 0, v_bs_6408_);
return v___x_6415_;
}
else
{
lean_object* v_v_6416_; lean_object* v___x_6417_; 
v_v_6416_ = lean_array_uget_borrowed(v_bs_6408_, v_i_6407_);
lean_inc_ref(v_onParams_6405_);
lean_inc(v___y_6412_);
lean_inc_ref(v___y_6411_);
lean_inc(v___y_6410_);
lean_inc_ref(v___y_6409_);
lean_inc(v_v_6416_);
v___x_6417_ = lean_apply_6(v_onParams_6405_, v_v_6416_, v___y_6409_, v___y_6410_, v___y_6411_, v___y_6412_, lean_box(0));
if (lean_obj_tag(v___x_6417_) == 0)
{
lean_object* v_a_6418_; lean_object* v___x_6419_; lean_object* v_bs_x27_6420_; size_t v___x_6421_; size_t v___x_6422_; lean_object* v___x_6423_; 
v_a_6418_ = lean_ctor_get(v___x_6417_, 0);
lean_inc(v_a_6418_);
lean_dec_ref(v___x_6417_);
v___x_6419_ = lean_unsigned_to_nat(0u);
v_bs_x27_6420_ = lean_array_uset(v_bs_6408_, v_i_6407_, v___x_6419_);
v___x_6421_ = ((size_t)1ULL);
v___x_6422_ = lean_usize_add(v_i_6407_, v___x_6421_);
v___x_6423_ = lean_array_uset(v_bs_x27_6420_, v_i_6407_, v_a_6418_);
v_i_6407_ = v___x_6422_;
v_bs_6408_ = v___x_6423_;
goto _start;
}
else
{
lean_object* v_a_6425_; lean_object* v___x_6427_; uint8_t v_isShared_6428_; uint8_t v_isSharedCheck_6432_; 
lean_dec(v___y_6412_);
lean_dec_ref(v___y_6411_);
lean_dec(v___y_6410_);
lean_dec_ref(v___y_6409_);
lean_dec_ref(v_bs_6408_);
lean_dec_ref(v_onParams_6405_);
v_a_6425_ = lean_ctor_get(v___x_6417_, 0);
v_isSharedCheck_6432_ = !lean_is_exclusive(v___x_6417_);
if (v_isSharedCheck_6432_ == 0)
{
v___x_6427_ = v___x_6417_;
v_isShared_6428_ = v_isSharedCheck_6432_;
goto v_resetjp_6426_;
}
else
{
lean_inc(v_a_6425_);
lean_dec(v___x_6417_);
v___x_6427_ = lean_box(0);
v_isShared_6428_ = v_isSharedCheck_6432_;
goto v_resetjp_6426_;
}
v_resetjp_6426_:
{
lean_object* v___x_6430_; 
if (v_isShared_6428_ == 0)
{
v___x_6430_ = v___x_6427_;
goto v_reusejp_6429_;
}
else
{
lean_object* v_reuseFailAlloc_6431_; 
v_reuseFailAlloc_6431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6431_, 0, v_a_6425_);
v___x_6430_ = v_reuseFailAlloc_6431_;
goto v_reusejp_6429_;
}
v_reusejp_6429_:
{
return v___x_6430_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6___boxed(lean_object* v_onParams_6433_, lean_object* v_sz_6434_, lean_object* v_i_6435_, lean_object* v_bs_6436_, lean_object* v___y_6437_, lean_object* v___y_6438_, lean_object* v___y_6439_, lean_object* v___y_6440_, lean_object* v___y_6441_){
_start:
{
size_t v_sz_boxed_6442_; size_t v_i_boxed_6443_; lean_object* v_res_6444_; 
v_sz_boxed_6442_ = lean_unbox_usize(v_sz_6434_);
lean_dec(v_sz_6434_);
v_i_boxed_6443_ = lean_unbox_usize(v_i_6435_);
lean_dec(v_i_6435_);
v_res_6444_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6433_, v_sz_boxed_6442_, v_i_boxed_6443_, v_bs_6436_, v___y_6437_, v___y_6438_, v___y_6439_, v___y_6440_);
return v_res_6444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(lean_object* v_declName_6445_, lean_object* v___y_6446_){
_start:
{
lean_object* v___x_6448_; lean_object* v_env_6449_; lean_object* v___x_6450_; lean_object* v___x_6451_; 
v___x_6448_ = lean_st_ref_get(v___y_6446_);
v_env_6449_ = lean_ctor_get(v___x_6448_, 0);
lean_inc_ref(v_env_6449_);
lean_dec(v___x_6448_);
v___x_6450_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_6449_, v_declName_6445_);
v___x_6451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6451_, 0, v___x_6450_);
return v___x_6451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg___boxed(lean_object* v_declName_6452_, lean_object* v___y_6453_, lean_object* v___y_6454_){
_start:
{
lean_object* v_res_6455_; 
v_res_6455_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_declName_6452_, v___y_6453_);
lean_dec(v___y_6453_);
return v_res_6455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(lean_object* v_matcherApp_6458_, uint8_t v_useSplitter_6459_, uint8_t v_addEqualities_6460_, lean_object* v_onParams_6461_, lean_object* v_onMotive_6462_, lean_object* v_onAlt_6463_, lean_object* v_onRemaining_6464_, lean_object* v___y_6465_, lean_object* v___y_6466_, lean_object* v___y_6467_, lean_object* v___y_6468_){
_start:
{
lean_object* v___x_6470_; lean_object* v_env_6471_; lean_object* v_toMatcherInfo_6472_; lean_object* v_matcherName_6473_; lean_object* v_matcherLevels_6474_; lean_object* v_params_6475_; lean_object* v_motive_6476_; lean_object* v_discrs_6477_; lean_object* v_alts_6478_; lean_object* v_remaining_6479_; lean_object* v___y_6481_; lean_object* v___y_6482_; lean_object* v___y_6483_; lean_object* v___y_6484_; lean_object* v___y_6485_; lean_object* v___y_6486_; lean_object* v___y_6487_; lean_object* v___y_6488_; lean_object* v___y_6489_; lean_object* v___y_6490_; lean_object* v___y_6491_; lean_object* v___y_6492_; lean_object* v___y_6493_; uint8_t v_isCasesOn_6576_; size_t v___y_6578_; lean_object* v___y_6579_; lean_object* v___y_6580_; lean_object* v___y_6581_; lean_object* v___y_6582_; lean_object* v___y_6583_; lean_object* v___y_6584_; lean_object* v_matcherLevels_6585_; lean_object* v___y_6586_; lean_object* v___y_6587_; lean_object* v___y_6588_; lean_object* v___y_6589_; lean_object* v_numDiscrEqs_6780_; lean_object* v___y_6781_; lean_object* v___y_6782_; lean_object* v___y_6783_; lean_object* v___y_6784_; 
v___x_6470_ = lean_st_ref_get(v___y_6468_);
v_env_6471_ = lean_ctor_get(v___x_6470_, 0);
lean_inc_ref(v_env_6471_);
lean_dec(v___x_6470_);
v_toMatcherInfo_6472_ = lean_ctor_get(v_matcherApp_6458_, 0);
lean_inc_ref(v_toMatcherInfo_6472_);
v_matcherName_6473_ = lean_ctor_get(v_matcherApp_6458_, 1);
lean_inc(v_matcherName_6473_);
v_matcherLevels_6474_ = lean_ctor_get(v_matcherApp_6458_, 2);
v_params_6475_ = lean_ctor_get(v_matcherApp_6458_, 3);
v_motive_6476_ = lean_ctor_get(v_matcherApp_6458_, 4);
v_discrs_6477_ = lean_ctor_get(v_matcherApp_6458_, 5);
v_alts_6478_ = lean_ctor_get(v_matcherApp_6458_, 6);
lean_inc_ref(v_alts_6478_);
v_remaining_6479_ = lean_ctor_get(v_matcherApp_6458_, 7);
lean_inc_ref(v_remaining_6479_);
lean_inc(v_matcherName_6473_);
v_isCasesOn_6576_ = l_Lean_isCasesOnRecursor(v_env_6471_, v_matcherName_6473_);
if (v_isCasesOn_6576_ == 0)
{
lean_object* v___x_6834_; lean_object* v_a_6835_; 
lean_inc(v_matcherName_6473_);
v___x_6834_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_matcherName_6473_, v___y_6468_);
v_a_6835_ = lean_ctor_get(v___x_6834_, 0);
lean_inc(v_a_6835_);
lean_dec_ref(v___x_6834_);
if (lean_obj_tag(v_a_6835_) == 0)
{
lean_object* v___x_6836_; lean_object* v___x_6837_; lean_object* v___x_6838_; lean_object* v___x_6839_; lean_object* v___x_6840_; lean_object* v___x_6841_; lean_object* v_a_6842_; lean_object* v___x_6844_; uint8_t v_isShared_6845_; uint8_t v_isSharedCheck_6849_; 
lean_dec_ref(v_remaining_6479_);
lean_dec_ref(v_alts_6478_);
lean_dec_ref(v_toMatcherInfo_6472_);
lean_dec_ref(v_onRemaining_6464_);
lean_dec_ref(v_onAlt_6463_);
lean_dec_ref(v_onMotive_6462_);
lean_dec_ref(v_onParams_6461_);
lean_dec_ref(v_matcherApp_6458_);
v___x_6836_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1);
v___x_6837_ = l_Lean_MessageData_ofName(v_matcherName_6473_);
v___x_6838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6838_, 0, v___x_6836_);
lean_ctor_set(v___x_6838_, 1, v___x_6837_);
v___x_6839_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3);
v___x_6840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6840_, 0, v___x_6838_);
lean_ctor_set(v___x_6840_, 1, v___x_6839_);
v___x_6841_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_6840_, v___y_6465_, v___y_6466_, v___y_6467_, v___y_6468_);
lean_dec(v___y_6468_);
lean_dec_ref(v___y_6467_);
lean_dec(v___y_6466_);
lean_dec_ref(v___y_6465_);
v_a_6842_ = lean_ctor_get(v___x_6841_, 0);
v_isSharedCheck_6849_ = !lean_is_exclusive(v___x_6841_);
if (v_isSharedCheck_6849_ == 0)
{
v___x_6844_ = v___x_6841_;
v_isShared_6845_ = v_isSharedCheck_6849_;
goto v_resetjp_6843_;
}
else
{
lean_inc(v_a_6842_);
lean_dec(v___x_6841_);
v___x_6844_ = lean_box(0);
v_isShared_6845_ = v_isSharedCheck_6849_;
goto v_resetjp_6843_;
}
v_resetjp_6843_:
{
lean_object* v___x_6847_; 
if (v_isShared_6845_ == 0)
{
v___x_6847_ = v___x_6844_;
goto v_reusejp_6846_;
}
else
{
lean_object* v_reuseFailAlloc_6848_; 
v_reuseFailAlloc_6848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6848_, 0, v_a_6842_);
v___x_6847_ = v_reuseFailAlloc_6848_;
goto v_reusejp_6846_;
}
v_reusejp_6846_:
{
return v___x_6847_;
}
}
}
else
{
lean_object* v_val_6850_; lean_object* v___x_6851_; 
v_val_6850_ = lean_ctor_get(v_a_6835_, 0);
lean_inc(v_val_6850_);
lean_dec_ref(v_a_6835_);
v___x_6851_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_6850_);
lean_dec(v_val_6850_);
v_numDiscrEqs_6780_ = v___x_6851_;
v___y_6781_ = v___y_6465_;
v___y_6782_ = v___y_6466_;
v___y_6783_ = v___y_6467_;
v___y_6784_ = v___y_6468_;
goto v___jp_6779_;
}
}
else
{
lean_object* v___x_6852_; 
v___x_6852_ = lean_unsigned_to_nat(0u);
v_numDiscrEqs_6780_ = v___x_6852_;
v___y_6781_ = v___y_6465_;
v___y_6782_ = v___y_6466_;
v___y_6783_ = v___y_6467_;
v___y_6784_ = v___y_6468_;
goto v___jp_6779_;
}
v___jp_6480_:
{
lean_object* v___x_6494_; lean_object* v___x_6495_; lean_object* v_aux_6496_; lean_object* v_aux_6497_; lean_object* v_aux_6498_; lean_object* v___x_6499_; lean_object* v___x_6500_; lean_object* v___x_6501_; lean_object* v___f_6502_; lean_object* v___x_6503_; lean_object* v___x_6504_; 
lean_inc_ref(v___y_6485_);
v___x_6494_ = lean_array_to_list(v___y_6485_);
lean_inc(v_matcherName_6473_);
v___x_6495_ = l_Lean_mkConst(v_matcherName_6473_, v___x_6494_);
v_aux_6496_ = l_Lean_mkAppN(v___x_6495_, v___y_6492_);
lean_inc_ref(v___y_6487_);
v_aux_6497_ = l_Lean_Expr_app___override(v_aux_6496_, v___y_6487_);
v_aux_6498_ = l_Lean_mkAppN(v_aux_6497_, v___y_6489_);
v___x_6499_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__1);
lean_inc_ref(v_aux_6498_);
v___x_6500_ = l_Lean_indentExpr(v_aux_6498_);
v___x_6501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6501_, 0, v___x_6499_);
lean_ctor_set(v___x_6501_, 1, v___x_6500_);
v___f_6502_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6502_, 0, v___x_6501_);
lean_inc_ref(v_aux_6498_);
v___x_6503_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(v___x_6503_, 0, v_aux_6498_);
lean_inc(v___y_6483_);
lean_inc_ref(v___y_6493_);
lean_inc(v___y_6482_);
lean_inc_ref(v___y_6488_);
v___x_6504_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6503_, v___f_6502_, v___y_6488_, v___y_6482_, v___y_6493_, v___y_6483_);
if (lean_obj_tag(v___x_6504_) == 0)
{
lean_object* v___x_6505_; lean_object* v___x_6506_; 
lean_dec_ref(v___x_6504_);
v___x_6505_ = lean_array_get_size(v_alts_6478_);
lean_inc(v___y_6483_);
lean_inc_ref(v___y_6493_);
lean_inc(v___y_6482_);
lean_inc_ref(v___y_6488_);
v___x_6506_ = l_Lean_Meta_inferArgumentTypesN(v___x_6505_, v_aux_6498_, v___y_6488_, v___y_6482_, v___y_6493_, v___y_6483_);
if (lean_obj_tag(v___x_6506_) == 0)
{
lean_object* v_a_6507_; lean_object* v___x_6508_; lean_object* v___x_6509_; lean_object* v___x_6510_; lean_object* v___x_6511_; lean_object* v___x_6512_; lean_object* v___x_6513_; lean_object* v___x_6514_; lean_object* v___x_6515_; lean_object* v___x_6516_; lean_object* v___x_6517_; 
v_a_6507_ = lean_ctor_get(v___x_6506_, 0);
lean_inc(v_a_6507_);
lean_dec_ref(v___x_6506_);
v___x_6508_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_6458_);
v___x_6509_ = lean_array_get_size(v___x_6508_);
v___x_6510_ = lean_array_get_size(v_a_6507_);
lean_inc(v___y_6481_);
v___x_6511_ = l_Array_toSubarray___redArg(v_alts_6478_, v___y_6481_, v___x_6505_);
lean_inc(v___y_6481_);
v___x_6512_ = l_Array_toSubarray___redArg(v___x_6508_, v___y_6481_, v___x_6509_);
lean_inc(v___y_6481_);
v___x_6513_ = l_Array_toSubarray___redArg(v_a_6507_, v___y_6481_, v___x_6510_);
v___x_6514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6514_, 0, v___x_6512_);
lean_ctor_set(v___x_6514_, 1, v___x_6513_);
v___x_6515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6515_, 0, v___x_6511_);
lean_ctor_set(v___x_6515_, 1, v___x_6514_);
v___x_6516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6516_, 0, v___y_6490_);
lean_ctor_set(v___x_6516_, 1, v___x_6515_);
lean_inc(v___y_6483_);
lean_inc_ref(v___y_6493_);
lean_inc(v___y_6482_);
lean_inc_ref(v___y_6488_);
v___x_6517_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v___x_6505_, v_onAlt_6463_, v___y_6484_, v___y_6481_, v___x_6516_, v___y_6488_, v___y_6482_, v___y_6493_, v___y_6483_);
if (lean_obj_tag(v___x_6517_) == 0)
{
lean_object* v_a_6518_; lean_object* v_fst_6519_; lean_object* v___x_6520_; 
v_a_6518_ = lean_ctor_get(v___x_6517_, 0);
lean_inc(v_a_6518_);
lean_dec_ref(v___x_6517_);
v_fst_6519_ = lean_ctor_get(v_a_6518_, 0);
lean_inc(v_fst_6519_);
lean_dec(v_a_6518_);
v___x_6520_ = lean_apply_6(v_onRemaining_6464_, v_remaining_6479_, v___y_6488_, v___y_6482_, v___y_6493_, v___y_6483_, lean_box(0));
if (lean_obj_tag(v___x_6520_) == 0)
{
lean_object* v_a_6521_; lean_object* v___x_6523_; uint8_t v_isShared_6524_; uint8_t v_isSharedCheck_6543_; 
v_a_6521_ = lean_ctor_get(v___x_6520_, 0);
v_isSharedCheck_6543_ = !lean_is_exclusive(v___x_6520_);
if (v_isSharedCheck_6543_ == 0)
{
v___x_6523_ = v___x_6520_;
v_isShared_6524_ = v_isSharedCheck_6543_;
goto v_resetjp_6522_;
}
else
{
lean_inc(v_a_6521_);
lean_dec(v___x_6520_);
v___x_6523_ = lean_box(0);
v_isShared_6524_ = v_isSharedCheck_6543_;
goto v_resetjp_6522_;
}
v_resetjp_6522_:
{
lean_object* v_numParams_6525_; lean_object* v_numDiscrs_6526_; lean_object* v_altInfos_6527_; lean_object* v_uElimPos_x3f_6528_; lean_object* v_overlaps_6529_; lean_object* v___x_6531_; uint8_t v_isShared_6532_; uint8_t v_isSharedCheck_6541_; 
v_numParams_6525_ = lean_ctor_get(v_toMatcherInfo_6472_, 0);
v_numDiscrs_6526_ = lean_ctor_get(v_toMatcherInfo_6472_, 1);
v_altInfos_6527_ = lean_ctor_get(v_toMatcherInfo_6472_, 2);
v_uElimPos_x3f_6528_ = lean_ctor_get(v_toMatcherInfo_6472_, 3);
v_overlaps_6529_ = lean_ctor_get(v_toMatcherInfo_6472_, 5);
v_isSharedCheck_6541_ = !lean_is_exclusive(v_toMatcherInfo_6472_);
if (v_isSharedCheck_6541_ == 0)
{
lean_object* v_unused_6542_; 
v_unused_6542_ = lean_ctor_get(v_toMatcherInfo_6472_, 4);
lean_dec(v_unused_6542_);
v___x_6531_ = v_toMatcherInfo_6472_;
v_isShared_6532_ = v_isSharedCheck_6541_;
goto v_resetjp_6530_;
}
else
{
lean_inc(v_overlaps_6529_);
lean_inc(v_uElimPos_x3f_6528_);
lean_inc(v_altInfos_6527_);
lean_inc(v_numDiscrs_6526_);
lean_inc(v_numParams_6525_);
lean_dec(v_toMatcherInfo_6472_);
v___x_6531_ = lean_box(0);
v_isShared_6532_ = v_isSharedCheck_6541_;
goto v_resetjp_6530_;
}
v_resetjp_6530_:
{
lean_object* v_remaining_x27_6533_; lean_object* v___x_6535_; 
v_remaining_x27_6533_ = l_Array_append___redArg(v___y_6491_, v_a_6521_);
lean_dec(v_a_6521_);
if (v_isShared_6532_ == 0)
{
lean_ctor_set(v___x_6531_, 4, v___y_6486_);
v___x_6535_ = v___x_6531_;
goto v_reusejp_6534_;
}
else
{
lean_object* v_reuseFailAlloc_6540_; 
v_reuseFailAlloc_6540_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6540_, 0, v_numParams_6525_);
lean_ctor_set(v_reuseFailAlloc_6540_, 1, v_numDiscrs_6526_);
lean_ctor_set(v_reuseFailAlloc_6540_, 2, v_altInfos_6527_);
lean_ctor_set(v_reuseFailAlloc_6540_, 3, v_uElimPos_x3f_6528_);
lean_ctor_set(v_reuseFailAlloc_6540_, 4, v___y_6486_);
lean_ctor_set(v_reuseFailAlloc_6540_, 5, v_overlaps_6529_);
v___x_6535_ = v_reuseFailAlloc_6540_;
goto v_reusejp_6534_;
}
v_reusejp_6534_:
{
lean_object* v___x_6536_; lean_object* v___x_6538_; 
v___x_6536_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6536_, 0, v___x_6535_);
lean_ctor_set(v___x_6536_, 1, v_matcherName_6473_);
lean_ctor_set(v___x_6536_, 2, v___y_6485_);
lean_ctor_set(v___x_6536_, 3, v___y_6492_);
lean_ctor_set(v___x_6536_, 4, v___y_6487_);
lean_ctor_set(v___x_6536_, 5, v___y_6489_);
lean_ctor_set(v___x_6536_, 6, v_fst_6519_);
lean_ctor_set(v___x_6536_, 7, v_remaining_x27_6533_);
if (v_isShared_6524_ == 0)
{
lean_ctor_set(v___x_6523_, 0, v___x_6536_);
v___x_6538_ = v___x_6523_;
goto v_reusejp_6537_;
}
else
{
lean_object* v_reuseFailAlloc_6539_; 
v_reuseFailAlloc_6539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6539_, 0, v___x_6536_);
v___x_6538_ = v_reuseFailAlloc_6539_;
goto v_reusejp_6537_;
}
v_reusejp_6537_:
{
return v___x_6538_;
}
}
}
}
}
else
{
lean_object* v_a_6544_; lean_object* v___x_6546_; uint8_t v_isShared_6547_; uint8_t v_isSharedCheck_6551_; 
lean_dec(v_fst_6519_);
lean_dec_ref(v___y_6492_);
lean_dec(v___y_6491_);
lean_dec_ref(v___y_6489_);
lean_dec_ref(v___y_6487_);
lean_dec_ref(v___y_6486_);
lean_dec_ref(v___y_6485_);
lean_dec(v_matcherName_6473_);
lean_dec_ref(v_toMatcherInfo_6472_);
v_a_6544_ = lean_ctor_get(v___x_6520_, 0);
v_isSharedCheck_6551_ = !lean_is_exclusive(v___x_6520_);
if (v_isSharedCheck_6551_ == 0)
{
v___x_6546_ = v___x_6520_;
v_isShared_6547_ = v_isSharedCheck_6551_;
goto v_resetjp_6545_;
}
else
{
lean_inc(v_a_6544_);
lean_dec(v___x_6520_);
v___x_6546_ = lean_box(0);
v_isShared_6547_ = v_isSharedCheck_6551_;
goto v_resetjp_6545_;
}
v_resetjp_6545_:
{
lean_object* v___x_6549_; 
if (v_isShared_6547_ == 0)
{
v___x_6549_ = v___x_6546_;
goto v_reusejp_6548_;
}
else
{
lean_object* v_reuseFailAlloc_6550_; 
v_reuseFailAlloc_6550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6550_, 0, v_a_6544_);
v___x_6549_ = v_reuseFailAlloc_6550_;
goto v_reusejp_6548_;
}
v_reusejp_6548_:
{
return v___x_6549_;
}
}
}
}
else
{
lean_object* v_a_6552_; lean_object* v___x_6554_; uint8_t v_isShared_6555_; uint8_t v_isSharedCheck_6559_; 
lean_dec_ref(v___y_6493_);
lean_dec_ref(v___y_6492_);
lean_dec(v___y_6491_);
lean_dec_ref(v___y_6489_);
lean_dec_ref(v___y_6488_);
lean_dec_ref(v___y_6487_);
lean_dec_ref(v___y_6486_);
lean_dec_ref(v___y_6485_);
lean_dec(v___y_6483_);
lean_dec(v___y_6482_);
lean_dec_ref(v_remaining_6479_);
lean_dec(v_matcherName_6473_);
lean_dec_ref(v_toMatcherInfo_6472_);
lean_dec_ref(v_onRemaining_6464_);
v_a_6552_ = lean_ctor_get(v___x_6517_, 0);
v_isSharedCheck_6559_ = !lean_is_exclusive(v___x_6517_);
if (v_isSharedCheck_6559_ == 0)
{
v___x_6554_ = v___x_6517_;
v_isShared_6555_ = v_isSharedCheck_6559_;
goto v_resetjp_6553_;
}
else
{
lean_inc(v_a_6552_);
lean_dec(v___x_6517_);
v___x_6554_ = lean_box(0);
v_isShared_6555_ = v_isSharedCheck_6559_;
goto v_resetjp_6553_;
}
v_resetjp_6553_:
{
lean_object* v___x_6557_; 
if (v_isShared_6555_ == 0)
{
v___x_6557_ = v___x_6554_;
goto v_reusejp_6556_;
}
else
{
lean_object* v_reuseFailAlloc_6558_; 
v_reuseFailAlloc_6558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6558_, 0, v_a_6552_);
v___x_6557_ = v_reuseFailAlloc_6558_;
goto v_reusejp_6556_;
}
v_reusejp_6556_:
{
return v___x_6557_;
}
}
}
}
else
{
lean_object* v_a_6560_; lean_object* v___x_6562_; uint8_t v_isShared_6563_; uint8_t v_isSharedCheck_6567_; 
lean_dec_ref(v___y_6493_);
lean_dec_ref(v___y_6492_);
lean_dec(v___y_6491_);
lean_dec_ref(v___y_6490_);
lean_dec_ref(v___y_6489_);
lean_dec_ref(v___y_6488_);
lean_dec_ref(v___y_6487_);
lean_dec_ref(v___y_6486_);
lean_dec_ref(v___y_6485_);
lean_dec(v___y_6484_);
lean_dec(v___y_6483_);
lean_dec(v___y_6482_);
lean_dec(v___y_6481_);
lean_dec_ref(v_remaining_6479_);
lean_dec_ref(v_alts_6478_);
lean_dec(v_matcherName_6473_);
lean_dec_ref(v_toMatcherInfo_6472_);
lean_dec_ref(v_onRemaining_6464_);
lean_dec_ref(v_onAlt_6463_);
lean_dec_ref(v_matcherApp_6458_);
v_a_6560_ = lean_ctor_get(v___x_6506_, 0);
v_isSharedCheck_6567_ = !lean_is_exclusive(v___x_6506_);
if (v_isSharedCheck_6567_ == 0)
{
v___x_6562_ = v___x_6506_;
v_isShared_6563_ = v_isSharedCheck_6567_;
goto v_resetjp_6561_;
}
else
{
lean_inc(v_a_6560_);
lean_dec(v___x_6506_);
v___x_6562_ = lean_box(0);
v_isShared_6563_ = v_isSharedCheck_6567_;
goto v_resetjp_6561_;
}
v_resetjp_6561_:
{
lean_object* v___x_6565_; 
if (v_isShared_6563_ == 0)
{
v___x_6565_ = v___x_6562_;
goto v_reusejp_6564_;
}
else
{
lean_object* v_reuseFailAlloc_6566_; 
v_reuseFailAlloc_6566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6566_, 0, v_a_6560_);
v___x_6565_ = v_reuseFailAlloc_6566_;
goto v_reusejp_6564_;
}
v_reusejp_6564_:
{
return v___x_6565_;
}
}
}
}
else
{
lean_object* v_a_6568_; lean_object* v___x_6570_; uint8_t v_isShared_6571_; uint8_t v_isSharedCheck_6575_; 
lean_dec_ref(v_aux_6498_);
lean_dec_ref(v___y_6493_);
lean_dec_ref(v___y_6492_);
lean_dec(v___y_6491_);
lean_dec_ref(v___y_6490_);
lean_dec_ref(v___y_6489_);
lean_dec_ref(v___y_6488_);
lean_dec_ref(v___y_6487_);
lean_dec_ref(v___y_6486_);
lean_dec_ref(v___y_6485_);
lean_dec(v___y_6484_);
lean_dec(v___y_6483_);
lean_dec(v___y_6482_);
lean_dec(v___y_6481_);
lean_dec_ref(v_remaining_6479_);
lean_dec_ref(v_alts_6478_);
lean_dec(v_matcherName_6473_);
lean_dec_ref(v_toMatcherInfo_6472_);
lean_dec_ref(v_onRemaining_6464_);
lean_dec_ref(v_onAlt_6463_);
lean_dec_ref(v_matcherApp_6458_);
v_a_6568_ = lean_ctor_get(v___x_6504_, 0);
v_isSharedCheck_6575_ = !lean_is_exclusive(v___x_6504_);
if (v_isSharedCheck_6575_ == 0)
{
v___x_6570_ = v___x_6504_;
v_isShared_6571_ = v_isSharedCheck_6575_;
goto v_resetjp_6569_;
}
else
{
lean_inc(v_a_6568_);
lean_dec(v___x_6504_);
v___x_6570_ = lean_box(0);
v_isShared_6571_ = v_isSharedCheck_6575_;
goto v_resetjp_6569_;
}
v_resetjp_6569_:
{
lean_object* v___x_6573_; 
if (v_isShared_6571_ == 0)
{
v___x_6573_ = v___x_6570_;
goto v_reusejp_6572_;
}
else
{
lean_object* v_reuseFailAlloc_6574_; 
v_reuseFailAlloc_6574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6574_, 0, v_a_6568_);
v___x_6573_ = v_reuseFailAlloc_6574_;
goto v_reusejp_6572_;
}
v_reusejp_6572_:
{
return v___x_6573_;
}
}
}
}
v___jp_6577_:
{
lean_object* v___x_6590_; lean_object* v_remaining_x27_6591_; lean_object* v___x_6592_; lean_object* v___x_6593_; lean_object* v___x_6594_; lean_object* v___x_6595_; lean_object* v___x_6596_; lean_object* v___x_6597_; size_t v_sz_6598_; lean_object* v___x_6599_; 
v___x_6590_ = lean_unsigned_to_nat(0u);
v_remaining_x27_6591_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_6592_ = l_Array_reverse___redArg(v___y_6580_);
v___x_6593_ = lean_array_get_size(v___x_6592_);
v___x_6594_ = l_Array_toSubarray___redArg(v___x_6592_, v___x_6590_, v___x_6593_);
lean_inc_ref(v___y_6583_);
v___x_6595_ = l_Array_reverse___redArg(v___y_6583_);
v___x_6596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6596_, 0, v___x_6590_);
lean_ctor_set(v___x_6596_, 1, v___x_6594_);
v___x_6597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6597_, 0, v_remaining_x27_6591_);
lean_ctor_set(v___x_6597_, 1, v___x_6596_);
v_sz_6598_ = lean_array_size(v___x_6595_);
lean_inc(v___y_6589_);
lean_inc_ref(v___y_6588_);
lean_inc(v___y_6587_);
lean_inc_ref(v___y_6586_);
v___x_6599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(v___x_6595_, v_sz_6598_, v___y_6578_, v___x_6597_, v___y_6586_, v___y_6587_, v___y_6588_, v___y_6589_);
lean_dec_ref(v___x_6595_);
if (lean_obj_tag(v___x_6599_) == 0)
{
lean_object* v_a_6600_; lean_object* v_snd_6601_; 
v_a_6600_ = lean_ctor_get(v___x_6599_, 0);
lean_inc(v_a_6600_);
lean_dec_ref(v___x_6599_);
v_snd_6601_ = lean_ctor_get(v_a_6600_, 1);
lean_inc(v_snd_6601_);
if (v_useSplitter_6459_ == 0)
{
lean_object* v_fst_6602_; lean_object* v_fst_6603_; 
lean_dec(v___y_6584_);
v_fst_6602_ = lean_ctor_get(v_a_6600_, 0);
lean_inc(v_fst_6602_);
lean_dec(v_a_6600_);
v_fst_6603_ = lean_ctor_get(v_snd_6601_, 0);
lean_inc(v_fst_6603_);
lean_dec(v_snd_6601_);
v___y_6481_ = v___x_6590_;
v___y_6482_ = v___y_6587_;
v___y_6483_ = v___y_6589_;
v___y_6484_ = v_fst_6603_;
v___y_6485_ = v_matcherLevels_6585_;
v___y_6486_ = v___y_6582_;
v___y_6487_ = v___y_6581_;
v___y_6488_ = v___y_6586_;
v___y_6489_ = v___y_6583_;
v___y_6490_ = v_remaining_x27_6591_;
v___y_6491_ = v_fst_6602_;
v___y_6492_ = v___y_6579_;
v___y_6493_ = v___y_6588_;
goto v___jp_6480_;
}
else
{
if (v_isCasesOn_6576_ == 0)
{
lean_object* v___x_6605_; uint8_t v_isShared_6606_; uint8_t v_isSharedCheck_6760_; 
v_isSharedCheck_6760_ = !lean_is_exclusive(v_matcherApp_6458_);
if (v_isSharedCheck_6760_ == 0)
{
lean_object* v_unused_6761_; lean_object* v_unused_6762_; lean_object* v_unused_6763_; lean_object* v_unused_6764_; lean_object* v_unused_6765_; lean_object* v_unused_6766_; lean_object* v_unused_6767_; lean_object* v_unused_6768_; 
v_unused_6761_ = lean_ctor_get(v_matcherApp_6458_, 7);
lean_dec(v_unused_6761_);
v_unused_6762_ = lean_ctor_get(v_matcherApp_6458_, 6);
lean_dec(v_unused_6762_);
v_unused_6763_ = lean_ctor_get(v_matcherApp_6458_, 5);
lean_dec(v_unused_6763_);
v_unused_6764_ = lean_ctor_get(v_matcherApp_6458_, 4);
lean_dec(v_unused_6764_);
v_unused_6765_ = lean_ctor_get(v_matcherApp_6458_, 3);
lean_dec(v_unused_6765_);
v_unused_6766_ = lean_ctor_get(v_matcherApp_6458_, 2);
lean_dec(v_unused_6766_);
v_unused_6767_ = lean_ctor_get(v_matcherApp_6458_, 1);
lean_dec(v_unused_6767_);
v_unused_6768_ = lean_ctor_get(v_matcherApp_6458_, 0);
lean_dec(v_unused_6768_);
v___x_6605_ = v_matcherApp_6458_;
v_isShared_6606_ = v_isSharedCheck_6760_;
goto v_resetjp_6604_;
}
else
{
lean_dec(v_matcherApp_6458_);
v___x_6605_ = lean_box(0);
v_isShared_6606_ = v_isSharedCheck_6760_;
goto v_resetjp_6604_;
}
v_resetjp_6604_:
{
lean_object* v_fst_6607_; lean_object* v___x_6609_; uint8_t v_isShared_6610_; uint8_t v_isSharedCheck_6758_; 
v_fst_6607_ = lean_ctor_get(v_a_6600_, 0);
v_isSharedCheck_6758_ = !lean_is_exclusive(v_a_6600_);
if (v_isSharedCheck_6758_ == 0)
{
lean_object* v_unused_6759_; 
v_unused_6759_ = lean_ctor_get(v_a_6600_, 1);
lean_dec(v_unused_6759_);
v___x_6609_ = v_a_6600_;
v_isShared_6610_ = v_isSharedCheck_6758_;
goto v_resetjp_6608_;
}
else
{
lean_inc(v_fst_6607_);
lean_dec(v_a_6600_);
v___x_6609_ = lean_box(0);
v_isShared_6610_ = v_isSharedCheck_6758_;
goto v_resetjp_6608_;
}
v_resetjp_6608_:
{
lean_object* v_fst_6611_; lean_object* v___x_6613_; uint8_t v_isShared_6614_; uint8_t v_isSharedCheck_6756_; 
v_fst_6611_ = lean_ctor_get(v_snd_6601_, 0);
v_isSharedCheck_6756_ = !lean_is_exclusive(v_snd_6601_);
if (v_isSharedCheck_6756_ == 0)
{
lean_object* v_unused_6757_; 
v_unused_6757_ = lean_ctor_get(v_snd_6601_, 1);
lean_dec(v_unused_6757_);
v___x_6613_ = v_snd_6601_;
v_isShared_6614_ = v_isSharedCheck_6756_;
goto v_resetjp_6612_;
}
else
{
lean_inc(v_fst_6611_);
lean_dec(v_snd_6601_);
v___x_6613_ = lean_box(0);
v_isShared_6614_ = v_isSharedCheck_6756_;
goto v_resetjp_6612_;
}
v_resetjp_6612_:
{
lean_object* v___x_6615_; lean_object* v___x_6616_; lean_object* v_aux1_6617_; lean_object* v_aux1_6618_; lean_object* v_aux1_6619_; lean_object* v___x_6620_; lean_object* v___x_6621_; lean_object* v___x_6622_; lean_object* v___x_6623_; lean_object* v___x_6624_; lean_object* v___f_6625_; lean_object* v___x_6626_; lean_object* v___x_6627_; 
lean_inc_ref(v_matcherLevels_6585_);
v___x_6615_ = lean_array_to_list(v_matcherLevels_6585_);
lean_inc(v___x_6615_);
lean_inc(v_matcherName_6473_);
v___x_6616_ = l_Lean_mkConst(v_matcherName_6473_, v___x_6615_);
v_aux1_6617_ = l_Lean_mkAppN(v___x_6616_, v___y_6579_);
lean_inc_ref(v___y_6581_);
v_aux1_6618_ = l_Lean_Expr_app___override(v_aux1_6617_, v___y_6581_);
v_aux1_6619_ = l_Lean_mkAppN(v_aux1_6618_, v___y_6583_);
v___x_6620_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__3);
lean_inc_ref(v_aux1_6619_);
v___x_6621_ = l_Lean_indentExpr(v_aux1_6619_);
v___x_6622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6622_, 0, v___x_6620_);
lean_ctor_set(v___x_6622_, 1, v___x_6621_);
v___x_6623_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__5);
v___x_6624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6624_, 0, v___x_6622_);
lean_ctor_set(v___x_6624_, 1, v___x_6623_);
v___f_6625_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6625_, 0, v___x_6624_);
lean_inc_ref(v_aux1_6619_);
v___x_6626_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(v___x_6626_, 0, v_aux1_6619_);
lean_inc(v___y_6589_);
lean_inc_ref(v___y_6588_);
lean_inc(v___y_6587_);
lean_inc_ref(v___y_6586_);
v___x_6627_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6626_, v___f_6625_, v___y_6586_, v___y_6587_, v___y_6588_, v___y_6589_);
if (lean_obj_tag(v___x_6627_) == 0)
{
lean_object* v___x_6628_; lean_object* v___x_6629_; 
lean_dec_ref(v___x_6627_);
v___x_6628_ = lean_array_get_size(v_alts_6478_);
lean_inc(v___y_6589_);
lean_inc_ref(v___y_6588_);
lean_inc(v___y_6587_);
lean_inc_ref(v___y_6586_);
v___x_6629_ = l_Lean_Meta_inferArgumentTypesN(v___x_6628_, v_aux1_6619_, v___y_6586_, v___y_6587_, v___y_6588_, v___y_6589_);
if (lean_obj_tag(v___x_6629_) == 0)
{
lean_object* v_a_6630_; lean_object* v___x_6631_; 
v_a_6630_ = lean_ctor_get(v___x_6629_, 0);
lean_inc(v_a_6630_);
lean_dec_ref(v___x_6629_);
lean_inc(v___y_6589_);
lean_inc_ref(v___y_6588_);
lean_inc(v___y_6587_);
lean_inc_ref(v___y_6586_);
v___x_6631_ = lean_get_match_equations_for(v_matcherName_6473_, v___y_6586_, v___y_6587_, v___y_6588_, v___y_6589_);
if (lean_obj_tag(v___x_6631_) == 0)
{
lean_object* v_a_6632_; lean_object* v_splitterName_6633_; lean_object* v_splitterMatchInfo_6634_; lean_object* v___x_6635_; lean_object* v_aux2_6636_; lean_object* v_aux2_6637_; lean_object* v_aux2_6638_; lean_object* v___x_6639_; lean_object* v___x_6640_; lean_object* v___x_6641_; lean_object* v___x_6642_; lean_object* v___f_6643_; lean_object* v___x_6644_; lean_object* v___x_6645_; 
v_a_6632_ = lean_ctor_get(v___x_6631_, 0);
lean_inc(v_a_6632_);
lean_dec_ref(v___x_6631_);
v_splitterName_6633_ = lean_ctor_get(v_a_6632_, 1);
lean_inc(v_splitterName_6633_);
v_splitterMatchInfo_6634_ = lean_ctor_get(v_a_6632_, 2);
lean_inc_ref(v_splitterMatchInfo_6634_);
lean_dec(v_a_6632_);
lean_inc(v_splitterName_6633_);
v___x_6635_ = l_Lean_mkConst(v_splitterName_6633_, v___x_6615_);
v_aux2_6636_ = l_Lean_mkAppN(v___x_6635_, v___y_6579_);
lean_inc_ref(v___y_6581_);
v_aux2_6637_ = l_Lean_Expr_app___override(v_aux2_6636_, v___y_6581_);
v_aux2_6638_ = l_Lean_mkAppN(v_aux2_6637_, v___y_6583_);
v___x_6639_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1);
lean_inc_ref(v_aux2_6638_);
v___x_6640_ = l_Lean_indentExpr(v_aux2_6638_);
v___x_6641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6641_, 0, v___x_6639_);
lean_ctor_set(v___x_6641_, 1, v___x_6640_);
v___x_6642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6642_, 0, v___x_6641_);
lean_ctor_set(v___x_6642_, 1, v___x_6623_);
v___f_6643_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6643_, 0, v___x_6642_);
lean_inc_ref(v_aux2_6638_);
v___x_6644_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(v___x_6644_, 0, v_aux2_6638_);
lean_inc(v___y_6589_);
lean_inc_ref(v___y_6588_);
lean_inc(v___y_6587_);
lean_inc_ref(v___y_6586_);
v___x_6645_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6644_, v___f_6643_, v___y_6586_, v___y_6587_, v___y_6588_, v___y_6589_);
if (lean_obj_tag(v___x_6645_) == 0)
{
lean_object* v___x_6646_; 
lean_dec_ref(v___x_6645_);
lean_inc(v___y_6589_);
lean_inc_ref(v___y_6588_);
lean_inc(v___y_6587_);
lean_inc_ref(v___y_6586_);
v___x_6646_ = l_Lean_Meta_inferArgumentTypesN(v___x_6628_, v_aux2_6638_, v___y_6586_, v___y_6587_, v___y_6588_, v___y_6589_);
if (lean_obj_tag(v___x_6646_) == 0)
{
lean_object* v_a_6647_; lean_object* v_numParams_6648_; lean_object* v_numDiscrs_6649_; lean_object* v_altInfos_6650_; lean_object* v_uElimPos_x3f_6651_; lean_object* v_overlaps_6652_; lean_object* v_altInfos_6653_; lean_object* v___x_6655_; uint8_t v_isShared_6656_; uint8_t v_isSharedCheck_6710_; 
v_a_6647_ = lean_ctor_get(v___x_6646_, 0);
lean_inc(v_a_6647_);
lean_dec_ref(v___x_6646_);
v_numParams_6648_ = lean_ctor_get(v_toMatcherInfo_6472_, 0);
lean_inc(v_numParams_6648_);
v_numDiscrs_6649_ = lean_ctor_get(v_toMatcherInfo_6472_, 1);
lean_inc(v_numDiscrs_6649_);
v_altInfos_6650_ = lean_ctor_get(v_toMatcherInfo_6472_, 2);
lean_inc_ref(v_altInfos_6650_);
v_uElimPos_x3f_6651_ = lean_ctor_get(v_toMatcherInfo_6472_, 3);
lean_inc(v_uElimPos_x3f_6651_);
v_overlaps_6652_ = lean_ctor_get(v_toMatcherInfo_6472_, 5);
lean_inc_ref(v_overlaps_6652_);
lean_dec_ref(v_toMatcherInfo_6472_);
v_altInfos_6653_ = lean_ctor_get(v_splitterMatchInfo_6634_, 2);
v_isSharedCheck_6710_ = !lean_is_exclusive(v_splitterMatchInfo_6634_);
if (v_isSharedCheck_6710_ == 0)
{
lean_object* v_unused_6711_; lean_object* v_unused_6712_; lean_object* v_unused_6713_; lean_object* v_unused_6714_; lean_object* v_unused_6715_; 
v_unused_6711_ = lean_ctor_get(v_splitterMatchInfo_6634_, 5);
lean_dec(v_unused_6711_);
v_unused_6712_ = lean_ctor_get(v_splitterMatchInfo_6634_, 4);
lean_dec(v_unused_6712_);
v_unused_6713_ = lean_ctor_get(v_splitterMatchInfo_6634_, 3);
lean_dec(v_unused_6713_);
v_unused_6714_ = lean_ctor_get(v_splitterMatchInfo_6634_, 1);
lean_dec(v_unused_6714_);
v_unused_6715_ = lean_ctor_get(v_splitterMatchInfo_6634_, 0);
lean_dec(v_unused_6715_);
v___x_6655_ = v_splitterMatchInfo_6634_;
v_isShared_6656_ = v_isSharedCheck_6710_;
goto v_resetjp_6654_;
}
else
{
lean_inc(v_altInfos_6653_);
lean_dec(v_splitterMatchInfo_6634_);
v___x_6655_ = lean_box(0);
v_isShared_6656_ = v_isSharedCheck_6710_;
goto v_resetjp_6654_;
}
v_resetjp_6654_:
{
lean_object* v___x_6657_; lean_object* v___x_6658_; lean_object* v___x_6659_; lean_object* v___x_6660_; lean_object* v___x_6661_; lean_object* v___x_6662_; lean_object* v___x_6663_; lean_object* v___x_6664_; lean_object* v___x_6665_; lean_object* v___x_6667_; 
v___x_6657_ = lean_array_get_size(v_altInfos_6650_);
v___x_6658_ = lean_array_get_size(v_altInfos_6653_);
v___x_6659_ = lean_array_get_size(v_a_6630_);
v___x_6660_ = lean_array_get_size(v_a_6647_);
v___x_6661_ = l_Array_toSubarray___redArg(v_alts_6478_, v___x_6590_, v___x_6628_);
lean_inc_ref(v_altInfos_6650_);
v___x_6662_ = l_Array_toSubarray___redArg(v_altInfos_6650_, v___x_6590_, v___x_6657_);
v___x_6663_ = l_Array_toSubarray___redArg(v_altInfos_6653_, v___x_6590_, v___x_6658_);
v___x_6664_ = l_Array_toSubarray___redArg(v_a_6630_, v___x_6590_, v___x_6659_);
v___x_6665_ = l_Array_toSubarray___redArg(v_a_6647_, v___x_6590_, v___x_6660_);
if (v_isShared_6614_ == 0)
{
lean_ctor_set(v___x_6613_, 1, v___x_6665_);
lean_ctor_set(v___x_6613_, 0, v___x_6664_);
v___x_6667_ = v___x_6613_;
goto v_reusejp_6666_;
}
else
{
lean_object* v_reuseFailAlloc_6709_; 
v_reuseFailAlloc_6709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6709_, 0, v___x_6664_);
lean_ctor_set(v_reuseFailAlloc_6709_, 1, v___x_6665_);
v___x_6667_ = v_reuseFailAlloc_6709_;
goto v_reusejp_6666_;
}
v_reusejp_6666_:
{
lean_object* v___x_6669_; 
if (v_isShared_6610_ == 0)
{
lean_ctor_set(v___x_6609_, 1, v___x_6667_);
lean_ctor_set(v___x_6609_, 0, v___x_6663_);
v___x_6669_ = v___x_6609_;
goto v_reusejp_6668_;
}
else
{
lean_object* v_reuseFailAlloc_6708_; 
v_reuseFailAlloc_6708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6708_, 0, v___x_6663_);
lean_ctor_set(v_reuseFailAlloc_6708_, 1, v___x_6667_);
v___x_6669_ = v_reuseFailAlloc_6708_;
goto v_reusejp_6668_;
}
v_reusejp_6668_:
{
lean_object* v___x_6670_; lean_object* v___x_6671_; lean_object* v___x_6672_; lean_object* v___x_6673_; 
v___x_6670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6670_, 0, v___x_6662_);
lean_ctor_set(v___x_6670_, 1, v___x_6669_);
v___x_6671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6671_, 0, v___x_6661_);
lean_ctor_set(v___x_6671_, 1, v___x_6670_);
v___x_6672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6672_, 0, v_remaining_x27_6591_);
lean_ctor_set(v___x_6672_, 1, v___x_6671_);
lean_inc(v___y_6589_);
lean_inc_ref(v___y_6588_);
lean_inc(v___y_6587_);
lean_inc_ref(v___y_6586_);
v___x_6673_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v___x_6628_, v_onAlt_6463_, v_useSplitter_6459_, v_fst_6611_, v___y_6584_, v___x_6590_, v___x_6672_, v___y_6586_, v___y_6587_, v___y_6588_, v___y_6589_);
if (lean_obj_tag(v___x_6673_) == 0)
{
lean_object* v_a_6674_; lean_object* v_fst_6675_; lean_object* v___x_6676_; 
v_a_6674_ = lean_ctor_get(v___x_6673_, 0);
lean_inc(v_a_6674_);
lean_dec_ref(v___x_6673_);
v_fst_6675_ = lean_ctor_get(v_a_6674_, 0);
lean_inc(v_fst_6675_);
lean_dec(v_a_6674_);
v___x_6676_ = lean_apply_6(v_onRemaining_6464_, v_remaining_6479_, v___y_6586_, v___y_6587_, v___y_6588_, v___y_6589_, lean_box(0));
if (lean_obj_tag(v___x_6676_) == 0)
{
lean_object* v_a_6677_; lean_object* v___x_6679_; uint8_t v_isShared_6680_; uint8_t v_isSharedCheck_6691_; 
v_a_6677_ = lean_ctor_get(v___x_6676_, 0);
v_isSharedCheck_6691_ = !lean_is_exclusive(v___x_6676_);
if (v_isSharedCheck_6691_ == 0)
{
v___x_6679_ = v___x_6676_;
v_isShared_6680_ = v_isSharedCheck_6691_;
goto v_resetjp_6678_;
}
else
{
lean_inc(v_a_6677_);
lean_dec(v___x_6676_);
v___x_6679_ = lean_box(0);
v_isShared_6680_ = v_isSharedCheck_6691_;
goto v_resetjp_6678_;
}
v_resetjp_6678_:
{
lean_object* v_remaining_x27_6681_; lean_object* v___x_6683_; 
v_remaining_x27_6681_ = l_Array_append___redArg(v_fst_6607_, v_a_6677_);
lean_dec(v_a_6677_);
if (v_isShared_6656_ == 0)
{
lean_ctor_set(v___x_6655_, 5, v_overlaps_6652_);
lean_ctor_set(v___x_6655_, 4, v___y_6582_);
lean_ctor_set(v___x_6655_, 3, v_uElimPos_x3f_6651_);
lean_ctor_set(v___x_6655_, 2, v_altInfos_6650_);
lean_ctor_set(v___x_6655_, 1, v_numDiscrs_6649_);
lean_ctor_set(v___x_6655_, 0, v_numParams_6648_);
v___x_6683_ = v___x_6655_;
goto v_reusejp_6682_;
}
else
{
lean_object* v_reuseFailAlloc_6690_; 
v_reuseFailAlloc_6690_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6690_, 0, v_numParams_6648_);
lean_ctor_set(v_reuseFailAlloc_6690_, 1, v_numDiscrs_6649_);
lean_ctor_set(v_reuseFailAlloc_6690_, 2, v_altInfos_6650_);
lean_ctor_set(v_reuseFailAlloc_6690_, 3, v_uElimPos_x3f_6651_);
lean_ctor_set(v_reuseFailAlloc_6690_, 4, v___y_6582_);
lean_ctor_set(v_reuseFailAlloc_6690_, 5, v_overlaps_6652_);
v___x_6683_ = v_reuseFailAlloc_6690_;
goto v_reusejp_6682_;
}
v_reusejp_6682_:
{
lean_object* v___x_6685_; 
if (v_isShared_6606_ == 0)
{
lean_ctor_set(v___x_6605_, 7, v_remaining_x27_6681_);
lean_ctor_set(v___x_6605_, 6, v_fst_6675_);
lean_ctor_set(v___x_6605_, 5, v___y_6583_);
lean_ctor_set(v___x_6605_, 4, v___y_6581_);
lean_ctor_set(v___x_6605_, 3, v___y_6579_);
lean_ctor_set(v___x_6605_, 2, v_matcherLevels_6585_);
lean_ctor_set(v___x_6605_, 1, v_splitterName_6633_);
lean_ctor_set(v___x_6605_, 0, v___x_6683_);
v___x_6685_ = v___x_6605_;
goto v_reusejp_6684_;
}
else
{
lean_object* v_reuseFailAlloc_6689_; 
v_reuseFailAlloc_6689_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_6689_, 0, v___x_6683_);
lean_ctor_set(v_reuseFailAlloc_6689_, 1, v_splitterName_6633_);
lean_ctor_set(v_reuseFailAlloc_6689_, 2, v_matcherLevels_6585_);
lean_ctor_set(v_reuseFailAlloc_6689_, 3, v___y_6579_);
lean_ctor_set(v_reuseFailAlloc_6689_, 4, v___y_6581_);
lean_ctor_set(v_reuseFailAlloc_6689_, 5, v___y_6583_);
lean_ctor_set(v_reuseFailAlloc_6689_, 6, v_fst_6675_);
lean_ctor_set(v_reuseFailAlloc_6689_, 7, v_remaining_x27_6681_);
v___x_6685_ = v_reuseFailAlloc_6689_;
goto v_reusejp_6684_;
}
v_reusejp_6684_:
{
lean_object* v___x_6687_; 
if (v_isShared_6680_ == 0)
{
lean_ctor_set(v___x_6679_, 0, v___x_6685_);
v___x_6687_ = v___x_6679_;
goto v_reusejp_6686_;
}
else
{
lean_object* v_reuseFailAlloc_6688_; 
v_reuseFailAlloc_6688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6688_, 0, v___x_6685_);
v___x_6687_ = v_reuseFailAlloc_6688_;
goto v_reusejp_6686_;
}
v_reusejp_6686_:
{
return v___x_6687_;
}
}
}
}
}
else
{
lean_object* v_a_6692_; lean_object* v___x_6694_; uint8_t v_isShared_6695_; uint8_t v_isSharedCheck_6699_; 
lean_dec(v_fst_6675_);
lean_del_object(v___x_6655_);
lean_dec_ref(v_overlaps_6652_);
lean_dec(v_uElimPos_x3f_6651_);
lean_dec_ref(v_altInfos_6650_);
lean_dec(v_numDiscrs_6649_);
lean_dec(v_numParams_6648_);
lean_dec(v_splitterName_6633_);
lean_dec(v_fst_6607_);
lean_del_object(v___x_6605_);
lean_dec_ref(v_matcherLevels_6585_);
lean_dec_ref(v___y_6583_);
lean_dec_ref(v___y_6582_);
lean_dec_ref(v___y_6581_);
lean_dec_ref(v___y_6579_);
v_a_6692_ = lean_ctor_get(v___x_6676_, 0);
v_isSharedCheck_6699_ = !lean_is_exclusive(v___x_6676_);
if (v_isSharedCheck_6699_ == 0)
{
v___x_6694_ = v___x_6676_;
v_isShared_6695_ = v_isSharedCheck_6699_;
goto v_resetjp_6693_;
}
else
{
lean_inc(v_a_6692_);
lean_dec(v___x_6676_);
v___x_6694_ = lean_box(0);
v_isShared_6695_ = v_isSharedCheck_6699_;
goto v_resetjp_6693_;
}
v_resetjp_6693_:
{
lean_object* v___x_6697_; 
if (v_isShared_6695_ == 0)
{
v___x_6697_ = v___x_6694_;
goto v_reusejp_6696_;
}
else
{
lean_object* v_reuseFailAlloc_6698_; 
v_reuseFailAlloc_6698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6698_, 0, v_a_6692_);
v___x_6697_ = v_reuseFailAlloc_6698_;
goto v_reusejp_6696_;
}
v_reusejp_6696_:
{
return v___x_6697_;
}
}
}
}
else
{
lean_object* v_a_6700_; lean_object* v___x_6702_; uint8_t v_isShared_6703_; uint8_t v_isSharedCheck_6707_; 
lean_del_object(v___x_6655_);
lean_dec_ref(v_overlaps_6652_);
lean_dec(v_uElimPos_x3f_6651_);
lean_dec_ref(v_altInfos_6650_);
lean_dec(v_numDiscrs_6649_);
lean_dec(v_numParams_6648_);
lean_dec(v_splitterName_6633_);
lean_dec(v_fst_6607_);
lean_del_object(v___x_6605_);
lean_dec(v___y_6589_);
lean_dec_ref(v___y_6588_);
lean_dec(v___y_6587_);
lean_dec_ref(v___y_6586_);
lean_dec_ref(v_matcherLevels_6585_);
lean_dec_ref(v___y_6583_);
lean_dec_ref(v___y_6582_);
lean_dec_ref(v___y_6581_);
lean_dec_ref(v___y_6579_);
lean_dec_ref(v_remaining_6479_);
lean_dec_ref(v_onRemaining_6464_);
v_a_6700_ = lean_ctor_get(v___x_6673_, 0);
v_isSharedCheck_6707_ = !lean_is_exclusive(v___x_6673_);
if (v_isSharedCheck_6707_ == 0)
{
v___x_6702_ = v___x_6673_;
v_isShared_6703_ = v_isSharedCheck_6707_;
goto v_resetjp_6701_;
}
else
{
lean_inc(v_a_6700_);
lean_dec(v___x_6673_);
v___x_6702_ = lean_box(0);
v_isShared_6703_ = v_isSharedCheck_6707_;
goto v_resetjp_6701_;
}
v_resetjp_6701_:
{
lean_object* v___x_6705_; 
if (v_isShared_6703_ == 0)
{
v___x_6705_ = v___x_6702_;
goto v_reusejp_6704_;
}
else
{
lean_object* v_reuseFailAlloc_6706_; 
v_reuseFailAlloc_6706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6706_, 0, v_a_6700_);
v___x_6705_ = v_reuseFailAlloc_6706_;
goto v_reusejp_6704_;
}
v_reusejp_6704_:
{
return v___x_6705_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_6716_; lean_object* v___x_6718_; uint8_t v_isShared_6719_; uint8_t v_isSharedCheck_6723_; 
lean_dec_ref(v_splitterMatchInfo_6634_);
lean_dec(v_splitterName_6633_);
lean_dec(v_a_6630_);
lean_del_object(v___x_6613_);
lean_dec(v_fst_6611_);
lean_del_object(v___x_6609_);
lean_dec(v_fst_6607_);
lean_del_object(v___x_6605_);
lean_dec(v___y_6589_);
lean_dec_ref(v___y_6588_);
lean_dec(v___y_6587_);
lean_dec_ref(v___y_6586_);
lean_dec_ref(v_matcherLevels_6585_);
lean_dec(v___y_6584_);
lean_dec_ref(v___y_6583_);
lean_dec_ref(v___y_6582_);
lean_dec_ref(v___y_6581_);
lean_dec_ref(v___y_6579_);
lean_dec_ref(v_remaining_6479_);
lean_dec_ref(v_alts_6478_);
lean_dec_ref(v_toMatcherInfo_6472_);
lean_dec_ref(v_onRemaining_6464_);
lean_dec_ref(v_onAlt_6463_);
v_a_6716_ = lean_ctor_get(v___x_6646_, 0);
v_isSharedCheck_6723_ = !lean_is_exclusive(v___x_6646_);
if (v_isSharedCheck_6723_ == 0)
{
v___x_6718_ = v___x_6646_;
v_isShared_6719_ = v_isSharedCheck_6723_;
goto v_resetjp_6717_;
}
else
{
lean_inc(v_a_6716_);
lean_dec(v___x_6646_);
v___x_6718_ = lean_box(0);
v_isShared_6719_ = v_isSharedCheck_6723_;
goto v_resetjp_6717_;
}
v_resetjp_6717_:
{
lean_object* v___x_6721_; 
if (v_isShared_6719_ == 0)
{
v___x_6721_ = v___x_6718_;
goto v_reusejp_6720_;
}
else
{
lean_object* v_reuseFailAlloc_6722_; 
v_reuseFailAlloc_6722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6722_, 0, v_a_6716_);
v___x_6721_ = v_reuseFailAlloc_6722_;
goto v_reusejp_6720_;
}
v_reusejp_6720_:
{
return v___x_6721_;
}
}
}
}
else
{
lean_object* v_a_6724_; lean_object* v___x_6726_; uint8_t v_isShared_6727_; uint8_t v_isSharedCheck_6731_; 
lean_dec_ref(v_aux2_6638_);
lean_dec_ref(v_splitterMatchInfo_6634_);
lean_dec(v_splitterName_6633_);
lean_dec(v_a_6630_);
lean_del_object(v___x_6613_);
lean_dec(v_fst_6611_);
lean_del_object(v___x_6609_);
lean_dec(v_fst_6607_);
lean_del_object(v___x_6605_);
lean_dec(v___y_6589_);
lean_dec_ref(v___y_6588_);
lean_dec(v___y_6587_);
lean_dec_ref(v___y_6586_);
lean_dec_ref(v_matcherLevels_6585_);
lean_dec(v___y_6584_);
lean_dec_ref(v___y_6583_);
lean_dec_ref(v___y_6582_);
lean_dec_ref(v___y_6581_);
lean_dec_ref(v___y_6579_);
lean_dec_ref(v_remaining_6479_);
lean_dec_ref(v_alts_6478_);
lean_dec_ref(v_toMatcherInfo_6472_);
lean_dec_ref(v_onRemaining_6464_);
lean_dec_ref(v_onAlt_6463_);
v_a_6724_ = lean_ctor_get(v___x_6645_, 0);
v_isSharedCheck_6731_ = !lean_is_exclusive(v___x_6645_);
if (v_isSharedCheck_6731_ == 0)
{
v___x_6726_ = v___x_6645_;
v_isShared_6727_ = v_isSharedCheck_6731_;
goto v_resetjp_6725_;
}
else
{
lean_inc(v_a_6724_);
lean_dec(v___x_6645_);
v___x_6726_ = lean_box(0);
v_isShared_6727_ = v_isSharedCheck_6731_;
goto v_resetjp_6725_;
}
v_resetjp_6725_:
{
lean_object* v___x_6729_; 
if (v_isShared_6727_ == 0)
{
v___x_6729_ = v___x_6726_;
goto v_reusejp_6728_;
}
else
{
lean_object* v_reuseFailAlloc_6730_; 
v_reuseFailAlloc_6730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6730_, 0, v_a_6724_);
v___x_6729_ = v_reuseFailAlloc_6730_;
goto v_reusejp_6728_;
}
v_reusejp_6728_:
{
return v___x_6729_;
}
}
}
}
else
{
lean_object* v_a_6732_; lean_object* v___x_6734_; uint8_t v_isShared_6735_; uint8_t v_isSharedCheck_6739_; 
lean_dec(v_a_6630_);
lean_dec(v___x_6615_);
lean_del_object(v___x_6613_);
lean_dec(v_fst_6611_);
lean_del_object(v___x_6609_);
lean_dec(v_fst_6607_);
lean_del_object(v___x_6605_);
lean_dec(v___y_6589_);
lean_dec_ref(v___y_6588_);
lean_dec(v___y_6587_);
lean_dec_ref(v___y_6586_);
lean_dec_ref(v_matcherLevels_6585_);
lean_dec(v___y_6584_);
lean_dec_ref(v___y_6583_);
lean_dec_ref(v___y_6582_);
lean_dec_ref(v___y_6581_);
lean_dec_ref(v___y_6579_);
lean_dec_ref(v_remaining_6479_);
lean_dec_ref(v_alts_6478_);
lean_dec_ref(v_toMatcherInfo_6472_);
lean_dec_ref(v_onRemaining_6464_);
lean_dec_ref(v_onAlt_6463_);
v_a_6732_ = lean_ctor_get(v___x_6631_, 0);
v_isSharedCheck_6739_ = !lean_is_exclusive(v___x_6631_);
if (v_isSharedCheck_6739_ == 0)
{
v___x_6734_ = v___x_6631_;
v_isShared_6735_ = v_isSharedCheck_6739_;
goto v_resetjp_6733_;
}
else
{
lean_inc(v_a_6732_);
lean_dec(v___x_6631_);
v___x_6734_ = lean_box(0);
v_isShared_6735_ = v_isSharedCheck_6739_;
goto v_resetjp_6733_;
}
v_resetjp_6733_:
{
lean_object* v___x_6737_; 
if (v_isShared_6735_ == 0)
{
v___x_6737_ = v___x_6734_;
goto v_reusejp_6736_;
}
else
{
lean_object* v_reuseFailAlloc_6738_; 
v_reuseFailAlloc_6738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6738_, 0, v_a_6732_);
v___x_6737_ = v_reuseFailAlloc_6738_;
goto v_reusejp_6736_;
}
v_reusejp_6736_:
{
return v___x_6737_;
}
}
}
}
else
{
lean_object* v_a_6740_; lean_object* v___x_6742_; uint8_t v_isShared_6743_; uint8_t v_isSharedCheck_6747_; 
lean_dec(v___x_6615_);
lean_del_object(v___x_6613_);
lean_dec(v_fst_6611_);
lean_del_object(v___x_6609_);
lean_dec(v_fst_6607_);
lean_del_object(v___x_6605_);
lean_dec(v___y_6589_);
lean_dec_ref(v___y_6588_);
lean_dec(v___y_6587_);
lean_dec_ref(v___y_6586_);
lean_dec_ref(v_matcherLevels_6585_);
lean_dec(v___y_6584_);
lean_dec_ref(v___y_6583_);
lean_dec_ref(v___y_6582_);
lean_dec_ref(v___y_6581_);
lean_dec_ref(v___y_6579_);
lean_dec_ref(v_remaining_6479_);
lean_dec_ref(v_alts_6478_);
lean_dec(v_matcherName_6473_);
lean_dec_ref(v_toMatcherInfo_6472_);
lean_dec_ref(v_onRemaining_6464_);
lean_dec_ref(v_onAlt_6463_);
v_a_6740_ = lean_ctor_get(v___x_6629_, 0);
v_isSharedCheck_6747_ = !lean_is_exclusive(v___x_6629_);
if (v_isSharedCheck_6747_ == 0)
{
v___x_6742_ = v___x_6629_;
v_isShared_6743_ = v_isSharedCheck_6747_;
goto v_resetjp_6741_;
}
else
{
lean_inc(v_a_6740_);
lean_dec(v___x_6629_);
v___x_6742_ = lean_box(0);
v_isShared_6743_ = v_isSharedCheck_6747_;
goto v_resetjp_6741_;
}
v_resetjp_6741_:
{
lean_object* v___x_6745_; 
if (v_isShared_6743_ == 0)
{
v___x_6745_ = v___x_6742_;
goto v_reusejp_6744_;
}
else
{
lean_object* v_reuseFailAlloc_6746_; 
v_reuseFailAlloc_6746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6746_, 0, v_a_6740_);
v___x_6745_ = v_reuseFailAlloc_6746_;
goto v_reusejp_6744_;
}
v_reusejp_6744_:
{
return v___x_6745_;
}
}
}
}
else
{
lean_object* v_a_6748_; lean_object* v___x_6750_; uint8_t v_isShared_6751_; uint8_t v_isSharedCheck_6755_; 
lean_dec_ref(v_aux1_6619_);
lean_dec(v___x_6615_);
lean_del_object(v___x_6613_);
lean_dec(v_fst_6611_);
lean_del_object(v___x_6609_);
lean_dec(v_fst_6607_);
lean_del_object(v___x_6605_);
lean_dec(v___y_6589_);
lean_dec_ref(v___y_6588_);
lean_dec(v___y_6587_);
lean_dec_ref(v___y_6586_);
lean_dec_ref(v_matcherLevels_6585_);
lean_dec(v___y_6584_);
lean_dec_ref(v___y_6583_);
lean_dec_ref(v___y_6582_);
lean_dec_ref(v___y_6581_);
lean_dec_ref(v___y_6579_);
lean_dec_ref(v_remaining_6479_);
lean_dec_ref(v_alts_6478_);
lean_dec(v_matcherName_6473_);
lean_dec_ref(v_toMatcherInfo_6472_);
lean_dec_ref(v_onRemaining_6464_);
lean_dec_ref(v_onAlt_6463_);
v_a_6748_ = lean_ctor_get(v___x_6627_, 0);
v_isSharedCheck_6755_ = !lean_is_exclusive(v___x_6627_);
if (v_isSharedCheck_6755_ == 0)
{
v___x_6750_ = v___x_6627_;
v_isShared_6751_ = v_isSharedCheck_6755_;
goto v_resetjp_6749_;
}
else
{
lean_inc(v_a_6748_);
lean_dec(v___x_6627_);
v___x_6750_ = lean_box(0);
v_isShared_6751_ = v_isSharedCheck_6755_;
goto v_resetjp_6749_;
}
v_resetjp_6749_:
{
lean_object* v___x_6753_; 
if (v_isShared_6751_ == 0)
{
v___x_6753_ = v___x_6750_;
goto v_reusejp_6752_;
}
else
{
lean_object* v_reuseFailAlloc_6754_; 
v_reuseFailAlloc_6754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6754_, 0, v_a_6748_);
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
}
}
else
{
lean_object* v_fst_6769_; lean_object* v_fst_6770_; 
lean_dec(v___y_6584_);
v_fst_6769_ = lean_ctor_get(v_a_6600_, 0);
lean_inc(v_fst_6769_);
lean_dec(v_a_6600_);
v_fst_6770_ = lean_ctor_get(v_snd_6601_, 0);
lean_inc(v_fst_6770_);
lean_dec(v_snd_6601_);
v___y_6481_ = v___x_6590_;
v___y_6482_ = v___y_6587_;
v___y_6483_ = v___y_6589_;
v___y_6484_ = v_fst_6770_;
v___y_6485_ = v_matcherLevels_6585_;
v___y_6486_ = v___y_6582_;
v___y_6487_ = v___y_6581_;
v___y_6488_ = v___y_6586_;
v___y_6489_ = v___y_6583_;
v___y_6490_ = v_remaining_x27_6591_;
v___y_6491_ = v_fst_6769_;
v___y_6492_ = v___y_6579_;
v___y_6493_ = v___y_6588_;
goto v___jp_6480_;
}
}
}
else
{
lean_object* v_a_6771_; lean_object* v___x_6773_; uint8_t v_isShared_6774_; uint8_t v_isSharedCheck_6778_; 
lean_dec(v___y_6589_);
lean_dec_ref(v___y_6588_);
lean_dec(v___y_6587_);
lean_dec_ref(v___y_6586_);
lean_dec_ref(v_matcherLevels_6585_);
lean_dec(v___y_6584_);
lean_dec_ref(v___y_6583_);
lean_dec_ref(v___y_6582_);
lean_dec_ref(v___y_6581_);
lean_dec_ref(v___y_6579_);
lean_dec_ref(v_remaining_6479_);
lean_dec_ref(v_alts_6478_);
lean_dec(v_matcherName_6473_);
lean_dec_ref(v_toMatcherInfo_6472_);
lean_dec_ref(v_onRemaining_6464_);
lean_dec_ref(v_onAlt_6463_);
lean_dec_ref(v_matcherApp_6458_);
v_a_6771_ = lean_ctor_get(v___x_6599_, 0);
v_isSharedCheck_6778_ = !lean_is_exclusive(v___x_6599_);
if (v_isSharedCheck_6778_ == 0)
{
v___x_6773_ = v___x_6599_;
v_isShared_6774_ = v_isSharedCheck_6778_;
goto v_resetjp_6772_;
}
else
{
lean_inc(v_a_6771_);
lean_dec(v___x_6599_);
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
v___jp_6779_:
{
size_t v_sz_6785_; size_t v___x_6786_; lean_object* v___x_6787_; 
v_sz_6785_ = lean_array_size(v_params_6475_);
v___x_6786_ = ((size_t)0ULL);
lean_inc(v___y_6784_);
lean_inc_ref(v___y_6783_);
lean_inc(v___y_6782_);
lean_inc_ref(v___y_6781_);
lean_inc_ref(v_params_6475_);
lean_inc_ref(v_onParams_6461_);
v___x_6787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6461_, v_sz_6785_, v___x_6786_, v_params_6475_, v___y_6781_, v___y_6782_, v___y_6783_, v___y_6784_);
if (lean_obj_tag(v___x_6787_) == 0)
{
lean_object* v_a_6788_; size_t v_sz_6789_; lean_object* v___x_6790_; 
v_a_6788_ = lean_ctor_get(v___x_6787_, 0);
lean_inc(v_a_6788_);
lean_dec_ref(v___x_6787_);
v_sz_6789_ = lean_array_size(v_discrs_6477_);
lean_inc(v___y_6784_);
lean_inc_ref(v___y_6783_);
lean_inc(v___y_6782_);
lean_inc_ref(v___y_6781_);
lean_inc_ref(v_discrs_6477_);
v___x_6790_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6461_, v_sz_6789_, v___x_6786_, v_discrs_6477_, v___y_6781_, v___y_6782_, v___y_6783_, v___y_6784_);
if (lean_obj_tag(v___x_6790_) == 0)
{
lean_object* v_a_6791_; lean_object* v___x_6792_; lean_object* v___x_6793_; lean_object* v___f_6794_; uint8_t v___x_6795_; lean_object* v___x_6796_; 
v_a_6791_ = lean_ctor_get(v___x_6790_, 0);
lean_inc(v_a_6791_);
lean_dec_ref(v___x_6790_);
v___x_6792_ = lean_box(v_addEqualities_6460_);
v___x_6793_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed__const__1));
lean_inc_ref(v_discrs_6477_);
lean_inc(v_a_6791_);
lean_inc_ref(v_toMatcherInfo_6472_);
v___f_6794_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed), 13, 6);
lean_closure_set(v___f_6794_, 0, v_onMotive_6462_);
lean_closure_set(v___f_6794_, 1, v_toMatcherInfo_6472_);
lean_closure_set(v___f_6794_, 2, v_a_6791_);
lean_closure_set(v___f_6794_, 3, v___x_6792_);
lean_closure_set(v___f_6794_, 4, v___x_6793_);
lean_closure_set(v___f_6794_, 5, v_discrs_6477_);
v___x_6795_ = 0;
lean_inc(v___y_6784_);
lean_inc_ref(v___y_6783_);
lean_inc(v___y_6782_);
lean_inc_ref(v___y_6781_);
lean_inc_ref(v_motive_6476_);
v___x_6796_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_6476_, v___f_6794_, v___x_6795_, v___y_6781_, v___y_6782_, v___y_6783_, v___y_6784_);
if (lean_obj_tag(v___x_6796_) == 0)
{
lean_object* v_a_6797_; lean_object* v_snd_6798_; lean_object* v_snd_6799_; lean_object* v_uElimPos_x3f_6800_; 
v_a_6797_ = lean_ctor_get(v___x_6796_, 0);
lean_inc(v_a_6797_);
lean_dec_ref(v___x_6796_);
v_snd_6798_ = lean_ctor_get(v_a_6797_, 1);
v_snd_6799_ = lean_ctor_get(v_snd_6798_, 1);
lean_inc(v_snd_6799_);
v_uElimPos_x3f_6800_ = lean_ctor_get(v_toMatcherInfo_6472_, 3);
if (lean_obj_tag(v_uElimPos_x3f_6800_) == 0)
{
lean_object* v_fst_6801_; lean_object* v_fst_6802_; lean_object* v_snd_6803_; 
v_fst_6801_ = lean_ctor_get(v_a_6797_, 0);
lean_inc(v_fst_6801_);
lean_dec(v_a_6797_);
v_fst_6802_ = lean_ctor_get(v_snd_6799_, 0);
lean_inc(v_fst_6802_);
v_snd_6803_ = lean_ctor_get(v_snd_6799_, 1);
lean_inc(v_snd_6803_);
lean_dec(v_snd_6799_);
lean_inc_ref(v_matcherLevels_6474_);
v___y_6578_ = v___x_6786_;
v___y_6579_ = v_a_6788_;
v___y_6580_ = v_fst_6802_;
v___y_6581_ = v_fst_6801_;
v___y_6582_ = v_snd_6803_;
v___y_6583_ = v_a_6791_;
v___y_6584_ = v_numDiscrEqs_6780_;
v_matcherLevels_6585_ = v_matcherLevels_6474_;
v___y_6586_ = v___y_6781_;
v___y_6587_ = v___y_6782_;
v___y_6588_ = v___y_6783_;
v___y_6589_ = v___y_6784_;
goto v___jp_6577_;
}
else
{
lean_object* v_fst_6804_; lean_object* v_fst_6805_; lean_object* v_fst_6806_; lean_object* v_snd_6807_; lean_object* v_val_6808_; lean_object* v___x_6809_; 
lean_inc(v_snd_6798_);
v_fst_6804_ = lean_ctor_get(v_a_6797_, 0);
lean_inc(v_fst_6804_);
lean_dec(v_a_6797_);
v_fst_6805_ = lean_ctor_get(v_snd_6798_, 0);
lean_inc(v_fst_6805_);
lean_dec(v_snd_6798_);
v_fst_6806_ = lean_ctor_get(v_snd_6799_, 0);
lean_inc(v_fst_6806_);
v_snd_6807_ = lean_ctor_get(v_snd_6799_, 1);
lean_inc(v_snd_6807_);
lean_dec(v_snd_6799_);
v_val_6808_ = lean_ctor_get(v_uElimPos_x3f_6800_, 0);
lean_inc_ref(v_matcherLevels_6474_);
v___x_6809_ = lean_array_set(v_matcherLevels_6474_, v_val_6808_, v_fst_6805_);
v___y_6578_ = v___x_6786_;
v___y_6579_ = v_a_6788_;
v___y_6580_ = v_fst_6806_;
v___y_6581_ = v_fst_6804_;
v___y_6582_ = v_snd_6807_;
v___y_6583_ = v_a_6791_;
v___y_6584_ = v_numDiscrEqs_6780_;
v_matcherLevels_6585_ = v___x_6809_;
v___y_6586_ = v___y_6781_;
v___y_6587_ = v___y_6782_;
v___y_6588_ = v___y_6783_;
v___y_6589_ = v___y_6784_;
goto v___jp_6577_;
}
}
else
{
lean_object* v_a_6810_; lean_object* v___x_6812_; uint8_t v_isShared_6813_; uint8_t v_isSharedCheck_6817_; 
lean_dec(v_a_6791_);
lean_dec(v_a_6788_);
lean_dec(v___y_6784_);
lean_dec_ref(v___y_6783_);
lean_dec(v___y_6782_);
lean_dec_ref(v___y_6781_);
lean_dec(v_numDiscrEqs_6780_);
lean_dec_ref(v_remaining_6479_);
lean_dec_ref(v_alts_6478_);
lean_dec(v_matcherName_6473_);
lean_dec_ref(v_toMatcherInfo_6472_);
lean_dec_ref(v_onRemaining_6464_);
lean_dec_ref(v_onAlt_6463_);
lean_dec_ref(v_matcherApp_6458_);
v_a_6810_ = lean_ctor_get(v___x_6796_, 0);
v_isSharedCheck_6817_ = !lean_is_exclusive(v___x_6796_);
if (v_isSharedCheck_6817_ == 0)
{
v___x_6812_ = v___x_6796_;
v_isShared_6813_ = v_isSharedCheck_6817_;
goto v_resetjp_6811_;
}
else
{
lean_inc(v_a_6810_);
lean_dec(v___x_6796_);
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
lean_dec(v_a_6788_);
lean_dec(v___y_6784_);
lean_dec_ref(v___y_6783_);
lean_dec(v___y_6782_);
lean_dec_ref(v___y_6781_);
lean_dec(v_numDiscrEqs_6780_);
lean_dec_ref(v_remaining_6479_);
lean_dec_ref(v_alts_6478_);
lean_dec(v_matcherName_6473_);
lean_dec_ref(v_toMatcherInfo_6472_);
lean_dec_ref(v_onRemaining_6464_);
lean_dec_ref(v_onAlt_6463_);
lean_dec_ref(v_onMotive_6462_);
lean_dec_ref(v_matcherApp_6458_);
v_a_6818_ = lean_ctor_get(v___x_6790_, 0);
v_isSharedCheck_6825_ = !lean_is_exclusive(v___x_6790_);
if (v_isSharedCheck_6825_ == 0)
{
v___x_6820_ = v___x_6790_;
v_isShared_6821_ = v_isSharedCheck_6825_;
goto v_resetjp_6819_;
}
else
{
lean_inc(v_a_6818_);
lean_dec(v___x_6790_);
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
lean_dec(v___y_6784_);
lean_dec_ref(v___y_6783_);
lean_dec(v___y_6782_);
lean_dec_ref(v___y_6781_);
lean_dec(v_numDiscrEqs_6780_);
lean_dec_ref(v_remaining_6479_);
lean_dec_ref(v_alts_6478_);
lean_dec(v_matcherName_6473_);
lean_dec_ref(v_toMatcherInfo_6472_);
lean_dec_ref(v_onRemaining_6464_);
lean_dec_ref(v_onAlt_6463_);
lean_dec_ref(v_onMotive_6462_);
lean_dec_ref(v_onParams_6461_);
lean_dec_ref(v_matcherApp_6458_);
v_a_6826_ = lean_ctor_get(v___x_6787_, 0);
v_isSharedCheck_6833_ = !lean_is_exclusive(v___x_6787_);
if (v_isSharedCheck_6833_ == 0)
{
v___x_6828_ = v___x_6787_;
v_isShared_6829_ = v_isSharedCheck_6833_;
goto v_resetjp_6827_;
}
else
{
lean_inc(v_a_6826_);
lean_dec(v___x_6787_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed(lean_object* v_matcherApp_6853_, lean_object* v_useSplitter_6854_, lean_object* v_addEqualities_6855_, lean_object* v_onParams_6856_, lean_object* v_onMotive_6857_, lean_object* v_onAlt_6858_, lean_object* v_onRemaining_6859_, lean_object* v___y_6860_, lean_object* v___y_6861_, lean_object* v___y_6862_, lean_object* v___y_6863_, lean_object* v___y_6864_){
_start:
{
uint8_t v_useSplitter_boxed_6865_; uint8_t v_addEqualities_boxed_6866_; lean_object* v_res_6867_; 
v_useSplitter_boxed_6865_ = lean_unbox(v_useSplitter_6854_);
v_addEqualities_boxed_6866_ = lean_unbox(v_addEqualities_6855_);
v_res_6867_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(v_matcherApp_6853_, v_useSplitter_boxed_6865_, v_addEqualities_boxed_6866_, v_onParams_6856_, v_onMotive_6857_, v_onAlt_6858_, v_onRemaining_6859_, v___y_6860_, v___y_6861_, v___y_6862_, v___y_6863_);
return v_res_6867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType(lean_object* v_matcherApp_6873_, lean_object* v_a_6874_, lean_object* v_a_6875_, lean_object* v_a_6876_, lean_object* v_a_6877_){
_start:
{
lean_object* v_toMatcherInfo_6879_; lean_object* v_matcherName_6880_; lean_object* v_matcherLevels_6881_; lean_object* v_params_6882_; lean_object* v_alts_6883_; lean_object* v_remaining_6884_; lean_object* v___f_6885_; lean_object* v___f_6886_; lean_object* v_nExtra_6887_; uint8_t v___x_6888_; lean_object* v___f_6889_; uint8_t v___x_6890_; lean_object* v___x_6891_; lean_object* v___x_6892_; lean_object* v___f_6893_; lean_object* v___x_6894_; 
v_toMatcherInfo_6879_ = lean_ctor_get(v_matcherApp_6873_, 0);
v_matcherName_6880_ = lean_ctor_get(v_matcherApp_6873_, 1);
v_matcherLevels_6881_ = lean_ctor_get(v_matcherApp_6873_, 2);
v_params_6882_ = lean_ctor_get(v_matcherApp_6873_, 3);
v_alts_6883_ = lean_ctor_get(v_matcherApp_6873_, 6);
v_remaining_6884_ = lean_ctor_get(v_matcherApp_6873_, 7);
v___f_6885_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__0));
v___f_6886_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__1));
v_nExtra_6887_ = lean_array_get_size(v_remaining_6884_);
v___x_6888_ = 1;
v___f_6889_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__2));
v___x_6890_ = 0;
v___x_6891_ = lean_box(v___x_6890_);
v___x_6892_ = lean_box(v___x_6888_);
lean_inc_ref(v_matcherLevels_6881_);
lean_inc_ref(v_params_6882_);
lean_inc(v_matcherName_6880_);
lean_inc_ref(v_toMatcherInfo_6879_);
lean_inc_ref(v_alts_6883_);
v___f_6893_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed), 15, 8);
lean_closure_set(v___f_6893_, 0, v_nExtra_6887_);
lean_closure_set(v___f_6893_, 1, v___x_6891_);
lean_closure_set(v___f_6893_, 2, v___x_6892_);
lean_closure_set(v___f_6893_, 3, v_alts_6883_);
lean_closure_set(v___f_6893_, 4, v_toMatcherInfo_6879_);
lean_closure_set(v___f_6893_, 5, v_matcherName_6880_);
lean_closure_set(v___f_6893_, 6, v_params_6882_);
lean_closure_set(v___f_6893_, 7, v_matcherLevels_6881_);
v___x_6894_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(v_matcherApp_6873_, v___x_6888_, v___x_6890_, v___f_6885_, v___f_6893_, v___f_6889_, v___f_6886_, v_a_6874_, v_a_6875_, v_a_6876_, v_a_6877_);
return v___x_6894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___boxed(lean_object* v_matcherApp_6895_, lean_object* v_a_6896_, lean_object* v_a_6897_, lean_object* v_a_6898_, lean_object* v_a_6899_, lean_object* v_a_6900_){
_start:
{
lean_object* v_res_6901_; 
v_res_6901_ = l_Lean_Meta_MatcherApp_inferMatchType(v_matcherApp_6895_, v_a_6896_, v_a_6897_, v_a_6898_, v_a_6899_);
return v_res_6901_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(lean_object* v_a_6902_, lean_object* v_termAlt_6903_, lean_object* v_inst_6904_, lean_object* v_R_6905_, lean_object* v_a_6906_, lean_object* v_b_6907_, lean_object* v_c_6908_, lean_object* v___y_6909_, lean_object* v___y_6910_, lean_object* v___y_6911_, lean_object* v___y_6912_){
_start:
{
lean_object* v___x_6914_; 
v___x_6914_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_6902_, v_termAlt_6903_, v_a_6906_, v_b_6907_, v___y_6909_, v___y_6910_, v___y_6911_, v___y_6912_);
return v___x_6914_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___boxed(lean_object* v_a_6915_, lean_object* v_termAlt_6916_, lean_object* v_inst_6917_, lean_object* v_R_6918_, lean_object* v_a_6919_, lean_object* v_b_6920_, lean_object* v_c_6921_, lean_object* v___y_6922_, lean_object* v___y_6923_, lean_object* v___y_6924_, lean_object* v___y_6925_, lean_object* v___y_6926_){
_start:
{
lean_object* v_res_6927_; 
v_res_6927_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(v_a_6915_, v_termAlt_6916_, v_inst_6917_, v_R_6918_, v_a_6919_, v_b_6920_, v_c_6921_, v___y_6922_, v___y_6923_, v___y_6924_, v___y_6925_);
lean_dec(v___y_6925_);
lean_dec_ref(v___y_6924_);
lean_dec(v___y_6923_);
lean_dec_ref(v___y_6922_);
return v_res_6927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(lean_object* v_00_u03b1_6928_, lean_object* v_fvars_6929_, lean_object* v_names_6930_, lean_object* v_k_6931_, lean_object* v___y_6932_, lean_object* v___y_6933_, lean_object* v___y_6934_, lean_object* v___y_6935_){
_start:
{
lean_object* v___x_6937_; 
v___x_6937_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_fvars_6929_, v_names_6930_, v_k_6931_, v___y_6932_, v___y_6933_, v___y_6934_, v___y_6935_);
return v___x_6937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___boxed(lean_object* v_00_u03b1_6938_, lean_object* v_fvars_6939_, lean_object* v_names_6940_, lean_object* v_k_6941_, lean_object* v___y_6942_, lean_object* v___y_6943_, lean_object* v___y_6944_, lean_object* v___y_6945_, lean_object* v___y_6946_){
_start:
{
lean_object* v_res_6947_; 
v_res_6947_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(v_00_u03b1_6938_, v_fvars_6939_, v_names_6940_, v_k_6941_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_);
lean_dec_ref(v_names_6940_);
lean_dec_ref(v_fvars_6939_);
return v_res_6947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(lean_object* v_00_u03b1_6948_, lean_object* v_origAltType_6949_, lean_object* v_altInfo_6950_, lean_object* v_k_6951_, lean_object* v___y_6952_, lean_object* v___y_6953_, lean_object* v___y_6954_, lean_object* v___y_6955_){
_start:
{
lean_object* v___x_6957_; 
v___x_6957_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v_origAltType_6949_, v_altInfo_6950_, v_k_6951_, v___y_6952_, v___y_6953_, v___y_6954_, v___y_6955_);
return v___x_6957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___boxed(lean_object* v_00_u03b1_6958_, lean_object* v_origAltType_6959_, lean_object* v_altInfo_6960_, lean_object* v_k_6961_, lean_object* v___y_6962_, lean_object* v___y_6963_, lean_object* v___y_6964_, lean_object* v___y_6965_, lean_object* v___y_6966_){
_start:
{
lean_object* v_res_6967_; 
v_res_6967_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(v_00_u03b1_6958_, v_origAltType_6959_, v_altInfo_6960_, v_k_6961_, v___y_6962_, v___y_6963_, v___y_6964_, v___y_6965_);
return v_res_6967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(lean_object* v_declName_6968_, lean_object* v___y_6969_, lean_object* v___y_6970_, lean_object* v___y_6971_, lean_object* v___y_6972_){
_start:
{
lean_object* v___x_6974_; 
v___x_6974_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_declName_6968_, v___y_6972_);
return v___x_6974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___boxed(lean_object* v_declName_6975_, lean_object* v___y_6976_, lean_object* v___y_6977_, lean_object* v___y_6978_, lean_object* v___y_6979_, lean_object* v___y_6980_){
_start:
{
lean_object* v_res_6981_; 
v_res_6981_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(v_declName_6975_, v___y_6976_, v___y_6977_, v___y_6978_, v___y_6979_);
lean_dec(v___y_6979_);
lean_dec_ref(v___y_6978_);
lean_dec(v___y_6977_);
lean_dec_ref(v___y_6976_);
return v_res_6981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(size_t v_sz_6982_, size_t v_i_6983_, lean_object* v_bs_6984_, lean_object* v___y_6985_, lean_object* v___y_6986_, lean_object* v___y_6987_, lean_object* v___y_6988_){
_start:
{
lean_object* v___x_6990_; 
v___x_6990_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_6982_, v_i_6983_, v_bs_6984_, v___y_6985_, v___y_6987_, v___y_6988_);
return v___x_6990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___boxed(lean_object* v_sz_6991_, lean_object* v_i_6992_, lean_object* v_bs_6993_, lean_object* v___y_6994_, lean_object* v___y_6995_, lean_object* v___y_6996_, lean_object* v___y_6997_, lean_object* v___y_6998_){
_start:
{
size_t v_sz_boxed_6999_; size_t v_i_boxed_7000_; lean_object* v_res_7001_; 
v_sz_boxed_6999_ = lean_unbox_usize(v_sz_6991_);
lean_dec(v_sz_6991_);
v_i_boxed_7000_ = lean_unbox_usize(v_i_6992_);
lean_dec(v_i_6992_);
v_res_7001_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(v_sz_boxed_6999_, v_i_boxed_7000_, v_bs_6993_, v___y_6994_, v___y_6995_, v___y_6996_, v___y_6997_);
lean_dec(v___y_6997_);
lean_dec_ref(v___y_6996_);
lean_dec(v___y_6995_);
return v_res_7001_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(lean_object* v_upperBound_7002_, lean_object* v_onAlt_7003_, lean_object* v_extraEqualities_7004_, lean_object* v_inst_7005_, lean_object* v_R_7006_, lean_object* v_a_7007_, lean_object* v_b_7008_, lean_object* v_c_7009_, lean_object* v___y_7010_, lean_object* v___y_7011_, lean_object* v___y_7012_, lean_object* v___y_7013_){
_start:
{
lean_object* v___x_7015_; 
v___x_7015_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v_upperBound_7002_, v_onAlt_7003_, v_extraEqualities_7004_, v_a_7007_, v_b_7008_, v___y_7010_, v___y_7011_, v___y_7012_, v___y_7013_);
return v___x_7015_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___boxed(lean_object* v_upperBound_7016_, lean_object* v_onAlt_7017_, lean_object* v_extraEqualities_7018_, lean_object* v_inst_7019_, lean_object* v_R_7020_, lean_object* v_a_7021_, lean_object* v_b_7022_, lean_object* v_c_7023_, lean_object* v___y_7024_, lean_object* v___y_7025_, lean_object* v___y_7026_, lean_object* v___y_7027_, lean_object* v___y_7028_){
_start:
{
lean_object* v_res_7029_; 
v_res_7029_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(v_upperBound_7016_, v_onAlt_7017_, v_extraEqualities_7018_, v_inst_7019_, v_R_7020_, v_a_7021_, v_b_7022_, v_c_7023_, v___y_7024_, v___y_7025_, v___y_7026_, v___y_7027_);
lean_dec(v_upperBound_7016_);
return v_res_7029_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(lean_object* v_upperBound_7030_, lean_object* v_onAlt_7031_, uint8_t v_useSplitter_7032_, lean_object* v_extraEqualities_7033_, lean_object* v_numDiscrEqs_7034_, lean_object* v_inst_7035_, lean_object* v_R_7036_, lean_object* v_a_7037_, lean_object* v_b_7038_, lean_object* v_c_7039_, lean_object* v___y_7040_, lean_object* v___y_7041_, lean_object* v___y_7042_, lean_object* v___y_7043_){
_start:
{
lean_object* v___x_7045_; 
v___x_7045_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v_upperBound_7030_, v_onAlt_7031_, v_useSplitter_7032_, v_extraEqualities_7033_, v_numDiscrEqs_7034_, v_a_7037_, v_b_7038_, v___y_7040_, v___y_7041_, v___y_7042_, v___y_7043_);
return v___x_7045_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___boxed(lean_object* v_upperBound_7046_, lean_object* v_onAlt_7047_, lean_object* v_useSplitter_7048_, lean_object* v_extraEqualities_7049_, lean_object* v_numDiscrEqs_7050_, lean_object* v_inst_7051_, lean_object* v_R_7052_, lean_object* v_a_7053_, lean_object* v_b_7054_, lean_object* v_c_7055_, lean_object* v___y_7056_, lean_object* v___y_7057_, lean_object* v___y_7058_, lean_object* v___y_7059_, lean_object* v___y_7060_){
_start:
{
uint8_t v_useSplitter_boxed_7061_; lean_object* v_res_7062_; 
v_useSplitter_boxed_7061_ = lean_unbox(v_useSplitter_7048_);
v_res_7062_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(v_upperBound_7046_, v_onAlt_7047_, v_useSplitter_boxed_7061_, v_extraEqualities_7049_, v_numDiscrEqs_7050_, v_inst_7051_, v_R_7052_, v_a_7053_, v_b_7054_, v_c_7055_, v___y_7056_, v___y_7057_, v___y_7058_, v___y_7059_);
lean_dec(v_upperBound_7046_);
return v_res_7062_;
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
