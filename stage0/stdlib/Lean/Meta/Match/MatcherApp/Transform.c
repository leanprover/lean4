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
v___x_319_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_a_316_, v___x_317_, v___f_309_, v___x_318_, v___x_318_, v___y_313_, v___y_312_, v___y_314_, v___y_311_);
return v___x_319_;
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
lean_dec_ref(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec(v___y_311_);
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
v___x_336_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_335_, v___y_332_, v___y_331_, v___y_333_, v___y_329_);
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
v___y_311_ = v___y_305_;
v___y_312_ = v___y_303_;
v___y_313_ = v___y_302_;
v___y_314_ = v___y_304_;
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
v___y_329_ = v___y_305_;
v___y_330_ = v___x_338_;
v___y_331_ = v___y_303_;
v___y_332_ = v___y_302_;
v___y_333_ = v___y_304_;
v___y_334_ = v___x_341_;
goto v___jp_328_;
}
else
{
lean_dec(v_a_339_);
v___y_329_ = v___y_305_;
v___y_330_ = v___x_338_;
v___y_331_ = v___y_303_;
v___y_332_ = v___y_302_;
v___y_333_ = v___y_304_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0(lean_object* v_matcherApp_574_, lean_object* v_e_575_, lean_object* v_discrs_576_, lean_object* v_toMatcherInfo_577_, lean_object* v_alts_578_, lean_object* v_remaining_579_, lean_object* v_params_580_, lean_object* v_matcherName_581_, lean_object* v_matcherLevels_582_, lean_object* v_motiveArgs_583_, lean_object* v_motiveBody_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; uint8_t v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v_matcherLevels_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_734_ = lean_array_get_size(v_motiveArgs_583_);
v___x_735_ = lean_array_get_size(v_discrs_576_);
v___x_736_ = lean_nat_dec_eq(v___x_734_, v___x_735_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec_ref(v_motiveBody_584_);
lean_dec_ref(v_matcherLevels_582_);
lean_dec(v_matcherName_581_);
lean_dec_ref(v_params_580_);
lean_dec_ref(v_alts_578_);
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
v___x_606_ = lean_infer_type(v___y_600_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref(v___x_606_);
v___x_608_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_574_);
v___x_609_ = lean_unsigned_to_nat(0u);
v___x_610_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(v___y_599_, v_a_607_, v___x_608_, v___y_595_, v___y_601_, v___x_609_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
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
lean_ctor_set(v___x_619_, 0, v___y_596_);
lean_ctor_set(v___x_619_, 1, v___y_593_);
lean_ctor_set(v___x_619_, 2, v___y_598_);
lean_ctor_set(v___x_619_, 3, v___y_592_);
lean_ctor_set(v___x_619_, 4, v___y_591_);
lean_ctor_set(v___x_619_, 5, v___y_597_);
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
lean_dec_ref(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec_ref(v___y_591_);
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
lean_dec_ref(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec_ref(v___y_591_);
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
v___x_663_ = l_Lean_mkAppN(v___x_662_, v___y_647_);
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
v___y_591_ = v_a_658_;
v___y_592_ = v___y_643_;
v___y_593_ = v___y_644_;
v___y_594_ = v___y_642_;
v___y_595_ = v___y_641_;
v___y_596_ = v___y_645_;
v___y_597_ = v___y_647_;
v___y_598_ = v_matcherLevels_649_;
v___y_599_ = v___y_648_;
v___y_600_ = v___x_663_;
v___y_601_ = v___x_654_;
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
v___y_641_ = v_alts_578_;
v___y_642_ = v_remaining_579_;
v___y_643_ = v_params_580_;
v___y_644_ = v_matcherName_581_;
v___y_645_ = v_toMatcherInfo_577_;
v___y_646_ = v_a_704_;
v___y_647_ = v_discrs_576_;
v___y_648_ = v_a_699_;
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
v___y_641_ = v_alts_578_;
v___y_642_ = v_remaining_579_;
v___y_643_ = v_params_580_;
v___y_644_ = v_matcherName_581_;
v___y_645_ = v_toMatcherInfo_577_;
v___y_646_ = v_a_705_;
v___y_647_ = v_discrs_576_;
v___y_648_ = v_a_699_;
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
lean_dec(v_matcherName_581_);
lean_dec_ref(v_params_580_);
lean_dec_ref(v_alts_578_);
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
lean_dec(v_matcherName_581_);
lean_dec_ref(v_params_580_);
lean_dec_ref(v_alts_578_);
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
lean_dec(v_matcherName_581_);
lean_dec_ref(v_params_580_);
lean_dec_ref(v_alts_578_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___boxed(lean_object* v_matcherApp_753_, lean_object* v_e_754_, lean_object* v_discrs_755_, lean_object* v_toMatcherInfo_756_, lean_object* v_alts_757_, lean_object* v_remaining_758_, lean_object* v_params_759_, lean_object* v_matcherName_760_, lean_object* v_matcherLevels_761_, lean_object* v_motiveArgs_762_, lean_object* v_motiveBody_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_Meta_MatcherApp_addArg___lam__0(v_matcherApp_753_, v_e_754_, v_discrs_755_, v_toMatcherInfo_756_, v_alts_757_, v_remaining_758_, v_params_759_, v_matcherName_760_, v_matcherLevels_761_, v_motiveArgs_762_, v_motiveBody_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
lean_dec_ref(v_motiveArgs_762_);
lean_dec_ref(v_remaining_758_);
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
lean_closure_set(v___f_785_, 4, v_alts_783_);
lean_closure_set(v___f_785_, 5, v_remaining_784_);
lean_closure_set(v___f_785_, 6, v_params_780_);
lean_closure_set(v___f_785_, 7, v_matcherName_778_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1(lean_object* v___f_1104_, lean_object* v_discrs_1105_, lean_object* v_e_1106_, lean_object* v_toMatcherInfo_1107_, lean_object* v_matcherName_1108_, lean_object* v_params_1109_, lean_object* v_matcherLevels_1110_, lean_object* v_motiveArgs_1111_, lean_object* v___motiveBody_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_){
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
lean_dec(v_matcherName_1108_);
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
v___x_1150_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_1111_, v___y_1138_, v___x_1147_, v___x_1148_, v___x_1147_, v___x_1148_, v___x_1149_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_a_1151_);
lean_dec_ref(v___x_1150_);
v___x_1152_ = lean_array_to_list(v_matcherLevels_1142_);
v___x_1153_ = l_Lean_mkConst(v___y_1139_, v___x_1152_);
v___x_1154_ = l_Lean_mkAppN(v___x_1153_, v___y_1141_);
v___x_1155_ = l_Lean_Expr_app___override(v___x_1154_, v_a_1151_);
v___x_1156_ = l_Lean_mkAppN(v___x_1155_, v___y_1140_);
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
v___y_1138_ = v_a_1196_;
v___y_1139_ = v_matcherName_1108_;
v___y_1140_ = v_discrs_1105_;
v___y_1141_ = v_params_1109_;
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
v___y_1138_ = v_a_1197_;
v___y_1139_ = v_matcherName_1108_;
v___y_1140_ = v_discrs_1105_;
v___y_1141_ = v_params_1109_;
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
lean_dec(v_matcherName_1108_);
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
lean_dec(v_matcherName_1108_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___boxed(lean_object* v___f_1236_, lean_object* v_discrs_1237_, lean_object* v_e_1238_, lean_object* v_toMatcherInfo_1239_, lean_object* v_matcherName_1240_, lean_object* v_params_1241_, lean_object* v_matcherLevels_1242_, lean_object* v_motiveArgs_1243_, lean_object* v___motiveBody_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_Meta_MatcherApp_refineThrough___lam__1(v___f_1236_, v_discrs_1237_, v_e_1238_, v_toMatcherInfo_1239_, v_matcherName_1240_, v_params_1241_, v_matcherLevels_1242_, v_motiveArgs_1243_, v___motiveBody_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
lean_dec_ref(v___motiveBody_1244_);
lean_dec_ref(v_motiveArgs_1243_);
lean_dec_ref(v_params_1241_);
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
lean_closure_set(v___f_1265_, 4, v_matcherName_1259_);
lean_closure_set(v___f_1265_, 5, v_params_1261_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_TransformAltFVars_altParams(lean_object* v_fvars_1573_){
_start:
{
lean_object* v_args_1574_; lean_object* v_discrEqs_1575_; lean_object* v___x_1576_; 
v_args_1574_ = lean_ctor_get(v_fvars_1573_, 0);
lean_inc_ref(v_args_1574_);
v_discrEqs_1575_ = lean_ctor_get(v_fvars_1573_, 3);
lean_inc_ref(v_discrEqs_1575_);
lean_dec_ref(v_fvars_1573_);
v___x_1576_ = l_Array_append___redArg(v_args_1574_, v_discrEqs_1575_);
lean_dec_ref(v_discrEqs_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_TransformAltFVars_all(lean_object* v_fvars_1577_){
_start:
{
lean_object* v_fields_1578_; lean_object* v_overlaps_1579_; lean_object* v_discrEqs_1580_; lean_object* v_extraEqs_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v_fields_1578_ = lean_ctor_get(v_fvars_1577_, 1);
lean_inc_ref(v_fields_1578_);
v_overlaps_1579_ = lean_ctor_get(v_fvars_1577_, 2);
lean_inc_ref(v_overlaps_1579_);
v_discrEqs_1580_ = lean_ctor_get(v_fvars_1577_, 3);
lean_inc_ref(v_discrEqs_1580_);
v_extraEqs_1581_ = lean_ctor_get(v_fvars_1577_, 4);
lean_inc_ref(v_extraEqs_1581_);
lean_dec_ref(v_fvars_1577_);
v___x_1582_ = l_Array_append___redArg(v_fields_1578_, v_overlaps_1579_);
lean_dec_ref(v_overlaps_1579_);
v___x_1583_ = l_Array_append___redArg(v___x_1582_, v_discrEqs_1580_);
lean_dec_ref(v_discrEqs_1580_);
v___x_1584_ = l_Array_append___redArg(v___x_1583_, v_extraEqs_1581_);
lean_dec_ref(v_extraEqs_1581_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0(lean_object* v_inst_1585_, lean_object* v_inst_1586_, lean_object* v_x_1587_){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2);
v___x_1589_ = l_Lean_throwError___redArg(v_inst_1585_, v_inst_1586_, v___x_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed(lean_object* v_inst_1590_, lean_object* v_inst_1591_, lean_object* v_x_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__0(v_inst_1590_, v_inst_1591_, v_x_1592_);
lean_dec_ref(v_x_1592_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1(lean_object* v_inst_1594_, lean_object* v_x_1595_){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1596_ = l_Lean_Expr_fvarId_x21(v_x_1595_);
v___x_1597_ = lean_alloc_closure((void*)(l_Lean_FVarId_getUserName___boxed), 6, 1);
lean_closure_set(v___x_1597_, 0, v___x_1596_);
v___x_1598_ = lean_apply_2(v_inst_1594_, lean_box(0), v___x_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed(lean_object* v_inst_1599_, lean_object* v_x_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__1(v_inst_1599_, v_x_1600_);
lean_dec_ref(v_x_1600_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2(lean_object* v_inst_1602_, lean_object* v___f_1603_, lean_object* v_xs_1604_, lean_object* v_x_1605_){
_start:
{
size_t v_sz_1606_; size_t v___x_1607_; lean_object* v___x_1608_; 
v_sz_1606_ = lean_array_size(v_xs_1604_);
v___x_1607_ = ((size_t)0ULL);
v___x_1608_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1602_, v___f_1603_, v_sz_1606_, v___x_1607_, v_xs_1604_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed(lean_object* v_inst_1609_, lean_object* v___f_1610_, lean_object* v_xs_1611_, lean_object* v_x_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__2(v_inst_1609_, v___f_1610_, v_xs_1611_, v_x_1612_);
lean_dec_ref(v_x_1612_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__3(lean_object* v_toPure_1614_, lean_object* v_____do__lift_1615_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = lean_apply_2(v_toPure_1614_, lean_box(0), v_____do__lift_1615_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__4(lean_object* v_toPure_1617_, lean_object* v_____do__lift_1618_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = lean_apply_2(v_toPure_1617_, lean_box(0), v_____do__lift_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__5(lean_object* v_fst_1620_, lean_object* v_fst_1621_, lean_object* v___x_1622_, lean_object* v___x_1623_, lean_object* v_toPure_1624_, lean_object* v_____do__lift_1625_){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1626_ = lean_array_push(v_fst_1620_, v_____do__lift_1625_);
v___x_1627_ = lean_nat_add(v_fst_1621_, v___x_1622_);
v___x_1628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
lean_ctor_set(v___x_1628_, 1, v___x_1623_);
v___x_1629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1626_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
v___x_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
v___x_1631_ = lean_apply_2(v_toPure_1624_, lean_box(0), v___x_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__5___boxed(lean_object* v_fst_1632_, lean_object* v_fst_1633_, lean_object* v___x_1634_, lean_object* v___x_1635_, lean_object* v_toPure_1636_, lean_object* v_____do__lift_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__5(v_fst_1632_, v_fst_1633_, v___x_1634_, v___x_1635_, v_toPure_1636_, v_____do__lift_1637_);
lean_dec(v___x_1634_);
lean_dec(v_fst_1633_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6(uint8_t v_val_1639_, lean_object* v_a_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
if (v_val_1639_ == 0)
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_Meta_mkEqRefl(v_a_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
return v___x_1646_;
}
else
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_Meta_mkHEqRefl(v_a_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
return v___x_1647_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed(lean_object* v_val_1648_, lean_object* v_a_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
uint8_t v_val_14305__boxed_1655_; lean_object* v_res_1656_; 
v_val_14305__boxed_1655_ = lean_unbox(v_val_1648_);
v_res_1656_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__6(v_val_14305__boxed_1655_, v_a_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7(lean_object* v_toPure_1657_, lean_object* v_inst_1658_, lean_object* v_toBind_1659_, lean_object* v_a_1660_, lean_object* v_x_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v_snd_1663_; lean_object* v_snd_1664_; lean_object* v_fst_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1713_; 
v_snd_1663_ = lean_ctor_get(v___y_1662_, 1);
lean_inc(v_snd_1663_);
v_snd_1664_ = lean_ctor_get(v_snd_1663_, 1);
lean_inc(v_snd_1664_);
v_fst_1665_ = lean_ctor_get(v___y_1662_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___y_1662_);
if (v_isSharedCheck_1713_ == 0)
{
lean_object* v_unused_1714_; 
v_unused_1714_ = lean_ctor_get(v___y_1662_, 1);
lean_dec(v_unused_1714_);
v___x_1667_ = v___y_1662_;
v_isShared_1668_ = v_isSharedCheck_1713_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_fst_1665_);
lean_dec(v___y_1662_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1713_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v_fst_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1711_; 
v_fst_1669_ = lean_ctor_get(v_snd_1663_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v_snd_1663_);
if (v_isSharedCheck_1711_ == 0)
{
lean_object* v_unused_1712_; 
v_unused_1712_ = lean_ctor_get(v_snd_1663_, 1);
lean_dec(v_unused_1712_);
v___x_1671_ = v_snd_1663_;
v_isShared_1672_ = v_isSharedCheck_1711_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_fst_1669_);
lean_dec(v_snd_1663_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1711_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v_array_1673_; lean_object* v_start_1674_; lean_object* v_stop_1675_; uint8_t v___x_1676_; 
v_array_1673_ = lean_ctor_get(v_snd_1664_, 0);
v_start_1674_ = lean_ctor_get(v_snd_1664_, 1);
v_stop_1675_ = lean_ctor_get(v_snd_1664_, 2);
v___x_1676_ = lean_nat_dec_lt(v_start_1674_, v_stop_1675_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1678_; 
lean_dec_ref(v_a_1660_);
lean_dec(v_toBind_1659_);
lean_dec(v_inst_1658_);
if (v_isShared_1672_ == 0)
{
v___x_1678_ = v___x_1671_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_fst_1669_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_snd_1664_);
v___x_1678_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
lean_object* v___x_1680_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 1, v___x_1678_);
v___x_1680_ = v___x_1667_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_fst_1665_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
v___x_1682_ = lean_apply_2(v_toPure_1657_, lean_box(0), v___x_1681_);
return v___x_1682_;
}
}
}
else
{
lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1707_; 
lean_inc(v_stop_1675_);
lean_inc(v_start_1674_);
lean_inc_ref(v_array_1673_);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_snd_1664_);
if (v_isSharedCheck_1707_ == 0)
{
lean_object* v_unused_1708_; lean_object* v_unused_1709_; lean_object* v_unused_1710_; 
v_unused_1708_ = lean_ctor_get(v_snd_1664_, 2);
lean_dec(v_unused_1708_);
v_unused_1709_ = lean_ctor_get(v_snd_1664_, 1);
lean_dec(v_unused_1709_);
v_unused_1710_ = lean_ctor_get(v_snd_1664_, 0);
lean_dec(v_unused_1710_);
v___x_1686_ = v_snd_1664_;
v_isShared_1687_ = v_isSharedCheck_1707_;
goto v_resetjp_1685_;
}
else
{
lean_dec(v_snd_1664_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1707_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1688_ = lean_array_fget(v_array_1673_, v_start_1674_);
v___x_1689_ = lean_unsigned_to_nat(1u);
v___x_1690_ = lean_nat_add(v_start_1674_, v___x_1689_);
lean_dec(v_start_1674_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 1, v___x_1690_);
v___x_1692_ = v___x_1686_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_array_1673_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v___x_1690_);
lean_ctor_set(v_reuseFailAlloc_1706_, 2, v_stop_1675_);
v___x_1692_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v___x_1694_; 
lean_dec_ref(v_a_1660_);
lean_dec(v_toBind_1659_);
lean_dec(v_inst_1658_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 1, v___x_1692_);
v___x_1694_ = v___x_1671_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_fst_1669_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v___x_1692_);
v___x_1694_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
lean_object* v___x_1696_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 1, v___x_1694_);
v___x_1696_ = v___x_1667_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_fst_1665_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
v___x_1698_ = lean_apply_2(v_toPure_1657_, lean_box(0), v___x_1697_);
return v___x_1698_;
}
}
}
else
{
lean_object* v_val_1701_; lean_object* v___f_1702_; lean_object* v___f_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
lean_del_object(v___x_1671_);
lean_del_object(v___x_1667_);
v_val_1701_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_val_1701_);
lean_dec_ref(v___x_1688_);
v___f_1702_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_1702_, 0, v_fst_1665_);
lean_closure_set(v___f_1702_, 1, v_fst_1669_);
lean_closure_set(v___f_1702_, 2, v___x_1689_);
lean_closure_set(v___f_1702_, 3, v___x_1692_);
lean_closure_set(v___f_1702_, 4, v_toPure_1657_);
v___f_1703_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed), 7, 2);
lean_closure_set(v___f_1703_, 0, v_val_1701_);
lean_closure_set(v___f_1703_, 1, v_a_1660_);
v___x_1704_ = lean_apply_2(v_inst_1658_, lean_box(0), v___f_1703_);
v___x_1705_ = lean_apply_4(v_toBind_1659_, lean_box(0), lean_box(0), v___x_1704_, v___f_1702_);
return v___x_1705_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8(lean_object* v_heq_1715_, lean_object* v_fst_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Lean_mkArrow(v_heq_1715_, v_fst_1716_, v___y_1719_, v___y_1720_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed(lean_object* v_heq_1723_, lean_object* v_fst_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__8(v_heq_1723_, v_fst_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9(lean_object* v_heq_1733_, lean_object* v_fst_1734_, lean_object* v_fst_1735_, lean_object* v___x_1736_, lean_object* v___x_1737_, lean_object* v_toPure_1738_, lean_object* v_motiveBody_x27_1739_){
_start:
{
uint8_t v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1740_ = l_Lean_Expr_isHEq(v_heq_1733_);
v___x_1741_ = lean_box(v___x_1740_);
v___x_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
v___x_1743_ = lean_array_push(v_fst_1734_, v___x_1742_);
v___x_1744_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9___closed__0));
v___x_1745_ = lean_array_push(v_fst_1735_, v___x_1744_);
v___x_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1736_);
lean_ctor_set(v___x_1746_, 1, v___x_1737_);
v___x_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1745_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
v___x_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1743_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
v___x_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1749_, 0, v_motiveBody_x27_1739_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
v___x_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
v___x_1751_ = lean_apply_2(v_toPure_1738_, lean_box(0), v___x_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9___boxed(lean_object* v_heq_1752_, lean_object* v_fst_1753_, lean_object* v_fst_1754_, lean_object* v___x_1755_, lean_object* v___x_1756_, lean_object* v_toPure_1757_, lean_object* v_motiveBody_x27_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__9(v_heq_1752_, v_fst_1753_, v_fst_1754_, v___x_1755_, v___x_1756_, v_toPure_1757_, v_motiveBody_x27_1758_);
lean_dec_ref(v_heq_1752_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10(lean_object* v_fst_1760_, lean_object* v_fst_1761_, lean_object* v_fst_1762_, lean_object* v___x_1763_, lean_object* v___x_1764_, lean_object* v_toPure_1765_, lean_object* v_inst_1766_, lean_object* v_toBind_1767_, lean_object* v_heq_1768_){
_start:
{
lean_object* v___f_1769_; lean_object* v___f_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
lean_inc_ref(v_heq_1768_);
v___f_1769_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed), 7, 2);
lean_closure_set(v___f_1769_, 0, v_heq_1768_);
lean_closure_set(v___f_1769_, 1, v_fst_1760_);
v___f_1770_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9___boxed), 7, 6);
lean_closure_set(v___f_1770_, 0, v_heq_1768_);
lean_closure_set(v___f_1770_, 1, v_fst_1761_);
lean_closure_set(v___f_1770_, 2, v_fst_1762_);
lean_closure_set(v___f_1770_, 3, v___x_1763_);
lean_closure_set(v___f_1770_, 4, v___x_1764_);
lean_closure_set(v___f_1770_, 5, v_toPure_1765_);
v___x_1771_ = lean_apply_2(v_inst_1766_, lean_box(0), v___f_1769_);
v___x_1772_ = lean_apply_4(v_toBind_1767_, lean_box(0), lean_box(0), v___x_1771_, v___f_1770_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11(lean_object* v___x_1773_, lean_object* v_a_1774_, lean_object* v_inst_1775_, lean_object* v_toBind_1776_, lean_object* v___f_1777_, lean_object* v_fst_1778_, lean_object* v_fst_1779_, lean_object* v___x_1780_, lean_object* v___x_1781_, lean_object* v___x_1782_, lean_object* v_fst_1783_, lean_object* v_toPure_1784_, uint8_t v_____do__lift_1785_){
_start:
{
if (v_____do__lift_1785_ == 0)
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
lean_dec(v_toPure_1784_);
lean_dec(v_fst_1783_);
lean_dec_ref(v___x_1782_);
lean_dec_ref(v___x_1781_);
lean_dec(v___x_1780_);
lean_dec(v_fst_1779_);
lean_dec(v_fst_1778_);
v___x_1786_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEqHEq___boxed), 7, 2);
lean_closure_set(v___x_1786_, 0, v___x_1773_);
lean_closure_set(v___x_1786_, 1, v_a_1774_);
v___x_1787_ = lean_apply_2(v_inst_1775_, lean_box(0), v___x_1786_);
v___x_1788_ = lean_apply_4(v_toBind_1776_, lean_box(0), lean_box(0), v___x_1787_, v___f_1777_);
return v___x_1788_;
}
else
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
lean_dec(v___f_1777_);
lean_dec(v_toBind_1776_);
lean_dec(v_inst_1775_);
lean_dec_ref(v_a_1774_);
lean_dec_ref(v___x_1773_);
v___x_1789_ = lean_box(0);
v___x_1790_ = lean_array_push(v_fst_1778_, v___x_1789_);
v___x_1791_ = lean_array_push(v_fst_1779_, v___x_1780_);
v___x_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1781_);
lean_ctor_set(v___x_1792_, 1, v___x_1782_);
v___x_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1791_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
v___x_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1790_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
v___x_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1795_, 0, v_fst_1783_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
v___x_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
v___x_1797_ = lean_apply_2(v_toPure_1784_, lean_box(0), v___x_1796_);
return v___x_1797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed(lean_object* v___x_1798_, lean_object* v_a_1799_, lean_object* v_inst_1800_, lean_object* v_toBind_1801_, lean_object* v___f_1802_, lean_object* v_fst_1803_, lean_object* v_fst_1804_, lean_object* v___x_1805_, lean_object* v___x_1806_, lean_object* v___x_1807_, lean_object* v_fst_1808_, lean_object* v_toPure_1809_, lean_object* v_____do__lift_1810_){
_start:
{
uint8_t v_____do__lift_14496__boxed_1811_; lean_object* v_res_1812_; 
v_____do__lift_14496__boxed_1811_ = lean_unbox(v_____do__lift_1810_);
v_res_1812_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__11(v___x_1798_, v_a_1799_, v_inst_1800_, v_toBind_1801_, v___f_1802_, v_fst_1803_, v_fst_1804_, v___x_1805_, v___x_1806_, v___x_1807_, v_fst_1808_, v_toPure_1809_, v_____do__lift_14496__boxed_1811_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12(lean_object* v_toPure_1813_, uint8_t v_addEqualities_1814_, lean_object* v_inst_1815_, lean_object* v_toBind_1816_, lean_object* v_a_1817_, lean_object* v_x_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_snd_1820_; lean_object* v_snd_1821_; lean_object* v_snd_1822_; lean_object* v_snd_1823_; lean_object* v_fst_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1930_; 
v_snd_1820_ = lean_ctor_get(v___y_1819_, 1);
lean_inc(v_snd_1820_);
v_snd_1821_ = lean_ctor_get(v_snd_1820_, 1);
lean_inc(v_snd_1821_);
v_snd_1822_ = lean_ctor_get(v_snd_1821_, 1);
lean_inc(v_snd_1822_);
v_snd_1823_ = lean_ctor_get(v_snd_1822_, 1);
lean_inc(v_snd_1823_);
v_fst_1824_ = lean_ctor_get(v___y_1819_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___y_1819_);
if (v_isSharedCheck_1930_ == 0)
{
lean_object* v_unused_1931_; 
v_unused_1931_ = lean_ctor_get(v___y_1819_, 1);
lean_dec(v_unused_1931_);
v___x_1826_ = v___y_1819_;
v_isShared_1827_ = v_isSharedCheck_1930_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_fst_1824_);
lean_dec(v___y_1819_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1930_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v_fst_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1928_; 
v_fst_1828_ = lean_ctor_get(v_snd_1820_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_snd_1820_);
if (v_isSharedCheck_1928_ == 0)
{
lean_object* v_unused_1929_; 
v_unused_1929_ = lean_ctor_get(v_snd_1820_, 1);
lean_dec(v_unused_1929_);
v___x_1830_ = v_snd_1820_;
v_isShared_1831_ = v_isSharedCheck_1928_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_fst_1828_);
lean_dec(v_snd_1820_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1928_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v_fst_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1926_; 
v_fst_1832_ = lean_ctor_get(v_snd_1821_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v_snd_1821_);
if (v_isSharedCheck_1926_ == 0)
{
lean_object* v_unused_1927_; 
v_unused_1927_ = lean_ctor_get(v_snd_1821_, 1);
lean_dec(v_unused_1927_);
v___x_1834_ = v_snd_1821_;
v_isShared_1835_ = v_isSharedCheck_1926_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_fst_1832_);
lean_dec(v_snd_1821_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1926_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v_fst_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1924_; 
v_fst_1836_ = lean_ctor_get(v_snd_1822_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_snd_1822_);
if (v_isSharedCheck_1924_ == 0)
{
lean_object* v_unused_1925_; 
v_unused_1925_ = lean_ctor_get(v_snd_1822_, 1);
lean_dec(v_unused_1925_);
v___x_1838_ = v_snd_1822_;
v_isShared_1839_ = v_isSharedCheck_1924_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_fst_1836_);
lean_dec(v_snd_1822_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1924_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v_array_1840_; lean_object* v_start_1841_; lean_object* v_stop_1842_; uint8_t v___x_1843_; 
v_array_1840_ = lean_ctor_get(v_snd_1823_, 0);
v_start_1841_ = lean_ctor_get(v_snd_1823_, 1);
v_stop_1842_ = lean_ctor_get(v_snd_1823_, 2);
v___x_1843_ = lean_nat_dec_lt(v_start_1841_, v_stop_1842_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1845_; 
lean_dec_ref(v_a_1817_);
lean_dec(v_toBind_1816_);
lean_dec(v_inst_1815_);
if (v_isShared_1839_ == 0)
{
v___x_1845_ = v___x_1838_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_fst_1836_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_snd_1823_);
v___x_1845_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1847_; 
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 1, v___x_1845_);
v___x_1847_ = v___x_1834_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_fst_1832_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v___x_1845_);
v___x_1847_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1849_; 
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 1, v___x_1847_);
v___x_1849_ = v___x_1830_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_fst_1828_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1851_; 
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 1, v___x_1849_);
v___x_1851_ = v___x_1826_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_fst_1824_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
v___x_1853_ = lean_apply_2(v_toPure_1813_, lean_box(0), v___x_1852_);
return v___x_1853_;
}
}
}
}
}
else
{
lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1920_; 
lean_inc(v_stop_1842_);
lean_inc(v_start_1841_);
lean_inc_ref(v_array_1840_);
v_isSharedCheck_1920_ = !lean_is_exclusive(v_snd_1823_);
if (v_isSharedCheck_1920_ == 0)
{
lean_object* v_unused_1921_; lean_object* v_unused_1922_; lean_object* v_unused_1923_; 
v_unused_1921_ = lean_ctor_get(v_snd_1823_, 2);
lean_dec(v_unused_1921_);
v_unused_1922_ = lean_ctor_get(v_snd_1823_, 1);
lean_dec(v_unused_1922_);
v_unused_1923_ = lean_ctor_get(v_snd_1823_, 0);
lean_dec(v_unused_1923_);
v___x_1859_ = v_snd_1823_;
v_isShared_1860_ = v_isSharedCheck_1920_;
goto v_resetjp_1858_;
}
else
{
lean_dec(v_snd_1823_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1920_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v_array_1861_; lean_object* v_start_1862_; lean_object* v_stop_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1868_; 
v_array_1861_ = lean_ctor_get(v_fst_1836_, 0);
v_start_1862_ = lean_ctor_get(v_fst_1836_, 1);
v_stop_1863_ = lean_ctor_get(v_fst_1836_, 2);
v___x_1864_ = lean_array_fget(v_array_1840_, v_start_1841_);
v___x_1865_ = lean_unsigned_to_nat(1u);
v___x_1866_ = lean_nat_add(v_start_1841_, v___x_1865_);
lean_dec(v_start_1841_);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 1, v___x_1866_);
v___x_1868_ = v___x_1859_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_array_1840_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v___x_1866_);
lean_ctor_set(v_reuseFailAlloc_1919_, 2, v_stop_1842_);
v___x_1868_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
uint8_t v___x_1869_; 
v___x_1869_ = lean_nat_dec_lt(v_start_1862_, v_stop_1863_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1871_; 
lean_dec(v___x_1864_);
lean_dec_ref(v_a_1817_);
lean_dec(v_toBind_1816_);
lean_dec(v_inst_1815_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 1, v___x_1868_);
v___x_1871_ = v___x_1838_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_fst_1836_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v___x_1868_);
v___x_1871_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
lean_object* v___x_1873_; 
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 1, v___x_1871_);
v___x_1873_ = v___x_1834_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_fst_1832_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v___x_1871_);
v___x_1873_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
lean_object* v___x_1875_; 
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 1, v___x_1873_);
v___x_1875_ = v___x_1830_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_fst_1828_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v___x_1873_);
v___x_1875_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
lean_object* v___x_1877_; 
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 1, v___x_1875_);
v___x_1877_ = v___x_1826_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_fst_1824_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
v___x_1879_ = lean_apply_2(v_toPure_1813_, lean_box(0), v___x_1878_);
return v___x_1879_;
}
}
}
}
}
else
{
lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1915_; 
lean_inc(v_stop_1863_);
lean_inc(v_start_1862_);
lean_inc_ref(v_array_1861_);
v_isSharedCheck_1915_ = !lean_is_exclusive(v_fst_1836_);
if (v_isSharedCheck_1915_ == 0)
{
lean_object* v_unused_1916_; lean_object* v_unused_1917_; lean_object* v_unused_1918_; 
v_unused_1916_ = lean_ctor_get(v_fst_1836_, 2);
lean_dec(v_unused_1916_);
v_unused_1917_ = lean_ctor_get(v_fst_1836_, 1);
lean_dec(v_unused_1917_);
v_unused_1918_ = lean_ctor_get(v_fst_1836_, 0);
lean_dec(v_unused_1918_);
v___x_1885_ = v_fst_1836_;
v_isShared_1886_ = v_isSharedCheck_1915_;
goto v_resetjp_1884_;
}
else
{
lean_dec(v_fst_1836_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1915_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1887_ = lean_array_fget(v_array_1861_, v_start_1862_);
v___x_1888_ = lean_nat_add(v_start_1862_, v___x_1865_);
lean_dec(v_start_1862_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 1, v___x_1888_);
v___x_1890_ = v___x_1885_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_array_1861_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1914_, 2, v_stop_1863_);
v___x_1890_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
if (v_addEqualities_1814_ == 0)
{
lean_dec(v___x_1887_);
lean_dec_ref(v_a_1817_);
lean_dec(v_toBind_1816_);
lean_dec(v_inst_1815_);
goto v___jp_1891_;
}
else
{
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v___f_1909_; lean_object* v___f_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
lean_del_object(v___x_1838_);
lean_del_object(v___x_1834_);
lean_del_object(v___x_1830_);
lean_del_object(v___x_1826_);
lean_inc(v_toBind_1816_);
lean_inc(v_inst_1815_);
lean_inc(v_toPure_1813_);
lean_inc_ref(v___x_1868_);
lean_inc_ref(v___x_1890_);
lean_inc(v_fst_1832_);
lean_inc(v_fst_1828_);
lean_inc(v_fst_1824_);
v___f_1909_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__10), 9, 8);
lean_closure_set(v___f_1909_, 0, v_fst_1824_);
lean_closure_set(v___f_1909_, 1, v_fst_1828_);
lean_closure_set(v___f_1909_, 2, v_fst_1832_);
lean_closure_set(v___f_1909_, 3, v___x_1890_);
lean_closure_set(v___f_1909_, 4, v___x_1868_);
lean_closure_set(v___f_1909_, 5, v_toPure_1813_);
lean_closure_set(v___f_1909_, 6, v_inst_1815_);
lean_closure_set(v___f_1909_, 7, v_toBind_1816_);
lean_inc(v_toBind_1816_);
lean_inc(v_inst_1815_);
lean_inc_ref(v_a_1817_);
v___f_1910_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_1910_, 0, v___x_1887_);
lean_closure_set(v___f_1910_, 1, v_a_1817_);
lean_closure_set(v___f_1910_, 2, v_inst_1815_);
lean_closure_set(v___f_1910_, 3, v_toBind_1816_);
lean_closure_set(v___f_1910_, 4, v___f_1909_);
lean_closure_set(v___f_1910_, 5, v_fst_1828_);
lean_closure_set(v___f_1910_, 6, v_fst_1832_);
lean_closure_set(v___f_1910_, 7, v___x_1864_);
lean_closure_set(v___f_1910_, 8, v___x_1890_);
lean_closure_set(v___f_1910_, 9, v___x_1868_);
lean_closure_set(v___f_1910_, 10, v_fst_1824_);
lean_closure_set(v___f_1910_, 11, v_toPure_1813_);
v___x_1911_ = lean_alloc_closure((void*)(l_Lean_Meta_isProof___boxed), 6, 1);
lean_closure_set(v___x_1911_, 0, v_a_1817_);
v___x_1912_ = lean_apply_2(v_inst_1815_, lean_box(0), v___x_1911_);
v___x_1913_ = lean_apply_4(v_toBind_1816_, lean_box(0), lean_box(0), v___x_1912_, v___f_1910_);
return v___x_1913_;
}
else
{
lean_dec(v___x_1887_);
lean_dec_ref(v_a_1817_);
lean_dec(v_toBind_1816_);
lean_dec(v_inst_1815_);
goto v___jp_1891_;
}
}
v___jp_1891_:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1892_ = lean_box(0);
v___x_1893_ = lean_array_push(v_fst_1828_, v___x_1892_);
v___x_1894_ = lean_array_push(v_fst_1832_, v___x_1864_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 1, v___x_1868_);
lean_ctor_set(v___x_1838_, 0, v___x_1890_);
v___x_1896_ = v___x_1838_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1890_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v___x_1868_);
v___x_1896_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_object* v___x_1898_; 
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 1, v___x_1896_);
lean_ctor_set(v___x_1834_, 0, v___x_1894_);
v___x_1898_ = v___x_1834_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1894_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v___x_1896_);
v___x_1898_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_object* v___x_1900_; 
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 1, v___x_1898_);
lean_ctor_set(v___x_1830_, 0, v___x_1893_);
v___x_1900_ = v___x_1830_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1893_);
lean_ctor_set(v_reuseFailAlloc_1906_, 1, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
lean_object* v___x_1902_; 
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 1, v___x_1900_);
v___x_1902_ = v___x_1826_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_fst_1824_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v___x_1900_);
v___x_1902_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
v___x_1904_ = lean_apply_2(v_toPure_1813_, lean_box(0), v___x_1903_);
return v___x_1904_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12___boxed(lean_object* v_toPure_1932_, lean_object* v_addEqualities_1933_, lean_object* v_inst_1934_, lean_object* v_toBind_1935_, lean_object* v_a_1936_, lean_object* v_x_1937_, lean_object* v___y_1938_){
_start:
{
uint8_t v_addEqualities_boxed_1939_; lean_object* v_res_1940_; 
v_addEqualities_boxed_1939_ = lean_unbox(v_addEqualities_1933_);
v_res_1940_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__12(v_toPure_1932_, v_addEqualities_boxed_1939_, v_inst_1934_, v_toBind_1935_, v_a_1936_, v_x_1937_, v___y_1938_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__13(lean_object* v_fst_1941_, lean_object* v_fst_1942_, lean_object* v_____do__lift_1943_, lean_object* v_toPure_1944_, lean_object* v_____do__lift_1945_){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1946_, 0, v_fst_1941_);
lean_ctor_set(v___x_1946_, 1, v_fst_1942_);
v___x_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1947_, 0, v_____do__lift_1945_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1948_, 0, v_____do__lift_1943_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = lean_apply_2(v_toPure_1944_, lean_box(0), v___x_1948_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__14(lean_object* v_fst_1950_, lean_object* v_fst_1951_, lean_object* v_toPure_1952_, lean_object* v_fst_1953_, lean_object* v_inst_1954_, lean_object* v_toBind_1955_, lean_object* v_____do__lift_1956_){
_start:
{
lean_object* v___f_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___f_1957_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__13), 5, 4);
lean_closure_set(v___f_1957_, 0, v_fst_1950_);
lean_closure_set(v___f_1957_, 1, v_fst_1951_);
lean_closure_set(v___f_1957_, 2, v_____do__lift_1956_);
lean_closure_set(v___f_1957_, 3, v_toPure_1952_);
v___x_1958_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1958_, 0, v_fst_1953_);
v___x_1959_ = lean_apply_2(v_inst_1954_, lean_box(0), v___x_1958_);
v___x_1960_ = lean_apply_4(v_toBind_1955_, lean_box(0), lean_box(0), v___x_1959_, v___f_1957_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__15(lean_object* v_toPure_1961_, lean_object* v_inst_1962_, lean_object* v_toBind_1963_, lean_object* v_motiveArgs_1964_, lean_object* v_____s_1965_){
_start:
{
lean_object* v_snd_1966_; lean_object* v_snd_1967_; lean_object* v_fst_1968_; lean_object* v_fst_1969_; lean_object* v_fst_1970_; lean_object* v___f_1971_; uint8_t v___x_1972_; uint8_t v___x_1973_; uint8_t v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v_snd_1966_ = lean_ctor_get(v_____s_1965_, 1);
lean_inc(v_snd_1966_);
v_snd_1967_ = lean_ctor_get(v_snd_1966_, 1);
lean_inc(v_snd_1967_);
v_fst_1968_ = lean_ctor_get(v_____s_1965_, 0);
lean_inc(v_fst_1968_);
lean_dec_ref(v_____s_1965_);
v_fst_1969_ = lean_ctor_get(v_snd_1966_, 0);
lean_inc(v_fst_1969_);
lean_dec(v_snd_1966_);
v_fst_1970_ = lean_ctor_get(v_snd_1967_, 0);
lean_inc(v_fst_1970_);
lean_dec(v_snd_1967_);
lean_inc(v_toBind_1963_);
lean_inc(v_inst_1962_);
lean_inc(v_fst_1968_);
v___f_1971_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14), 7, 6);
lean_closure_set(v___f_1971_, 0, v_fst_1969_);
lean_closure_set(v___f_1971_, 1, v_fst_1970_);
lean_closure_set(v___f_1971_, 2, v_toPure_1961_);
lean_closure_set(v___f_1971_, 3, v_fst_1968_);
lean_closure_set(v___f_1971_, 4, v_inst_1962_);
lean_closure_set(v___f_1971_, 5, v_toBind_1963_);
v___x_1972_ = 0;
v___x_1973_ = 1;
v___x_1974_ = 1;
v___x_1975_ = lean_box(v___x_1972_);
v___x_1976_ = lean_box(v___x_1973_);
v___x_1977_ = lean_box(v___x_1972_);
v___x_1978_ = lean_box(v___x_1973_);
v___x_1979_ = lean_box(v___x_1974_);
v___x_1980_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1980_, 0, v_motiveArgs_1964_);
lean_closure_set(v___x_1980_, 1, v_fst_1968_);
lean_closure_set(v___x_1980_, 2, v___x_1975_);
lean_closure_set(v___x_1980_, 3, v___x_1976_);
lean_closure_set(v___x_1980_, 4, v___x_1977_);
lean_closure_set(v___x_1980_, 5, v___x_1978_);
lean_closure_set(v___x_1980_, 6, v___x_1979_);
v___x_1981_ = lean_apply_2(v_inst_1962_, lean_box(0), v___x_1980_);
v___x_1982_ = lean_apply_4(v_toBind_1963_, lean_box(0), lean_box(0), v___x_1981_, v___f_1971_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__16(lean_object* v_toMatcherInfo_1985_, lean_object* v_discrs_x27_1986_, lean_object* v_motiveArgs_1987_, lean_object* v_inst_1988_, lean_object* v___f_1989_, lean_object* v_toBind_1990_, lean_object* v___f_1991_, lean_object* v_motiveBody_x27_1992_){
_start:
{
lean_object* v_discrInfos_1993_; lean_object* v___x_1994_; lean_object* v_addHEqualities_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; size_t v_sz_2004_; size_t v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v_discrInfos_1993_ = lean_ctor_get(v_toMatcherInfo_1985_, 4);
lean_inc_ref(v_discrInfos_1993_);
lean_dec_ref(v_toMatcherInfo_1985_);
v___x_1994_ = lean_unsigned_to_nat(0u);
v_addHEqualities_1995_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___closed__0));
v___x_1996_ = lean_array_get_size(v_discrs_x27_1986_);
v___x_1997_ = l_Array_toSubarray___redArg(v_discrs_x27_1986_, v___x_1994_, v___x_1996_);
v___x_1998_ = lean_array_get_size(v_discrInfos_1993_);
v___x_1999_ = l_Array_toSubarray___redArg(v_discrInfos_1993_, v___x_1994_, v___x_1998_);
v___x_2000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1997_);
lean_ctor_set(v___x_2000_, 1, v___x_1999_);
v___x_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2001_, 0, v_addHEqualities_1995_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
v___x_2002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2002_, 0, v_addHEqualities_1995_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
v___x_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2003_, 0, v_motiveBody_x27_1992_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
v_sz_2004_ = lean_array_size(v_motiveArgs_1987_);
v___x_2005_ = ((size_t)0ULL);
v___x_2006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1988_, v_motiveArgs_1987_, v___f_1989_, v_sz_2004_, v___x_2005_, v___x_2003_);
v___x_2007_ = lean_apply_4(v_toBind_1990_, lean_box(0), lean_box(0), v___x_2006_, v___f_1991_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__17(lean_object* v_onMotive_2008_, lean_object* v_motiveArgs_2009_, lean_object* v_motiveBody_2010_, lean_object* v_toBind_2011_, lean_object* v___f_2012_, lean_object* v_____r_2013_){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = lean_apply_2(v_onMotive_2008_, v_motiveArgs_2009_, v_motiveBody_2010_);
v___x_2015_ = lean_apply_4(v_toBind_2011_, lean_box(0), lean_box(0), v___x_2014_, v___f_2012_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__18(lean_object* v___f_2016_, lean_object* v_____r_2017_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = lean_apply_1(v___f_2016_, v_____r_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19(lean_object* v_toPure_2019_, lean_object* v_inst_2020_, lean_object* v_toBind_2021_, lean_object* v_toMatcherInfo_2022_, lean_object* v_discrs_x27_2023_, lean_object* v_inst_2024_, lean_object* v___f_2025_, lean_object* v_onMotive_2026_, lean_object* v_discrs_2027_, lean_object* v_inst_2028_, lean_object* v_motiveArgs_2029_, lean_object* v_motiveBody_2030_){
_start:
{
lean_object* v___f_2031_; lean_object* v___f_2032_; lean_object* v___f_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; 
lean_inc_ref(v_motiveArgs_2029_);
lean_inc(v_toBind_2021_);
v___f_2031_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__15), 5, 4);
lean_closure_set(v___f_2031_, 0, v_toPure_2019_);
lean_closure_set(v___f_2031_, 1, v_inst_2020_);
lean_closure_set(v___f_2031_, 2, v_toBind_2021_);
lean_closure_set(v___f_2031_, 3, v_motiveArgs_2029_);
lean_inc(v_toBind_2021_);
lean_inc_ref(v_inst_2024_);
lean_inc_ref(v_motiveArgs_2029_);
v___f_2032_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16), 8, 7);
lean_closure_set(v___f_2032_, 0, v_toMatcherInfo_2022_);
lean_closure_set(v___f_2032_, 1, v_discrs_x27_2023_);
lean_closure_set(v___f_2032_, 2, v_motiveArgs_2029_);
lean_closure_set(v___f_2032_, 3, v_inst_2024_);
lean_closure_set(v___f_2032_, 4, v___f_2025_);
lean_closure_set(v___f_2032_, 5, v_toBind_2021_);
lean_closure_set(v___f_2032_, 6, v___f_2031_);
lean_inc_ref(v___f_2032_);
lean_inc(v_toBind_2021_);
lean_inc_ref(v_motiveBody_2030_);
lean_inc_ref(v_motiveArgs_2029_);
lean_inc(v_onMotive_2026_);
v___f_2033_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__17), 6, 5);
lean_closure_set(v___f_2033_, 0, v_onMotive_2026_);
lean_closure_set(v___f_2033_, 1, v_motiveArgs_2029_);
lean_closure_set(v___f_2033_, 2, v_motiveBody_2030_);
lean_closure_set(v___f_2033_, 3, v_toBind_2021_);
lean_closure_set(v___f_2033_, 4, v___f_2032_);
v___x_2034_ = lean_array_get_size(v_motiveArgs_2029_);
v___x_2035_ = lean_array_get_size(v_discrs_2027_);
v___x_2036_ = lean_nat_dec_eq(v___x_2034_, v___x_2035_);
if (v___x_2036_ == 0)
{
lean_object* v___f_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
lean_dec_ref(v___f_2032_);
lean_dec_ref(v_motiveBody_2030_);
lean_dec_ref(v_motiveArgs_2029_);
lean_dec(v_onMotive_2026_);
v___f_2037_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__18), 2, 1);
lean_closure_set(v___f_2037_, 0, v___f_2033_);
v___x_2038_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_2039_ = l_Nat_reprFast(v___x_2035_);
v___x_2040_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
v___x_2041_ = l_Lean_MessageData_ofFormat(v___x_2040_);
v___x_2042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2038_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
v___x_2043_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_2044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2042_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
v___x_2045_ = l_Lean_throwError___redArg(v_inst_2024_, v_inst_2028_, v___x_2044_);
v___x_2046_ = lean_apply_4(v_toBind_2021_, lean_box(0), lean_box(0), v___x_2045_, v___f_2037_);
return v___x_2046_;
}
else
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
lean_dec_ref(v___f_2033_);
lean_dec_ref(v_inst_2028_);
lean_dec_ref(v_inst_2024_);
v___x_2047_ = lean_box(0);
v___x_2048_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__17(v_onMotive_2026_, v_motiveArgs_2029_, v_motiveBody_2030_, v_toBind_2021_, v___f_2032_, v___x_2047_);
return v___x_2048_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19___boxed(lean_object* v_toPure_2049_, lean_object* v_inst_2050_, lean_object* v_toBind_2051_, lean_object* v_toMatcherInfo_2052_, lean_object* v_discrs_x27_2053_, lean_object* v_inst_2054_, lean_object* v___f_2055_, lean_object* v_onMotive_2056_, lean_object* v_discrs_2057_, lean_object* v_inst_2058_, lean_object* v_motiveArgs_2059_, lean_object* v_motiveBody_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__19(v_toPure_2049_, v_inst_2050_, v_toBind_2051_, v_toMatcherInfo_2052_, v_discrs_x27_2053_, v_inst_2054_, v___f_2055_, v_onMotive_2056_, v_discrs_2057_, v_inst_2058_, v_motiveArgs_2059_, v_motiveBody_2060_);
lean_dec_ref(v_discrs_2057_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20(lean_object* v_fst_2062_, lean_object* v_numParams_2063_, lean_object* v_numDiscrs_2064_, lean_object* v_altInfos_2065_, lean_object* v_uElimPos_x3f_2066_, lean_object* v_snd_2067_, lean_object* v_overlaps_2068_, lean_object* v_matcherName_2069_, lean_object* v_matcherLevels_2070_, lean_object* v_params_x27_2071_, lean_object* v_fst_2072_, lean_object* v_discrs_x27_2073_, lean_object* v_fst_2074_, lean_object* v_toPure_2075_, lean_object* v_____do__lift_2076_){
_start:
{
lean_object* v_remaining_x27_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v_remaining_x27_2077_ = l_Array_append___redArg(v_fst_2062_, v_____do__lift_2076_);
v___x_2078_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2078_, 0, v_numParams_2063_);
lean_ctor_set(v___x_2078_, 1, v_numDiscrs_2064_);
lean_ctor_set(v___x_2078_, 2, v_altInfos_2065_);
lean_ctor_set(v___x_2078_, 3, v_uElimPos_x3f_2066_);
lean_ctor_set(v___x_2078_, 4, v_snd_2067_);
lean_ctor_set(v___x_2078_, 5, v_overlaps_2068_);
v___x_2079_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
lean_ctor_set(v___x_2079_, 1, v_matcherName_2069_);
lean_ctor_set(v___x_2079_, 2, v_matcherLevels_2070_);
lean_ctor_set(v___x_2079_, 3, v_params_x27_2071_);
lean_ctor_set(v___x_2079_, 4, v_fst_2072_);
lean_ctor_set(v___x_2079_, 5, v_discrs_x27_2073_);
lean_ctor_set(v___x_2079_, 6, v_fst_2074_);
lean_ctor_set(v___x_2079_, 7, v_remaining_x27_2077_);
v___x_2080_ = lean_apply_2(v_toPure_2075_, lean_box(0), v___x_2079_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20___boxed(lean_object* v_fst_2081_, lean_object* v_numParams_2082_, lean_object* v_numDiscrs_2083_, lean_object* v_altInfos_2084_, lean_object* v_uElimPos_x3f_2085_, lean_object* v_snd_2086_, lean_object* v_overlaps_2087_, lean_object* v_matcherName_2088_, lean_object* v_matcherLevels_2089_, lean_object* v_params_x27_2090_, lean_object* v_fst_2091_, lean_object* v_discrs_x27_2092_, lean_object* v_fst_2093_, lean_object* v_toPure_2094_, lean_object* v_____do__lift_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__20(v_fst_2081_, v_numParams_2082_, v_numDiscrs_2083_, v_altInfos_2084_, v_uElimPos_x3f_2085_, v_snd_2086_, v_overlaps_2087_, v_matcherName_2088_, v_matcherLevels_2089_, v_params_x27_2090_, v_fst_2091_, v_discrs_x27_2092_, v_fst_2093_, v_toPure_2094_, v_____do__lift_2095_);
lean_dec_ref(v_____do__lift_2095_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21(lean_object* v_fst_2097_, lean_object* v_numParams_2098_, lean_object* v_numDiscrs_2099_, lean_object* v_altInfos_2100_, lean_object* v_uElimPos_x3f_2101_, lean_object* v_snd_2102_, lean_object* v_overlaps_2103_, lean_object* v_matcherName_2104_, lean_object* v_matcherLevels_2105_, lean_object* v_params_x27_2106_, lean_object* v_fst_2107_, lean_object* v_discrs_x27_2108_, lean_object* v_toPure_2109_, lean_object* v_onRemaining_2110_, lean_object* v_remaining_2111_, lean_object* v_toBind_2112_, lean_object* v_____s_2113_){
_start:
{
lean_object* v_fst_2114_; lean_object* v___f_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v_fst_2114_ = lean_ctor_get(v_____s_2113_, 0);
lean_inc(v_fst_2114_);
lean_dec_ref(v_____s_2113_);
v___f_2115_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__20___boxed), 15, 14);
lean_closure_set(v___f_2115_, 0, v_fst_2097_);
lean_closure_set(v___f_2115_, 1, v_numParams_2098_);
lean_closure_set(v___f_2115_, 2, v_numDiscrs_2099_);
lean_closure_set(v___f_2115_, 3, v_altInfos_2100_);
lean_closure_set(v___f_2115_, 4, v_uElimPos_x3f_2101_);
lean_closure_set(v___f_2115_, 5, v_snd_2102_);
lean_closure_set(v___f_2115_, 6, v_overlaps_2103_);
lean_closure_set(v___f_2115_, 7, v_matcherName_2104_);
lean_closure_set(v___f_2115_, 8, v_matcherLevels_2105_);
lean_closure_set(v___f_2115_, 9, v_params_x27_2106_);
lean_closure_set(v___f_2115_, 10, v_fst_2107_);
lean_closure_set(v___f_2115_, 11, v_discrs_x27_2108_);
lean_closure_set(v___f_2115_, 12, v_fst_2114_);
lean_closure_set(v___f_2115_, 13, v_toPure_2109_);
v___x_2116_ = lean_apply_1(v_onRemaining_2110_, v_remaining_2111_);
v___x_2117_ = lean_apply_4(v_toBind_2112_, lean_box(0), lean_box(0), v___x_2116_, v___f_2115_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed(lean_object** _args){
lean_object* v_fst_2118_ = _args[0];
lean_object* v_numParams_2119_ = _args[1];
lean_object* v_numDiscrs_2120_ = _args[2];
lean_object* v_altInfos_2121_ = _args[3];
lean_object* v_uElimPos_x3f_2122_ = _args[4];
lean_object* v_snd_2123_ = _args[5];
lean_object* v_overlaps_2124_ = _args[6];
lean_object* v_matcherName_2125_ = _args[7];
lean_object* v_matcherLevels_2126_ = _args[8];
lean_object* v_params_x27_2127_ = _args[9];
lean_object* v_fst_2128_ = _args[10];
lean_object* v_discrs_x27_2129_ = _args[11];
lean_object* v_toPure_2130_ = _args[12];
lean_object* v_onRemaining_2131_ = _args[13];
lean_object* v_remaining_2132_ = _args[14];
lean_object* v_toBind_2133_ = _args[15];
lean_object* v_____s_2134_ = _args[16];
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__21(v_fst_2118_, v_numParams_2119_, v_numDiscrs_2120_, v_altInfos_2121_, v_uElimPos_x3f_2122_, v_snd_2123_, v_overlaps_2124_, v_matcherName_2125_, v_matcherLevels_2126_, v_params_x27_2127_, v_fst_2128_, v_discrs_x27_2129_, v_toPure_2130_, v_onRemaining_2131_, v_remaining_2132_, v_toBind_2133_, v_____s_2134_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22(lean_object* v_toPure_2136_, lean_object* v_next_2137_, lean_object* v_G_2138_, lean_object* v_____do__lift_2139_){
_start:
{
if (lean_obj_tag(v_____do__lift_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2141_; 
lean_dec(v_G_2138_);
v_a_2140_ = lean_ctor_get(v_____do__lift_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref(v_____do__lift_2139_);
v___x_2141_ = lean_apply_2(v_toPure_2136_, lean_box(0), v_a_2140_);
return v___x_2141_;
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
lean_dec(v_toPure_2136_);
v_a_2142_ = lean_ctor_get(v_____do__lift_2139_, 0);
lean_inc(v_a_2142_);
lean_dec_ref(v_____do__lift_2139_);
v___x_2143_ = lean_unsigned_to_nat(1u);
v___x_2144_ = lean_nat_add(v_next_2137_, v___x_2143_);
v___x_2145_ = lean_apply_4(v_G_2138_, v___x_2144_, v_a_2142_, lean_box(0), lean_box(0));
return v___x_2145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22___boxed(lean_object* v_toPure_2146_, lean_object* v_next_2147_, lean_object* v_G_2148_, lean_object* v_____do__lift_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__22(v_toPure_2146_, v_next_2147_, v_G_2148_, v_____do__lift_2149_);
lean_dec(v_next_2147_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23(lean_object* v_xs_2151_, lean_object* v_ys4_2152_, uint8_t v___x_2153_, uint8_t v___x_2154_, lean_object* v_inst_2155_, lean_object* v_alt_x27_2156_){
_start:
{
lean_object* v___x_2157_; uint8_t v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2157_ = l_Array_append___redArg(v_xs_2151_, v_ys4_2152_);
v___x_2158_ = 1;
v___x_2159_ = lean_box(v___x_2153_);
v___x_2160_ = lean_box(v___x_2154_);
v___x_2161_ = lean_box(v___x_2153_);
v___x_2162_ = lean_box(v___x_2154_);
v___x_2163_ = lean_box(v___x_2158_);
v___x_2164_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_2164_, 0, v___x_2157_);
lean_closure_set(v___x_2164_, 1, v_alt_x27_2156_);
lean_closure_set(v___x_2164_, 2, v___x_2159_);
lean_closure_set(v___x_2164_, 3, v___x_2160_);
lean_closure_set(v___x_2164_, 4, v___x_2161_);
lean_closure_set(v___x_2164_, 5, v___x_2162_);
lean_closure_set(v___x_2164_, 6, v___x_2163_);
v___x_2165_ = lean_apply_2(v_inst_2155_, lean_box(0), v___x_2164_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed(lean_object* v_xs_2166_, lean_object* v_ys4_2167_, lean_object* v___x_2168_, lean_object* v___x_2169_, lean_object* v_inst_2170_, lean_object* v_alt_x27_2171_){
_start:
{
uint8_t v___x_14941__boxed_2172_; uint8_t v___x_14942__boxed_2173_; lean_object* v_res_2174_; 
v___x_14941__boxed_2172_ = lean_unbox(v___x_2168_);
v___x_14942__boxed_2173_ = lean_unbox(v___x_2169_);
v_res_2174_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__23(v_xs_2166_, v_ys4_2167_, v___x_14941__boxed_2172_, v___x_14942__boxed_2173_, v_inst_2170_, v_alt_x27_2171_);
lean_dec_ref(v_ys4_2167_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__24(lean_object* v_xs_2175_, lean_object* v_remaining_x27_2176_, lean_object* v_ys4_2177_, lean_object* v_onAlt_2178_, lean_object* v_next_2179_, lean_object* v_altType_2180_, lean_object* v_toBind_2181_, lean_object* v___f_2182_, lean_object* v_alt_2183_){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
lean_inc_ref(v_remaining_x27_2176_);
lean_inc_ref(v_xs_2175_);
v___x_2184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2184_, 0, v_xs_2175_);
lean_ctor_set(v___x_2184_, 1, v_xs_2175_);
lean_ctor_set(v___x_2184_, 2, v_remaining_x27_2176_);
lean_ctor_set(v___x_2184_, 3, v_remaining_x27_2176_);
lean_ctor_set(v___x_2184_, 4, v_ys4_2177_);
v___x_2185_ = lean_apply_4(v_onAlt_2178_, v_next_2179_, v_altType_2180_, v___x_2184_, v_alt_2183_);
v___x_2186_ = lean_apply_4(v_toBind_2181_, lean_box(0), lean_box(0), v___x_2185_, v___f_2182_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25(lean_object* v___x_2187_, lean_object* v_xs_2188_, lean_object* v_inst_2189_, lean_object* v_toBind_2190_, lean_object* v___f_2191_, lean_object* v_inst_2192_, lean_object* v_inst_2193_, lean_object* v_names_2194_){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
lean_inc_ref(v_xs_2188_);
v___x_2195_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLambda___boxed), 7, 2);
lean_closure_set(v___x_2195_, 0, v___x_2187_);
lean_closure_set(v___x_2195_, 1, v_xs_2188_);
v___x_2196_ = lean_apply_2(v_inst_2189_, lean_box(0), v___x_2195_);
v___x_2197_ = lean_apply_4(v_toBind_2190_, lean_box(0), lean_box(0), v___x_2196_, v___f_2191_);
v___x_2198_ = l_Lean_Meta_MatcherApp_withUserNames___redArg(v_inst_2192_, v_inst_2193_, v_xs_2188_, v_names_2194_, v___x_2197_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26(lean_object* v_xs_2199_, uint8_t v___x_2200_, uint8_t v___x_2201_, lean_object* v_inst_2202_, lean_object* v_remaining_x27_2203_, lean_object* v_onAlt_2204_, lean_object* v_next_2205_, lean_object* v_toBind_2206_, lean_object* v___x_2207_, lean_object* v_inst_2208_, lean_object* v_inst_2209_, lean_object* v___f_2210_, lean_object* v_ys4_2211_, lean_object* v_altType_2212_){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___f_2215_; lean_object* v___f_2216_; lean_object* v___f_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2213_ = lean_box(v___x_2200_);
v___x_2214_ = lean_box(v___x_2201_);
lean_inc(v_inst_2202_);
lean_inc_ref(v_ys4_2211_);
lean_inc_ref(v_xs_2199_);
v___f_2215_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed), 6, 5);
lean_closure_set(v___f_2215_, 0, v_xs_2199_);
lean_closure_set(v___f_2215_, 1, v_ys4_2211_);
lean_closure_set(v___f_2215_, 2, v___x_2213_);
lean_closure_set(v___f_2215_, 3, v___x_2214_);
lean_closure_set(v___f_2215_, 4, v_inst_2202_);
lean_inc(v_toBind_2206_);
lean_inc_ref(v_xs_2199_);
v___f_2216_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__24), 9, 8);
lean_closure_set(v___f_2216_, 0, v_xs_2199_);
lean_closure_set(v___f_2216_, 1, v_remaining_x27_2203_);
lean_closure_set(v___f_2216_, 2, v_ys4_2211_);
lean_closure_set(v___f_2216_, 3, v_onAlt_2204_);
lean_closure_set(v___f_2216_, 4, v_next_2205_);
lean_closure_set(v___f_2216_, 5, v_altType_2212_);
lean_closure_set(v___f_2216_, 6, v_toBind_2206_);
lean_closure_set(v___f_2216_, 7, v___f_2215_);
lean_inc_ref(v_inst_2209_);
lean_inc_ref(v_inst_2208_);
lean_inc(v_toBind_2206_);
lean_inc_ref(v___x_2207_);
v___f_2217_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__25), 8, 7);
lean_closure_set(v___f_2217_, 0, v___x_2207_);
lean_closure_set(v___f_2217_, 1, v_xs_2199_);
lean_closure_set(v___f_2217_, 2, v_inst_2202_);
lean_closure_set(v___f_2217_, 3, v_toBind_2206_);
lean_closure_set(v___f_2217_, 4, v___f_2216_);
lean_closure_set(v___f_2217_, 5, v_inst_2208_);
lean_closure_set(v___f_2217_, 6, v_inst_2209_);
v___x_2218_ = l_Lean_Meta_lambdaTelescope___redArg(v_inst_2208_, v_inst_2209_, v___x_2207_, v___f_2210_, v___x_2200_);
v___x_2219_ = lean_apply_4(v_toBind_2206_, lean_box(0), lean_box(0), v___x_2218_, v___f_2217_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed(lean_object* v_xs_2220_, lean_object* v___x_2221_, lean_object* v___x_2222_, lean_object* v_inst_2223_, lean_object* v_remaining_x27_2224_, lean_object* v_onAlt_2225_, lean_object* v_next_2226_, lean_object* v_toBind_2227_, lean_object* v___x_2228_, lean_object* v_inst_2229_, lean_object* v_inst_2230_, lean_object* v___f_2231_, lean_object* v_ys4_2232_, lean_object* v_altType_2233_){
_start:
{
uint8_t v___x_14994__boxed_2234_; uint8_t v___x_14995__boxed_2235_; lean_object* v_res_2236_; 
v___x_14994__boxed_2234_ = lean_unbox(v___x_2221_);
v___x_14995__boxed_2235_ = lean_unbox(v___x_2222_);
v_res_2236_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__26(v_xs_2220_, v___x_14994__boxed_2234_, v___x_14995__boxed_2235_, v_inst_2223_, v_remaining_x27_2224_, v_onAlt_2225_, v_next_2226_, v_toBind_2227_, v___x_2228_, v_inst_2229_, v_inst_2230_, v___f_2231_, v_ys4_2232_, v_altType_2233_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27(uint8_t v___x_2237_, uint8_t v___x_2238_, lean_object* v_inst_2239_, lean_object* v_remaining_x27_2240_, lean_object* v_onAlt_2241_, lean_object* v_next_2242_, lean_object* v_toBind_2243_, lean_object* v___x_2244_, lean_object* v_inst_2245_, lean_object* v_inst_2246_, lean_object* v___f_2247_, lean_object* v_fst_2248_, lean_object* v_xs_2249_, lean_object* v_altType_2250_){
_start:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___f_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2251_ = lean_box(v___x_2237_);
v___x_2252_ = lean_box(v___x_2238_);
lean_inc_ref(v_inst_2246_);
lean_inc_ref(v_inst_2245_);
v___f_2253_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed), 14, 12);
lean_closure_set(v___f_2253_, 0, v_xs_2249_);
lean_closure_set(v___f_2253_, 1, v___x_2251_);
lean_closure_set(v___f_2253_, 2, v___x_2252_);
lean_closure_set(v___f_2253_, 3, v_inst_2239_);
lean_closure_set(v___f_2253_, 4, v_remaining_x27_2240_);
lean_closure_set(v___f_2253_, 5, v_onAlt_2241_);
lean_closure_set(v___f_2253_, 6, v_next_2242_);
lean_closure_set(v___f_2253_, 7, v_toBind_2243_);
lean_closure_set(v___f_2253_, 8, v___x_2244_);
lean_closure_set(v___f_2253_, 9, v_inst_2245_);
lean_closure_set(v___f_2253_, 10, v_inst_2246_);
lean_closure_set(v___f_2253_, 11, v___f_2247_);
v___x_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2254_, 0, v_fst_2248_);
v___x_2255_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2245_, v_inst_2246_, v_altType_2250_, v___x_2254_, v___f_2253_, v___x_2237_, v___x_2237_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed(lean_object* v___x_2256_, lean_object* v___x_2257_, lean_object* v_inst_2258_, lean_object* v_remaining_x27_2259_, lean_object* v_onAlt_2260_, lean_object* v_next_2261_, lean_object* v_toBind_2262_, lean_object* v___x_2263_, lean_object* v_inst_2264_, lean_object* v_inst_2265_, lean_object* v___f_2266_, lean_object* v_fst_2267_, lean_object* v_xs_2268_, lean_object* v_altType_2269_){
_start:
{
uint8_t v___x_15029__boxed_2270_; uint8_t v___x_15030__boxed_2271_; lean_object* v_res_2272_; 
v___x_15029__boxed_2270_ = lean_unbox(v___x_2256_);
v___x_15030__boxed_2271_ = lean_unbox(v___x_2257_);
v_res_2272_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__27(v___x_15029__boxed_2270_, v___x_15030__boxed_2271_, v_inst_2258_, v_remaining_x27_2259_, v_onAlt_2260_, v_next_2261_, v_toBind_2262_, v___x_2263_, v_inst_2264_, v_inst_2265_, v___f_2266_, v_fst_2267_, v_xs_2268_, v_altType_2269_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__28(lean_object* v_fst_2273_, lean_object* v___x_2274_, lean_object* v___x_2275_, lean_object* v___x_2276_, lean_object* v_toPure_2277_, lean_object* v_alt_x27_2278_){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2279_ = lean_array_push(v_fst_2273_, v_alt_x27_2278_);
v___x_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2274_);
lean_ctor_set(v___x_2280_, 1, v___x_2275_);
v___x_2281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2276_);
lean_ctor_set(v___x_2281_, 1, v___x_2280_);
v___x_2282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2279_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
v___x_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2282_);
v___x_2284_ = lean_apply_2(v_toPure_2277_, lean_box(0), v___x_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29(lean_object* v___x_2285_, lean_object* v_toPure_2286_, lean_object* v_toBind_2287_, lean_object* v___f_2288_, uint8_t v___x_2289_, uint8_t v___x_2290_, lean_object* v_inst_2291_, lean_object* v_remaining_x27_2292_, lean_object* v_onAlt_2293_, lean_object* v_inst_2294_, lean_object* v_inst_2295_, lean_object* v___f_2296_, lean_object* v_fst_2297_, lean_object* v_next_2298_, lean_object* v_acc_2299_, lean_object* v_h_2300_, lean_object* v_G_2301_){
_start:
{
uint8_t v___x_2302_; 
v___x_2302_ = lean_nat_dec_lt(v_next_2298_, v___x_2285_);
if (v___x_2302_ == 0)
{
lean_object* v___x_2303_; 
lean_dec(v_G_2301_);
lean_dec(v_next_2298_);
lean_dec(v_fst_2297_);
lean_dec(v___f_2296_);
lean_dec_ref(v_inst_2295_);
lean_dec_ref(v_inst_2294_);
lean_dec(v_onAlt_2293_);
lean_dec_ref(v_remaining_x27_2292_);
lean_dec(v_inst_2291_);
lean_dec(v___f_2288_);
lean_dec(v_toBind_2287_);
v___x_2303_ = lean_apply_2(v_toPure_2286_, lean_box(0), v_acc_2299_);
return v___x_2303_;
}
else
{
lean_object* v_snd_2304_; lean_object* v_snd_2305_; lean_object* v_snd_2306_; lean_object* v_fst_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2417_; 
v_snd_2304_ = lean_ctor_get(v_acc_2299_, 1);
lean_inc(v_snd_2304_);
v_snd_2305_ = lean_ctor_get(v_snd_2304_, 1);
lean_inc(v_snd_2305_);
v_snd_2306_ = lean_ctor_get(v_snd_2305_, 1);
lean_inc(v_snd_2306_);
v_fst_2307_ = lean_ctor_get(v_acc_2299_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v_acc_2299_);
if (v_isSharedCheck_2417_ == 0)
{
lean_object* v_unused_2418_; 
v_unused_2418_ = lean_ctor_get(v_acc_2299_, 1);
lean_dec(v_unused_2418_);
v___x_2309_ = v_acc_2299_;
v_isShared_2310_ = v_isSharedCheck_2417_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_fst_2307_);
lean_dec(v_acc_2299_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2417_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v_fst_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2415_; 
v_fst_2311_ = lean_ctor_get(v_snd_2304_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v_snd_2304_);
if (v_isSharedCheck_2415_ == 0)
{
lean_object* v_unused_2416_; 
v_unused_2416_ = lean_ctor_get(v_snd_2304_, 1);
lean_dec(v_unused_2416_);
v___x_2313_ = v_snd_2304_;
v_isShared_2314_ = v_isSharedCheck_2415_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_fst_2311_);
lean_dec(v_snd_2304_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2415_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v_fst_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2413_; 
v_fst_2315_ = lean_ctor_get(v_snd_2305_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v_snd_2305_);
if (v_isSharedCheck_2413_ == 0)
{
lean_object* v_unused_2414_; 
v_unused_2414_ = lean_ctor_get(v_snd_2305_, 1);
lean_dec(v_unused_2414_);
v___x_2317_ = v_snd_2305_;
v_isShared_2318_ = v_isSharedCheck_2413_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_fst_2315_);
lean_dec(v_snd_2305_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2413_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v_array_2319_; lean_object* v_start_2320_; lean_object* v_stop_2321_; lean_object* v___f_2322_; lean_object* v___y_2324_; uint8_t v___x_2327_; 
v_array_2319_ = lean_ctor_get(v_snd_2306_, 0);
v_start_2320_ = lean_ctor_get(v_snd_2306_, 1);
v_stop_2321_ = lean_ctor_get(v_snd_2306_, 2);
lean_inc(v_next_2298_);
lean_inc(v_toPure_2286_);
v___f_2322_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__22___boxed), 4, 3);
lean_closure_set(v___f_2322_, 0, v_toPure_2286_);
lean_closure_set(v___f_2322_, 1, v_next_2298_);
lean_closure_set(v___f_2322_, 2, v_G_2301_);
v___x_2327_ = lean_nat_dec_lt(v_start_2320_, v_stop_2321_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2329_; 
lean_dec(v_next_2298_);
lean_dec(v_fst_2297_);
lean_dec(v___f_2296_);
lean_dec_ref(v_inst_2295_);
lean_dec_ref(v_inst_2294_);
lean_dec(v_onAlt_2293_);
lean_dec_ref(v_remaining_x27_2292_);
lean_dec(v_inst_2291_);
if (v_isShared_2318_ == 0)
{
v___x_2329_ = v___x_2317_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_fst_2315_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v_snd_2306_);
v___x_2329_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
lean_object* v___x_2331_; 
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 1, v___x_2329_);
v___x_2331_ = v___x_2313_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_fst_2311_);
lean_ctor_set(v_reuseFailAlloc_2337_, 1, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2333_; 
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 1, v___x_2331_);
v___x_2333_ = v___x_2309_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_fst_2307_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2333_);
v___x_2335_ = lean_apply_2(v_toPure_2286_, lean_box(0), v___x_2334_);
v___y_2324_ = v___x_2335_;
goto v___jp_2323_;
}
}
}
}
else
{
lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2409_; 
lean_inc(v_stop_2321_);
lean_inc(v_start_2320_);
lean_inc_ref(v_array_2319_);
v_isSharedCheck_2409_ = !lean_is_exclusive(v_snd_2306_);
if (v_isSharedCheck_2409_ == 0)
{
lean_object* v_unused_2410_; lean_object* v_unused_2411_; lean_object* v_unused_2412_; 
v_unused_2410_ = lean_ctor_get(v_snd_2306_, 2);
lean_dec(v_unused_2410_);
v_unused_2411_ = lean_ctor_get(v_snd_2306_, 1);
lean_dec(v_unused_2411_);
v_unused_2412_ = lean_ctor_get(v_snd_2306_, 0);
lean_dec(v_unused_2412_);
v___x_2340_ = v_snd_2306_;
v_isShared_2341_ = v_isSharedCheck_2409_;
goto v_resetjp_2339_;
}
else
{
lean_dec(v_snd_2306_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2409_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v_array_2342_; lean_object* v_start_2343_; lean_object* v_stop_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2349_; 
v_array_2342_ = lean_ctor_get(v_fst_2315_, 0);
v_start_2343_ = lean_ctor_get(v_fst_2315_, 1);
v_stop_2344_ = lean_ctor_get(v_fst_2315_, 2);
v___x_2345_ = lean_array_fget(v_array_2319_, v_start_2320_);
v___x_2346_ = lean_unsigned_to_nat(1u);
v___x_2347_ = lean_nat_add(v_start_2320_, v___x_2346_);
lean_dec(v_start_2320_);
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 1, v___x_2347_);
v___x_2349_ = v___x_2340_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_array_2319_);
lean_ctor_set(v_reuseFailAlloc_2408_, 1, v___x_2347_);
lean_ctor_set(v_reuseFailAlloc_2408_, 2, v_stop_2321_);
v___x_2349_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
uint8_t v___x_2350_; 
v___x_2350_ = lean_nat_dec_lt(v_start_2343_, v_stop_2344_);
if (v___x_2350_ == 0)
{
lean_object* v___x_2352_; 
lean_dec(v___x_2345_);
lean_dec(v_next_2298_);
lean_dec(v_fst_2297_);
lean_dec(v___f_2296_);
lean_dec_ref(v_inst_2295_);
lean_dec_ref(v_inst_2294_);
lean_dec(v_onAlt_2293_);
lean_dec_ref(v_remaining_x27_2292_);
lean_dec(v_inst_2291_);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 1, v___x_2349_);
v___x_2352_ = v___x_2317_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_fst_2315_);
lean_ctor_set(v_reuseFailAlloc_2361_, 1, v___x_2349_);
v___x_2352_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
lean_object* v___x_2354_; 
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 1, v___x_2352_);
v___x_2354_ = v___x_2313_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_fst_2311_);
lean_ctor_set(v_reuseFailAlloc_2360_, 1, v___x_2352_);
v___x_2354_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
lean_object* v___x_2356_; 
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 1, v___x_2354_);
v___x_2356_ = v___x_2309_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_fst_2307_);
lean_ctor_set(v_reuseFailAlloc_2359_, 1, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
v___x_2358_ = lean_apply_2(v_toPure_2286_, lean_box(0), v___x_2357_);
v___y_2324_ = v___x_2358_;
goto v___jp_2323_;
}
}
}
}
else
{
lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2404_; 
lean_inc(v_stop_2344_);
lean_inc(v_start_2343_);
lean_inc_ref(v_array_2342_);
v_isSharedCheck_2404_ = !lean_is_exclusive(v_fst_2315_);
if (v_isSharedCheck_2404_ == 0)
{
lean_object* v_unused_2405_; lean_object* v_unused_2406_; lean_object* v_unused_2407_; 
v_unused_2405_ = lean_ctor_get(v_fst_2315_, 2);
lean_dec(v_unused_2405_);
v_unused_2406_ = lean_ctor_get(v_fst_2315_, 1);
lean_dec(v_unused_2406_);
v_unused_2407_ = lean_ctor_get(v_fst_2315_, 0);
lean_dec(v_unused_2407_);
v___x_2363_ = v_fst_2315_;
v_isShared_2364_ = v_isSharedCheck_2404_;
goto v_resetjp_2362_;
}
else
{
lean_dec(v_fst_2315_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2404_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v_array_2365_; lean_object* v_start_2366_; lean_object* v_stop_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2371_; 
v_array_2365_ = lean_ctor_get(v_fst_2311_, 0);
v_start_2366_ = lean_ctor_get(v_fst_2311_, 1);
v_stop_2367_ = lean_ctor_get(v_fst_2311_, 2);
v___x_2368_ = lean_array_fget(v_array_2342_, v_start_2343_);
v___x_2369_ = lean_nat_add(v_start_2343_, v___x_2346_);
lean_dec(v_start_2343_);
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 1, v___x_2369_);
v___x_2371_ = v___x_2363_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_array_2342_);
lean_ctor_set(v_reuseFailAlloc_2403_, 1, v___x_2369_);
lean_ctor_set(v_reuseFailAlloc_2403_, 2, v_stop_2344_);
v___x_2371_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
uint8_t v___x_2372_; 
v___x_2372_ = lean_nat_dec_lt(v_start_2366_, v_stop_2367_);
if (v___x_2372_ == 0)
{
lean_object* v___x_2374_; 
lean_dec(v___x_2368_);
lean_dec(v___x_2345_);
lean_dec(v_next_2298_);
lean_dec(v_fst_2297_);
lean_dec(v___f_2296_);
lean_dec_ref(v_inst_2295_);
lean_dec_ref(v_inst_2294_);
lean_dec(v_onAlt_2293_);
lean_dec_ref(v_remaining_x27_2292_);
lean_dec(v_inst_2291_);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 1, v___x_2349_);
lean_ctor_set(v___x_2317_, 0, v___x_2371_);
v___x_2374_ = v___x_2317_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v___x_2371_);
lean_ctor_set(v_reuseFailAlloc_2383_, 1, v___x_2349_);
v___x_2374_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
lean_object* v___x_2376_; 
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 1, v___x_2374_);
v___x_2376_ = v___x_2313_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_fst_2311_);
lean_ctor_set(v_reuseFailAlloc_2382_, 1, v___x_2374_);
v___x_2376_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
lean_object* v___x_2378_; 
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 1, v___x_2376_);
v___x_2378_ = v___x_2309_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_fst_2307_);
lean_ctor_set(v_reuseFailAlloc_2381_, 1, v___x_2376_);
v___x_2378_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2378_);
v___x_2380_ = lean_apply_2(v_toPure_2286_, lean_box(0), v___x_2379_);
v___y_2324_ = v___x_2380_;
goto v___jp_2323_;
}
}
}
}
else
{
lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2399_; 
lean_inc(v_stop_2367_);
lean_inc(v_start_2366_);
lean_inc_ref(v_array_2365_);
lean_del_object(v___x_2317_);
lean_del_object(v___x_2313_);
lean_del_object(v___x_2309_);
v_isSharedCheck_2399_ = !lean_is_exclusive(v_fst_2311_);
if (v_isSharedCheck_2399_ == 0)
{
lean_object* v_unused_2400_; lean_object* v_unused_2401_; lean_object* v_unused_2402_; 
v_unused_2400_ = lean_ctor_get(v_fst_2311_, 2);
lean_dec(v_unused_2400_);
v_unused_2401_ = lean_ctor_get(v_fst_2311_, 1);
lean_dec(v_unused_2401_);
v_unused_2402_ = lean_ctor_get(v_fst_2311_, 0);
lean_dec(v_unused_2402_);
v___x_2385_ = v_fst_2311_;
v_isShared_2386_ = v_isSharedCheck_2399_;
goto v_resetjp_2384_;
}
else
{
lean_dec(v_fst_2311_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2399_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___f_2390_; lean_object* v___x_2391_; lean_object* v___x_2393_; 
v___x_2387_ = lean_array_fget_borrowed(v_array_2365_, v_start_2366_);
v___x_2388_ = lean_box(v___x_2289_);
v___x_2389_ = lean_box(v___x_2290_);
lean_inc_ref(v_inst_2295_);
lean_inc_ref(v_inst_2294_);
lean_inc(v___x_2387_);
lean_inc(v_toBind_2287_);
v___f_2390_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed), 14, 12);
lean_closure_set(v___f_2390_, 0, v___x_2388_);
lean_closure_set(v___f_2390_, 1, v___x_2389_);
lean_closure_set(v___f_2390_, 2, v_inst_2291_);
lean_closure_set(v___f_2390_, 3, v_remaining_x27_2292_);
lean_closure_set(v___f_2390_, 4, v_onAlt_2293_);
lean_closure_set(v___f_2390_, 5, v_next_2298_);
lean_closure_set(v___f_2390_, 6, v_toBind_2287_);
lean_closure_set(v___f_2390_, 7, v___x_2387_);
lean_closure_set(v___f_2390_, 8, v_inst_2294_);
lean_closure_set(v___f_2390_, 9, v_inst_2295_);
lean_closure_set(v___f_2390_, 10, v___f_2296_);
lean_closure_set(v___f_2390_, 11, v_fst_2297_);
v___x_2391_ = lean_nat_add(v_start_2366_, v___x_2346_);
lean_dec(v_start_2366_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 1, v___x_2391_);
v___x_2393_ = v___x_2385_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_array_2365_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v___x_2391_);
lean_ctor_set(v_reuseFailAlloc_2398_, 2, v_stop_2367_);
v___x_2393_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
lean_object* v___f_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___f_2394_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__28), 6, 5);
lean_closure_set(v___f_2394_, 0, v_fst_2307_);
lean_closure_set(v___f_2394_, 1, v___x_2371_);
lean_closure_set(v___f_2394_, 2, v___x_2349_);
lean_closure_set(v___f_2394_, 3, v___x_2393_);
lean_closure_set(v___f_2394_, 4, v_toPure_2286_);
v___x_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2368_);
v___x_2396_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2294_, v_inst_2295_, v___x_2345_, v___x_2395_, v___f_2390_, v___x_2289_, v___x_2289_);
lean_inc(v_toBind_2287_);
v___x_2397_ = lean_apply_4(v_toBind_2287_, lean_box(0), lean_box(0), v___x_2396_, v___f_2394_);
v___y_2324_ = v___x_2397_;
goto v___jp_2323_;
}
}
}
}
}
}
}
}
}
v___jp_2323_:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
lean_inc(v_toBind_2287_);
v___x_2325_ = lean_apply_4(v_toBind_2287_, lean_box(0), lean_box(0), v___y_2324_, v___f_2288_);
v___x_2326_ = lean_apply_4(v_toBind_2287_, lean_box(0), lean_box(0), v___x_2325_, v___f_2322_);
return v___x_2326_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29___boxed(lean_object** _args){
lean_object* v___x_2419_ = _args[0];
lean_object* v_toPure_2420_ = _args[1];
lean_object* v_toBind_2421_ = _args[2];
lean_object* v___f_2422_ = _args[3];
lean_object* v___x_2423_ = _args[4];
lean_object* v___x_2424_ = _args[5];
lean_object* v_inst_2425_ = _args[6];
lean_object* v_remaining_x27_2426_ = _args[7];
lean_object* v_onAlt_2427_ = _args[8];
lean_object* v_inst_2428_ = _args[9];
lean_object* v_inst_2429_ = _args[10];
lean_object* v___f_2430_ = _args[11];
lean_object* v_fst_2431_ = _args[12];
lean_object* v_next_2432_ = _args[13];
lean_object* v_acc_2433_ = _args[14];
lean_object* v_h_2434_ = _args[15];
lean_object* v_G_2435_ = _args[16];
_start:
{
uint8_t v___x_15080__boxed_2436_; uint8_t v___x_15081__boxed_2437_; lean_object* v_res_2438_; 
v___x_15080__boxed_2436_ = lean_unbox(v___x_2423_);
v___x_15081__boxed_2437_ = lean_unbox(v___x_2424_);
v_res_2438_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__29(v___x_2419_, v_toPure_2420_, v_toBind_2421_, v___f_2422_, v___x_15080__boxed_2436_, v___x_15081__boxed_2437_, v_inst_2425_, v_remaining_x27_2426_, v_onAlt_2427_, v_inst_2428_, v_inst_2429_, v___f_2430_, v_fst_2431_, v_next_2432_, v_acc_2433_, v_h_2434_, v_G_2435_);
lean_dec(v___x_2419_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__30(lean_object* v_matcherApp_2439_, lean_object* v_alts_2440_, lean_object* v___x_2441_, lean_object* v___x_2442_, lean_object* v_remaining_x27_2443_, lean_object* v___f_2444_, lean_object* v_toBind_2445_, lean_object* v___f_2446_, lean_object* v_altTypes_2447_){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2448_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_2439_);
v___x_2449_ = lean_array_get_size(v___x_2448_);
v___x_2450_ = lean_array_get_size(v_altTypes_2447_);
lean_inc(v___x_2441_);
v___x_2451_ = l_Array_toSubarray___redArg(v_alts_2440_, v___x_2441_, v___x_2442_);
lean_inc(v___x_2441_);
v___x_2452_ = l_Array_toSubarray___redArg(v___x_2448_, v___x_2441_, v___x_2449_);
lean_inc(v___x_2441_);
v___x_2453_ = l_Array_toSubarray___redArg(v_altTypes_2447_, v___x_2441_, v___x_2450_);
v___x_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2452_);
lean_ctor_set(v___x_2454_, 1, v___x_2453_);
v___x_2455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2451_);
lean_ctor_set(v___x_2455_, 1, v___x_2454_);
v___x_2456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2456_, 0, v_remaining_x27_2443_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
v___x_2457_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2444_, v___x_2441_, v___x_2456_, lean_box(0));
v___x_2458_ = lean_apply_4(v_toBind_2445_, lean_box(0), lean_box(0), v___x_2457_, v___f_2446_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31(lean_object* v_alts_2459_, lean_object* v_toPure_2460_, lean_object* v_toBind_2461_, lean_object* v___f_2462_, uint8_t v___x_2463_, uint8_t v___x_2464_, lean_object* v_inst_2465_, lean_object* v_remaining_x27_2466_, lean_object* v_onAlt_2467_, lean_object* v_inst_2468_, lean_object* v_inst_2469_, lean_object* v___f_2470_, lean_object* v_fst_2471_, lean_object* v_matcherApp_2472_, lean_object* v___x_2473_, lean_object* v___f_2474_, lean_object* v_aux_2475_, lean_object* v_____r_2476_){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___f_2480_; lean_object* v___f_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2477_ = lean_array_get_size(v_alts_2459_);
v___x_2478_ = lean_box(v___x_2463_);
v___x_2479_ = lean_box(v___x_2464_);
lean_inc_ref(v_remaining_x27_2466_);
lean_inc(v_inst_2465_);
lean_inc(v_toBind_2461_);
v___f_2480_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__29___boxed), 17, 13);
lean_closure_set(v___f_2480_, 0, v___x_2477_);
lean_closure_set(v___f_2480_, 1, v_toPure_2460_);
lean_closure_set(v___f_2480_, 2, v_toBind_2461_);
lean_closure_set(v___f_2480_, 3, v___f_2462_);
lean_closure_set(v___f_2480_, 4, v___x_2478_);
lean_closure_set(v___f_2480_, 5, v___x_2479_);
lean_closure_set(v___f_2480_, 6, v_inst_2465_);
lean_closure_set(v___f_2480_, 7, v_remaining_x27_2466_);
lean_closure_set(v___f_2480_, 8, v_onAlt_2467_);
lean_closure_set(v___f_2480_, 9, v_inst_2468_);
lean_closure_set(v___f_2480_, 10, v_inst_2469_);
lean_closure_set(v___f_2480_, 11, v___f_2470_);
lean_closure_set(v___f_2480_, 12, v_fst_2471_);
lean_inc(v_toBind_2461_);
v___f_2481_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__30), 9, 8);
lean_closure_set(v___f_2481_, 0, v_matcherApp_2472_);
lean_closure_set(v___f_2481_, 1, v_alts_2459_);
lean_closure_set(v___f_2481_, 2, v___x_2473_);
lean_closure_set(v___f_2481_, 3, v___x_2477_);
lean_closure_set(v___f_2481_, 4, v_remaining_x27_2466_);
lean_closure_set(v___f_2481_, 5, v___f_2480_);
lean_closure_set(v___f_2481_, 6, v_toBind_2461_);
lean_closure_set(v___f_2481_, 7, v___f_2474_);
v___x_2482_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_2482_, 0, v___x_2477_);
lean_closure_set(v___x_2482_, 1, v_aux_2475_);
v___x_2483_ = lean_apply_2(v_inst_2465_, lean_box(0), v___x_2482_);
v___x_2484_ = lean_apply_4(v_toBind_2461_, lean_box(0), lean_box(0), v___x_2483_, v___f_2481_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed(lean_object** _args){
lean_object* v_alts_2485_ = _args[0];
lean_object* v_toPure_2486_ = _args[1];
lean_object* v_toBind_2487_ = _args[2];
lean_object* v___f_2488_ = _args[3];
lean_object* v___x_2489_ = _args[4];
lean_object* v___x_2490_ = _args[5];
lean_object* v_inst_2491_ = _args[6];
lean_object* v_remaining_x27_2492_ = _args[7];
lean_object* v_onAlt_2493_ = _args[8];
lean_object* v_inst_2494_ = _args[9];
lean_object* v_inst_2495_ = _args[10];
lean_object* v___f_2496_ = _args[11];
lean_object* v_fst_2497_ = _args[12];
lean_object* v_matcherApp_2498_ = _args[13];
lean_object* v___x_2499_ = _args[14];
lean_object* v___f_2500_ = _args[15];
lean_object* v_aux_2501_ = _args[16];
lean_object* v_____r_2502_ = _args[17];
_start:
{
uint8_t v___x_15337__boxed_2503_; uint8_t v___x_15338__boxed_2504_; lean_object* v_res_2505_; 
v___x_15337__boxed_2503_ = lean_unbox(v___x_2489_);
v___x_15338__boxed_2504_ = lean_unbox(v___x_2490_);
v_res_2505_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__31(v_alts_2485_, v_toPure_2486_, v_toBind_2487_, v___f_2488_, v___x_15337__boxed_2503_, v___x_15338__boxed_2504_, v_inst_2491_, v_remaining_x27_2492_, v_onAlt_2493_, v_inst_2494_, v_inst_2495_, v___f_2496_, v_fst_2497_, v_matcherApp_2498_, v___x_2499_, v___f_2500_, v_aux_2501_, v_____r_2502_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__32(lean_object* v___x_2506_, lean_object* v_e_2507_){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = l_Lean_indentD(v_e_2507_);
v___x_2509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2506_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33(lean_object* v___x_2510_, lean_object* v___f_2511_, lean_object* v_runInBase_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2518_ = lean_apply_2(v_runInBase_2512_, lean_box(0), v___x_2510_);
v___x_2519_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2518_, v___f_2511_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed(lean_object* v___x_2520_, lean_object* v___f_2521_, lean_object* v_runInBase_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__33(v___x_2520_, v___f_2521_, v_runInBase_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34(lean_object* v_toPure_2529_, lean_object* v_next_2530_, lean_object* v_G_2531_, lean_object* v_____do__lift_2532_){
_start:
{
if (lean_obj_tag(v_____do__lift_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___x_2534_; 
lean_dec(v_G_2531_);
v_a_2533_ = lean_ctor_get(v_____do__lift_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref(v_____do__lift_2532_);
v___x_2534_ = lean_apply_2(v_toPure_2529_, lean_box(0), v_a_2533_);
return v___x_2534_;
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
lean_dec(v_toPure_2529_);
v_a_2535_ = lean_ctor_get(v_____do__lift_2532_, 0);
lean_inc(v_a_2535_);
lean_dec_ref(v_____do__lift_2532_);
v___x_2536_ = lean_unsigned_to_nat(1u);
v___x_2537_ = lean_nat_add(v_next_2530_, v___x_2536_);
v___x_2538_ = lean_apply_4(v_G_2531_, v___x_2537_, v_a_2535_, lean_box(0), lean_box(0));
return v___x_2538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed(lean_object* v_toPure_2539_, lean_object* v_next_2540_, lean_object* v_G_2541_, lean_object* v_____do__lift_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__34(v_toPure_2539_, v_next_2540_, v_G_2541_, v_____do__lift_2542_);
lean_dec(v_next_2540_);
return v_res_2543_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__5(void){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2552_ = lean_box(0);
v___x_2553_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__4));
v___x_2554_ = l_Lean_mkConst(v___x_2553_, v___x_2552_);
return v___x_2554_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__6(void){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2555_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__5);
v___x_2556_ = lean_unsigned_to_nat(2u);
v___x_2557_ = lean_mk_empty_array_with_capacity(v___x_2556_);
v___x_2558_ = lean_array_push(v___x_2557_, v___x_2555_);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35(lean_object* v___x_2559_, lean_object* v_toPure_2560_, lean_object* v_inst_2561_, lean_object* v_alt_x27_2562_){
_start:
{
uint8_t v_hasUnitThunk_2563_; 
v_hasUnitThunk_2563_ = lean_ctor_get_uint8(v___x_2559_, sizeof(void*)*2);
if (v_hasUnitThunk_2563_ == 0)
{
lean_object* v___x_2564_; 
lean_dec(v_inst_2561_);
v___x_2564_ = lean_apply_2(v_toPure_2560_, lean_box(0), v_alt_x27_2562_);
return v___x_2564_;
}
else
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
lean_dec(v_toPure_2560_);
v___x_2565_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__2));
v___x_2566_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__6);
v___x_2567_ = lean_array_push(v___x_2566_, v_alt_x27_2562_);
v___x_2568_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___boxed), 7, 2);
lean_closure_set(v___x_2568_, 0, v___x_2565_);
lean_closure_set(v___x_2568_, 1, v___x_2567_);
v___x_2569_ = lean_apply_2(v_inst_2561_, lean_box(0), v___x_2568_);
return v___x_2569_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed(lean_object* v___x_2570_, lean_object* v_toPure_2571_, lean_object* v_inst_2572_, lean_object* v_alt_x27_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__35(v___x_2570_, v_toPure_2571_, v_inst_2572_, v_alt_x27_2573_);
lean_dec_ref(v___x_2570_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36(lean_object* v_ys_2575_, lean_object* v_ys2_2576_, lean_object* v_ys3_2577_, lean_object* v_ys4_2578_, uint8_t v___x_2579_, uint8_t v_useSplitter_2580_, lean_object* v_inst_2581_, lean_object* v_alt_x27_2582_){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; uint8_t v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2583_ = l_Array_append___redArg(v_ys_2575_, v_ys2_2576_);
v___x_2584_ = l_Array_append___redArg(v___x_2583_, v_ys3_2577_);
v___x_2585_ = l_Array_append___redArg(v___x_2584_, v_ys4_2578_);
v___x_2586_ = 1;
v___x_2587_ = lean_box(v___x_2579_);
v___x_2588_ = lean_box(v_useSplitter_2580_);
v___x_2589_ = lean_box(v___x_2579_);
v___x_2590_ = lean_box(v_useSplitter_2580_);
v___x_2591_ = lean_box(v___x_2586_);
v___x_2592_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_2592_, 0, v___x_2585_);
lean_closure_set(v___x_2592_, 1, v_alt_x27_2582_);
lean_closure_set(v___x_2592_, 2, v___x_2587_);
lean_closure_set(v___x_2592_, 3, v___x_2588_);
lean_closure_set(v___x_2592_, 4, v___x_2589_);
lean_closure_set(v___x_2592_, 5, v___x_2590_);
lean_closure_set(v___x_2592_, 6, v___x_2591_);
v___x_2593_ = lean_apply_2(v_inst_2581_, lean_box(0), v___x_2592_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed(lean_object* v_ys_2594_, lean_object* v_ys2_2595_, lean_object* v_ys3_2596_, lean_object* v_ys4_2597_, lean_object* v___x_2598_, lean_object* v_useSplitter_2599_, lean_object* v_inst_2600_, lean_object* v_alt_x27_2601_){
_start:
{
uint8_t v___x_15491__boxed_2602_; uint8_t v_useSplitter_boxed_2603_; lean_object* v_res_2604_; 
v___x_15491__boxed_2602_ = lean_unbox(v___x_2598_);
v_useSplitter_boxed_2603_ = lean_unbox(v_useSplitter_2599_);
v_res_2604_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__36(v_ys_2594_, v_ys2_2595_, v_ys3_2596_, v_ys4_2597_, v___x_15491__boxed_2602_, v_useSplitter_boxed_2603_, v_inst_2600_, v_alt_x27_2601_);
lean_dec_ref(v_ys4_2597_);
lean_dec_ref(v_ys3_2596_);
lean_dec_ref(v_ys2_2595_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__37(lean_object* v_args_2605_, lean_object* v_ys_2606_, lean_object* v_ys2_2607_, lean_object* v_ys3_2608_, lean_object* v_ys4_2609_, lean_object* v_onAlt_2610_, lean_object* v_next_2611_, lean_object* v_altType_2612_, lean_object* v_toBind_2613_, lean_object* v___f_2614_, lean_object* v_alt_2615_){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2616_, 0, v_args_2605_);
lean_ctor_set(v___x_2616_, 1, v_ys_2606_);
lean_ctor_set(v___x_2616_, 2, v_ys2_2607_);
lean_ctor_set(v___x_2616_, 3, v_ys3_2608_);
lean_ctor_set(v___x_2616_, 4, v_ys4_2609_);
v___x_2617_ = lean_apply_4(v_onAlt_2610_, v_next_2611_, v_altType_2612_, v___x_2616_, v_alt_2615_);
v___x_2618_ = lean_apply_4(v_toBind_2613_, lean_box(0), lean_box(0), v___x_2617_, v___f_2614_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38(lean_object* v_inst_2619_, lean_object* v_ys_2620_, lean_object* v_ys2_2621_, lean_object* v_ys3_2622_, uint8_t v___x_2623_, uint8_t v_useSplitter_2624_, lean_object* v_inst_2625_, lean_object* v_args_2626_, lean_object* v_onAlt_2627_, lean_object* v_next_2628_, lean_object* v_toBind_2629_, lean_object* v___x_2630_, lean_object* v___f_2631_, lean_object* v_ys4_2632_, lean_object* v_altType_2633_){
_start:
{
lean_object* v_toMonadExceptOf_2634_; lean_object* v_tryCatch_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___f_2638_; lean_object* v___f_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
v_toMonadExceptOf_2634_ = lean_ctor_get(v_inst_2619_, 0);
lean_inc_ref(v_toMonadExceptOf_2634_);
lean_dec_ref(v_inst_2619_);
v_tryCatch_2635_ = lean_ctor_get(v_toMonadExceptOf_2634_, 1);
lean_inc(v_tryCatch_2635_);
lean_dec_ref(v_toMonadExceptOf_2634_);
v___x_2636_ = lean_box(v___x_2623_);
v___x_2637_ = lean_box(v_useSplitter_2624_);
lean_inc(v_inst_2625_);
lean_inc_ref(v_ys4_2632_);
lean_inc_ref(v_ys3_2622_);
lean_inc_ref(v_ys2_2621_);
lean_inc_ref(v_ys_2620_);
v___f_2638_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed), 8, 7);
lean_closure_set(v___f_2638_, 0, v_ys_2620_);
lean_closure_set(v___f_2638_, 1, v_ys2_2621_);
lean_closure_set(v___f_2638_, 2, v_ys3_2622_);
lean_closure_set(v___f_2638_, 3, v_ys4_2632_);
lean_closure_set(v___f_2638_, 4, v___x_2636_);
lean_closure_set(v___f_2638_, 5, v___x_2637_);
lean_closure_set(v___f_2638_, 6, v_inst_2625_);
lean_inc(v_toBind_2629_);
lean_inc_ref(v_ys3_2622_);
lean_inc_ref(v_args_2626_);
v___f_2639_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37), 11, 10);
lean_closure_set(v___f_2639_, 0, v_args_2626_);
lean_closure_set(v___f_2639_, 1, v_ys_2620_);
lean_closure_set(v___f_2639_, 2, v_ys2_2621_);
lean_closure_set(v___f_2639_, 3, v_ys3_2622_);
lean_closure_set(v___f_2639_, 4, v_ys4_2632_);
lean_closure_set(v___f_2639_, 5, v_onAlt_2627_);
lean_closure_set(v___f_2639_, 6, v_next_2628_);
lean_closure_set(v___f_2639_, 7, v_altType_2633_);
lean_closure_set(v___f_2639_, 8, v_toBind_2629_);
lean_closure_set(v___f_2639_, 9, v___f_2638_);
v___x_2640_ = l_Array_append___redArg(v_args_2626_, v_ys3_2622_);
lean_dec_ref(v_ys3_2622_);
v___x_2641_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLambda___boxed), 7, 2);
lean_closure_set(v___x_2641_, 0, v___x_2630_);
lean_closure_set(v___x_2641_, 1, v___x_2640_);
v___x_2642_ = lean_apply_2(v_inst_2625_, lean_box(0), v___x_2641_);
v___x_2643_ = lean_apply_3(v_tryCatch_2635_, lean_box(0), v___x_2642_, v___f_2631_);
v___x_2644_ = lean_apply_4(v_toBind_2629_, lean_box(0), lean_box(0), v___x_2643_, v___f_2639_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed(lean_object* v_inst_2645_, lean_object* v_ys_2646_, lean_object* v_ys2_2647_, lean_object* v_ys3_2648_, lean_object* v___x_2649_, lean_object* v_useSplitter_2650_, lean_object* v_inst_2651_, lean_object* v_args_2652_, lean_object* v_onAlt_2653_, lean_object* v_next_2654_, lean_object* v_toBind_2655_, lean_object* v___x_2656_, lean_object* v___f_2657_, lean_object* v_ys4_2658_, lean_object* v_altType_2659_){
_start:
{
uint8_t v___x_15528__boxed_2660_; uint8_t v_useSplitter_boxed_2661_; lean_object* v_res_2662_; 
v___x_15528__boxed_2660_ = lean_unbox(v___x_2649_);
v_useSplitter_boxed_2661_ = lean_unbox(v_useSplitter_2650_);
v_res_2662_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__38(v_inst_2645_, v_ys_2646_, v_ys2_2647_, v_ys3_2648_, v___x_15528__boxed_2660_, v_useSplitter_boxed_2661_, v_inst_2651_, v_args_2652_, v_onAlt_2653_, v_next_2654_, v_toBind_2655_, v___x_2656_, v___f_2657_, v_ys4_2658_, v_altType_2659_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39(lean_object* v_inst_2663_, lean_object* v_ys_2664_, lean_object* v_ys2_2665_, uint8_t v___x_2666_, uint8_t v_useSplitter_2667_, lean_object* v_inst_2668_, lean_object* v_args_2669_, lean_object* v_onAlt_2670_, lean_object* v_next_2671_, lean_object* v_toBind_2672_, lean_object* v___x_2673_, lean_object* v___f_2674_, lean_object* v_fst_2675_, lean_object* v_inst_2676_, lean_object* v_inst_2677_, lean_object* v_ys3_2678_, lean_object* v_altType_2679_){
_start:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___f_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2680_ = lean_box(v___x_2666_);
v___x_2681_ = lean_box(v_useSplitter_2667_);
v___f_2682_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed), 15, 13);
lean_closure_set(v___f_2682_, 0, v_inst_2663_);
lean_closure_set(v___f_2682_, 1, v_ys_2664_);
lean_closure_set(v___f_2682_, 2, v_ys2_2665_);
lean_closure_set(v___f_2682_, 3, v_ys3_2678_);
lean_closure_set(v___f_2682_, 4, v___x_2680_);
lean_closure_set(v___f_2682_, 5, v___x_2681_);
lean_closure_set(v___f_2682_, 6, v_inst_2668_);
lean_closure_set(v___f_2682_, 7, v_args_2669_);
lean_closure_set(v___f_2682_, 8, v_onAlt_2670_);
lean_closure_set(v___f_2682_, 9, v_next_2671_);
lean_closure_set(v___f_2682_, 10, v_toBind_2672_);
lean_closure_set(v___f_2682_, 11, v___x_2673_);
lean_closure_set(v___f_2682_, 12, v___f_2674_);
v___x_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2683_, 0, v_fst_2675_);
v___x_2684_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2676_, v_inst_2677_, v_altType_2679_, v___x_2683_, v___f_2682_, v___x_2666_, v___x_2666_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39___boxed(lean_object** _args){
lean_object* v_inst_2685_ = _args[0];
lean_object* v_ys_2686_ = _args[1];
lean_object* v_ys2_2687_ = _args[2];
lean_object* v___x_2688_ = _args[3];
lean_object* v_useSplitter_2689_ = _args[4];
lean_object* v_inst_2690_ = _args[5];
lean_object* v_args_2691_ = _args[6];
lean_object* v_onAlt_2692_ = _args[7];
lean_object* v_next_2693_ = _args[8];
lean_object* v_toBind_2694_ = _args[9];
lean_object* v___x_2695_ = _args[10];
lean_object* v___f_2696_ = _args[11];
lean_object* v_fst_2697_ = _args[12];
lean_object* v_inst_2698_ = _args[13];
lean_object* v_inst_2699_ = _args[14];
lean_object* v_ys3_2700_ = _args[15];
lean_object* v_altType_2701_ = _args[16];
_start:
{
uint8_t v___x_15561__boxed_2702_; uint8_t v_useSplitter_boxed_2703_; lean_object* v_res_2704_; 
v___x_15561__boxed_2702_ = lean_unbox(v___x_2688_);
v_useSplitter_boxed_2703_ = lean_unbox(v_useSplitter_2689_);
v_res_2704_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__39(v_inst_2685_, v_ys_2686_, v_ys2_2687_, v___x_15561__boxed_2702_, v_useSplitter_boxed_2703_, v_inst_2690_, v_args_2691_, v_onAlt_2692_, v_next_2693_, v_toBind_2694_, v___x_2695_, v___f_2696_, v_fst_2697_, v_inst_2698_, v_inst_2699_, v_ys3_2700_, v_altType_2701_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40(lean_object* v_inst_2705_, lean_object* v_ys_2706_, uint8_t v___x_2707_, uint8_t v_useSplitter_2708_, lean_object* v_inst_2709_, lean_object* v_args_2710_, lean_object* v_onAlt_2711_, lean_object* v_next_2712_, lean_object* v_toBind_2713_, lean_object* v___x_2714_, lean_object* v___f_2715_, lean_object* v_fst_2716_, lean_object* v_inst_2717_, lean_object* v_inst_2718_, lean_object* v_numDiscrEqs_2719_, lean_object* v_ys2_2720_, lean_object* v_altType_2721_){
_start:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___f_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2722_ = lean_box(v___x_2707_);
v___x_2723_ = lean_box(v_useSplitter_2708_);
lean_inc_ref(v_inst_2718_);
lean_inc_ref(v_inst_2717_);
v___f_2724_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__39___boxed), 17, 15);
lean_closure_set(v___f_2724_, 0, v_inst_2705_);
lean_closure_set(v___f_2724_, 1, v_ys_2706_);
lean_closure_set(v___f_2724_, 2, v_ys2_2720_);
lean_closure_set(v___f_2724_, 3, v___x_2722_);
lean_closure_set(v___f_2724_, 4, v___x_2723_);
lean_closure_set(v___f_2724_, 5, v_inst_2709_);
lean_closure_set(v___f_2724_, 6, v_args_2710_);
lean_closure_set(v___f_2724_, 7, v_onAlt_2711_);
lean_closure_set(v___f_2724_, 8, v_next_2712_);
lean_closure_set(v___f_2724_, 9, v_toBind_2713_);
lean_closure_set(v___f_2724_, 10, v___x_2714_);
lean_closure_set(v___f_2724_, 11, v___f_2715_);
lean_closure_set(v___f_2724_, 12, v_fst_2716_);
lean_closure_set(v___f_2724_, 13, v_inst_2717_);
lean_closure_set(v___f_2724_, 14, v_inst_2718_);
v___x_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2725_, 0, v_numDiscrEqs_2719_);
v___x_2726_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2717_, v_inst_2718_, v_altType_2721_, v___x_2725_, v___f_2724_, v___x_2707_, v___x_2707_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed(lean_object** _args){
lean_object* v_inst_2727_ = _args[0];
lean_object* v_ys_2728_ = _args[1];
lean_object* v___x_2729_ = _args[2];
lean_object* v_useSplitter_2730_ = _args[3];
lean_object* v_inst_2731_ = _args[4];
lean_object* v_args_2732_ = _args[5];
lean_object* v_onAlt_2733_ = _args[6];
lean_object* v_next_2734_ = _args[7];
lean_object* v_toBind_2735_ = _args[8];
lean_object* v___x_2736_ = _args[9];
lean_object* v___f_2737_ = _args[10];
lean_object* v_fst_2738_ = _args[11];
lean_object* v_inst_2739_ = _args[12];
lean_object* v_inst_2740_ = _args[13];
lean_object* v_numDiscrEqs_2741_ = _args[14];
lean_object* v_ys2_2742_ = _args[15];
lean_object* v_altType_2743_ = _args[16];
_start:
{
uint8_t v___x_15592__boxed_2744_; uint8_t v_useSplitter_boxed_2745_; lean_object* v_res_2746_; 
v___x_15592__boxed_2744_ = lean_unbox(v___x_2729_);
v_useSplitter_boxed_2745_ = lean_unbox(v_useSplitter_2730_);
v_res_2746_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__40(v_inst_2727_, v_ys_2728_, v___x_15592__boxed_2744_, v_useSplitter_boxed_2745_, v_inst_2731_, v_args_2732_, v_onAlt_2733_, v_next_2734_, v_toBind_2735_, v___x_2736_, v___f_2737_, v_fst_2738_, v_inst_2739_, v_inst_2740_, v_numDiscrEqs_2741_, v_ys2_2742_, v_altType_2743_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41(lean_object* v___x_2747_, lean_object* v_inst_2748_, lean_object* v_inst_2749_, lean_object* v___f_2750_, uint8_t v___x_2751_, lean_object* v_toBind_2752_, lean_object* v___f_2753_, lean_object* v_altType_2754_){
_start:
{
lean_object* v_numOverlaps_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v_numOverlaps_2755_ = lean_ctor_get(v___x_2747_, 1);
lean_inc(v_numOverlaps_2755_);
v___x_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2756_, 0, v_numOverlaps_2755_);
v___x_2757_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2748_, v_inst_2749_, v_altType_2754_, v___x_2756_, v___f_2750_, v___x_2751_, v___x_2751_);
v___x_2758_ = lean_apply_4(v_toBind_2752_, lean_box(0), lean_box(0), v___x_2757_, v___f_2753_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed(lean_object* v___x_2759_, lean_object* v_inst_2760_, lean_object* v_inst_2761_, lean_object* v___f_2762_, lean_object* v___x_2763_, lean_object* v_toBind_2764_, lean_object* v___f_2765_, lean_object* v_altType_2766_){
_start:
{
uint8_t v___x_15626__boxed_2767_; lean_object* v_res_2768_; 
v___x_15626__boxed_2767_ = lean_unbox(v___x_2763_);
v_res_2768_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__41(v___x_2759_, v_inst_2760_, v_inst_2761_, v___f_2762_, v___x_15626__boxed_2767_, v_toBind_2764_, v___f_2765_, v_altType_2766_);
lean_dec_ref(v___x_2759_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__42(lean_object* v___f_2769_, lean_object* v_altType_2770_){
_start:
{
lean_object* v___x_2771_; 
v___x_2771_ = lean_apply_1(v___f_2769_, v_altType_2770_);
return v___x_2771_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2(void){
_start:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2776_ = lean_box(0);
v___x_2777_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__1));
v___x_2778_ = l_Lean_mkConst(v___x_2777_, v___x_2776_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44(uint8_t v_hasUnitThunk_2779_, lean_object* v_toPure_2780_, lean_object* v_toBind_2781_, lean_object* v___f_2782_, lean_object* v___x_2783_, lean_object* v_inst_2784_, lean_object* v___f_2785_, lean_object* v_altType_2786_){
_start:
{
if (v_hasUnitThunk_2779_ == 0)
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
lean_dec(v___f_2785_);
lean_dec(v_inst_2784_);
v___x_2787_ = lean_apply_2(v_toPure_2780_, lean_box(0), v_altType_2786_);
v___x_2788_ = lean_apply_4(v_toBind_2781_, lean_box(0), lean_box(0), v___x_2787_, v___f_2782_);
return v___x_2788_;
}
else
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
lean_dec(v___f_2782_);
lean_dec(v_toPure_2780_);
v___x_2789_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2);
v___x_2790_ = lean_mk_empty_array_with_capacity(v___x_2783_);
v___x_2791_ = lean_array_push(v___x_2790_, v___x_2789_);
v___x_2792_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateForall___boxed), 7, 2);
lean_closure_set(v___x_2792_, 0, v_altType_2786_);
lean_closure_set(v___x_2792_, 1, v___x_2791_);
v___x_2793_ = lean_apply_2(v_inst_2784_, lean_box(0), v___x_2792_);
v___x_2794_ = lean_apply_4(v_toBind_2781_, lean_box(0), lean_box(0), v___x_2793_, v___f_2785_);
return v___x_2794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed(lean_object* v_hasUnitThunk_2795_, lean_object* v_toPure_2796_, lean_object* v_toBind_2797_, lean_object* v___f_2798_, lean_object* v___x_2799_, lean_object* v_inst_2800_, lean_object* v___f_2801_, lean_object* v_altType_2802_){
_start:
{
uint8_t v_hasUnitThunk_boxed_2803_; lean_object* v_res_2804_; 
v_hasUnitThunk_boxed_2803_ = lean_unbox(v_hasUnitThunk_2795_);
v_res_2804_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__44(v_hasUnitThunk_boxed_2803_, v_toPure_2796_, v_toBind_2797_, v___f_2798_, v___x_2799_, v_inst_2800_, v___f_2801_, v_altType_2802_);
lean_dec(v___x_2799_);
return v_res_2804_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3(void){
_start:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2808_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__2));
v___x_2809_ = lean_unsigned_to_nat(8u);
v___x_2810_ = lean_unsigned_to_nat(360u);
v___x_2811_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__1));
v___x_2812_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__0));
v___x_2813_ = l_mkPanicMessageWithDecl(v___x_2812_, v___x_2811_, v___x_2810_, v___x_2809_, v___x_2808_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43(lean_object* v___x_2814_, lean_object* v_inst_2815_, lean_object* v_inst_2816_, uint8_t v___x_2817_, uint8_t v_useSplitter_2818_, lean_object* v_inst_2819_, lean_object* v_onAlt_2820_, lean_object* v_next_2821_, lean_object* v_toBind_2822_, lean_object* v___x_2823_, lean_object* v___f_2824_, lean_object* v_fst_2825_, lean_object* v_inst_2826_, lean_object* v_numDiscrEqs_2827_, lean_object* v___f_2828_, uint8_t v_hasUnitThunk_2829_, lean_object* v_toPure_2830_, lean_object* v___x_2831_, lean_object* v___x_2832_, lean_object* v_ys_2833_, lean_object* v_args_2834_){
_start:
{
lean_object* v_numFields_2835_; lean_object* v___x_2836_; uint8_t v___x_2837_; 
v_numFields_2835_ = lean_ctor_get(v___x_2814_, 0);
v___x_2836_ = lean_array_get_size(v_ys_2833_);
v___x_2837_ = lean_nat_dec_eq(v___x_2836_, v_numFields_2835_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
lean_dec_ref(v_args_2834_);
lean_dec_ref(v_ys_2833_);
lean_dec_ref(v___x_2832_);
lean_dec(v___x_2831_);
lean_dec(v_toPure_2830_);
lean_dec(v___f_2828_);
lean_dec(v_numDiscrEqs_2827_);
lean_dec_ref(v_inst_2826_);
lean_dec(v_fst_2825_);
lean_dec(v___f_2824_);
lean_dec_ref(v___x_2823_);
lean_dec(v_toBind_2822_);
lean_dec(v_next_2821_);
lean_dec(v_onAlt_2820_);
lean_dec(v_inst_2819_);
lean_dec_ref(v_inst_2816_);
lean_dec_ref(v___x_2814_);
v___x_2838_ = l_Lean_instInhabitedExpr;
v___x_2839_ = l_instInhabitedOfMonad___redArg(v_inst_2815_, v___x_2838_);
v___x_2840_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3);
v___x_2841_ = l_panic___redArg(v___x_2839_, v___x_2840_);
return v___x_2841_;
}
else
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___f_2844_; lean_object* v___x_2845_; lean_object* v___f_2846_; lean_object* v___f_2847_; lean_object* v___x_2848_; lean_object* v___f_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2842_ = lean_box(v___x_2817_);
v___x_2843_ = lean_box(v_useSplitter_2818_);
lean_inc_ref(v_inst_2815_);
lean_inc_ref(v_inst_2826_);
lean_inc(v_toBind_2822_);
lean_inc(v_inst_2819_);
lean_inc_ref(v_ys_2833_);
v___f_2844_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed), 17, 15);
lean_closure_set(v___f_2844_, 0, v_inst_2816_);
lean_closure_set(v___f_2844_, 1, v_ys_2833_);
lean_closure_set(v___f_2844_, 2, v___x_2842_);
lean_closure_set(v___f_2844_, 3, v___x_2843_);
lean_closure_set(v___f_2844_, 4, v_inst_2819_);
lean_closure_set(v___f_2844_, 5, v_args_2834_);
lean_closure_set(v___f_2844_, 6, v_onAlt_2820_);
lean_closure_set(v___f_2844_, 7, v_next_2821_);
lean_closure_set(v___f_2844_, 8, v_toBind_2822_);
lean_closure_set(v___f_2844_, 9, v___x_2823_);
lean_closure_set(v___f_2844_, 10, v___f_2824_);
lean_closure_set(v___f_2844_, 11, v_fst_2825_);
lean_closure_set(v___f_2844_, 12, v_inst_2826_);
lean_closure_set(v___f_2844_, 13, v_inst_2815_);
lean_closure_set(v___f_2844_, 14, v_numDiscrEqs_2827_);
v___x_2845_ = lean_box(v___x_2817_);
lean_inc(v_toBind_2822_);
v___f_2846_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed), 8, 7);
lean_closure_set(v___f_2846_, 0, v___x_2814_);
lean_closure_set(v___f_2846_, 1, v_inst_2826_);
lean_closure_set(v___f_2846_, 2, v_inst_2815_);
lean_closure_set(v___f_2846_, 3, v___f_2844_);
lean_closure_set(v___f_2846_, 4, v___x_2845_);
lean_closure_set(v___f_2846_, 5, v_toBind_2822_);
lean_closure_set(v___f_2846_, 6, v___f_2828_);
v___f_2847_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__42), 2, 1);
lean_closure_set(v___f_2847_, 0, v___f_2846_);
v___x_2848_ = lean_box(v_hasUnitThunk_2829_);
lean_inc(v_inst_2819_);
lean_inc_ref(v___f_2847_);
lean_inc(v_toBind_2822_);
v___f_2849_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed), 8, 7);
lean_closure_set(v___f_2849_, 0, v___x_2848_);
lean_closure_set(v___f_2849_, 1, v_toPure_2830_);
lean_closure_set(v___f_2849_, 2, v_toBind_2822_);
lean_closure_set(v___f_2849_, 3, v___f_2847_);
lean_closure_set(v___f_2849_, 4, v___x_2831_);
lean_closure_set(v___f_2849_, 5, v_inst_2819_);
lean_closure_set(v___f_2849_, 6, v___f_2847_);
v___x_2850_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateForall___boxed), 7, 2);
lean_closure_set(v___x_2850_, 0, v___x_2832_);
lean_closure_set(v___x_2850_, 1, v_ys_2833_);
v___x_2851_ = lean_apply_2(v_inst_2819_, lean_box(0), v___x_2850_);
v___x_2852_ = lean_apply_4(v_toBind_2822_, lean_box(0), lean_box(0), v___x_2851_, v___f_2849_);
return v___x_2852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed(lean_object** _args){
lean_object* v___x_2853_ = _args[0];
lean_object* v_inst_2854_ = _args[1];
lean_object* v_inst_2855_ = _args[2];
lean_object* v___x_2856_ = _args[3];
lean_object* v_useSplitter_2857_ = _args[4];
lean_object* v_inst_2858_ = _args[5];
lean_object* v_onAlt_2859_ = _args[6];
lean_object* v_next_2860_ = _args[7];
lean_object* v_toBind_2861_ = _args[8];
lean_object* v___x_2862_ = _args[9];
lean_object* v___f_2863_ = _args[10];
lean_object* v_fst_2864_ = _args[11];
lean_object* v_inst_2865_ = _args[12];
lean_object* v_numDiscrEqs_2866_ = _args[13];
lean_object* v___f_2867_ = _args[14];
lean_object* v_hasUnitThunk_2868_ = _args[15];
lean_object* v_toPure_2869_ = _args[16];
lean_object* v___x_2870_ = _args[17];
lean_object* v___x_2871_ = _args[18];
lean_object* v_ys_2872_ = _args[19];
lean_object* v_args_2873_ = _args[20];
_start:
{
uint8_t v___x_15721__boxed_2874_; uint8_t v_useSplitter_boxed_2875_; uint8_t v_hasUnitThunk_boxed_2876_; lean_object* v_res_2877_; 
v___x_15721__boxed_2874_ = lean_unbox(v___x_2856_);
v_useSplitter_boxed_2875_ = lean_unbox(v_useSplitter_2857_);
v_hasUnitThunk_boxed_2876_ = lean_unbox(v_hasUnitThunk_2868_);
v_res_2877_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__43(v___x_2853_, v_inst_2854_, v_inst_2855_, v___x_15721__boxed_2874_, v_useSplitter_boxed_2875_, v_inst_2858_, v_onAlt_2859_, v_next_2860_, v_toBind_2861_, v___x_2862_, v___f_2863_, v_fst_2864_, v_inst_2865_, v_numDiscrEqs_2866_, v___f_2867_, v_hasUnitThunk_boxed_2876_, v_toPure_2869_, v___x_2870_, v___x_2871_, v_ys_2872_, v_args_2873_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45(lean_object* v_fst_2878_, lean_object* v___x_2879_, lean_object* v___x_2880_, lean_object* v___x_2881_, lean_object* v___x_2882_, lean_object* v___x_2883_, lean_object* v_toPure_2884_, lean_object* v_alt_x27_2885_){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2886_ = lean_array_push(v_fst_2878_, v_alt_x27_2885_);
v___x_2887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2879_);
lean_ctor_set(v___x_2887_, 1, v___x_2880_);
v___x_2888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2881_);
lean_ctor_set(v___x_2888_, 1, v___x_2887_);
v___x_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2882_);
lean_ctor_set(v___x_2889_, 1, v___x_2888_);
v___x_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2883_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
v___x_2891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2886_);
lean_ctor_set(v___x_2891_, 1, v___x_2890_);
v___x_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
v___x_2893_ = lean_apply_2(v_toPure_2884_, lean_box(0), v___x_2892_);
return v___x_2893_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0(void){
_start:
{
lean_object* v___x_2894_; 
v___x_2894_ = l_Array_instInhabited(lean_box(0));
return v___x_2894_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1(void){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = l_Subarray_empty(lean_box(0));
return v___x_2895_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2(void){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2896_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
lean_ctor_set(v___x_2897_, 1, v___x_2896_);
return v___x_2897_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__3(void){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2898_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2);
v___x_2899_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_2900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2899_);
lean_ctor_set(v___x_2900_, 1, v___x_2898_);
return v___x_2900_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__4(void){
_start:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2901_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__3);
v___x_2902_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_2903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2902_);
lean_ctor_set(v___x_2903_, 1, v___x_2901_);
return v___x_2903_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__5(void){
_start:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2904_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__4, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__4_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__4);
v___x_2905_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_2906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2905_);
lean_ctor_set(v___x_2906_, 1, v___x_2904_);
return v___x_2906_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__6(void){
_start:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2907_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__5);
v___x_2908_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0);
v___x_2909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2908_);
lean_ctor_set(v___x_2909_, 1, v___x_2907_);
return v___x_2909_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7(void){
_start:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2910_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__6);
v___x_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2910_);
return v___x_2911_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9(void){
_start:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2913_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__8));
v___x_2914_ = lean_unsigned_to_nat(6u);
v___x_2915_ = lean_unsigned_to_nat(358u);
v___x_2916_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__1));
v___x_2917_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__0));
v___x_2918_ = l_mkPanicMessageWithDecl(v___x_2917_, v___x_2916_, v___x_2915_, v___x_2914_, v___x_2913_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46(lean_object* v___x_2919_, lean_object* v_toPure_2920_, lean_object* v_toBind_2921_, lean_object* v___f_2922_, lean_object* v___x_2923_, lean_object* v_inst_2924_, lean_object* v_inst_2925_, lean_object* v_inst_2926_, uint8_t v___x_2927_, uint8_t v_useSplitter_2928_, lean_object* v_onAlt_2929_, lean_object* v___f_2930_, lean_object* v_fst_2931_, lean_object* v_inst_2932_, lean_object* v_numDiscrEqs_2933_, lean_object* v_next_2934_, lean_object* v_acc_2935_, lean_object* v_h_2936_, lean_object* v_G_2937_){
_start:
{
uint8_t v___x_2938_; 
v___x_2938_ = lean_nat_dec_lt(v_next_2934_, v___x_2919_);
if (v___x_2938_ == 0)
{
lean_object* v___x_2939_; 
lean_dec(v_G_2937_);
lean_dec(v_next_2934_);
lean_dec(v_numDiscrEqs_2933_);
lean_dec_ref(v_inst_2932_);
lean_dec(v_fst_2931_);
lean_dec(v___f_2930_);
lean_dec(v_onAlt_2929_);
lean_dec_ref(v_inst_2926_);
lean_dec(v_inst_2925_);
lean_dec_ref(v_inst_2924_);
lean_dec(v___f_2922_);
lean_dec(v_toBind_2921_);
v___x_2939_ = lean_apply_2(v_toPure_2920_, lean_box(0), v_acc_2935_);
return v___x_2939_;
}
else
{
lean_object* v_snd_2940_; lean_object* v_snd_2941_; lean_object* v_snd_2942_; lean_object* v_snd_2943_; lean_object* v_snd_2944_; lean_object* v_fst_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_3159_; 
v_snd_2940_ = lean_ctor_get(v_acc_2935_, 1);
lean_inc(v_snd_2940_);
v_snd_2941_ = lean_ctor_get(v_snd_2940_, 1);
lean_inc(v_snd_2941_);
v_snd_2942_ = lean_ctor_get(v_snd_2941_, 1);
lean_inc(v_snd_2942_);
v_snd_2943_ = lean_ctor_get(v_snd_2942_, 1);
lean_inc(v_snd_2943_);
v_snd_2944_ = lean_ctor_get(v_snd_2943_, 1);
lean_inc(v_snd_2944_);
v_fst_2945_ = lean_ctor_get(v_acc_2935_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v_acc_2935_);
if (v_isSharedCheck_3159_ == 0)
{
lean_object* v_unused_3160_; 
v_unused_3160_ = lean_ctor_get(v_acc_2935_, 1);
lean_dec(v_unused_3160_);
v___x_2947_ = v_acc_2935_;
v_isShared_2948_ = v_isSharedCheck_3159_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_fst_2945_);
lean_dec(v_acc_2935_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_3159_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v_fst_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_3157_; 
v_fst_2949_ = lean_ctor_get(v_snd_2940_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v_snd_2940_);
if (v_isSharedCheck_3157_ == 0)
{
lean_object* v_unused_3158_; 
v_unused_3158_ = lean_ctor_get(v_snd_2940_, 1);
lean_dec(v_unused_3158_);
v___x_2951_ = v_snd_2940_;
v_isShared_2952_ = v_isSharedCheck_3157_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_fst_2949_);
lean_dec(v_snd_2940_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_3157_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v_fst_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_3155_; 
v_fst_2953_ = lean_ctor_get(v_snd_2941_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v_snd_2941_);
if (v_isSharedCheck_3155_ == 0)
{
lean_object* v_unused_3156_; 
v_unused_3156_ = lean_ctor_get(v_snd_2941_, 1);
lean_dec(v_unused_3156_);
v___x_2955_ = v_snd_2941_;
v_isShared_2956_ = v_isSharedCheck_3155_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_fst_2953_);
lean_dec(v_snd_2941_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_3155_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v_fst_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_3153_; 
v_fst_2957_ = lean_ctor_get(v_snd_2942_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v_snd_2942_);
if (v_isSharedCheck_3153_ == 0)
{
lean_object* v_unused_3154_; 
v_unused_3154_ = lean_ctor_get(v_snd_2942_, 1);
lean_dec(v_unused_3154_);
v___x_2959_ = v_snd_2942_;
v_isShared_2960_ = v_isSharedCheck_3153_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_fst_2957_);
lean_dec(v_snd_2942_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_3153_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v_fst_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_3151_; 
v_fst_2961_ = lean_ctor_get(v_snd_2943_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v_snd_2943_);
if (v_isSharedCheck_3151_ == 0)
{
lean_object* v_unused_3152_; 
v_unused_3152_ = lean_ctor_get(v_snd_2943_, 1);
lean_dec(v_unused_3152_);
v___x_2963_ = v_snd_2943_;
v_isShared_2964_ = v_isSharedCheck_3151_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_fst_2961_);
lean_dec(v_snd_2943_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_3151_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v_array_2965_; lean_object* v_start_2966_; lean_object* v_stop_2967_; lean_object* v___f_2968_; lean_object* v___y_2970_; uint8_t v___x_2973_; 
v_array_2965_ = lean_ctor_get(v_snd_2944_, 0);
v_start_2966_ = lean_ctor_get(v_snd_2944_, 1);
v_stop_2967_ = lean_ctor_get(v_snd_2944_, 2);
lean_inc(v_next_2934_);
lean_inc(v_toPure_2920_);
v___f_2968_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed), 4, 3);
lean_closure_set(v___f_2968_, 0, v_toPure_2920_);
lean_closure_set(v___f_2968_, 1, v_next_2934_);
lean_closure_set(v___f_2968_, 2, v_G_2937_);
v___x_2973_ = lean_nat_dec_lt(v_start_2966_, v_stop_2967_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2975_; 
lean_dec(v_next_2934_);
lean_dec(v_numDiscrEqs_2933_);
lean_dec_ref(v_inst_2932_);
lean_dec(v_fst_2931_);
lean_dec(v___f_2930_);
lean_dec(v_onAlt_2929_);
lean_dec_ref(v_inst_2926_);
lean_dec(v_inst_2925_);
lean_dec_ref(v_inst_2924_);
if (v_isShared_2964_ == 0)
{
v___x_2975_ = v___x_2963_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_fst_2961_);
lean_ctor_set(v_reuseFailAlloc_2990_, 1, v_snd_2944_);
v___x_2975_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
lean_object* v___x_2977_; 
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 1, v___x_2975_);
v___x_2977_ = v___x_2959_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_fst_2957_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v___x_2975_);
v___x_2977_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
lean_object* v___x_2979_; 
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 1, v___x_2977_);
v___x_2979_ = v___x_2955_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_fst_2953_);
lean_ctor_set(v_reuseFailAlloc_2988_, 1, v___x_2977_);
v___x_2979_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
lean_object* v___x_2981_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 1, v___x_2979_);
v___x_2981_ = v___x_2951_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_fst_2949_);
lean_ctor_set(v_reuseFailAlloc_2987_, 1, v___x_2979_);
v___x_2981_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
lean_object* v___x_2983_; 
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 1, v___x_2981_);
v___x_2983_ = v___x_2947_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_fst_2945_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v___x_2981_);
v___x_2983_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2983_);
v___x_2985_ = lean_apply_2(v_toPure_2920_, lean_box(0), v___x_2984_);
v___y_2970_ = v___x_2985_;
goto v___jp_2969_;
}
}
}
}
}
}
else
{
lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3147_; 
lean_inc(v_stop_2967_);
lean_inc(v_start_2966_);
lean_inc_ref(v_array_2965_);
v_isSharedCheck_3147_ = !lean_is_exclusive(v_snd_2944_);
if (v_isSharedCheck_3147_ == 0)
{
lean_object* v_unused_3148_; lean_object* v_unused_3149_; lean_object* v_unused_3150_; 
v_unused_3148_ = lean_ctor_get(v_snd_2944_, 2);
lean_dec(v_unused_3148_);
v_unused_3149_ = lean_ctor_get(v_snd_2944_, 1);
lean_dec(v_unused_3149_);
v_unused_3150_ = lean_ctor_get(v_snd_2944_, 0);
lean_dec(v_unused_3150_);
v___x_2992_ = v_snd_2944_;
v_isShared_2993_ = v_isSharedCheck_3147_;
goto v_resetjp_2991_;
}
else
{
lean_dec(v_snd_2944_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3147_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v_array_2994_; lean_object* v_start_2995_; lean_object* v_stop_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3001_; 
v_array_2994_ = lean_ctor_get(v_fst_2961_, 0);
v_start_2995_ = lean_ctor_get(v_fst_2961_, 1);
v_stop_2996_ = lean_ctor_get(v_fst_2961_, 2);
v___x_2997_ = lean_array_fget(v_array_2965_, v_start_2966_);
v___x_2998_ = lean_unsigned_to_nat(1u);
v___x_2999_ = lean_nat_add(v_start_2966_, v___x_2998_);
lean_dec(v_start_2966_);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 1, v___x_2999_);
v___x_3001_ = v___x_2992_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_array_2965_);
lean_ctor_set(v_reuseFailAlloc_3146_, 1, v___x_2999_);
lean_ctor_set(v_reuseFailAlloc_3146_, 2, v_stop_2967_);
v___x_3001_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
uint8_t v___x_3002_; 
v___x_3002_ = lean_nat_dec_lt(v_start_2995_, v_stop_2996_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3004_; 
lean_dec(v___x_2997_);
lean_dec(v_next_2934_);
lean_dec(v_numDiscrEqs_2933_);
lean_dec_ref(v_inst_2932_);
lean_dec(v_fst_2931_);
lean_dec(v___f_2930_);
lean_dec(v_onAlt_2929_);
lean_dec_ref(v_inst_2926_);
lean_dec(v_inst_2925_);
lean_dec_ref(v_inst_2924_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 1, v___x_3001_);
v___x_3004_ = v___x_2963_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_fst_2961_);
lean_ctor_set(v_reuseFailAlloc_3019_, 1, v___x_3001_);
v___x_3004_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
lean_object* v___x_3006_; 
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 1, v___x_3004_);
v___x_3006_ = v___x_2959_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_fst_2957_);
lean_ctor_set(v_reuseFailAlloc_3018_, 1, v___x_3004_);
v___x_3006_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
lean_object* v___x_3008_; 
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 1, v___x_3006_);
v___x_3008_ = v___x_2955_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_fst_2953_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v___x_3006_);
v___x_3008_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
lean_object* v___x_3010_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 1, v___x_3008_);
v___x_3010_ = v___x_2951_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_fst_2949_);
lean_ctor_set(v_reuseFailAlloc_3016_, 1, v___x_3008_);
v___x_3010_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
lean_object* v___x_3012_; 
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 1, v___x_3010_);
v___x_3012_ = v___x_2947_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_fst_2945_);
lean_ctor_set(v_reuseFailAlloc_3015_, 1, v___x_3010_);
v___x_3012_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3012_);
v___x_3014_ = lean_apply_2(v_toPure_2920_, lean_box(0), v___x_3013_);
v___y_2970_ = v___x_3014_;
goto v___jp_2969_;
}
}
}
}
}
}
else
{
lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3142_; 
lean_inc(v_stop_2996_);
lean_inc(v_start_2995_);
lean_inc_ref(v_array_2994_);
v_isSharedCheck_3142_ = !lean_is_exclusive(v_fst_2961_);
if (v_isSharedCheck_3142_ == 0)
{
lean_object* v_unused_3143_; lean_object* v_unused_3144_; lean_object* v_unused_3145_; 
v_unused_3143_ = lean_ctor_get(v_fst_2961_, 2);
lean_dec(v_unused_3143_);
v_unused_3144_ = lean_ctor_get(v_fst_2961_, 1);
lean_dec(v_unused_3144_);
v_unused_3145_ = lean_ctor_get(v_fst_2961_, 0);
lean_dec(v_unused_3145_);
v___x_3021_ = v_fst_2961_;
v_isShared_3022_ = v_isSharedCheck_3142_;
goto v_resetjp_3020_;
}
else
{
lean_dec(v_fst_2961_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3142_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v_array_3023_; lean_object* v_start_3024_; lean_object* v_stop_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3029_; 
v_array_3023_ = lean_ctor_get(v_fst_2957_, 0);
v_start_3024_ = lean_ctor_get(v_fst_2957_, 1);
v_stop_3025_ = lean_ctor_get(v_fst_2957_, 2);
v___x_3026_ = lean_array_fget(v_array_2994_, v_start_2995_);
v___x_3027_ = lean_nat_add(v_start_2995_, v___x_2998_);
lean_dec(v_start_2995_);
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 1, v___x_3027_);
v___x_3029_ = v___x_3021_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_array_2994_);
lean_ctor_set(v_reuseFailAlloc_3141_, 1, v___x_3027_);
lean_ctor_set(v_reuseFailAlloc_3141_, 2, v_stop_2996_);
v___x_3029_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
uint8_t v___x_3030_; 
v___x_3030_ = lean_nat_dec_lt(v_start_3024_, v_stop_3025_);
if (v___x_3030_ == 0)
{
lean_object* v___x_3032_; 
lean_dec(v___x_3026_);
lean_dec(v___x_2997_);
lean_dec(v_next_2934_);
lean_dec(v_numDiscrEqs_2933_);
lean_dec_ref(v_inst_2932_);
lean_dec(v_fst_2931_);
lean_dec(v___f_2930_);
lean_dec(v_onAlt_2929_);
lean_dec_ref(v_inst_2926_);
lean_dec(v_inst_2925_);
lean_dec_ref(v_inst_2924_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 1, v___x_3001_);
lean_ctor_set(v___x_2963_, 0, v___x_3029_);
v___x_3032_ = v___x_2963_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3029_);
lean_ctor_set(v_reuseFailAlloc_3047_, 1, v___x_3001_);
v___x_3032_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
lean_object* v___x_3034_; 
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 1, v___x_3032_);
v___x_3034_ = v___x_2959_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_fst_2957_);
lean_ctor_set(v_reuseFailAlloc_3046_, 1, v___x_3032_);
v___x_3034_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
lean_object* v___x_3036_; 
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 1, v___x_3034_);
v___x_3036_ = v___x_2955_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_fst_2953_);
lean_ctor_set(v_reuseFailAlloc_3045_, 1, v___x_3034_);
v___x_3036_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
lean_object* v___x_3038_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 1, v___x_3036_);
v___x_3038_ = v___x_2951_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_fst_2949_);
lean_ctor_set(v_reuseFailAlloc_3044_, 1, v___x_3036_);
v___x_3038_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
lean_object* v___x_3040_; 
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 1, v___x_3038_);
v___x_3040_ = v___x_2947_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_fst_2945_);
lean_ctor_set(v_reuseFailAlloc_3043_, 1, v___x_3038_);
v___x_3040_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3040_);
v___x_3042_ = lean_apply_2(v_toPure_2920_, lean_box(0), v___x_3041_);
v___y_2970_ = v___x_3042_;
goto v___jp_2969_;
}
}
}
}
}
}
else
{
lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3137_; 
lean_inc(v_stop_3025_);
lean_inc(v_start_3024_);
lean_inc_ref(v_array_3023_);
v_isSharedCheck_3137_ = !lean_is_exclusive(v_fst_2957_);
if (v_isSharedCheck_3137_ == 0)
{
lean_object* v_unused_3138_; lean_object* v_unused_3139_; lean_object* v_unused_3140_; 
v_unused_3138_ = lean_ctor_get(v_fst_2957_, 2);
lean_dec(v_unused_3138_);
v_unused_3139_ = lean_ctor_get(v_fst_2957_, 1);
lean_dec(v_unused_3139_);
v_unused_3140_ = lean_ctor_get(v_fst_2957_, 0);
lean_dec(v_unused_3140_);
v___x_3049_ = v_fst_2957_;
v_isShared_3050_ = v_isSharedCheck_3137_;
goto v_resetjp_3048_;
}
else
{
lean_dec(v_fst_2957_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3137_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v_array_3051_; lean_object* v_start_3052_; lean_object* v_stop_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3057_; 
v_array_3051_ = lean_ctor_get(v_fst_2953_, 0);
v_start_3052_ = lean_ctor_get(v_fst_2953_, 1);
v_stop_3053_ = lean_ctor_get(v_fst_2953_, 2);
v___x_3054_ = lean_array_fget(v_array_3023_, v_start_3024_);
v___x_3055_ = lean_nat_add(v_start_3024_, v___x_2998_);
lean_dec(v_start_3024_);
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 1, v___x_3055_);
v___x_3057_ = v___x_3049_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_array_3023_);
lean_ctor_set(v_reuseFailAlloc_3136_, 1, v___x_3055_);
lean_ctor_set(v_reuseFailAlloc_3136_, 2, v_stop_3025_);
v___x_3057_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
uint8_t v___x_3058_; 
v___x_3058_ = lean_nat_dec_lt(v_start_3052_, v_stop_3053_);
if (v___x_3058_ == 0)
{
lean_object* v___x_3060_; 
lean_dec(v___x_3054_);
lean_dec(v___x_3026_);
lean_dec(v___x_2997_);
lean_dec(v_next_2934_);
lean_dec(v_numDiscrEqs_2933_);
lean_dec_ref(v_inst_2932_);
lean_dec(v_fst_2931_);
lean_dec(v___f_2930_);
lean_dec(v_onAlt_2929_);
lean_dec_ref(v_inst_2926_);
lean_dec(v_inst_2925_);
lean_dec_ref(v_inst_2924_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 1, v___x_3001_);
lean_ctor_set(v___x_2963_, 0, v___x_3029_);
v___x_3060_ = v___x_2963_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3029_);
lean_ctor_set(v_reuseFailAlloc_3075_, 1, v___x_3001_);
v___x_3060_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
lean_object* v___x_3062_; 
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 1, v___x_3060_);
lean_ctor_set(v___x_2959_, 0, v___x_3057_);
v___x_3062_ = v___x_2959_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3057_);
lean_ctor_set(v_reuseFailAlloc_3074_, 1, v___x_3060_);
v___x_3062_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
lean_object* v___x_3064_; 
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 1, v___x_3062_);
v___x_3064_ = v___x_2955_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_fst_2953_);
lean_ctor_set(v_reuseFailAlloc_3073_, 1, v___x_3062_);
v___x_3064_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
lean_object* v___x_3066_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 1, v___x_3064_);
v___x_3066_ = v___x_2951_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_fst_2949_);
lean_ctor_set(v_reuseFailAlloc_3072_, 1, v___x_3064_);
v___x_3066_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
lean_object* v___x_3068_; 
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 1, v___x_3066_);
v___x_3068_ = v___x_2947_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_fst_2945_);
lean_ctor_set(v_reuseFailAlloc_3071_, 1, v___x_3066_);
v___x_3068_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3068_);
v___x_3070_ = lean_apply_2(v_toPure_2920_, lean_box(0), v___x_3069_);
v___y_2970_ = v___x_3070_;
goto v___jp_2969_;
}
}
}
}
}
}
else
{
lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3132_; 
lean_inc(v_stop_3053_);
lean_inc(v_start_3052_);
lean_inc_ref(v_array_3051_);
v_isSharedCheck_3132_ = !lean_is_exclusive(v_fst_2953_);
if (v_isSharedCheck_3132_ == 0)
{
lean_object* v_unused_3133_; lean_object* v_unused_3134_; lean_object* v_unused_3135_; 
v_unused_3133_ = lean_ctor_get(v_fst_2953_, 2);
lean_dec(v_unused_3133_);
v_unused_3134_ = lean_ctor_get(v_fst_2953_, 1);
lean_dec(v_unused_3134_);
v_unused_3135_ = lean_ctor_get(v_fst_2953_, 0);
lean_dec(v_unused_3135_);
v___x_3077_ = v_fst_2953_;
v_isShared_3078_ = v_isSharedCheck_3132_;
goto v_resetjp_3076_;
}
else
{
lean_dec(v_fst_2953_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3132_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v_array_3079_; lean_object* v_start_3080_; lean_object* v_stop_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3085_; 
v_array_3079_ = lean_ctor_get(v_fst_2949_, 0);
v_start_3080_ = lean_ctor_get(v_fst_2949_, 1);
v_stop_3081_ = lean_ctor_get(v_fst_2949_, 2);
v___x_3082_ = lean_array_fget(v_array_3051_, v_start_3052_);
v___x_3083_ = lean_nat_add(v_start_3052_, v___x_2998_);
lean_dec(v_start_3052_);
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 1, v___x_3083_);
v___x_3085_ = v___x_3077_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_array_3051_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v___x_3083_);
lean_ctor_set(v_reuseFailAlloc_3131_, 2, v_stop_3053_);
v___x_3085_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
uint8_t v___x_3086_; 
v___x_3086_ = lean_nat_dec_lt(v_start_3080_, v_stop_3081_);
if (v___x_3086_ == 0)
{
lean_object* v___x_3088_; 
lean_dec(v___x_3082_);
lean_dec(v___x_3054_);
lean_dec(v___x_3026_);
lean_dec(v___x_2997_);
lean_dec(v_next_2934_);
lean_dec(v_numDiscrEqs_2933_);
lean_dec_ref(v_inst_2932_);
lean_dec(v_fst_2931_);
lean_dec(v___f_2930_);
lean_dec(v_onAlt_2929_);
lean_dec_ref(v_inst_2926_);
lean_dec(v_inst_2925_);
lean_dec_ref(v_inst_2924_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 1, v___x_3001_);
lean_ctor_set(v___x_2963_, 0, v___x_3029_);
v___x_3088_ = v___x_2963_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v___x_3029_);
lean_ctor_set(v_reuseFailAlloc_3103_, 1, v___x_3001_);
v___x_3088_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
lean_object* v___x_3090_; 
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 1, v___x_3088_);
lean_ctor_set(v___x_2959_, 0, v___x_3057_);
v___x_3090_ = v___x_2959_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3057_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v___x_3088_);
v___x_3090_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
lean_object* v___x_3092_; 
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 1, v___x_3090_);
lean_ctor_set(v___x_2955_, 0, v___x_3085_);
v___x_3092_ = v___x_2955_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3085_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v___x_3090_);
v___x_3092_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
lean_object* v___x_3094_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 1, v___x_3092_);
v___x_3094_ = v___x_2951_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_fst_2949_);
lean_ctor_set(v_reuseFailAlloc_3100_, 1, v___x_3092_);
v___x_3094_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
lean_object* v___x_3096_; 
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 1, v___x_3094_);
v___x_3096_ = v___x_2947_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_fst_2945_);
lean_ctor_set(v_reuseFailAlloc_3099_, 1, v___x_3094_);
v___x_3096_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3096_);
v___x_3098_ = lean_apply_2(v_toPure_2920_, lean_box(0), v___x_3097_);
v___y_2970_ = v___x_3098_;
goto v___jp_2969_;
}
}
}
}
}
}
else
{
lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3127_; 
lean_inc(v_stop_3081_);
lean_inc(v_start_3080_);
lean_inc_ref(v_array_3079_);
lean_del_object(v___x_2963_);
lean_del_object(v___x_2959_);
lean_del_object(v___x_2955_);
lean_del_object(v___x_2951_);
lean_del_object(v___x_2947_);
v_isSharedCheck_3127_ = !lean_is_exclusive(v_fst_2949_);
if (v_isSharedCheck_3127_ == 0)
{
lean_object* v_unused_3128_; lean_object* v_unused_3129_; lean_object* v_unused_3130_; 
v_unused_3128_ = lean_ctor_get(v_fst_2949_, 2);
lean_dec(v_unused_3128_);
v_unused_3129_ = lean_ctor_get(v_fst_2949_, 1);
lean_dec(v_unused_3129_);
v_unused_3130_ = lean_ctor_get(v_fst_2949_, 0);
lean_dec(v_unused_3130_);
v___x_3105_ = v_fst_2949_;
v_isShared_3106_ = v_isSharedCheck_3127_;
goto v_resetjp_3104_;
}
else
{
lean_dec(v_fst_2949_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3127_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v_numOverlaps_3107_; uint8_t v_hasUnitThunk_3108_; uint8_t v___x_3109_; 
v_numOverlaps_3107_ = lean_ctor_get(v___x_3082_, 1);
v_hasUnitThunk_3108_ = lean_ctor_get_uint8(v___x_3082_, sizeof(void*)*2);
v___x_3109_ = lean_nat_dec_eq(v_numOverlaps_3107_, v___x_2923_);
if (v___x_3109_ == 0)
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
lean_del_object(v___x_3105_);
lean_dec_ref(v___x_3085_);
lean_dec(v___x_3082_);
lean_dec(v_stop_3081_);
lean_dec(v_start_3080_);
lean_dec_ref(v_array_3079_);
lean_dec_ref(v___x_3057_);
lean_dec(v___x_3054_);
lean_dec_ref(v___x_3029_);
lean_dec(v___x_3026_);
lean_dec_ref(v___x_3001_);
lean_dec(v___x_2997_);
lean_dec(v_fst_2945_);
lean_dec(v_next_2934_);
lean_dec(v_numDiscrEqs_2933_);
lean_dec_ref(v_inst_2932_);
lean_dec(v_fst_2931_);
lean_dec(v___f_2930_);
lean_dec(v_onAlt_2929_);
lean_dec_ref(v_inst_2926_);
lean_dec(v_inst_2925_);
lean_dec(v_toPure_2920_);
v___x_3110_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7);
v___x_3111_ = l_instInhabitedOfMonad___redArg(v_inst_2924_, v___x_3110_);
v___x_3112_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9);
v___x_3113_ = l_panic___redArg(v___x_3111_, v___x_3112_);
v___y_2970_ = v___x_3113_;
goto v___jp_2969_;
}
else
{
lean_object* v___f_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___f_3119_; lean_object* v___x_3120_; lean_object* v___x_3122_; 
lean_inc(v_inst_2925_);
lean_inc(v_toPure_2920_);
lean_inc(v___x_3054_);
v___f_3114_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed), 4, 3);
lean_closure_set(v___f_3114_, 0, v___x_3054_);
lean_closure_set(v___f_3114_, 1, v_toPure_2920_);
lean_closure_set(v___f_3114_, 2, v_inst_2925_);
v___x_3115_ = lean_array_fget_borrowed(v_array_3079_, v_start_3080_);
v___x_3116_ = lean_box(v___x_2927_);
v___x_3117_ = lean_box(v_useSplitter_2928_);
v___x_3118_ = lean_box(v_hasUnitThunk_3108_);
lean_inc(v_toPure_2920_);
lean_inc_ref(v_inst_2932_);
lean_inc(v___x_3115_);
lean_inc(v_toBind_2921_);
lean_inc_ref(v_inst_2924_);
v___f_3119_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed), 21, 19);
lean_closure_set(v___f_3119_, 0, v___x_3054_);
lean_closure_set(v___f_3119_, 1, v_inst_2924_);
lean_closure_set(v___f_3119_, 2, v_inst_2926_);
lean_closure_set(v___f_3119_, 3, v___x_3116_);
lean_closure_set(v___f_3119_, 4, v___x_3117_);
lean_closure_set(v___f_3119_, 5, v_inst_2925_);
lean_closure_set(v___f_3119_, 6, v_onAlt_2929_);
lean_closure_set(v___f_3119_, 7, v_next_2934_);
lean_closure_set(v___f_3119_, 8, v_toBind_2921_);
lean_closure_set(v___f_3119_, 9, v___x_3115_);
lean_closure_set(v___f_3119_, 10, v___f_2930_);
lean_closure_set(v___f_3119_, 11, v_fst_2931_);
lean_closure_set(v___f_3119_, 12, v_inst_2932_);
lean_closure_set(v___f_3119_, 13, v_numDiscrEqs_2933_);
lean_closure_set(v___f_3119_, 14, v___f_3114_);
lean_closure_set(v___f_3119_, 15, v___x_3118_);
lean_closure_set(v___f_3119_, 16, v_toPure_2920_);
lean_closure_set(v___f_3119_, 17, v___x_2998_);
lean_closure_set(v___f_3119_, 18, v___x_2997_);
v___x_3120_ = lean_nat_add(v_start_3080_, v___x_2998_);
lean_dec(v_start_3080_);
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 1, v___x_3120_);
v___x_3122_ = v___x_3105_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_array_3079_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v___x_3120_);
lean_ctor_set(v_reuseFailAlloc_3126_, 2, v_stop_3081_);
v___x_3122_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
lean_object* v___f_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___f_3123_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__45), 8, 7);
lean_closure_set(v___f_3123_, 0, v_fst_2945_);
lean_closure_set(v___f_3123_, 1, v___x_3029_);
lean_closure_set(v___f_3123_, 2, v___x_3001_);
lean_closure_set(v___f_3123_, 3, v___x_3057_);
lean_closure_set(v___f_3123_, 4, v___x_3085_);
lean_closure_set(v___f_3123_, 5, v___x_3122_);
lean_closure_set(v___f_3123_, 6, v_toPure_2920_);
v___x_3124_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(v_inst_2924_, v_inst_2932_, v___x_3026_, v___x_3082_, v___f_3119_);
lean_inc(v_toBind_2921_);
v___x_3125_ = lean_apply_4(v_toBind_2921_, lean_box(0), lean_box(0), v___x_3124_, v___f_3123_);
v___y_2970_ = v___x_3125_;
goto v___jp_2969_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_2969_:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; 
lean_inc(v_toBind_2921_);
v___x_2971_ = lean_apply_4(v_toBind_2921_, lean_box(0), lean_box(0), v___y_2970_, v___f_2922_);
v___x_2972_ = lean_apply_4(v_toBind_2921_, lean_box(0), lean_box(0), v___x_2971_, v___f_2968_);
return v___x_2972_;
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
lean_object* v___x_3161_ = _args[0];
lean_object* v_toPure_3162_ = _args[1];
lean_object* v_toBind_3163_ = _args[2];
lean_object* v___f_3164_ = _args[3];
lean_object* v___x_3165_ = _args[4];
lean_object* v_inst_3166_ = _args[5];
lean_object* v_inst_3167_ = _args[6];
lean_object* v_inst_3168_ = _args[7];
lean_object* v___x_3169_ = _args[8];
lean_object* v_useSplitter_3170_ = _args[9];
lean_object* v_onAlt_3171_ = _args[10];
lean_object* v___f_3172_ = _args[11];
lean_object* v_fst_3173_ = _args[12];
lean_object* v_inst_3174_ = _args[13];
lean_object* v_numDiscrEqs_3175_ = _args[14];
lean_object* v_next_3176_ = _args[15];
lean_object* v_acc_3177_ = _args[16];
lean_object* v_h_3178_ = _args[17];
lean_object* v_G_3179_ = _args[18];
_start:
{
uint8_t v___x_15880__boxed_3180_; uint8_t v_useSplitter_boxed_3181_; lean_object* v_res_3182_; 
v___x_15880__boxed_3180_ = lean_unbox(v___x_3169_);
v_useSplitter_boxed_3181_ = lean_unbox(v_useSplitter_3170_);
v_res_3182_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__46(v___x_3161_, v_toPure_3162_, v_toBind_3163_, v___f_3164_, v___x_3165_, v_inst_3166_, v_inst_3167_, v_inst_3168_, v___x_15880__boxed_3180_, v_useSplitter_boxed_3181_, v_onAlt_3171_, v___f_3172_, v_fst_3173_, v_inst_3174_, v_numDiscrEqs_3175_, v_next_3176_, v_acc_3177_, v_h_3178_, v_G_3179_);
lean_dec(v___x_3165_);
lean_dec(v___x_3161_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47(lean_object* v_fst_3183_, lean_object* v_numParams_3184_, lean_object* v_numDiscrs_3185_, lean_object* v_altInfos_3186_, lean_object* v_uElimPos_x3f_3187_, lean_object* v_snd_3188_, lean_object* v_overlaps_3189_, lean_object* v_splitterName_3190_, lean_object* v_matcherLevels_3191_, lean_object* v_params_x27_3192_, lean_object* v_fst_3193_, lean_object* v_discrs_x27_3194_, lean_object* v_fst_3195_, lean_object* v_toPure_3196_, lean_object* v_____do__lift_3197_){
_start:
{
lean_object* v_remaining_x27_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
v_remaining_x27_3198_ = l_Array_append___redArg(v_fst_3183_, v_____do__lift_3197_);
v___x_3199_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3199_, 0, v_numParams_3184_);
lean_ctor_set(v___x_3199_, 1, v_numDiscrs_3185_);
lean_ctor_set(v___x_3199_, 2, v_altInfos_3186_);
lean_ctor_set(v___x_3199_, 3, v_uElimPos_x3f_3187_);
lean_ctor_set(v___x_3199_, 4, v_snd_3188_);
lean_ctor_set(v___x_3199_, 5, v_overlaps_3189_);
v___x_3200_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3199_);
lean_ctor_set(v___x_3200_, 1, v_splitterName_3190_);
lean_ctor_set(v___x_3200_, 2, v_matcherLevels_3191_);
lean_ctor_set(v___x_3200_, 3, v_params_x27_3192_);
lean_ctor_set(v___x_3200_, 4, v_fst_3193_);
lean_ctor_set(v___x_3200_, 5, v_discrs_x27_3194_);
lean_ctor_set(v___x_3200_, 6, v_fst_3195_);
lean_ctor_set(v___x_3200_, 7, v_remaining_x27_3198_);
v___x_3201_ = lean_apply_2(v_toPure_3196_, lean_box(0), v___x_3200_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47___boxed(lean_object* v_fst_3202_, lean_object* v_numParams_3203_, lean_object* v_numDiscrs_3204_, lean_object* v_altInfos_3205_, lean_object* v_uElimPos_x3f_3206_, lean_object* v_snd_3207_, lean_object* v_overlaps_3208_, lean_object* v_splitterName_3209_, lean_object* v_matcherLevels_3210_, lean_object* v_params_x27_3211_, lean_object* v_fst_3212_, lean_object* v_discrs_x27_3213_, lean_object* v_fst_3214_, lean_object* v_toPure_3215_, lean_object* v_____do__lift_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__47(v_fst_3202_, v_numParams_3203_, v_numDiscrs_3204_, v_altInfos_3205_, v_uElimPos_x3f_3206_, v_snd_3207_, v_overlaps_3208_, v_splitterName_3209_, v_matcherLevels_3210_, v_params_x27_3211_, v_fst_3212_, v_discrs_x27_3213_, v_fst_3214_, v_toPure_3215_, v_____do__lift_3216_);
lean_dec_ref(v_____do__lift_3216_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48(lean_object* v_fst_3218_, lean_object* v_numParams_3219_, lean_object* v_numDiscrs_3220_, lean_object* v_altInfos_3221_, lean_object* v_uElimPos_x3f_3222_, lean_object* v_snd_3223_, lean_object* v_overlaps_3224_, lean_object* v_splitterName_3225_, lean_object* v_matcherLevels_3226_, lean_object* v_params_x27_3227_, lean_object* v_fst_3228_, lean_object* v_discrs_x27_3229_, lean_object* v_toPure_3230_, lean_object* v_onRemaining_3231_, lean_object* v_remaining_3232_, lean_object* v_toBind_3233_, lean_object* v_____s_3234_){
_start:
{
lean_object* v_fst_3235_; lean_object* v___f_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v_fst_3235_ = lean_ctor_get(v_____s_3234_, 0);
lean_inc(v_fst_3235_);
lean_dec_ref(v_____s_3234_);
v___f_3236_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__47___boxed), 15, 14);
lean_closure_set(v___f_3236_, 0, v_fst_3218_);
lean_closure_set(v___f_3236_, 1, v_numParams_3219_);
lean_closure_set(v___f_3236_, 2, v_numDiscrs_3220_);
lean_closure_set(v___f_3236_, 3, v_altInfos_3221_);
lean_closure_set(v___f_3236_, 4, v_uElimPos_x3f_3222_);
lean_closure_set(v___f_3236_, 5, v_snd_3223_);
lean_closure_set(v___f_3236_, 6, v_overlaps_3224_);
lean_closure_set(v___f_3236_, 7, v_splitterName_3225_);
lean_closure_set(v___f_3236_, 8, v_matcherLevels_3226_);
lean_closure_set(v___f_3236_, 9, v_params_x27_3227_);
lean_closure_set(v___f_3236_, 10, v_fst_3228_);
lean_closure_set(v___f_3236_, 11, v_discrs_x27_3229_);
lean_closure_set(v___f_3236_, 12, v_fst_3235_);
lean_closure_set(v___f_3236_, 13, v_toPure_3230_);
v___x_3237_ = lean_apply_1(v_onRemaining_3231_, v_remaining_3232_);
v___x_3238_ = lean_apply_4(v_toBind_3233_, lean_box(0), lean_box(0), v___x_3237_, v___f_3236_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed(lean_object** _args){
lean_object* v_fst_3239_ = _args[0];
lean_object* v_numParams_3240_ = _args[1];
lean_object* v_numDiscrs_3241_ = _args[2];
lean_object* v_altInfos_3242_ = _args[3];
lean_object* v_uElimPos_x3f_3243_ = _args[4];
lean_object* v_snd_3244_ = _args[5];
lean_object* v_overlaps_3245_ = _args[6];
lean_object* v_splitterName_3246_ = _args[7];
lean_object* v_matcherLevels_3247_ = _args[8];
lean_object* v_params_x27_3248_ = _args[9];
lean_object* v_fst_3249_ = _args[10];
lean_object* v_discrs_x27_3250_ = _args[11];
lean_object* v_toPure_3251_ = _args[12];
lean_object* v_onRemaining_3252_ = _args[13];
lean_object* v_remaining_3253_ = _args[14];
lean_object* v_toBind_3254_ = _args[15];
lean_object* v_____s_3255_ = _args[16];
_start:
{
lean_object* v_res_3256_; 
v_res_3256_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__48(v_fst_3239_, v_numParams_3240_, v_numDiscrs_3241_, v_altInfos_3242_, v_uElimPos_x3f_3243_, v_snd_3244_, v_overlaps_3245_, v_splitterName_3246_, v_matcherLevels_3247_, v_params_x27_3248_, v_fst_3249_, v_discrs_x27_3250_, v_toPure_3251_, v_onRemaining_3252_, v_remaining_3253_, v_toBind_3254_, v_____s_3255_);
return v_res_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49(lean_object* v_splitterMatchInfo_3257_, lean_object* v_fst_3258_, lean_object* v_numParams_3259_, lean_object* v_numDiscrs_3260_, lean_object* v_altInfos_3261_, lean_object* v_uElimPos_x3f_3262_, lean_object* v_snd_3263_, lean_object* v_overlaps_3264_, lean_object* v_splitterName_3265_, lean_object* v_matcherLevels_3266_, lean_object* v_params_x27_3267_, lean_object* v_fst_3268_, lean_object* v_discrs_x27_3269_, lean_object* v_toPure_3270_, lean_object* v_onRemaining_3271_, lean_object* v_remaining_3272_, lean_object* v_toBind_3273_, lean_object* v_origAltTypes_3274_, lean_object* v_alts_3275_, lean_object* v___x_3276_, lean_object* v___x_3277_, lean_object* v_remaining_x27_3278_, lean_object* v___f_3279_, lean_object* v_altTypes_3280_){
_start:
{
lean_object* v_altInfos_3281_; lean_object* v___f_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v_altInfos_3281_ = lean_ctor_get(v_splitterMatchInfo_3257_, 2);
lean_inc_ref(v_altInfos_3281_);
lean_dec_ref(v_splitterMatchInfo_3257_);
lean_inc(v_toBind_3273_);
lean_inc_ref(v_altInfos_3261_);
v___f_3282_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 17, 16);
lean_closure_set(v___f_3282_, 0, v_fst_3258_);
lean_closure_set(v___f_3282_, 1, v_numParams_3259_);
lean_closure_set(v___f_3282_, 2, v_numDiscrs_3260_);
lean_closure_set(v___f_3282_, 3, v_altInfos_3261_);
lean_closure_set(v___f_3282_, 4, v_uElimPos_x3f_3262_);
lean_closure_set(v___f_3282_, 5, v_snd_3263_);
lean_closure_set(v___f_3282_, 6, v_overlaps_3264_);
lean_closure_set(v___f_3282_, 7, v_splitterName_3265_);
lean_closure_set(v___f_3282_, 8, v_matcherLevels_3266_);
lean_closure_set(v___f_3282_, 9, v_params_x27_3267_);
lean_closure_set(v___f_3282_, 10, v_fst_3268_);
lean_closure_set(v___f_3282_, 11, v_discrs_x27_3269_);
lean_closure_set(v___f_3282_, 12, v_toPure_3270_);
lean_closure_set(v___f_3282_, 13, v_onRemaining_3271_);
lean_closure_set(v___f_3282_, 14, v_remaining_3272_);
lean_closure_set(v___f_3282_, 15, v_toBind_3273_);
v___x_3283_ = lean_array_get_size(v_altInfos_3261_);
v___x_3284_ = lean_array_get_size(v_altInfos_3281_);
v___x_3285_ = lean_array_get_size(v_origAltTypes_3274_);
v___x_3286_ = lean_array_get_size(v_altTypes_3280_);
lean_inc(v___x_3276_);
v___x_3287_ = l_Array_toSubarray___redArg(v_alts_3275_, v___x_3276_, v___x_3277_);
lean_inc(v___x_3276_);
v___x_3288_ = l_Array_toSubarray___redArg(v_altInfos_3261_, v___x_3276_, v___x_3283_);
lean_inc(v___x_3276_);
v___x_3289_ = l_Array_toSubarray___redArg(v_altInfos_3281_, v___x_3276_, v___x_3284_);
lean_inc(v___x_3276_);
v___x_3290_ = l_Array_toSubarray___redArg(v_origAltTypes_3274_, v___x_3276_, v___x_3285_);
lean_inc(v___x_3276_);
v___x_3291_ = l_Array_toSubarray___redArg(v_altTypes_3280_, v___x_3276_, v___x_3286_);
v___x_3292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3290_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
v___x_3293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3289_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
v___x_3294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3288_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
v___x_3295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3287_);
lean_ctor_set(v___x_3295_, 1, v___x_3294_);
v___x_3296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3296_, 0, v_remaining_x27_3278_);
lean_ctor_set(v___x_3296_, 1, v___x_3295_);
v___x_3297_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3279_, v___x_3276_, v___x_3296_, lean_box(0));
v___x_3298_ = lean_apply_4(v_toBind_3273_, lean_box(0), lean_box(0), v___x_3297_, v___f_3282_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed(lean_object** _args){
lean_object* v_splitterMatchInfo_3299_ = _args[0];
lean_object* v_fst_3300_ = _args[1];
lean_object* v_numParams_3301_ = _args[2];
lean_object* v_numDiscrs_3302_ = _args[3];
lean_object* v_altInfos_3303_ = _args[4];
lean_object* v_uElimPos_x3f_3304_ = _args[5];
lean_object* v_snd_3305_ = _args[6];
lean_object* v_overlaps_3306_ = _args[7];
lean_object* v_splitterName_3307_ = _args[8];
lean_object* v_matcherLevels_3308_ = _args[9];
lean_object* v_params_x27_3309_ = _args[10];
lean_object* v_fst_3310_ = _args[11];
lean_object* v_discrs_x27_3311_ = _args[12];
lean_object* v_toPure_3312_ = _args[13];
lean_object* v_onRemaining_3313_ = _args[14];
lean_object* v_remaining_3314_ = _args[15];
lean_object* v_toBind_3315_ = _args[16];
lean_object* v_origAltTypes_3316_ = _args[17];
lean_object* v_alts_3317_ = _args[18];
lean_object* v___x_3318_ = _args[19];
lean_object* v___x_3319_ = _args[20];
lean_object* v_remaining_x27_3320_ = _args[21];
lean_object* v___f_3321_ = _args[22];
lean_object* v_altTypes_3322_ = _args[23];
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__49(v_splitterMatchInfo_3299_, v_fst_3300_, v_numParams_3301_, v_numDiscrs_3302_, v_altInfos_3303_, v_uElimPos_x3f_3304_, v_snd_3305_, v_overlaps_3306_, v_splitterName_3307_, v_matcherLevels_3308_, v_params_x27_3309_, v_fst_3310_, v_discrs_x27_3311_, v_toPure_3312_, v_onRemaining_3313_, v_remaining_3314_, v_toBind_3315_, v_origAltTypes_3316_, v_alts_3317_, v___x_3318_, v___x_3319_, v_remaining_x27_3320_, v___f_3321_, v_altTypes_3322_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__50(lean_object* v___x_3324_, lean_object* v_aux2_3325_, lean_object* v_inst_3326_, lean_object* v_toBind_3327_, lean_object* v___f_3328_, lean_object* v_____r_3329_){
_start:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3330_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_3330_, 0, v___x_3324_);
lean_closure_set(v___x_3330_, 1, v_aux2_3325_);
v___x_3331_ = lean_apply_2(v_inst_3326_, lean_box(0), v___x_3330_);
v___x_3332_ = lean_apply_4(v_toBind_3327_, lean_box(0), lean_box(0), v___x_3331_, v___f_3328_);
return v___x_3332_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1(void){
_start:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3334_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__0));
v___x_3335_ = l_Lean_stringToMessageData(v___x_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53(lean_object* v___x_3336_, lean_object* v_params_x27_3337_, lean_object* v_fst_3338_, lean_object* v_discrs_x27_3339_, lean_object* v_fst_3340_, lean_object* v_numParams_3341_, lean_object* v_numDiscrs_3342_, lean_object* v_altInfos_3343_, lean_object* v_uElimPos_x3f_3344_, lean_object* v_snd_3345_, lean_object* v_overlaps_3346_, lean_object* v_matcherLevels_3347_, lean_object* v_toPure_3348_, lean_object* v_onRemaining_3349_, lean_object* v_remaining_3350_, lean_object* v_toBind_3351_, lean_object* v_origAltTypes_3352_, lean_object* v_alts_3353_, lean_object* v___x_3354_, lean_object* v___x_3355_, lean_object* v_remaining_x27_3356_, lean_object* v___f_3357_, lean_object* v_inst_3358_, lean_object* v___x_3359_, lean_object* v_liftWith_3360_, lean_object* v_restoreM_3361_, lean_object* v_matchEqns_3362_){
_start:
{
lean_object* v_splitterName_3363_; lean_object* v_splitterMatchInfo_3364_; lean_object* v___x_3365_; lean_object* v_aux2_3366_; lean_object* v_aux2_3367_; lean_object* v_aux2_3368_; lean_object* v___x_3369_; lean_object* v___f_3370_; lean_object* v___f_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___f_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___f_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
v_splitterName_3363_ = lean_ctor_get(v_matchEqns_3362_, 1);
lean_inc(v_splitterName_3363_);
v_splitterMatchInfo_3364_ = lean_ctor_get(v_matchEqns_3362_, 2);
lean_inc_ref(v_splitterMatchInfo_3364_);
lean_dec_ref(v_matchEqns_3362_);
lean_inc(v_splitterName_3363_);
v___x_3365_ = l_Lean_mkConst(v_splitterName_3363_, v___x_3336_);
v_aux2_3366_ = l_Lean_mkAppN(v___x_3365_, v_params_x27_3337_);
lean_inc_ref(v_fst_3338_);
v_aux2_3367_ = l_Lean_Expr_app___override(v_aux2_3366_, v_fst_3338_);
v_aux2_3368_ = l_Lean_mkAppN(v_aux2_3367_, v_discrs_x27_3339_);
lean_inc_ref(v_aux2_3368_);
v___x_3369_ = l_Lean_indentExpr(v_aux2_3368_);
lean_inc(v___x_3355_);
lean_inc(v_toBind_3351_);
v___f_3370_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed), 24, 23);
lean_closure_set(v___f_3370_, 0, v_splitterMatchInfo_3364_);
lean_closure_set(v___f_3370_, 1, v_fst_3340_);
lean_closure_set(v___f_3370_, 2, v_numParams_3341_);
lean_closure_set(v___f_3370_, 3, v_numDiscrs_3342_);
lean_closure_set(v___f_3370_, 4, v_altInfos_3343_);
lean_closure_set(v___f_3370_, 5, v_uElimPos_x3f_3344_);
lean_closure_set(v___f_3370_, 6, v_snd_3345_);
lean_closure_set(v___f_3370_, 7, v_overlaps_3346_);
lean_closure_set(v___f_3370_, 8, v_splitterName_3363_);
lean_closure_set(v___f_3370_, 9, v_matcherLevels_3347_);
lean_closure_set(v___f_3370_, 10, v_params_x27_3337_);
lean_closure_set(v___f_3370_, 11, v_fst_3338_);
lean_closure_set(v___f_3370_, 12, v_discrs_x27_3339_);
lean_closure_set(v___f_3370_, 13, v_toPure_3348_);
lean_closure_set(v___f_3370_, 14, v_onRemaining_3349_);
lean_closure_set(v___f_3370_, 15, v_remaining_3350_);
lean_closure_set(v___f_3370_, 16, v_toBind_3351_);
lean_closure_set(v___f_3370_, 17, v_origAltTypes_3352_);
lean_closure_set(v___f_3370_, 18, v_alts_3353_);
lean_closure_set(v___f_3370_, 19, v___x_3354_);
lean_closure_set(v___f_3370_, 20, v___x_3355_);
lean_closure_set(v___f_3370_, 21, v_remaining_x27_3356_);
lean_closure_set(v___f_3370_, 22, v___f_3357_);
lean_inc(v_toBind_3351_);
lean_inc(v_inst_3358_);
lean_inc_ref(v_aux2_3368_);
v___f_3371_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__50), 6, 5);
lean_closure_set(v___f_3371_, 0, v___x_3355_);
lean_closure_set(v___f_3371_, 1, v_aux2_3368_);
lean_closure_set(v___f_3371_, 2, v_inst_3358_);
lean_closure_set(v___f_3371_, 3, v_toBind_3351_);
lean_closure_set(v___f_3371_, 4, v___f_3370_);
v___x_3372_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1);
v___x_3373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3372_);
lean_ctor_set(v___x_3373_, 1, v___x_3369_);
v___x_3374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3373_);
lean_ctor_set(v___x_3374_, 1, v___x_3359_);
v___f_3375_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3375_, 0, v___x_3374_);
v___x_3376_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(v___x_3376_, 0, v_aux2_3368_);
v___x_3377_ = lean_apply_2(v_inst_3358_, lean_box(0), v___x_3376_);
v___f_3378_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3378_, 0, v___x_3377_);
lean_closure_set(v___f_3378_, 1, v___f_3375_);
v___x_3379_ = lean_apply_2(v_liftWith_3360_, lean_box(0), v___f_3378_);
v___x_3380_ = lean_apply_1(v_restoreM_3361_, lean_box(0));
lean_inc(v_toBind_3351_);
v___x_3381_ = lean_apply_4(v_toBind_3351_, lean_box(0), lean_box(0), v___x_3379_, v___x_3380_);
v___x_3382_ = lean_apply_4(v_toBind_3351_, lean_box(0), lean_box(0), v___x_3381_, v___f_3371_);
return v___x_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed(lean_object** _args){
lean_object* v___x_3383_ = _args[0];
lean_object* v_params_x27_3384_ = _args[1];
lean_object* v_fst_3385_ = _args[2];
lean_object* v_discrs_x27_3386_ = _args[3];
lean_object* v_fst_3387_ = _args[4];
lean_object* v_numParams_3388_ = _args[5];
lean_object* v_numDiscrs_3389_ = _args[6];
lean_object* v_altInfos_3390_ = _args[7];
lean_object* v_uElimPos_x3f_3391_ = _args[8];
lean_object* v_snd_3392_ = _args[9];
lean_object* v_overlaps_3393_ = _args[10];
lean_object* v_matcherLevels_3394_ = _args[11];
lean_object* v_toPure_3395_ = _args[12];
lean_object* v_onRemaining_3396_ = _args[13];
lean_object* v_remaining_3397_ = _args[14];
lean_object* v_toBind_3398_ = _args[15];
lean_object* v_origAltTypes_3399_ = _args[16];
lean_object* v_alts_3400_ = _args[17];
lean_object* v___x_3401_ = _args[18];
lean_object* v___x_3402_ = _args[19];
lean_object* v_remaining_x27_3403_ = _args[20];
lean_object* v___f_3404_ = _args[21];
lean_object* v_inst_3405_ = _args[22];
lean_object* v___x_3406_ = _args[23];
lean_object* v_liftWith_3407_ = _args[24];
lean_object* v_restoreM_3408_ = _args[25];
lean_object* v_matchEqns_3409_ = _args[26];
_start:
{
lean_object* v_res_3410_; 
v_res_3410_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__53(v___x_3383_, v_params_x27_3384_, v_fst_3385_, v_discrs_x27_3386_, v_fst_3387_, v_numParams_3388_, v_numDiscrs_3389_, v_altInfos_3390_, v_uElimPos_x3f_3391_, v_snd_3392_, v_overlaps_3393_, v_matcherLevels_3394_, v_toPure_3395_, v_onRemaining_3396_, v_remaining_3397_, v_toBind_3398_, v_origAltTypes_3399_, v_alts_3400_, v___x_3401_, v___x_3402_, v_remaining_x27_3403_, v___f_3404_, v_inst_3405_, v___x_3406_, v_liftWith_3407_, v_restoreM_3408_, v_matchEqns_3409_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51(lean_object* v___x_3411_, lean_object* v_params_x27_3412_, lean_object* v_fst_3413_, lean_object* v_discrs_x27_3414_, lean_object* v_fst_3415_, lean_object* v_numParams_3416_, lean_object* v_numDiscrs_3417_, lean_object* v_altInfos_3418_, lean_object* v_uElimPos_x3f_3419_, lean_object* v_snd_3420_, lean_object* v_overlaps_3421_, lean_object* v_matcherLevels_3422_, lean_object* v_toPure_3423_, lean_object* v_onRemaining_3424_, lean_object* v_remaining_3425_, lean_object* v_toBind_3426_, lean_object* v_alts_3427_, lean_object* v___x_3428_, lean_object* v___x_3429_, lean_object* v_remaining_x27_3430_, lean_object* v___f_3431_, lean_object* v_inst_3432_, lean_object* v___x_3433_, lean_object* v_liftWith_3434_, lean_object* v_restoreM_3435_, lean_object* v_matcherName_3436_, lean_object* v_origAltTypes_3437_){
_start:
{
lean_object* v___f_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
lean_inc(v_inst_3432_);
lean_inc(v_toBind_3426_);
v___f_3438_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed), 27, 26);
lean_closure_set(v___f_3438_, 0, v___x_3411_);
lean_closure_set(v___f_3438_, 1, v_params_x27_3412_);
lean_closure_set(v___f_3438_, 2, v_fst_3413_);
lean_closure_set(v___f_3438_, 3, v_discrs_x27_3414_);
lean_closure_set(v___f_3438_, 4, v_fst_3415_);
lean_closure_set(v___f_3438_, 5, v_numParams_3416_);
lean_closure_set(v___f_3438_, 6, v_numDiscrs_3417_);
lean_closure_set(v___f_3438_, 7, v_altInfos_3418_);
lean_closure_set(v___f_3438_, 8, v_uElimPos_x3f_3419_);
lean_closure_set(v___f_3438_, 9, v_snd_3420_);
lean_closure_set(v___f_3438_, 10, v_overlaps_3421_);
lean_closure_set(v___f_3438_, 11, v_matcherLevels_3422_);
lean_closure_set(v___f_3438_, 12, v_toPure_3423_);
lean_closure_set(v___f_3438_, 13, v_onRemaining_3424_);
lean_closure_set(v___f_3438_, 14, v_remaining_3425_);
lean_closure_set(v___f_3438_, 15, v_toBind_3426_);
lean_closure_set(v___f_3438_, 16, v_origAltTypes_3437_);
lean_closure_set(v___f_3438_, 17, v_alts_3427_);
lean_closure_set(v___f_3438_, 18, v___x_3428_);
lean_closure_set(v___f_3438_, 19, v___x_3429_);
lean_closure_set(v___f_3438_, 20, v_remaining_x27_3430_);
lean_closure_set(v___f_3438_, 21, v___f_3431_);
lean_closure_set(v___f_3438_, 22, v_inst_3432_);
lean_closure_set(v___f_3438_, 23, v___x_3433_);
lean_closure_set(v___f_3438_, 24, v_liftWith_3434_);
lean_closure_set(v___f_3438_, 25, v_restoreM_3435_);
v___x_3439_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_getEquationsFor___boxed), 6, 1);
lean_closure_set(v___x_3439_, 0, v_matcherName_3436_);
v___x_3440_ = lean_apply_2(v_inst_3432_, lean_box(0), v___x_3439_);
v___x_3441_ = lean_apply_4(v_toBind_3426_, lean_box(0), lean_box(0), v___x_3440_, v___f_3438_);
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
lean_object* v_liftWith_3465_ = _args[23];
lean_object* v_restoreM_3466_ = _args[24];
lean_object* v_matcherName_3467_ = _args[25];
lean_object* v_origAltTypes_3468_ = _args[26];
_start:
{
lean_object* v_res_3469_; 
v_res_3469_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__51(v___x_3442_, v_params_x27_3443_, v_fst_3444_, v_discrs_x27_3445_, v_fst_3446_, v_numParams_3447_, v_numDiscrs_3448_, v_altInfos_3449_, v_uElimPos_x3f_3450_, v_snd_3451_, v_overlaps_3452_, v_matcherLevels_3453_, v_toPure_3454_, v_onRemaining_3455_, v_remaining_3456_, v_toBind_3457_, v_alts_3458_, v___x_3459_, v___x_3460_, v_remaining_x27_3461_, v___f_3462_, v_inst_3463_, v___x_3464_, v_liftWith_3465_, v_restoreM_3466_, v_matcherName_3467_, v_origAltTypes_3468_);
return v_res_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52(lean_object* v_alts_3470_, lean_object* v_toPure_3471_, lean_object* v_toBind_3472_, lean_object* v___f_3473_, lean_object* v___x_3474_, lean_object* v_inst_3475_, lean_object* v_inst_3476_, lean_object* v_inst_3477_, uint8_t v___x_3478_, uint8_t v_useSplitter_3479_, lean_object* v_onAlt_3480_, lean_object* v___f_3481_, lean_object* v_fst_3482_, lean_object* v_inst_3483_, lean_object* v_numDiscrEqs_3484_, lean_object* v___x_3485_, lean_object* v_params_x27_3486_, lean_object* v_fst_3487_, lean_object* v_discrs_x27_3488_, lean_object* v_fst_3489_, lean_object* v_numParams_3490_, lean_object* v_numDiscrs_3491_, lean_object* v_altInfos_3492_, lean_object* v_uElimPos_x3f_3493_, lean_object* v_snd_3494_, lean_object* v_overlaps_3495_, lean_object* v_matcherLevels_3496_, lean_object* v_onRemaining_3497_, lean_object* v_remaining_3498_, lean_object* v_remaining_x27_3499_, lean_object* v___x_3500_, lean_object* v_liftWith_3501_, lean_object* v_restoreM_3502_, lean_object* v_matcherName_3503_, lean_object* v_aux1_3504_, lean_object* v_____r_3505_){
_start:
{
lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___f_3509_; lean_object* v___f_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3506_ = lean_array_get_size(v_alts_3470_);
v___x_3507_ = lean_box(v___x_3478_);
v___x_3508_ = lean_box(v_useSplitter_3479_);
lean_inc(v_inst_3476_);
lean_inc(v___x_3474_);
lean_inc(v_toBind_3472_);
lean_inc(v_toPure_3471_);
v___f_3509_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46___boxed), 19, 15);
lean_closure_set(v___f_3509_, 0, v___x_3506_);
lean_closure_set(v___f_3509_, 1, v_toPure_3471_);
lean_closure_set(v___f_3509_, 2, v_toBind_3472_);
lean_closure_set(v___f_3509_, 3, v___f_3473_);
lean_closure_set(v___f_3509_, 4, v___x_3474_);
lean_closure_set(v___f_3509_, 5, v_inst_3475_);
lean_closure_set(v___f_3509_, 6, v_inst_3476_);
lean_closure_set(v___f_3509_, 7, v_inst_3477_);
lean_closure_set(v___f_3509_, 8, v___x_3507_);
lean_closure_set(v___f_3509_, 9, v___x_3508_);
lean_closure_set(v___f_3509_, 10, v_onAlt_3480_);
lean_closure_set(v___f_3509_, 11, v___f_3481_);
lean_closure_set(v___f_3509_, 12, v_fst_3482_);
lean_closure_set(v___f_3509_, 13, v_inst_3483_);
lean_closure_set(v___f_3509_, 14, v_numDiscrEqs_3484_);
lean_inc(v_inst_3476_);
lean_inc(v_toBind_3472_);
v___f_3510_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed), 27, 26);
lean_closure_set(v___f_3510_, 0, v___x_3485_);
lean_closure_set(v___f_3510_, 1, v_params_x27_3486_);
lean_closure_set(v___f_3510_, 2, v_fst_3487_);
lean_closure_set(v___f_3510_, 3, v_discrs_x27_3488_);
lean_closure_set(v___f_3510_, 4, v_fst_3489_);
lean_closure_set(v___f_3510_, 5, v_numParams_3490_);
lean_closure_set(v___f_3510_, 6, v_numDiscrs_3491_);
lean_closure_set(v___f_3510_, 7, v_altInfos_3492_);
lean_closure_set(v___f_3510_, 8, v_uElimPos_x3f_3493_);
lean_closure_set(v___f_3510_, 9, v_snd_3494_);
lean_closure_set(v___f_3510_, 10, v_overlaps_3495_);
lean_closure_set(v___f_3510_, 11, v_matcherLevels_3496_);
lean_closure_set(v___f_3510_, 12, v_toPure_3471_);
lean_closure_set(v___f_3510_, 13, v_onRemaining_3497_);
lean_closure_set(v___f_3510_, 14, v_remaining_3498_);
lean_closure_set(v___f_3510_, 15, v_toBind_3472_);
lean_closure_set(v___f_3510_, 16, v_alts_3470_);
lean_closure_set(v___f_3510_, 17, v___x_3474_);
lean_closure_set(v___f_3510_, 18, v___x_3506_);
lean_closure_set(v___f_3510_, 19, v_remaining_x27_3499_);
lean_closure_set(v___f_3510_, 20, v___f_3509_);
lean_closure_set(v___f_3510_, 21, v_inst_3476_);
lean_closure_set(v___f_3510_, 22, v___x_3500_);
lean_closure_set(v___f_3510_, 23, v_liftWith_3501_);
lean_closure_set(v___f_3510_, 24, v_restoreM_3502_);
lean_closure_set(v___f_3510_, 25, v_matcherName_3503_);
v___x_3511_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_3511_, 0, v___x_3506_);
lean_closure_set(v___x_3511_, 1, v_aux1_3504_);
v___x_3512_ = lean_apply_2(v_inst_3476_, lean_box(0), v___x_3511_);
v___x_3513_ = lean_apply_4(v_toBind_3472_, lean_box(0), lean_box(0), v___x_3512_, v___f_3510_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed(lean_object** _args){
lean_object* v_alts_3514_ = _args[0];
lean_object* v_toPure_3515_ = _args[1];
lean_object* v_toBind_3516_ = _args[2];
lean_object* v___f_3517_ = _args[3];
lean_object* v___x_3518_ = _args[4];
lean_object* v_inst_3519_ = _args[5];
lean_object* v_inst_3520_ = _args[6];
lean_object* v_inst_3521_ = _args[7];
lean_object* v___x_3522_ = _args[8];
lean_object* v_useSplitter_3523_ = _args[9];
lean_object* v_onAlt_3524_ = _args[10];
lean_object* v___f_3525_ = _args[11];
lean_object* v_fst_3526_ = _args[12];
lean_object* v_inst_3527_ = _args[13];
lean_object* v_numDiscrEqs_3528_ = _args[14];
lean_object* v___x_3529_ = _args[15];
lean_object* v_params_x27_3530_ = _args[16];
lean_object* v_fst_3531_ = _args[17];
lean_object* v_discrs_x27_3532_ = _args[18];
lean_object* v_fst_3533_ = _args[19];
lean_object* v_numParams_3534_ = _args[20];
lean_object* v_numDiscrs_3535_ = _args[21];
lean_object* v_altInfos_3536_ = _args[22];
lean_object* v_uElimPos_x3f_3537_ = _args[23];
lean_object* v_snd_3538_ = _args[24];
lean_object* v_overlaps_3539_ = _args[25];
lean_object* v_matcherLevels_3540_ = _args[26];
lean_object* v_onRemaining_3541_ = _args[27];
lean_object* v_remaining_3542_ = _args[28];
lean_object* v_remaining_x27_3543_ = _args[29];
lean_object* v___x_3544_ = _args[30];
lean_object* v_liftWith_3545_ = _args[31];
lean_object* v_restoreM_3546_ = _args[32];
lean_object* v_matcherName_3547_ = _args[33];
lean_object* v_aux1_3548_ = _args[34];
lean_object* v_____r_3549_ = _args[35];
_start:
{
uint8_t v___x_16511__boxed_3550_; uint8_t v_useSplitter_boxed_3551_; lean_object* v_res_3552_; 
v___x_16511__boxed_3550_ = lean_unbox(v___x_3522_);
v_useSplitter_boxed_3551_ = lean_unbox(v_useSplitter_3523_);
v_res_3552_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__52(v_alts_3514_, v_toPure_3515_, v_toBind_3516_, v___f_3517_, v___x_3518_, v_inst_3519_, v_inst_3520_, v_inst_3521_, v___x_16511__boxed_3550_, v_useSplitter_boxed_3551_, v_onAlt_3524_, v___f_3525_, v_fst_3526_, v_inst_3527_, v_numDiscrEqs_3528_, v___x_3529_, v_params_x27_3530_, v_fst_3531_, v_discrs_x27_3532_, v_fst_3533_, v_numParams_3534_, v_numDiscrs_3535_, v_altInfos_3536_, v_uElimPos_x3f_3537_, v_snd_3538_, v_overlaps_3539_, v_matcherLevels_3540_, v_onRemaining_3541_, v_remaining_3542_, v_remaining_x27_3543_, v___x_3544_, v_liftWith_3545_, v_restoreM_3546_, v_matcherName_3547_, v_aux1_3548_, v_____r_3549_);
return v_res_3552_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__1(void){
_start:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3554_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__0));
v___x_3555_ = l_Lean_stringToMessageData(v___x_3554_);
return v___x_3555_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__3(void){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__2));
v___x_3558_ = l_Lean_stringToMessageData(v___x_3557_);
return v___x_3558_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__5(void){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3560_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__4));
v___x_3561_ = l_Lean_stringToMessageData(v___x_3560_);
return v___x_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56(lean_object* v_numParams_3562_, lean_object* v_numDiscrs_3563_, lean_object* v_altInfos_3564_, lean_object* v_uElimPos_x3f_3565_, lean_object* v_snd_3566_, lean_object* v_overlaps_3567_, lean_object* v_matcherName_3568_, lean_object* v_matcherLevels_3569_, lean_object* v_params_x27_3570_, lean_object* v_fst_3571_, lean_object* v_discrs_x27_3572_, lean_object* v_toPure_3573_, lean_object* v_onRemaining_3574_, lean_object* v_remaining_3575_, lean_object* v_toBind_3576_, lean_object* v_inst_3577_, lean_object* v_alts_3578_, lean_object* v___f_3579_, uint8_t v___x_3580_, lean_object* v_inst_3581_, lean_object* v_remaining_x27_3582_, lean_object* v_onAlt_3583_, lean_object* v_inst_3584_, lean_object* v___f_3585_, lean_object* v_matcherApp_3586_, lean_object* v___x_3587_, uint8_t v_useSplitter_3588_, uint8_t v_isCasesOn_3589_, lean_object* v___f_3590_, lean_object* v_inst_3591_, lean_object* v___f_3592_, lean_object* v_numDiscrEqs_3593_, lean_object* v_____s_3594_){
_start:
{
lean_object* v_snd_3595_; lean_object* v_fst_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3657_; 
v_snd_3595_ = lean_ctor_get(v_____s_3594_, 1);
v_fst_3596_ = lean_ctor_get(v_____s_3594_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v_____s_3594_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3598_ = v_____s_3594_;
v_isShared_3599_ = v_isSharedCheck_3657_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_snd_3595_);
lean_inc(v_fst_3596_);
lean_dec(v_____s_3594_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3657_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v_fst_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3655_; 
v_fst_3600_ = lean_ctor_get(v_snd_3595_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v_snd_3595_);
if (v_isSharedCheck_3655_ == 0)
{
lean_object* v_unused_3656_; 
v_unused_3656_ = lean_ctor_get(v_snd_3595_, 1);
lean_dec(v_unused_3656_);
v___x_3602_ = v_snd_3595_;
v_isShared_3603_ = v_isSharedCheck_3655_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_fst_3600_);
lean_dec(v_snd_3595_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3655_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___f_3604_; 
lean_inc(v_toBind_3576_);
lean_inc_ref(v_remaining_3575_);
lean_inc(v_onRemaining_3574_);
lean_inc(v_toPure_3573_);
lean_inc_ref(v_discrs_x27_3572_);
lean_inc_ref(v_fst_3571_);
lean_inc_ref(v_params_x27_3570_);
lean_inc_ref(v_matcherLevels_3569_);
lean_inc(v_matcherName_3568_);
lean_inc_ref(v_overlaps_3567_);
lean_inc_ref(v_snd_3566_);
lean_inc(v_uElimPos_x3f_3565_);
lean_inc_ref(v_altInfos_3564_);
lean_inc(v_numDiscrs_3563_);
lean_inc(v_numParams_3562_);
lean_inc(v_fst_3596_);
v___f_3604_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed), 17, 16);
lean_closure_set(v___f_3604_, 0, v_fst_3596_);
lean_closure_set(v___f_3604_, 1, v_numParams_3562_);
lean_closure_set(v___f_3604_, 2, v_numDiscrs_3563_);
lean_closure_set(v___f_3604_, 3, v_altInfos_3564_);
lean_closure_set(v___f_3604_, 4, v_uElimPos_x3f_3565_);
lean_closure_set(v___f_3604_, 5, v_snd_3566_);
lean_closure_set(v___f_3604_, 6, v_overlaps_3567_);
lean_closure_set(v___f_3604_, 7, v_matcherName_3568_);
lean_closure_set(v___f_3604_, 8, v_matcherLevels_3569_);
lean_closure_set(v___f_3604_, 9, v_params_x27_3570_);
lean_closure_set(v___f_3604_, 10, v_fst_3571_);
lean_closure_set(v___f_3604_, 11, v_discrs_x27_3572_);
lean_closure_set(v___f_3604_, 12, v_toPure_3573_);
lean_closure_set(v___f_3604_, 13, v_onRemaining_3574_);
lean_closure_set(v___f_3604_, 14, v_remaining_3575_);
lean_closure_set(v___f_3604_, 15, v_toBind_3576_);
if (v_useSplitter_3588_ == 0)
{
lean_del_object(v___x_3598_);
lean_dec(v_fst_3596_);
lean_dec(v_numDiscrEqs_3593_);
lean_dec(v___f_3592_);
lean_dec_ref(v_inst_3591_);
lean_dec(v___f_3590_);
lean_dec_ref(v_remaining_3575_);
lean_dec(v_onRemaining_3574_);
lean_dec_ref(v_overlaps_3567_);
lean_dec_ref(v_snd_3566_);
lean_dec(v_uElimPos_x3f_3565_);
lean_dec_ref(v_altInfos_3564_);
lean_dec(v_numDiscrs_3563_);
lean_dec(v_numParams_3562_);
goto v___jp_3605_;
}
else
{
if (v_isCasesOn_3589_ == 0)
{
lean_object* v_liftWith_3630_; lean_object* v_restoreM_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v_aux1_3634_; lean_object* v_aux1_3635_; lean_object* v_aux1_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3640_; 
lean_dec_ref(v___f_3604_);
lean_del_object(v___x_3602_);
lean_dec_ref(v_matcherApp_3586_);
lean_dec(v___f_3585_);
lean_dec(v___f_3579_);
v_liftWith_3630_ = lean_ctor_get(v_inst_3577_, 0);
lean_inc(v_liftWith_3630_);
v_restoreM_3631_ = lean_ctor_get(v_inst_3577_, 1);
lean_inc(v_restoreM_3631_);
lean_inc_ref(v_matcherLevels_3569_);
v___x_3632_ = lean_array_to_list(v_matcherLevels_3569_);
lean_inc(v___x_3632_);
lean_inc(v_matcherName_3568_);
v___x_3633_ = l_Lean_mkConst(v_matcherName_3568_, v___x_3632_);
v_aux1_3634_ = l_Lean_mkAppN(v___x_3633_, v_params_x27_3570_);
lean_inc_ref(v_fst_3571_);
v_aux1_3635_ = l_Lean_Expr_app___override(v_aux1_3634_, v_fst_3571_);
v_aux1_3636_ = l_Lean_mkAppN(v_aux1_3635_, v_discrs_x27_3572_);
lean_inc_ref(v_aux1_3636_);
v___x_3637_ = l_Lean_indentExpr(v_aux1_3636_);
v___x_3638_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__3);
if (v_isShared_3599_ == 0)
{
lean_ctor_set_tag(v___x_3598_, 7);
lean_ctor_set(v___x_3598_, 1, v___x_3637_);
lean_ctor_set(v___x_3598_, 0, v___x_3638_);
v___x_3640_ = v___x_3598_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___x_3638_);
lean_ctor_set(v_reuseFailAlloc_3654_, 1, v___x_3637_);
v___x_3640_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___f_3644_; lean_object* v___x_3645_; lean_object* v___f_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___f_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3641_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__5);
v___x_3642_ = lean_box(v___x_3580_);
v___x_3643_ = lean_box(v_useSplitter_3588_);
lean_inc_ref(v_aux1_3636_);
lean_inc(v_restoreM_3631_);
lean_inc(v_liftWith_3630_);
lean_inc(v_inst_3581_);
lean_inc(v_toBind_3576_);
v___f_3644_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed), 36, 35);
lean_closure_set(v___f_3644_, 0, v_alts_3578_);
lean_closure_set(v___f_3644_, 1, v_toPure_3573_);
lean_closure_set(v___f_3644_, 2, v_toBind_3576_);
lean_closure_set(v___f_3644_, 3, v___f_3590_);
lean_closure_set(v___f_3644_, 4, v___x_3587_);
lean_closure_set(v___f_3644_, 5, v_inst_3584_);
lean_closure_set(v___f_3644_, 6, v_inst_3581_);
lean_closure_set(v___f_3644_, 7, v_inst_3591_);
lean_closure_set(v___f_3644_, 8, v___x_3642_);
lean_closure_set(v___f_3644_, 9, v___x_3643_);
lean_closure_set(v___f_3644_, 10, v_onAlt_3583_);
lean_closure_set(v___f_3644_, 11, v___f_3592_);
lean_closure_set(v___f_3644_, 12, v_fst_3600_);
lean_closure_set(v___f_3644_, 13, v_inst_3577_);
lean_closure_set(v___f_3644_, 14, v_numDiscrEqs_3593_);
lean_closure_set(v___f_3644_, 15, v___x_3632_);
lean_closure_set(v___f_3644_, 16, v_params_x27_3570_);
lean_closure_set(v___f_3644_, 17, v_fst_3571_);
lean_closure_set(v___f_3644_, 18, v_discrs_x27_3572_);
lean_closure_set(v___f_3644_, 19, v_fst_3596_);
lean_closure_set(v___f_3644_, 20, v_numParams_3562_);
lean_closure_set(v___f_3644_, 21, v_numDiscrs_3563_);
lean_closure_set(v___f_3644_, 22, v_altInfos_3564_);
lean_closure_set(v___f_3644_, 23, v_uElimPos_x3f_3565_);
lean_closure_set(v___f_3644_, 24, v_snd_3566_);
lean_closure_set(v___f_3644_, 25, v_overlaps_3567_);
lean_closure_set(v___f_3644_, 26, v_matcherLevels_3569_);
lean_closure_set(v___f_3644_, 27, v_onRemaining_3574_);
lean_closure_set(v___f_3644_, 28, v_remaining_3575_);
lean_closure_set(v___f_3644_, 29, v_remaining_x27_3582_);
lean_closure_set(v___f_3644_, 30, v___x_3641_);
lean_closure_set(v___f_3644_, 31, v_liftWith_3630_);
lean_closure_set(v___f_3644_, 32, v_restoreM_3631_);
lean_closure_set(v___f_3644_, 33, v_matcherName_3568_);
lean_closure_set(v___f_3644_, 34, v_aux1_3636_);
v___x_3645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3640_);
lean_ctor_set(v___x_3645_, 1, v___x_3641_);
v___f_3646_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3646_, 0, v___x_3645_);
v___x_3647_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(v___x_3647_, 0, v_aux1_3636_);
v___x_3648_ = lean_apply_2(v_inst_3581_, lean_box(0), v___x_3647_);
v___f_3649_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3649_, 0, v___x_3648_);
lean_closure_set(v___f_3649_, 1, v___f_3646_);
v___x_3650_ = lean_apply_2(v_liftWith_3630_, lean_box(0), v___f_3649_);
v___x_3651_ = lean_apply_1(v_restoreM_3631_, lean_box(0));
lean_inc(v_toBind_3576_);
v___x_3652_ = lean_apply_4(v_toBind_3576_, lean_box(0), lean_box(0), v___x_3650_, v___x_3651_);
v___x_3653_ = lean_apply_4(v_toBind_3576_, lean_box(0), lean_box(0), v___x_3652_, v___f_3644_);
return v___x_3653_;
}
}
else
{
lean_del_object(v___x_3598_);
lean_dec(v_fst_3596_);
lean_dec(v_numDiscrEqs_3593_);
lean_dec(v___f_3592_);
lean_dec_ref(v_inst_3591_);
lean_dec(v___f_3590_);
lean_dec_ref(v_remaining_3575_);
lean_dec(v_onRemaining_3574_);
lean_dec_ref(v_overlaps_3567_);
lean_dec_ref(v_snd_3566_);
lean_dec(v_uElimPos_x3f_3565_);
lean_dec_ref(v_altInfos_3564_);
lean_dec(v_numDiscrs_3563_);
lean_dec(v_numParams_3562_);
goto v___jp_3605_;
}
}
v___jp_3605_:
{
lean_object* v_liftWith_3606_; lean_object* v_restoreM_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v_aux_3610_; lean_object* v_aux_3611_; lean_object* v_aux_3612_; lean_object* v___x_3613_; uint8_t v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___f_3617_; lean_object* v___x_3618_; lean_object* v___x_3620_; 
v_liftWith_3606_ = lean_ctor_get(v_inst_3577_, 0);
lean_inc(v_liftWith_3606_);
v_restoreM_3607_ = lean_ctor_get(v_inst_3577_, 1);
lean_inc(v_restoreM_3607_);
v___x_3608_ = lean_array_to_list(v_matcherLevels_3569_);
v___x_3609_ = l_Lean_mkConst(v_matcherName_3568_, v___x_3608_);
v_aux_3610_ = l_Lean_mkAppN(v___x_3609_, v_params_x27_3570_);
lean_dec_ref(v_params_x27_3570_);
v_aux_3611_ = l_Lean_Expr_app___override(v_aux_3610_, v_fst_3571_);
v_aux_3612_ = l_Lean_mkAppN(v_aux_3611_, v_discrs_x27_3572_);
lean_dec_ref(v_discrs_x27_3572_);
lean_inc_ref(v_aux_3612_);
v___x_3613_ = l_Lean_indentExpr(v_aux_3612_);
v___x_3614_ = 1;
v___x_3615_ = lean_box(v___x_3580_);
v___x_3616_ = lean_box(v___x_3614_);
lean_inc_ref(v_aux_3612_);
lean_inc(v_inst_3581_);
lean_inc(v_toBind_3576_);
v___f_3617_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 18, 17);
lean_closure_set(v___f_3617_, 0, v_alts_3578_);
lean_closure_set(v___f_3617_, 1, v_toPure_3573_);
lean_closure_set(v___f_3617_, 2, v_toBind_3576_);
lean_closure_set(v___f_3617_, 3, v___f_3579_);
lean_closure_set(v___f_3617_, 4, v___x_3615_);
lean_closure_set(v___f_3617_, 5, v___x_3616_);
lean_closure_set(v___f_3617_, 6, v_inst_3581_);
lean_closure_set(v___f_3617_, 7, v_remaining_x27_3582_);
lean_closure_set(v___f_3617_, 8, v_onAlt_3583_);
lean_closure_set(v___f_3617_, 9, v_inst_3577_);
lean_closure_set(v___f_3617_, 10, v_inst_3584_);
lean_closure_set(v___f_3617_, 11, v___f_3585_);
lean_closure_set(v___f_3617_, 12, v_fst_3600_);
lean_closure_set(v___f_3617_, 13, v_matcherApp_3586_);
lean_closure_set(v___f_3617_, 14, v___x_3587_);
lean_closure_set(v___f_3617_, 15, v___f_3604_);
lean_closure_set(v___f_3617_, 16, v_aux_3612_);
v___x_3618_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__1);
if (v_isShared_3603_ == 0)
{
lean_ctor_set_tag(v___x_3602_, 7);
lean_ctor_set(v___x_3602_, 1, v___x_3613_);
lean_ctor_set(v___x_3602_, 0, v___x_3618_);
v___x_3620_ = v___x_3602_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v___x_3618_);
lean_ctor_set(v_reuseFailAlloc_3629_, 1, v___x_3613_);
v___x_3620_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
lean_object* v___f_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___f_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___f_3621_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3621_, 0, v___x_3620_);
v___x_3622_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(v___x_3622_, 0, v_aux_3612_);
v___x_3623_ = lean_apply_2(v_inst_3581_, lean_box(0), v___x_3622_);
v___f_3624_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3624_, 0, v___x_3623_);
lean_closure_set(v___f_3624_, 1, v___f_3621_);
v___x_3625_ = lean_apply_2(v_liftWith_3606_, lean_box(0), v___f_3624_);
v___x_3626_ = lean_apply_1(v_restoreM_3607_, lean_box(0));
lean_inc(v_toBind_3576_);
v___x_3627_ = lean_apply_4(v_toBind_3576_, lean_box(0), lean_box(0), v___x_3625_, v___x_3626_);
v___x_3628_ = lean_apply_4(v_toBind_3576_, lean_box(0), lean_box(0), v___x_3627_, v___f_3617_);
return v___x_3628_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56___boxed(lean_object** _args){
lean_object* v_numParams_3658_ = _args[0];
lean_object* v_numDiscrs_3659_ = _args[1];
lean_object* v_altInfos_3660_ = _args[2];
lean_object* v_uElimPos_x3f_3661_ = _args[3];
lean_object* v_snd_3662_ = _args[4];
lean_object* v_overlaps_3663_ = _args[5];
lean_object* v_matcherName_3664_ = _args[6];
lean_object* v_matcherLevels_3665_ = _args[7];
lean_object* v_params_x27_3666_ = _args[8];
lean_object* v_fst_3667_ = _args[9];
lean_object* v_discrs_x27_3668_ = _args[10];
lean_object* v_toPure_3669_ = _args[11];
lean_object* v_onRemaining_3670_ = _args[12];
lean_object* v_remaining_3671_ = _args[13];
lean_object* v_toBind_3672_ = _args[14];
lean_object* v_inst_3673_ = _args[15];
lean_object* v_alts_3674_ = _args[16];
lean_object* v___f_3675_ = _args[17];
lean_object* v___x_3676_ = _args[18];
lean_object* v_inst_3677_ = _args[19];
lean_object* v_remaining_x27_3678_ = _args[20];
lean_object* v_onAlt_3679_ = _args[21];
lean_object* v_inst_3680_ = _args[22];
lean_object* v___f_3681_ = _args[23];
lean_object* v_matcherApp_3682_ = _args[24];
lean_object* v___x_3683_ = _args[25];
lean_object* v_useSplitter_3684_ = _args[26];
lean_object* v_isCasesOn_3685_ = _args[27];
lean_object* v___f_3686_ = _args[28];
lean_object* v_inst_3687_ = _args[29];
lean_object* v___f_3688_ = _args[30];
lean_object* v_numDiscrEqs_3689_ = _args[31];
lean_object* v_____s_3690_ = _args[32];
_start:
{
uint8_t v___x_16583__boxed_3691_; uint8_t v_useSplitter_boxed_3692_; uint8_t v_isCasesOn_boxed_3693_; lean_object* v_res_3694_; 
v___x_16583__boxed_3691_ = lean_unbox(v___x_3676_);
v_useSplitter_boxed_3692_ = lean_unbox(v_useSplitter_3684_);
v_isCasesOn_boxed_3693_ = lean_unbox(v_isCasesOn_3685_);
v_res_3694_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__56(v_numParams_3658_, v_numDiscrs_3659_, v_altInfos_3660_, v_uElimPos_x3f_3661_, v_snd_3662_, v_overlaps_3663_, v_matcherName_3664_, v_matcherLevels_3665_, v_params_x27_3666_, v_fst_3667_, v_discrs_x27_3668_, v_toPure_3669_, v_onRemaining_3670_, v_remaining_3671_, v_toBind_3672_, v_inst_3673_, v_alts_3674_, v___f_3675_, v___x_16583__boxed_3691_, v_inst_3677_, v_remaining_x27_3678_, v_onAlt_3679_, v_inst_3680_, v___f_3681_, v_matcherApp_3682_, v___x_3683_, v_useSplitter_boxed_3692_, v_isCasesOn_boxed_3693_, v___f_3686_, v_inst_3687_, v___f_3688_, v_numDiscrEqs_3689_, v_____s_3690_);
return v_res_3694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54(lean_object* v_numParams_3695_, lean_object* v_numDiscrs_3696_, lean_object* v_altInfos_3697_, lean_object* v_uElimPos_x3f_3698_, lean_object* v_snd_3699_, lean_object* v_overlaps_3700_, lean_object* v_matcherName_3701_, lean_object* v_params_x27_3702_, lean_object* v_fst_3703_, lean_object* v_discrs_x27_3704_, lean_object* v_toPure_3705_, lean_object* v_onRemaining_3706_, lean_object* v_remaining_3707_, lean_object* v_toBind_3708_, lean_object* v_inst_3709_, lean_object* v_alts_3710_, lean_object* v___f_3711_, uint8_t v___x_3712_, lean_object* v_inst_3713_, lean_object* v_onAlt_3714_, lean_object* v_inst_3715_, lean_object* v___f_3716_, lean_object* v_matcherApp_3717_, uint8_t v_useSplitter_3718_, uint8_t v_isCasesOn_3719_, lean_object* v___f_3720_, lean_object* v_inst_3721_, lean_object* v___f_3722_, lean_object* v_numDiscrEqs_3723_, lean_object* v_fst_3724_, lean_object* v___f_3725_, lean_object* v_matcherLevels_3726_){
_start:
{
lean_object* v___x_3727_; lean_object* v_remaining_x27_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___f_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; size_t v_sz_3739_; size_t v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v___x_3727_ = lean_unsigned_to_nat(0u);
v_remaining_x27_3728_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_3729_ = lean_box(v___x_3712_);
v___x_3730_ = lean_box(v_useSplitter_3718_);
v___x_3731_ = lean_box(v_isCasesOn_3719_);
lean_inc_ref(v_inst_3715_);
lean_inc(v_toBind_3708_);
lean_inc_ref(v_discrs_x27_3704_);
v___f_3732_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56___boxed), 33, 32);
lean_closure_set(v___f_3732_, 0, v_numParams_3695_);
lean_closure_set(v___f_3732_, 1, v_numDiscrs_3696_);
lean_closure_set(v___f_3732_, 2, v_altInfos_3697_);
lean_closure_set(v___f_3732_, 3, v_uElimPos_x3f_3698_);
lean_closure_set(v___f_3732_, 4, v_snd_3699_);
lean_closure_set(v___f_3732_, 5, v_overlaps_3700_);
lean_closure_set(v___f_3732_, 6, v_matcherName_3701_);
lean_closure_set(v___f_3732_, 7, v_matcherLevels_3726_);
lean_closure_set(v___f_3732_, 8, v_params_x27_3702_);
lean_closure_set(v___f_3732_, 9, v_fst_3703_);
lean_closure_set(v___f_3732_, 10, v_discrs_x27_3704_);
lean_closure_set(v___f_3732_, 11, v_toPure_3705_);
lean_closure_set(v___f_3732_, 12, v_onRemaining_3706_);
lean_closure_set(v___f_3732_, 13, v_remaining_3707_);
lean_closure_set(v___f_3732_, 14, v_toBind_3708_);
lean_closure_set(v___f_3732_, 15, v_inst_3709_);
lean_closure_set(v___f_3732_, 16, v_alts_3710_);
lean_closure_set(v___f_3732_, 17, v___f_3711_);
lean_closure_set(v___f_3732_, 18, v___x_3729_);
lean_closure_set(v___f_3732_, 19, v_inst_3713_);
lean_closure_set(v___f_3732_, 20, v_remaining_x27_3728_);
lean_closure_set(v___f_3732_, 21, v_onAlt_3714_);
lean_closure_set(v___f_3732_, 22, v_inst_3715_);
lean_closure_set(v___f_3732_, 23, v___f_3716_);
lean_closure_set(v___f_3732_, 24, v_matcherApp_3717_);
lean_closure_set(v___f_3732_, 25, v___x_3727_);
lean_closure_set(v___f_3732_, 26, v___x_3730_);
lean_closure_set(v___f_3732_, 27, v___x_3731_);
lean_closure_set(v___f_3732_, 28, v___f_3720_);
lean_closure_set(v___f_3732_, 29, v_inst_3721_);
lean_closure_set(v___f_3732_, 30, v___f_3722_);
lean_closure_set(v___f_3732_, 31, v_numDiscrEqs_3723_);
v___x_3733_ = l_Array_reverse___redArg(v_fst_3724_);
v___x_3734_ = lean_array_get_size(v___x_3733_);
v___x_3735_ = l_Array_toSubarray___redArg(v___x_3733_, v___x_3727_, v___x_3734_);
v___x_3736_ = l_Array_reverse___redArg(v_discrs_x27_3704_);
v___x_3737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3727_);
lean_ctor_set(v___x_3737_, 1, v___x_3735_);
v___x_3738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3738_, 0, v_remaining_x27_3728_);
lean_ctor_set(v___x_3738_, 1, v___x_3737_);
v_sz_3739_ = lean_array_size(v___x_3736_);
v___x_3740_ = ((size_t)0ULL);
v___x_3741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3715_, v___x_3736_, v___f_3725_, v_sz_3739_, v___x_3740_, v___x_3738_);
v___x_3742_ = lean_apply_4(v_toBind_3708_, lean_box(0), lean_box(0), v___x_3741_, v___f_3732_);
return v___x_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed(lean_object** _args){
lean_object* v_numParams_3743_ = _args[0];
lean_object* v_numDiscrs_3744_ = _args[1];
lean_object* v_altInfos_3745_ = _args[2];
lean_object* v_uElimPos_x3f_3746_ = _args[3];
lean_object* v_snd_3747_ = _args[4];
lean_object* v_overlaps_3748_ = _args[5];
lean_object* v_matcherName_3749_ = _args[6];
lean_object* v_params_x27_3750_ = _args[7];
lean_object* v_fst_3751_ = _args[8];
lean_object* v_discrs_x27_3752_ = _args[9];
lean_object* v_toPure_3753_ = _args[10];
lean_object* v_onRemaining_3754_ = _args[11];
lean_object* v_remaining_3755_ = _args[12];
lean_object* v_toBind_3756_ = _args[13];
lean_object* v_inst_3757_ = _args[14];
lean_object* v_alts_3758_ = _args[15];
lean_object* v___f_3759_ = _args[16];
lean_object* v___x_3760_ = _args[17];
lean_object* v_inst_3761_ = _args[18];
lean_object* v_onAlt_3762_ = _args[19];
lean_object* v_inst_3763_ = _args[20];
lean_object* v___f_3764_ = _args[21];
lean_object* v_matcherApp_3765_ = _args[22];
lean_object* v_useSplitter_3766_ = _args[23];
lean_object* v_isCasesOn_3767_ = _args[24];
lean_object* v___f_3768_ = _args[25];
lean_object* v_inst_3769_ = _args[26];
lean_object* v___f_3770_ = _args[27];
lean_object* v_numDiscrEqs_3771_ = _args[28];
lean_object* v_fst_3772_ = _args[29];
lean_object* v___f_3773_ = _args[30];
lean_object* v_matcherLevels_3774_ = _args[31];
_start:
{
uint8_t v___x_16732__boxed_3775_; uint8_t v_useSplitter_boxed_3776_; uint8_t v_isCasesOn_boxed_3777_; lean_object* v_res_3778_; 
v___x_16732__boxed_3775_ = lean_unbox(v___x_3760_);
v_useSplitter_boxed_3776_ = lean_unbox(v_useSplitter_3766_);
v_isCasesOn_boxed_3777_ = lean_unbox(v_isCasesOn_3767_);
v_res_3778_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__54(v_numParams_3743_, v_numDiscrs_3744_, v_altInfos_3745_, v_uElimPos_x3f_3746_, v_snd_3747_, v_overlaps_3748_, v_matcherName_3749_, v_params_x27_3750_, v_fst_3751_, v_discrs_x27_3752_, v_toPure_3753_, v_onRemaining_3754_, v_remaining_3755_, v_toBind_3756_, v_inst_3757_, v_alts_3758_, v___f_3759_, v___x_16732__boxed_3775_, v_inst_3761_, v_onAlt_3762_, v_inst_3763_, v___f_3764_, v_matcherApp_3765_, v_useSplitter_boxed_3776_, v_isCasesOn_boxed_3777_, v___f_3768_, v_inst_3769_, v___f_3770_, v_numDiscrEqs_3771_, v_fst_3772_, v___f_3773_, v_matcherLevels_3774_);
return v_res_3778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55(lean_object* v___f_3779_, lean_object* v_matcherLevels_3780_){
_start:
{
lean_object* v___x_3781_; 
v___x_3781_ = lean_apply_1(v___f_3779_, v_matcherLevels_3780_);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58(lean_object* v_toMatcherInfo_3782_, lean_object* v_matcherName_3783_, lean_object* v_params_x27_3784_, lean_object* v_discrs_x27_3785_, lean_object* v_toPure_3786_, lean_object* v_onRemaining_3787_, lean_object* v_remaining_3788_, lean_object* v_toBind_3789_, lean_object* v_inst_3790_, lean_object* v_alts_3791_, lean_object* v___f_3792_, uint8_t v___x_3793_, lean_object* v_inst_3794_, lean_object* v_onAlt_3795_, lean_object* v_inst_3796_, lean_object* v___f_3797_, lean_object* v_matcherApp_3798_, uint8_t v_useSplitter_3799_, uint8_t v_isCasesOn_3800_, lean_object* v___f_3801_, lean_object* v_inst_3802_, lean_object* v___f_3803_, lean_object* v_numDiscrEqs_3804_, lean_object* v___f_3805_, lean_object* v_matcherLevels_3806_, lean_object* v_____x_3807_){
_start:
{
lean_object* v_snd_3808_; lean_object* v_snd_3809_; lean_object* v_fst_3810_; lean_object* v_fst_3811_; lean_object* v_fst_3812_; lean_object* v_snd_3813_; lean_object* v_numParams_3814_; lean_object* v_numDiscrs_3815_; lean_object* v_altInfos_3816_; lean_object* v_uElimPos_x3f_3817_; lean_object* v_overlaps_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___f_3822_; 
v_snd_3808_ = lean_ctor_get(v_____x_3807_, 1);
lean_inc(v_snd_3808_);
v_snd_3809_ = lean_ctor_get(v_snd_3808_, 1);
lean_inc(v_snd_3809_);
v_fst_3810_ = lean_ctor_get(v_____x_3807_, 0);
lean_inc(v_fst_3810_);
lean_dec_ref(v_____x_3807_);
v_fst_3811_ = lean_ctor_get(v_snd_3808_, 0);
lean_inc(v_fst_3811_);
lean_dec(v_snd_3808_);
v_fst_3812_ = lean_ctor_get(v_snd_3809_, 0);
lean_inc(v_fst_3812_);
v_snd_3813_ = lean_ctor_get(v_snd_3809_, 1);
lean_inc(v_snd_3813_);
lean_dec(v_snd_3809_);
v_numParams_3814_ = lean_ctor_get(v_toMatcherInfo_3782_, 0);
lean_inc(v_numParams_3814_);
v_numDiscrs_3815_ = lean_ctor_get(v_toMatcherInfo_3782_, 1);
lean_inc(v_numDiscrs_3815_);
v_altInfos_3816_ = lean_ctor_get(v_toMatcherInfo_3782_, 2);
lean_inc_ref(v_altInfos_3816_);
v_uElimPos_x3f_3817_ = lean_ctor_get(v_toMatcherInfo_3782_, 3);
lean_inc(v_uElimPos_x3f_3817_);
v_overlaps_3818_ = lean_ctor_get(v_toMatcherInfo_3782_, 5);
lean_inc_ref(v_overlaps_3818_);
lean_dec_ref(v_toMatcherInfo_3782_);
v___x_3819_ = lean_box(v___x_3793_);
v___x_3820_ = lean_box(v_useSplitter_3799_);
v___x_3821_ = lean_box(v_isCasesOn_3800_);
lean_inc(v_toBind_3789_);
lean_inc(v_toPure_3786_);
lean_inc(v_uElimPos_x3f_3817_);
v___f_3822_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed), 32, 31);
lean_closure_set(v___f_3822_, 0, v_numParams_3814_);
lean_closure_set(v___f_3822_, 1, v_numDiscrs_3815_);
lean_closure_set(v___f_3822_, 2, v_altInfos_3816_);
lean_closure_set(v___f_3822_, 3, v_uElimPos_x3f_3817_);
lean_closure_set(v___f_3822_, 4, v_snd_3813_);
lean_closure_set(v___f_3822_, 5, v_overlaps_3818_);
lean_closure_set(v___f_3822_, 6, v_matcherName_3783_);
lean_closure_set(v___f_3822_, 7, v_params_x27_3784_);
lean_closure_set(v___f_3822_, 8, v_fst_3810_);
lean_closure_set(v___f_3822_, 9, v_discrs_x27_3785_);
lean_closure_set(v___f_3822_, 10, v_toPure_3786_);
lean_closure_set(v___f_3822_, 11, v_onRemaining_3787_);
lean_closure_set(v___f_3822_, 12, v_remaining_3788_);
lean_closure_set(v___f_3822_, 13, v_toBind_3789_);
lean_closure_set(v___f_3822_, 14, v_inst_3790_);
lean_closure_set(v___f_3822_, 15, v_alts_3791_);
lean_closure_set(v___f_3822_, 16, v___f_3792_);
lean_closure_set(v___f_3822_, 17, v___x_3819_);
lean_closure_set(v___f_3822_, 18, v_inst_3794_);
lean_closure_set(v___f_3822_, 19, v_onAlt_3795_);
lean_closure_set(v___f_3822_, 20, v_inst_3796_);
lean_closure_set(v___f_3822_, 21, v___f_3797_);
lean_closure_set(v___f_3822_, 22, v_matcherApp_3798_);
lean_closure_set(v___f_3822_, 23, v___x_3820_);
lean_closure_set(v___f_3822_, 24, v___x_3821_);
lean_closure_set(v___f_3822_, 25, v___f_3801_);
lean_closure_set(v___f_3822_, 26, v_inst_3802_);
lean_closure_set(v___f_3822_, 27, v___f_3803_);
lean_closure_set(v___f_3822_, 28, v_numDiscrEqs_3804_);
lean_closure_set(v___f_3822_, 29, v_fst_3812_);
lean_closure_set(v___f_3822_, 30, v___f_3805_);
if (lean_obj_tag(v_uElimPos_x3f_3817_) == 0)
{
lean_object* v___f_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; 
lean_dec(v_fst_3811_);
v___f_3823_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55), 2, 1);
lean_closure_set(v___f_3823_, 0, v___f_3822_);
v___x_3824_ = lean_apply_2(v_toPure_3786_, lean_box(0), v_matcherLevels_3806_);
v___x_3825_ = lean_apply_4(v_toBind_3789_, lean_box(0), lean_box(0), v___x_3824_, v___f_3823_);
return v___x_3825_;
}
else
{
lean_object* v_val_3826_; lean_object* v___f_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; 
v_val_3826_ = lean_ctor_get(v_uElimPos_x3f_3817_, 0);
lean_inc(v_val_3826_);
lean_dec_ref(v_uElimPos_x3f_3817_);
v___f_3827_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55), 2, 1);
lean_closure_set(v___f_3827_, 0, v___f_3822_);
v___x_3828_ = lean_array_set(v_matcherLevels_3806_, v_val_3826_, v_fst_3811_);
lean_dec(v_val_3826_);
v___x_3829_ = lean_apply_2(v_toPure_3786_, lean_box(0), v___x_3828_);
v___x_3830_ = lean_apply_4(v_toBind_3789_, lean_box(0), lean_box(0), v___x_3829_, v___f_3827_);
return v___x_3830_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed(lean_object** _args){
lean_object* v_toMatcherInfo_3831_ = _args[0];
lean_object* v_matcherName_3832_ = _args[1];
lean_object* v_params_x27_3833_ = _args[2];
lean_object* v_discrs_x27_3834_ = _args[3];
lean_object* v_toPure_3835_ = _args[4];
lean_object* v_onRemaining_3836_ = _args[5];
lean_object* v_remaining_3837_ = _args[6];
lean_object* v_toBind_3838_ = _args[7];
lean_object* v_inst_3839_ = _args[8];
lean_object* v_alts_3840_ = _args[9];
lean_object* v___f_3841_ = _args[10];
lean_object* v___x_3842_ = _args[11];
lean_object* v_inst_3843_ = _args[12];
lean_object* v_onAlt_3844_ = _args[13];
lean_object* v_inst_3845_ = _args[14];
lean_object* v___f_3846_ = _args[15];
lean_object* v_matcherApp_3847_ = _args[16];
lean_object* v_useSplitter_3848_ = _args[17];
lean_object* v_isCasesOn_3849_ = _args[18];
lean_object* v___f_3850_ = _args[19];
lean_object* v_inst_3851_ = _args[20];
lean_object* v___f_3852_ = _args[21];
lean_object* v_numDiscrEqs_3853_ = _args[22];
lean_object* v___f_3854_ = _args[23];
lean_object* v_matcherLevels_3855_ = _args[24];
lean_object* v_____x_3856_ = _args[25];
_start:
{
uint8_t v___x_16801__boxed_3857_; uint8_t v_useSplitter_boxed_3858_; uint8_t v_isCasesOn_boxed_3859_; lean_object* v_res_3860_; 
v___x_16801__boxed_3857_ = lean_unbox(v___x_3842_);
v_useSplitter_boxed_3858_ = lean_unbox(v_useSplitter_3848_);
v_isCasesOn_boxed_3859_ = lean_unbox(v_isCasesOn_3849_);
v_res_3860_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__58(v_toMatcherInfo_3831_, v_matcherName_3832_, v_params_x27_3833_, v_discrs_x27_3834_, v_toPure_3835_, v_onRemaining_3836_, v_remaining_3837_, v_toBind_3838_, v_inst_3839_, v_alts_3840_, v___f_3841_, v___x_16801__boxed_3857_, v_inst_3843_, v_onAlt_3844_, v_inst_3845_, v___f_3846_, v_matcherApp_3847_, v_useSplitter_boxed_3858_, v_isCasesOn_boxed_3859_, v___f_3850_, v_inst_3851_, v___f_3852_, v_numDiscrEqs_3853_, v___f_3854_, v_matcherLevels_3855_, v_____x_3856_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57(lean_object* v_toPure_3861_, lean_object* v_inst_3862_, lean_object* v_toBind_3863_, lean_object* v_toMatcherInfo_3864_, lean_object* v_inst_3865_, lean_object* v___f_3866_, lean_object* v_onMotive_3867_, lean_object* v_discrs_3868_, lean_object* v_inst_3869_, lean_object* v_matcherName_3870_, lean_object* v_params_x27_3871_, lean_object* v_onRemaining_3872_, lean_object* v_remaining_3873_, lean_object* v_inst_3874_, lean_object* v_alts_3875_, lean_object* v___f_3876_, lean_object* v_onAlt_3877_, lean_object* v___f_3878_, lean_object* v_matcherApp_3879_, uint8_t v_useSplitter_3880_, uint8_t v_isCasesOn_3881_, lean_object* v___f_3882_, lean_object* v___f_3883_, lean_object* v_numDiscrEqs_3884_, lean_object* v___f_3885_, lean_object* v_matcherLevels_3886_, lean_object* v_motive_3887_, lean_object* v_discrs_x27_3888_){
_start:
{
lean_object* v___f_3889_; uint8_t v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___f_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
lean_inc_ref(v_inst_3869_);
lean_inc_ref(v_inst_3865_);
lean_inc_ref(v_discrs_x27_3888_);
lean_inc_ref(v_toMatcherInfo_3864_);
lean_inc(v_toBind_3863_);
lean_inc(v_inst_3862_);
lean_inc(v_toPure_3861_);
v___f_3889_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__19___boxed), 12, 10);
lean_closure_set(v___f_3889_, 0, v_toPure_3861_);
lean_closure_set(v___f_3889_, 1, v_inst_3862_);
lean_closure_set(v___f_3889_, 2, v_toBind_3863_);
lean_closure_set(v___f_3889_, 3, v_toMatcherInfo_3864_);
lean_closure_set(v___f_3889_, 4, v_discrs_x27_3888_);
lean_closure_set(v___f_3889_, 5, v_inst_3865_);
lean_closure_set(v___f_3889_, 6, v___f_3866_);
lean_closure_set(v___f_3889_, 7, v_onMotive_3867_);
lean_closure_set(v___f_3889_, 8, v_discrs_3868_);
lean_closure_set(v___f_3889_, 9, v_inst_3869_);
v___x_3890_ = 0;
v___x_3891_ = lean_box(v___x_3890_);
v___x_3892_ = lean_box(v_useSplitter_3880_);
v___x_3893_ = lean_box(v_isCasesOn_3881_);
lean_inc_ref(v_inst_3865_);
lean_inc_ref(v_inst_3874_);
lean_inc(v_toBind_3863_);
v___f_3894_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed), 26, 25);
lean_closure_set(v___f_3894_, 0, v_toMatcherInfo_3864_);
lean_closure_set(v___f_3894_, 1, v_matcherName_3870_);
lean_closure_set(v___f_3894_, 2, v_params_x27_3871_);
lean_closure_set(v___f_3894_, 3, v_discrs_x27_3888_);
lean_closure_set(v___f_3894_, 4, v_toPure_3861_);
lean_closure_set(v___f_3894_, 5, v_onRemaining_3872_);
lean_closure_set(v___f_3894_, 6, v_remaining_3873_);
lean_closure_set(v___f_3894_, 7, v_toBind_3863_);
lean_closure_set(v___f_3894_, 8, v_inst_3874_);
lean_closure_set(v___f_3894_, 9, v_alts_3875_);
lean_closure_set(v___f_3894_, 10, v___f_3876_);
lean_closure_set(v___f_3894_, 11, v___x_3891_);
lean_closure_set(v___f_3894_, 12, v_inst_3862_);
lean_closure_set(v___f_3894_, 13, v_onAlt_3877_);
lean_closure_set(v___f_3894_, 14, v_inst_3865_);
lean_closure_set(v___f_3894_, 15, v___f_3878_);
lean_closure_set(v___f_3894_, 16, v_matcherApp_3879_);
lean_closure_set(v___f_3894_, 17, v___x_3892_);
lean_closure_set(v___f_3894_, 18, v___x_3893_);
lean_closure_set(v___f_3894_, 19, v___f_3882_);
lean_closure_set(v___f_3894_, 20, v_inst_3869_);
lean_closure_set(v___f_3894_, 21, v___f_3883_);
lean_closure_set(v___f_3894_, 22, v_numDiscrEqs_3884_);
lean_closure_set(v___f_3894_, 23, v___f_3885_);
lean_closure_set(v___f_3894_, 24, v_matcherLevels_3886_);
v___x_3895_ = l_Lean_Meta_lambdaTelescope___redArg(v_inst_3874_, v_inst_3865_, v_motive_3887_, v___f_3889_, v___x_3890_);
v___x_3896_ = lean_apply_4(v_toBind_3863_, lean_box(0), lean_box(0), v___x_3895_, v___f_3894_);
return v___x_3896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed(lean_object** _args){
lean_object* v_toPure_3897_ = _args[0];
lean_object* v_inst_3898_ = _args[1];
lean_object* v_toBind_3899_ = _args[2];
lean_object* v_toMatcherInfo_3900_ = _args[3];
lean_object* v_inst_3901_ = _args[4];
lean_object* v___f_3902_ = _args[5];
lean_object* v_onMotive_3903_ = _args[6];
lean_object* v_discrs_3904_ = _args[7];
lean_object* v_inst_3905_ = _args[8];
lean_object* v_matcherName_3906_ = _args[9];
lean_object* v_params_x27_3907_ = _args[10];
lean_object* v_onRemaining_3908_ = _args[11];
lean_object* v_remaining_3909_ = _args[12];
lean_object* v_inst_3910_ = _args[13];
lean_object* v_alts_3911_ = _args[14];
lean_object* v___f_3912_ = _args[15];
lean_object* v_onAlt_3913_ = _args[16];
lean_object* v___f_3914_ = _args[17];
lean_object* v_matcherApp_3915_ = _args[18];
lean_object* v_useSplitter_3916_ = _args[19];
lean_object* v_isCasesOn_3917_ = _args[20];
lean_object* v___f_3918_ = _args[21];
lean_object* v___f_3919_ = _args[22];
lean_object* v_numDiscrEqs_3920_ = _args[23];
lean_object* v___f_3921_ = _args[24];
lean_object* v_matcherLevels_3922_ = _args[25];
lean_object* v_motive_3923_ = _args[26];
lean_object* v_discrs_x27_3924_ = _args[27];
_start:
{
uint8_t v_useSplitter_boxed_3925_; uint8_t v_isCasesOn_boxed_3926_; lean_object* v_res_3927_; 
v_useSplitter_boxed_3925_ = lean_unbox(v_useSplitter_3916_);
v_isCasesOn_boxed_3926_ = lean_unbox(v_isCasesOn_3917_);
v_res_3927_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__57(v_toPure_3897_, v_inst_3898_, v_toBind_3899_, v_toMatcherInfo_3900_, v_inst_3901_, v___f_3902_, v_onMotive_3903_, v_discrs_3904_, v_inst_3905_, v_matcherName_3906_, v_params_x27_3907_, v_onRemaining_3908_, v_remaining_3909_, v_inst_3910_, v_alts_3911_, v___f_3912_, v_onAlt_3913_, v___f_3914_, v_matcherApp_3915_, v_useSplitter_boxed_3925_, v_isCasesOn_boxed_3926_, v___f_3918_, v___f_3919_, v_numDiscrEqs_3920_, v___f_3921_, v_matcherLevels_3922_, v_motive_3923_, v_discrs_x27_3924_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59(lean_object* v_toPure_3928_, lean_object* v_inst_3929_, lean_object* v_toBind_3930_, lean_object* v_toMatcherInfo_3931_, lean_object* v_inst_3932_, lean_object* v___f_3933_, lean_object* v_onMotive_3934_, lean_object* v_discrs_3935_, lean_object* v_inst_3936_, lean_object* v_matcherName_3937_, lean_object* v_onRemaining_3938_, lean_object* v_remaining_3939_, lean_object* v_inst_3940_, lean_object* v_alts_3941_, lean_object* v___f_3942_, lean_object* v_onAlt_3943_, lean_object* v___f_3944_, lean_object* v_matcherApp_3945_, uint8_t v_useSplitter_3946_, uint8_t v_isCasesOn_3947_, lean_object* v___f_3948_, lean_object* v___f_3949_, lean_object* v_numDiscrEqs_3950_, lean_object* v___f_3951_, lean_object* v_matcherLevels_3952_, lean_object* v_motive_3953_, lean_object* v_onParams_3954_, lean_object* v_params_x27_3955_){
_start:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___f_3958_; size_t v_sz_3959_; size_t v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3956_ = lean_box(v_useSplitter_3946_);
v___x_3957_ = lean_box(v_isCasesOn_3947_);
lean_inc_ref(v_discrs_3935_);
lean_inc_ref(v_inst_3932_);
lean_inc(v_toBind_3930_);
v___f_3958_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed), 28, 27);
lean_closure_set(v___f_3958_, 0, v_toPure_3928_);
lean_closure_set(v___f_3958_, 1, v_inst_3929_);
lean_closure_set(v___f_3958_, 2, v_toBind_3930_);
lean_closure_set(v___f_3958_, 3, v_toMatcherInfo_3931_);
lean_closure_set(v___f_3958_, 4, v_inst_3932_);
lean_closure_set(v___f_3958_, 5, v___f_3933_);
lean_closure_set(v___f_3958_, 6, v_onMotive_3934_);
lean_closure_set(v___f_3958_, 7, v_discrs_3935_);
lean_closure_set(v___f_3958_, 8, v_inst_3936_);
lean_closure_set(v___f_3958_, 9, v_matcherName_3937_);
lean_closure_set(v___f_3958_, 10, v_params_x27_3955_);
lean_closure_set(v___f_3958_, 11, v_onRemaining_3938_);
lean_closure_set(v___f_3958_, 12, v_remaining_3939_);
lean_closure_set(v___f_3958_, 13, v_inst_3940_);
lean_closure_set(v___f_3958_, 14, v_alts_3941_);
lean_closure_set(v___f_3958_, 15, v___f_3942_);
lean_closure_set(v___f_3958_, 16, v_onAlt_3943_);
lean_closure_set(v___f_3958_, 17, v___f_3944_);
lean_closure_set(v___f_3958_, 18, v_matcherApp_3945_);
lean_closure_set(v___f_3958_, 19, v___x_3956_);
lean_closure_set(v___f_3958_, 20, v___x_3957_);
lean_closure_set(v___f_3958_, 21, v___f_3948_);
lean_closure_set(v___f_3958_, 22, v___f_3949_);
lean_closure_set(v___f_3958_, 23, v_numDiscrEqs_3950_);
lean_closure_set(v___f_3958_, 24, v___f_3951_);
lean_closure_set(v___f_3958_, 25, v_matcherLevels_3952_);
lean_closure_set(v___f_3958_, 26, v_motive_3953_);
v_sz_3959_ = lean_array_size(v_discrs_3935_);
v___x_3960_ = ((size_t)0ULL);
v___x_3961_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_3932_, v_onParams_3954_, v_sz_3959_, v___x_3960_, v_discrs_3935_);
v___x_3962_ = lean_apply_4(v_toBind_3930_, lean_box(0), lean_box(0), v___x_3961_, v___f_3958_);
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
lean_object* v___f_3984_ = _args[21];
lean_object* v_numDiscrEqs_3985_ = _args[22];
lean_object* v___f_3986_ = _args[23];
lean_object* v_matcherLevels_3987_ = _args[24];
lean_object* v_motive_3988_ = _args[25];
lean_object* v_onParams_3989_ = _args[26];
lean_object* v_params_x27_3990_ = _args[27];
_start:
{
uint8_t v_useSplitter_boxed_3991_; uint8_t v_isCasesOn_boxed_3992_; lean_object* v_res_3993_; 
v_useSplitter_boxed_3991_ = lean_unbox(v_useSplitter_3981_);
v_isCasesOn_boxed_3992_ = lean_unbox(v_isCasesOn_3982_);
v_res_3993_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__59(v_toPure_3963_, v_inst_3964_, v_toBind_3965_, v_toMatcherInfo_3966_, v_inst_3967_, v___f_3968_, v_onMotive_3969_, v_discrs_3970_, v_inst_3971_, v_matcherName_3972_, v_onRemaining_3973_, v_remaining_3974_, v_inst_3975_, v_alts_3976_, v___f_3977_, v_onAlt_3978_, v___f_3979_, v_matcherApp_3980_, v_useSplitter_boxed_3991_, v_isCasesOn_boxed_3992_, v___f_3983_, v___f_3984_, v_numDiscrEqs_3985_, v___f_3986_, v_matcherLevels_3987_, v_motive_3988_, v_onParams_3989_, v_params_x27_3990_);
return v_res_3993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60(lean_object* v_toPure_3994_, lean_object* v_inst_3995_, lean_object* v_toBind_3996_, lean_object* v_toMatcherInfo_3997_, lean_object* v_inst_3998_, lean_object* v___f_3999_, lean_object* v_onMotive_4000_, lean_object* v_discrs_4001_, lean_object* v_inst_4002_, lean_object* v_matcherName_4003_, lean_object* v_onRemaining_4004_, lean_object* v_remaining_4005_, lean_object* v_inst_4006_, lean_object* v_alts_4007_, lean_object* v___f_4008_, lean_object* v_onAlt_4009_, lean_object* v___f_4010_, lean_object* v_matcherApp_4011_, uint8_t v_useSplitter_4012_, uint8_t v_isCasesOn_4013_, lean_object* v___f_4014_, lean_object* v___f_4015_, lean_object* v___f_4016_, lean_object* v_matcherLevels_4017_, lean_object* v_motive_4018_, lean_object* v_onParams_4019_, lean_object* v_params_4020_, lean_object* v_numDiscrEqs_4021_){
_start:
{
lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___f_4024_; size_t v_sz_4025_; size_t v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4022_ = lean_box(v_useSplitter_4012_);
v___x_4023_ = lean_box(v_isCasesOn_4013_);
lean_inc(v_onParams_4019_);
lean_inc_ref(v_inst_3998_);
lean_inc(v_toBind_3996_);
v___f_4024_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed), 28, 27);
lean_closure_set(v___f_4024_, 0, v_toPure_3994_);
lean_closure_set(v___f_4024_, 1, v_inst_3995_);
lean_closure_set(v___f_4024_, 2, v_toBind_3996_);
lean_closure_set(v___f_4024_, 3, v_toMatcherInfo_3997_);
lean_closure_set(v___f_4024_, 4, v_inst_3998_);
lean_closure_set(v___f_4024_, 5, v___f_3999_);
lean_closure_set(v___f_4024_, 6, v_onMotive_4000_);
lean_closure_set(v___f_4024_, 7, v_discrs_4001_);
lean_closure_set(v___f_4024_, 8, v_inst_4002_);
lean_closure_set(v___f_4024_, 9, v_matcherName_4003_);
lean_closure_set(v___f_4024_, 10, v_onRemaining_4004_);
lean_closure_set(v___f_4024_, 11, v_remaining_4005_);
lean_closure_set(v___f_4024_, 12, v_inst_4006_);
lean_closure_set(v___f_4024_, 13, v_alts_4007_);
lean_closure_set(v___f_4024_, 14, v___f_4008_);
lean_closure_set(v___f_4024_, 15, v_onAlt_4009_);
lean_closure_set(v___f_4024_, 16, v___f_4010_);
lean_closure_set(v___f_4024_, 17, v_matcherApp_4011_);
lean_closure_set(v___f_4024_, 18, v___x_4022_);
lean_closure_set(v___f_4024_, 19, v___x_4023_);
lean_closure_set(v___f_4024_, 20, v___f_4014_);
lean_closure_set(v___f_4024_, 21, v___f_4015_);
lean_closure_set(v___f_4024_, 22, v_numDiscrEqs_4021_);
lean_closure_set(v___f_4024_, 23, v___f_4016_);
lean_closure_set(v___f_4024_, 24, v_matcherLevels_4017_);
lean_closure_set(v___f_4024_, 25, v_motive_4018_);
lean_closure_set(v___f_4024_, 26, v_onParams_4019_);
v_sz_4025_ = lean_array_size(v_params_4020_);
v___x_4026_ = ((size_t)0ULL);
v___x_4027_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_3998_, v_onParams_4019_, v_sz_4025_, v___x_4026_, v_params_4020_);
v___x_4028_ = lean_apply_4(v_toBind_3996_, lean_box(0), lean_box(0), v___x_4027_, v___f_4024_);
return v___x_4028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed(lean_object** _args){
lean_object* v_toPure_4029_ = _args[0];
lean_object* v_inst_4030_ = _args[1];
lean_object* v_toBind_4031_ = _args[2];
lean_object* v_toMatcherInfo_4032_ = _args[3];
lean_object* v_inst_4033_ = _args[4];
lean_object* v___f_4034_ = _args[5];
lean_object* v_onMotive_4035_ = _args[6];
lean_object* v_discrs_4036_ = _args[7];
lean_object* v_inst_4037_ = _args[8];
lean_object* v_matcherName_4038_ = _args[9];
lean_object* v_onRemaining_4039_ = _args[10];
lean_object* v_remaining_4040_ = _args[11];
lean_object* v_inst_4041_ = _args[12];
lean_object* v_alts_4042_ = _args[13];
lean_object* v___f_4043_ = _args[14];
lean_object* v_onAlt_4044_ = _args[15];
lean_object* v___f_4045_ = _args[16];
lean_object* v_matcherApp_4046_ = _args[17];
lean_object* v_useSplitter_4047_ = _args[18];
lean_object* v_isCasesOn_4048_ = _args[19];
lean_object* v___f_4049_ = _args[20];
lean_object* v___f_4050_ = _args[21];
lean_object* v___f_4051_ = _args[22];
lean_object* v_matcherLevels_4052_ = _args[23];
lean_object* v_motive_4053_ = _args[24];
lean_object* v_onParams_4054_ = _args[25];
lean_object* v_params_4055_ = _args[26];
lean_object* v_numDiscrEqs_4056_ = _args[27];
_start:
{
uint8_t v_useSplitter_boxed_4057_; uint8_t v_isCasesOn_boxed_4058_; lean_object* v_res_4059_; 
v_useSplitter_boxed_4057_ = lean_unbox(v_useSplitter_4047_);
v_isCasesOn_boxed_4058_ = lean_unbox(v_isCasesOn_4048_);
v_res_4059_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__60(v_toPure_4029_, v_inst_4030_, v_toBind_4031_, v_toMatcherInfo_4032_, v_inst_4033_, v___f_4034_, v_onMotive_4035_, v_discrs_4036_, v_inst_4037_, v_matcherName_4038_, v_onRemaining_4039_, v_remaining_4040_, v_inst_4041_, v_alts_4042_, v___f_4043_, v_onAlt_4044_, v___f_4045_, v_matcherApp_4046_, v_useSplitter_boxed_4057_, v_isCasesOn_boxed_4058_, v___f_4049_, v___f_4050_, v___f_4051_, v_matcherLevels_4052_, v_motive_4053_, v_onParams_4054_, v_params_4055_, v_numDiscrEqs_4056_);
return v_res_4059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__61(lean_object* v___f_4060_, lean_object* v_numDiscrEqs_4061_){
_start:
{
lean_object* v___x_4062_; 
v___x_4062_ = lean_apply_1(v___f_4060_, v_numDiscrEqs_4061_);
return v___x_4062_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1(void){
_start:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4064_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__0));
v___x_4065_ = l_Lean_stringToMessageData(v___x_4064_);
return v___x_4065_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3(void){
_start:
{
lean_object* v___x_4067_; lean_object* v___x_4068_; 
v___x_4067_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__2));
v___x_4068_ = l_Lean_stringToMessageData(v___x_4067_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63(lean_object* v_matcherName_4069_, lean_object* v_inst_4070_, lean_object* v_inst_4071_, lean_object* v_toBind_4072_, lean_object* v___f_4073_, lean_object* v_toPure_4074_, lean_object* v___f_4075_, lean_object* v_____do__lift_4076_){
_start:
{
if (lean_obj_tag(v_____do__lift_4076_) == 0)
{
lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
lean_dec(v___f_4075_);
lean_dec(v_toPure_4074_);
v___x_4077_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1);
v___x_4078_ = l_Lean_MessageData_ofName(v_matcherName_4069_);
v___x_4079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4079_, 0, v___x_4077_);
lean_ctor_set(v___x_4079_, 1, v___x_4078_);
v___x_4080_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3);
v___x_4081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4079_);
lean_ctor_set(v___x_4081_, 1, v___x_4080_);
v___x_4082_ = l_Lean_throwError___redArg(v_inst_4070_, v_inst_4071_, v___x_4081_);
v___x_4083_ = lean_apply_4(v_toBind_4072_, lean_box(0), lean_box(0), v___x_4082_, v___f_4073_);
return v___x_4083_;
}
else
{
lean_object* v_val_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
lean_dec(v___f_4073_);
lean_dec_ref(v_inst_4071_);
lean_dec_ref(v_inst_4070_);
lean_dec(v_matcherName_4069_);
v_val_4084_ = lean_ctor_get(v_____do__lift_4076_, 0);
v___x_4085_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_4084_);
v___x_4086_ = lean_apply_2(v_toPure_4074_, lean_box(0), v___x_4085_);
v___x_4087_ = lean_apply_4(v_toBind_4072_, lean_box(0), lean_box(0), v___x_4086_, v___f_4075_);
return v___x_4087_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed(lean_object* v_matcherName_4088_, lean_object* v_inst_4089_, lean_object* v_inst_4090_, lean_object* v_toBind_4091_, lean_object* v___f_4092_, lean_object* v_toPure_4093_, lean_object* v___f_4094_, lean_object* v_____do__lift_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__63(v_matcherName_4088_, v_inst_4089_, v_inst_4090_, v_toBind_4091_, v___f_4092_, v_toPure_4093_, v___f_4094_, v_____do__lift_4095_);
lean_dec(v_____do__lift_4095_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64(lean_object* v_matcherApp_4097_, lean_object* v_toPure_4098_, lean_object* v_inst_4099_, lean_object* v_toBind_4100_, lean_object* v_inst_4101_, lean_object* v___f_4102_, lean_object* v_onMotive_4103_, lean_object* v_inst_4104_, lean_object* v_onRemaining_4105_, lean_object* v_inst_4106_, lean_object* v___f_4107_, lean_object* v_onAlt_4108_, lean_object* v___f_4109_, uint8_t v_useSplitter_4110_, lean_object* v___f_4111_, lean_object* v___f_4112_, lean_object* v___f_4113_, lean_object* v_onParams_4114_, lean_object* v_inst_4115_, lean_object* v_____do__lift_4116_){
_start:
{
lean_object* v_toMatcherInfo_4117_; lean_object* v_matcherName_4118_; lean_object* v_matcherLevels_4119_; lean_object* v_params_4120_; lean_object* v_motive_4121_; lean_object* v_discrs_4122_; lean_object* v_alts_4123_; lean_object* v_remaining_4124_; uint8_t v_isCasesOn_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___f_4128_; 
v_toMatcherInfo_4117_ = lean_ctor_get(v_matcherApp_4097_, 0);
lean_inc_ref(v_toMatcherInfo_4117_);
v_matcherName_4118_ = lean_ctor_get(v_matcherApp_4097_, 1);
lean_inc(v_matcherName_4118_);
v_matcherLevels_4119_ = lean_ctor_get(v_matcherApp_4097_, 2);
lean_inc_ref(v_matcherLevels_4119_);
v_params_4120_ = lean_ctor_get(v_matcherApp_4097_, 3);
lean_inc_ref(v_params_4120_);
v_motive_4121_ = lean_ctor_get(v_matcherApp_4097_, 4);
lean_inc_ref(v_motive_4121_);
v_discrs_4122_ = lean_ctor_get(v_matcherApp_4097_, 5);
lean_inc_ref(v_discrs_4122_);
v_alts_4123_ = lean_ctor_get(v_matcherApp_4097_, 6);
lean_inc_ref(v_alts_4123_);
v_remaining_4124_ = lean_ctor_get(v_matcherApp_4097_, 7);
lean_inc_ref(v_remaining_4124_);
lean_inc(v_matcherName_4118_);
v_isCasesOn_4125_ = l_Lean_isCasesOnRecursor(v_____do__lift_4116_, v_matcherName_4118_);
v___x_4126_ = lean_box(v_useSplitter_4110_);
v___x_4127_ = lean_box(v_isCasesOn_4125_);
lean_inc(v_matcherName_4118_);
lean_inc_ref(v_inst_4104_);
lean_inc_ref(v_inst_4101_);
lean_inc(v_toBind_4100_);
lean_inc(v_toPure_4098_);
v___f_4128_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed), 28, 27);
lean_closure_set(v___f_4128_, 0, v_toPure_4098_);
lean_closure_set(v___f_4128_, 1, v_inst_4099_);
lean_closure_set(v___f_4128_, 2, v_toBind_4100_);
lean_closure_set(v___f_4128_, 3, v_toMatcherInfo_4117_);
lean_closure_set(v___f_4128_, 4, v_inst_4101_);
lean_closure_set(v___f_4128_, 5, v___f_4102_);
lean_closure_set(v___f_4128_, 6, v_onMotive_4103_);
lean_closure_set(v___f_4128_, 7, v_discrs_4122_);
lean_closure_set(v___f_4128_, 8, v_inst_4104_);
lean_closure_set(v___f_4128_, 9, v_matcherName_4118_);
lean_closure_set(v___f_4128_, 10, v_onRemaining_4105_);
lean_closure_set(v___f_4128_, 11, v_remaining_4124_);
lean_closure_set(v___f_4128_, 12, v_inst_4106_);
lean_closure_set(v___f_4128_, 13, v_alts_4123_);
lean_closure_set(v___f_4128_, 14, v___f_4107_);
lean_closure_set(v___f_4128_, 15, v_onAlt_4108_);
lean_closure_set(v___f_4128_, 16, v___f_4109_);
lean_closure_set(v___f_4128_, 17, v_matcherApp_4097_);
lean_closure_set(v___f_4128_, 18, v___x_4126_);
lean_closure_set(v___f_4128_, 19, v___x_4127_);
lean_closure_set(v___f_4128_, 20, v___f_4111_);
lean_closure_set(v___f_4128_, 21, v___f_4112_);
lean_closure_set(v___f_4128_, 22, v___f_4113_);
lean_closure_set(v___f_4128_, 23, v_matcherLevels_4119_);
lean_closure_set(v___f_4128_, 24, v_motive_4121_);
lean_closure_set(v___f_4128_, 25, v_onParams_4114_);
lean_closure_set(v___f_4128_, 26, v_params_4120_);
if (v_isCasesOn_4125_ == 0)
{
lean_object* v___f_4129_; lean_object* v___f_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
v___f_4129_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61), 2, 1);
lean_closure_set(v___f_4129_, 0, v___f_4128_);
lean_inc_ref(v___f_4129_);
lean_inc(v_toBind_4100_);
lean_inc_ref(v_inst_4101_);
lean_inc(v_matcherName_4118_);
v___f_4130_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed), 8, 7);
lean_closure_set(v___f_4130_, 0, v_matcherName_4118_);
lean_closure_set(v___f_4130_, 1, v_inst_4101_);
lean_closure_set(v___f_4130_, 2, v_inst_4104_);
lean_closure_set(v___f_4130_, 3, v_toBind_4100_);
lean_closure_set(v___f_4130_, 4, v___f_4129_);
lean_closure_set(v___f_4130_, 5, v_toPure_4098_);
lean_closure_set(v___f_4130_, 6, v___f_4129_);
v___x_4131_ = l_Lean_Meta_getMatcherInfo_x3f___redArg(v_inst_4101_, v_inst_4115_, v_matcherName_4118_);
v___x_4132_ = lean_apply_4(v_toBind_4100_, lean_box(0), lean_box(0), v___x_4131_, v___f_4130_);
return v___x_4132_;
}
else
{
lean_object* v___f_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; 
lean_dec(v_matcherName_4118_);
lean_dec_ref(v_inst_4115_);
lean_dec_ref(v_inst_4104_);
lean_dec_ref(v_inst_4101_);
v___f_4133_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61), 2, 1);
lean_closure_set(v___f_4133_, 0, v___f_4128_);
v___x_4134_ = lean_unsigned_to_nat(0u);
v___x_4135_ = lean_apply_2(v_toPure_4098_, lean_box(0), v___x_4134_);
v___x_4136_ = lean_apply_4(v_toBind_4100_, lean_box(0), lean_box(0), v___x_4135_, v___f_4133_);
return v___x_4136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed(lean_object** _args){
lean_object* v_matcherApp_4137_ = _args[0];
lean_object* v_toPure_4138_ = _args[1];
lean_object* v_inst_4139_ = _args[2];
lean_object* v_toBind_4140_ = _args[3];
lean_object* v_inst_4141_ = _args[4];
lean_object* v___f_4142_ = _args[5];
lean_object* v_onMotive_4143_ = _args[6];
lean_object* v_inst_4144_ = _args[7];
lean_object* v_onRemaining_4145_ = _args[8];
lean_object* v_inst_4146_ = _args[9];
lean_object* v___f_4147_ = _args[10];
lean_object* v_onAlt_4148_ = _args[11];
lean_object* v___f_4149_ = _args[12];
lean_object* v_useSplitter_4150_ = _args[13];
lean_object* v___f_4151_ = _args[14];
lean_object* v___f_4152_ = _args[15];
lean_object* v___f_4153_ = _args[16];
lean_object* v_onParams_4154_ = _args[17];
lean_object* v_inst_4155_ = _args[18];
lean_object* v_____do__lift_4156_ = _args[19];
_start:
{
uint8_t v_useSplitter_boxed_4157_; lean_object* v_res_4158_; 
v_useSplitter_boxed_4157_ = lean_unbox(v_useSplitter_4150_);
v_res_4158_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__64(v_matcherApp_4137_, v_toPure_4138_, v_inst_4139_, v_toBind_4140_, v_inst_4141_, v___f_4142_, v_onMotive_4143_, v_inst_4144_, v_onRemaining_4145_, v_inst_4146_, v___f_4147_, v_onAlt_4148_, v___f_4149_, v_useSplitter_boxed_4157_, v___f_4151_, v___f_4152_, v___f_4153_, v_onParams_4154_, v_inst_4155_, v_____do__lift_4156_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg(lean_object* v_inst_4159_, lean_object* v_inst_4160_, lean_object* v_inst_4161_, lean_object* v_inst_4162_, lean_object* v_inst_4163_, lean_object* v_matcherApp_4164_, uint8_t v_useSplitter_4165_, uint8_t v_addEqualities_4166_, lean_object* v_onParams_4167_, lean_object* v_onMotive_4168_, lean_object* v_onAlt_4169_, lean_object* v_onRemaining_4170_){
_start:
{
lean_object* v_toApplicative_4171_; lean_object* v_toBind_4172_; lean_object* v_getEnv_4173_; lean_object* v_toPure_4174_; lean_object* v___f_4175_; lean_object* v___f_4176_; lean_object* v___f_4177_; lean_object* v___f_4178_; lean_object* v___f_4179_; lean_object* v___f_4180_; lean_object* v___x_4181_; lean_object* v___f_4182_; lean_object* v___x_4183_; lean_object* v___f_4184_; lean_object* v___x_4185_; 
v_toApplicative_4171_ = lean_ctor_get(v_inst_4161_, 0);
v_toBind_4172_ = lean_ctor_get(v_inst_4161_, 1);
lean_inc(v_toBind_4172_);
v_getEnv_4173_ = lean_ctor_get(v_inst_4163_, 0);
lean_inc(v_getEnv_4173_);
v_toPure_4174_ = lean_ctor_get(v_toApplicative_4171_, 1);
lean_inc(v_toPure_4174_);
lean_inc_ref(v_inst_4162_);
lean_inc_ref(v_inst_4161_);
v___f_4175_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4175_, 0, v_inst_4161_);
lean_closure_set(v___f_4175_, 1, v_inst_4162_);
lean_inc(v_inst_4159_);
v___f_4176_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4176_, 0, v_inst_4159_);
lean_inc_ref(v_inst_4161_);
v___f_4177_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4177_, 0, v_inst_4161_);
lean_closure_set(v___f_4177_, 1, v___f_4176_);
lean_inc(v_toPure_4174_);
v___f_4178_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__3), 2, 1);
lean_closure_set(v___f_4178_, 0, v_toPure_4174_);
lean_inc(v_toPure_4174_);
v___f_4179_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__4), 2, 1);
lean_closure_set(v___f_4179_, 0, v_toPure_4174_);
lean_inc(v_toBind_4172_);
lean_inc(v_inst_4159_);
lean_inc(v_toPure_4174_);
v___f_4180_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7), 6, 3);
lean_closure_set(v___f_4180_, 0, v_toPure_4174_);
lean_closure_set(v___f_4180_, 1, v_inst_4159_);
lean_closure_set(v___f_4180_, 2, v_toBind_4172_);
v___x_4181_ = lean_box(v_addEqualities_4166_);
lean_inc(v_toBind_4172_);
lean_inc(v_inst_4159_);
lean_inc(v_toPure_4174_);
v___f_4182_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__12___boxed), 7, 4);
lean_closure_set(v___f_4182_, 0, v_toPure_4174_);
lean_closure_set(v___f_4182_, 1, v___x_4181_);
lean_closure_set(v___f_4182_, 2, v_inst_4159_);
lean_closure_set(v___f_4182_, 3, v_toBind_4172_);
v___x_4183_ = lean_box(v_useSplitter_4165_);
lean_inc(v_toBind_4172_);
v___f_4184_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed), 20, 19);
lean_closure_set(v___f_4184_, 0, v_matcherApp_4164_);
lean_closure_set(v___f_4184_, 1, v_toPure_4174_);
lean_closure_set(v___f_4184_, 2, v_inst_4159_);
lean_closure_set(v___f_4184_, 3, v_toBind_4172_);
lean_closure_set(v___f_4184_, 4, v_inst_4161_);
lean_closure_set(v___f_4184_, 5, v___f_4182_);
lean_closure_set(v___f_4184_, 6, v_onMotive_4168_);
lean_closure_set(v___f_4184_, 7, v_inst_4162_);
lean_closure_set(v___f_4184_, 8, v_onRemaining_4170_);
lean_closure_set(v___f_4184_, 9, v_inst_4160_);
lean_closure_set(v___f_4184_, 10, v___f_4178_);
lean_closure_set(v___f_4184_, 11, v_onAlt_4169_);
lean_closure_set(v___f_4184_, 12, v___f_4177_);
lean_closure_set(v___f_4184_, 13, v___x_4183_);
lean_closure_set(v___f_4184_, 14, v___f_4179_);
lean_closure_set(v___f_4184_, 15, v___f_4175_);
lean_closure_set(v___f_4184_, 16, v___f_4180_);
lean_closure_set(v___f_4184_, 17, v_onParams_4167_);
lean_closure_set(v___f_4184_, 18, v_inst_4163_);
v___x_4185_ = lean_apply_4(v_toBind_4172_, lean_box(0), lean_box(0), v_getEnv_4173_, v___f_4184_);
return v___x_4185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___boxed(lean_object* v_inst_4186_, lean_object* v_inst_4187_, lean_object* v_inst_4188_, lean_object* v_inst_4189_, lean_object* v_inst_4190_, lean_object* v_matcherApp_4191_, lean_object* v_useSplitter_4192_, lean_object* v_addEqualities_4193_, lean_object* v_onParams_4194_, lean_object* v_onMotive_4195_, lean_object* v_onAlt_4196_, lean_object* v_onRemaining_4197_){
_start:
{
uint8_t v_useSplitter_boxed_4198_; uint8_t v_addEqualities_boxed_4199_; lean_object* v_res_4200_; 
v_useSplitter_boxed_4198_ = lean_unbox(v_useSplitter_4192_);
v_addEqualities_boxed_4199_ = lean_unbox(v_addEqualities_4193_);
v_res_4200_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_4186_, v_inst_4187_, v_inst_4188_, v_inst_4189_, v_inst_4190_, v_matcherApp_4191_, v_useSplitter_boxed_4198_, v_addEqualities_boxed_4199_, v_onParams_4194_, v_onMotive_4195_, v_onAlt_4196_, v_onRemaining_4197_);
return v_res_4200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform(lean_object* v_n_4201_, lean_object* v_inst_4202_, lean_object* v_inst_4203_, lean_object* v_inst_4204_, lean_object* v_inst_4205_, lean_object* v_inst_4206_, lean_object* v_inst_4207_, lean_object* v_inst_4208_, lean_object* v_inst_4209_, lean_object* v_matcherApp_4210_, uint8_t v_useSplitter_4211_, uint8_t v_addEqualities_4212_, lean_object* v_onParams_4213_, lean_object* v_onMotive_4214_, lean_object* v_onAlt_4215_, lean_object* v_onRemaining_4216_){
_start:
{
lean_object* v___x_4217_; 
v___x_4217_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_4202_, v_inst_4203_, v_inst_4204_, v_inst_4205_, v_inst_4206_, v_matcherApp_4210_, v_useSplitter_4211_, v_addEqualities_4212_, v_onParams_4213_, v_onMotive_4214_, v_onAlt_4215_, v_onRemaining_4216_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___boxed(lean_object* v_n_4218_, lean_object* v_inst_4219_, lean_object* v_inst_4220_, lean_object* v_inst_4221_, lean_object* v_inst_4222_, lean_object* v_inst_4223_, lean_object* v_inst_4224_, lean_object* v_inst_4225_, lean_object* v_inst_4226_, lean_object* v_matcherApp_4227_, lean_object* v_useSplitter_4228_, lean_object* v_addEqualities_4229_, lean_object* v_onParams_4230_, lean_object* v_onMotive_4231_, lean_object* v_onAlt_4232_, lean_object* v_onRemaining_4233_){
_start:
{
uint8_t v_useSplitter_boxed_4234_; uint8_t v_addEqualities_boxed_4235_; lean_object* v_res_4236_; 
v_useSplitter_boxed_4234_ = lean_unbox(v_useSplitter_4228_);
v_addEqualities_boxed_4235_ = lean_unbox(v_addEqualities_4229_);
v_res_4236_ = l_Lean_Meta_MatcherApp_transform(v_n_4218_, v_inst_4219_, v_inst_4220_, v_inst_4221_, v_inst_4222_, v_inst_4223_, v_inst_4224_, v_inst_4225_, v_inst_4226_, v_matcherApp_4227_, v_useSplitter_boxed_4234_, v_addEqualities_boxed_4235_, v_onParams_4230_, v_onMotive_4231_, v_onAlt_4232_, v_onRemaining_4233_);
lean_dec(v_inst_4226_);
lean_dec(v_inst_4225_);
lean_dec_ref(v_inst_4224_);
return v_res_4236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0(lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_){
_start:
{
lean_object* v___x_4243_; 
v___x_4243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4243_, 0, v___y_4237_);
return v___x_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0___boxed(lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_){
_start:
{
lean_object* v_res_4250_; 
v_res_4250_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__0(v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_);
lean_dec(v___y_4248_);
lean_dec_ref(v___y_4247_);
lean_dec(v___y_4246_);
lean_dec_ref(v___y_4245_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1(lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_){
_start:
{
lean_object* v___x_4257_; 
v___x_4257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4257_, 0, v___y_4251_);
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1___boxed(lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_){
_start:
{
lean_object* v_res_4264_; 
v_res_4264_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__1(v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec(v___y_4260_);
lean_dec_ref(v___y_4259_);
return v_res_4264_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(lean_object* v_opts_4265_, lean_object* v_opt_4266_){
_start:
{
lean_object* v_name_4267_; lean_object* v_defValue_4268_; lean_object* v_map_4269_; lean_object* v___x_4270_; 
v_name_4267_ = lean_ctor_get(v_opt_4266_, 0);
v_defValue_4268_ = lean_ctor_get(v_opt_4266_, 1);
v_map_4269_ = lean_ctor_get(v_opts_4265_, 0);
v___x_4270_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4269_, v_name_4267_);
if (lean_obj_tag(v___x_4270_) == 0)
{
uint8_t v___x_4271_; 
v___x_4271_ = lean_unbox(v_defValue_4268_);
return v___x_4271_;
}
else
{
lean_object* v_val_4272_; 
v_val_4272_ = lean_ctor_get(v___x_4270_, 0);
lean_inc(v_val_4272_);
lean_dec_ref(v___x_4270_);
if (lean_obj_tag(v_val_4272_) == 1)
{
uint8_t v_v_4273_; 
v_v_4273_ = lean_ctor_get_uint8(v_val_4272_, 0);
lean_dec_ref(v_val_4272_);
return v_v_4273_;
}
else
{
uint8_t v___x_4274_; 
lean_dec(v_val_4272_);
v___x_4274_ = lean_unbox(v_defValue_4268_);
return v___x_4274_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11___boxed(lean_object* v_opts_4275_, lean_object* v_opt_4276_){
_start:
{
uint8_t v_res_4277_; lean_object* v_r_4278_; 
v_res_4277_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(v_opts_4275_, v_opt_4276_);
lean_dec_ref(v_opt_4276_);
lean_dec_ref(v_opts_4275_);
v_r_4278_ = lean_box(v_res_4277_);
return v_r_4278_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(uint8_t v___y_4287_, uint8_t v_suppressElabErrors_4288_, lean_object* v_x_4289_){
_start:
{
if (lean_obj_tag(v_x_4289_) == 1)
{
lean_object* v_pre_4290_; 
v_pre_4290_ = lean_ctor_get(v_x_4289_, 0);
switch(lean_obj_tag(v_pre_4290_))
{
case 1:
{
lean_object* v_pre_4291_; 
v_pre_4291_ = lean_ctor_get(v_pre_4290_, 0);
switch(lean_obj_tag(v_pre_4291_))
{
case 0:
{
lean_object* v_str_4292_; lean_object* v_str_4293_; lean_object* v___x_4294_; uint8_t v___x_4295_; 
v_str_4292_ = lean_ctor_get(v_x_4289_, 1);
v_str_4293_ = lean_ctor_get(v_pre_4290_, 1);
v___x_4294_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_4295_ = lean_string_dec_eq(v_str_4293_, v___x_4294_);
if (v___x_4295_ == 0)
{
lean_object* v___x_4296_; uint8_t v___x_4297_; 
v___x_4296_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_4297_ = lean_string_dec_eq(v_str_4293_, v___x_4296_);
if (v___x_4297_ == 0)
{
return v___y_4287_;
}
else
{
lean_object* v___x_4298_; uint8_t v___x_4299_; 
v___x_4298_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_4299_ = lean_string_dec_eq(v_str_4292_, v___x_4298_);
if (v___x_4299_ == 0)
{
return v___y_4287_;
}
else
{
return v_suppressElabErrors_4288_;
}
}
}
else
{
lean_object* v___x_4300_; uint8_t v___x_4301_; 
v___x_4300_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_4301_ = lean_string_dec_eq(v_str_4292_, v___x_4300_);
if (v___x_4301_ == 0)
{
return v___y_4287_;
}
else
{
return v_suppressElabErrors_4288_;
}
}
}
case 1:
{
lean_object* v_pre_4302_; 
v_pre_4302_ = lean_ctor_get(v_pre_4291_, 0);
if (lean_obj_tag(v_pre_4302_) == 0)
{
lean_object* v_str_4303_; lean_object* v_str_4304_; lean_object* v_str_4305_; lean_object* v___x_4306_; uint8_t v___x_4307_; 
v_str_4303_ = lean_ctor_get(v_x_4289_, 1);
v_str_4304_ = lean_ctor_get(v_pre_4290_, 1);
v_str_4305_ = lean_ctor_get(v_pre_4291_, 1);
v___x_4306_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_4307_ = lean_string_dec_eq(v_str_4305_, v___x_4306_);
if (v___x_4307_ == 0)
{
return v___y_4287_;
}
else
{
lean_object* v___x_4308_; uint8_t v___x_4309_; 
v___x_4308_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_4309_ = lean_string_dec_eq(v_str_4304_, v___x_4308_);
if (v___x_4309_ == 0)
{
return v___y_4287_;
}
else
{
lean_object* v___x_4310_; uint8_t v___x_4311_; 
v___x_4310_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_4311_ = lean_string_dec_eq(v_str_4303_, v___x_4310_);
if (v___x_4311_ == 0)
{
return v___y_4287_;
}
else
{
return v_suppressElabErrors_4288_;
}
}
}
}
else
{
return v___y_4287_;
}
}
default: 
{
return v___y_4287_;
}
}
}
case 0:
{
lean_object* v_str_4312_; lean_object* v___x_4313_; uint8_t v___x_4314_; 
v_str_4312_ = lean_ctor_get(v_x_4289_, 1);
v___x_4313_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_4314_ = lean_string_dec_eq(v_str_4312_, v___x_4313_);
if (v___x_4314_ == 0)
{
return v___y_4287_;
}
else
{
return v_suppressElabErrors_4288_;
}
}
default: 
{
return v___y_4287_;
}
}
}
else
{
return v___y_4287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___y_4315_, lean_object* v_suppressElabErrors_4316_, lean_object* v_x_4317_){
_start:
{
uint8_t v___y_32276__boxed_4318_; uint8_t v_suppressElabErrors_boxed_4319_; uint8_t v_res_4320_; lean_object* v_r_4321_; 
v___y_32276__boxed_4318_ = lean_unbox(v___y_4315_);
v_suppressElabErrors_boxed_4319_ = lean_unbox(v_suppressElabErrors_4316_);
v_res_4320_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(v___y_32276__boxed_4318_, v_suppressElabErrors_boxed_4319_, v_x_4317_);
lean_dec(v_x_4317_);
v_r_4321_ = lean_box(v_res_4320_);
return v_r_4321_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(lean_object* v_ref_4323_, lean_object* v_msgData_4324_, uint8_t v_severity_4325_, uint8_t v_isSilent_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_){
_start:
{
uint8_t v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; uint8_t v___y_4338_; lean_object* v___y_4339_; lean_object* v___y_4340_; lean_object* v___y_4341_; lean_object* v___y_4369_; uint8_t v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4372_; uint8_t v___y_4373_; uint8_t v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4394_; uint8_t v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; uint8_t v___y_4398_; uint8_t v___y_4399_; lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v___y_4405_; uint8_t v___y_4406_; lean_object* v___y_4407_; lean_object* v___y_4408_; lean_object* v___y_4409_; uint8_t v___y_4410_; uint8_t v___y_4411_; uint8_t v___x_4416_; lean_object* v___y_4418_; lean_object* v___y_4419_; lean_object* v___y_4420_; lean_object* v___y_4421_; uint8_t v___y_4422_; uint8_t v___y_4423_; uint8_t v___y_4424_; uint8_t v___y_4426_; uint8_t v___x_4441_; 
v___x_4416_ = 2;
v___x_4441_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4325_, v___x_4416_);
if (v___x_4441_ == 0)
{
v___y_4426_ = v___x_4441_;
goto v___jp_4425_;
}
else
{
uint8_t v___x_4442_; 
lean_inc_ref(v_msgData_4324_);
v___x_4442_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4324_);
v___y_4426_ = v___x_4442_;
goto v___jp_4425_;
}
v___jp_4332_:
{
lean_object* v___x_4342_; lean_object* v_currNamespace_4343_; lean_object* v_openDecls_4344_; lean_object* v_env_4345_; lean_object* v_nextMacroScope_4346_; lean_object* v_ngen_4347_; lean_object* v_auxDeclNGen_4348_; lean_object* v_traceState_4349_; lean_object* v_cache_4350_; lean_object* v_messages_4351_; lean_object* v_infoState_4352_; lean_object* v_snapshotTasks_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4367_; 
v___x_4342_ = lean_st_ref_take(v___y_4341_);
v_currNamespace_4343_ = lean_ctor_get(v___y_4340_, 6);
lean_inc(v_currNamespace_4343_);
v_openDecls_4344_ = lean_ctor_get(v___y_4340_, 7);
lean_inc(v_openDecls_4344_);
lean_dec_ref(v___y_4340_);
v_env_4345_ = lean_ctor_get(v___x_4342_, 0);
v_nextMacroScope_4346_ = lean_ctor_get(v___x_4342_, 1);
v_ngen_4347_ = lean_ctor_get(v___x_4342_, 2);
v_auxDeclNGen_4348_ = lean_ctor_get(v___x_4342_, 3);
v_traceState_4349_ = lean_ctor_get(v___x_4342_, 4);
v_cache_4350_ = lean_ctor_get(v___x_4342_, 5);
v_messages_4351_ = lean_ctor_get(v___x_4342_, 6);
v_infoState_4352_ = lean_ctor_get(v___x_4342_, 7);
v_snapshotTasks_4353_ = lean_ctor_get(v___x_4342_, 8);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4342_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4355_ = v___x_4342_;
v_isShared_4356_ = v_isSharedCheck_4367_;
goto v_resetjp_4354_;
}
else
{
lean_inc(v_snapshotTasks_4353_);
lean_inc(v_infoState_4352_);
lean_inc(v_messages_4351_);
lean_inc(v_cache_4350_);
lean_inc(v_traceState_4349_);
lean_inc(v_auxDeclNGen_4348_);
lean_inc(v_ngen_4347_);
lean_inc(v_nextMacroScope_4346_);
lean_inc(v_env_4345_);
lean_dec(v___x_4342_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4367_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4362_; 
v___x_4357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4357_, 0, v_currNamespace_4343_);
lean_ctor_set(v___x_4357_, 1, v_openDecls_4344_);
v___x_4358_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4358_, 0, v___x_4357_);
lean_ctor_set(v___x_4358_, 1, v___y_4337_);
v___x_4359_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4359_, 0, v___y_4335_);
lean_ctor_set(v___x_4359_, 1, v___y_4336_);
lean_ctor_set(v___x_4359_, 2, v___y_4334_);
lean_ctor_set(v___x_4359_, 3, v___y_4339_);
lean_ctor_set(v___x_4359_, 4, v___x_4358_);
lean_ctor_set_uint8(v___x_4359_, sizeof(void*)*5, v___y_4333_);
lean_ctor_set_uint8(v___x_4359_, sizeof(void*)*5 + 1, v___y_4338_);
lean_ctor_set_uint8(v___x_4359_, sizeof(void*)*5 + 2, v_isSilent_4326_);
v___x_4360_ = l_Lean_MessageLog_add(v___x_4359_, v_messages_4351_);
if (v_isShared_4356_ == 0)
{
lean_ctor_set(v___x_4355_, 6, v___x_4360_);
v___x_4362_ = v___x_4355_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_env_4345_);
lean_ctor_set(v_reuseFailAlloc_4366_, 1, v_nextMacroScope_4346_);
lean_ctor_set(v_reuseFailAlloc_4366_, 2, v_ngen_4347_);
lean_ctor_set(v_reuseFailAlloc_4366_, 3, v_auxDeclNGen_4348_);
lean_ctor_set(v_reuseFailAlloc_4366_, 4, v_traceState_4349_);
lean_ctor_set(v_reuseFailAlloc_4366_, 5, v_cache_4350_);
lean_ctor_set(v_reuseFailAlloc_4366_, 6, v___x_4360_);
lean_ctor_set(v_reuseFailAlloc_4366_, 7, v_infoState_4352_);
lean_ctor_set(v_reuseFailAlloc_4366_, 8, v_snapshotTasks_4353_);
v___x_4362_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4363_ = lean_st_ref_set(v___y_4341_, v___x_4362_);
v___x_4364_ = lean_box(0);
v___x_4365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4365_, 0, v___x_4364_);
return v___x_4365_;
}
}
}
v___jp_4368_:
{
lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v_a_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4392_; 
v___x_4377_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4324_);
v___x_4378_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(v___x_4377_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_);
v_a_4379_ = lean_ctor_get(v___x_4378_, 0);
v_isSharedCheck_4392_ = !lean_is_exclusive(v___x_4378_);
if (v_isSharedCheck_4392_ == 0)
{
v___x_4381_ = v___x_4378_;
v_isShared_4382_ = v_isSharedCheck_4392_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_a_4379_);
lean_dec(v___x_4378_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4392_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; 
lean_inc_ref(v___y_4371_);
v___x_4383_ = l_Lean_FileMap_toPosition(v___y_4371_, v___y_4375_);
lean_dec(v___y_4375_);
v___x_4384_ = l_Lean_FileMap_toPosition(v___y_4371_, v___y_4376_);
lean_dec(v___y_4376_);
v___x_4385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4385_, 0, v___x_4384_);
v___x_4386_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___closed__0));
if (v___y_4374_ == 0)
{
lean_del_object(v___x_4381_);
lean_dec_ref(v___y_4369_);
v___y_4333_ = v___y_4370_;
v___y_4334_ = v___x_4385_;
v___y_4335_ = v___y_4372_;
v___y_4336_ = v___x_4383_;
v___y_4337_ = v_a_4379_;
v___y_4338_ = v___y_4373_;
v___y_4339_ = v___x_4386_;
v___y_4340_ = v___y_4329_;
v___y_4341_ = v___y_4330_;
goto v___jp_4332_;
}
else
{
uint8_t v___x_4387_; 
lean_inc(v_a_4379_);
v___x_4387_ = l_Lean_MessageData_hasTag(v___y_4369_, v_a_4379_);
if (v___x_4387_ == 0)
{
lean_object* v___x_4388_; lean_object* v___x_4390_; 
lean_dec_ref(v___x_4385_);
lean_dec_ref(v___x_4383_);
lean_dec(v_a_4379_);
lean_dec_ref(v___y_4372_);
lean_dec_ref(v___y_4329_);
v___x_4388_ = lean_box(0);
if (v_isShared_4382_ == 0)
{
lean_ctor_set(v___x_4381_, 0, v___x_4388_);
v___x_4390_ = v___x_4381_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4391_; 
v_reuseFailAlloc_4391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4391_, 0, v___x_4388_);
v___x_4390_ = v_reuseFailAlloc_4391_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
return v___x_4390_;
}
}
else
{
lean_del_object(v___x_4381_);
v___y_4333_ = v___y_4370_;
v___y_4334_ = v___x_4385_;
v___y_4335_ = v___y_4372_;
v___y_4336_ = v___x_4383_;
v___y_4337_ = v_a_4379_;
v___y_4338_ = v___y_4373_;
v___y_4339_ = v___x_4386_;
v___y_4340_ = v___y_4329_;
v___y_4341_ = v___y_4330_;
goto v___jp_4332_;
}
}
}
}
v___jp_4393_:
{
lean_object* v___x_4402_; 
v___x_4402_ = l_Lean_Syntax_getTailPos_x3f(v___y_4400_, v___y_4395_);
lean_dec(v___y_4400_);
if (lean_obj_tag(v___x_4402_) == 0)
{
lean_inc(v___y_4401_);
v___y_4369_ = v___y_4394_;
v___y_4370_ = v___y_4395_;
v___y_4371_ = v___y_4396_;
v___y_4372_ = v___y_4397_;
v___y_4373_ = v___y_4398_;
v___y_4374_ = v___y_4399_;
v___y_4375_ = v___y_4401_;
v___y_4376_ = v___y_4401_;
goto v___jp_4368_;
}
else
{
lean_object* v_val_4403_; 
v_val_4403_ = lean_ctor_get(v___x_4402_, 0);
lean_inc(v_val_4403_);
lean_dec_ref(v___x_4402_);
v___y_4369_ = v___y_4394_;
v___y_4370_ = v___y_4395_;
v___y_4371_ = v___y_4396_;
v___y_4372_ = v___y_4397_;
v___y_4373_ = v___y_4398_;
v___y_4374_ = v___y_4399_;
v___y_4375_ = v___y_4401_;
v___y_4376_ = v_val_4403_;
goto v___jp_4368_;
}
}
v___jp_4404_:
{
lean_object* v_ref_4412_; lean_object* v___x_4413_; 
v_ref_4412_ = l_Lean_replaceRef(v_ref_4323_, v___y_4408_);
lean_dec(v___y_4408_);
v___x_4413_ = l_Lean_Syntax_getPos_x3f(v_ref_4412_, v___y_4406_);
if (lean_obj_tag(v___x_4413_) == 0)
{
lean_object* v___x_4414_; 
v___x_4414_ = lean_unsigned_to_nat(0u);
v___y_4394_ = v___y_4405_;
v___y_4395_ = v___y_4406_;
v___y_4396_ = v___y_4407_;
v___y_4397_ = v___y_4409_;
v___y_4398_ = v___y_4411_;
v___y_4399_ = v___y_4410_;
v___y_4400_ = v_ref_4412_;
v___y_4401_ = v___x_4414_;
goto v___jp_4393_;
}
else
{
lean_object* v_val_4415_; 
v_val_4415_ = lean_ctor_get(v___x_4413_, 0);
lean_inc(v_val_4415_);
lean_dec_ref(v___x_4413_);
v___y_4394_ = v___y_4405_;
v___y_4395_ = v___y_4406_;
v___y_4396_ = v___y_4407_;
v___y_4397_ = v___y_4409_;
v___y_4398_ = v___y_4411_;
v___y_4399_ = v___y_4410_;
v___y_4400_ = v_ref_4412_;
v___y_4401_ = v_val_4415_;
goto v___jp_4393_;
}
}
v___jp_4417_:
{
if (v___y_4424_ == 0)
{
v___y_4405_ = v___y_4420_;
v___y_4406_ = v___y_4423_;
v___y_4407_ = v___y_4419_;
v___y_4408_ = v___y_4418_;
v___y_4409_ = v___y_4421_;
v___y_4410_ = v___y_4422_;
v___y_4411_ = v_severity_4325_;
goto v___jp_4404_;
}
else
{
v___y_4405_ = v___y_4420_;
v___y_4406_ = v___y_4423_;
v___y_4407_ = v___y_4419_;
v___y_4408_ = v___y_4418_;
v___y_4409_ = v___y_4421_;
v___y_4410_ = v___y_4422_;
v___y_4411_ = v___x_4416_;
goto v___jp_4404_;
}
}
v___jp_4425_:
{
if (v___y_4426_ == 0)
{
lean_object* v_fileName_4427_; lean_object* v_fileMap_4428_; lean_object* v_options_4429_; lean_object* v_ref_4430_; uint8_t v_suppressElabErrors_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___f_4434_; uint8_t v___x_4435_; uint8_t v___x_4436_; 
v_fileName_4427_ = lean_ctor_get(v___y_4329_, 0);
v_fileMap_4428_ = lean_ctor_get(v___y_4329_, 1);
v_options_4429_ = lean_ctor_get(v___y_4329_, 2);
v_ref_4430_ = lean_ctor_get(v___y_4329_, 5);
v_suppressElabErrors_4431_ = lean_ctor_get_uint8(v___y_4329_, sizeof(void*)*14 + 1);
v___x_4432_ = lean_box(v___y_4426_);
v___x_4433_ = lean_box(v_suppressElabErrors_4431_);
v___f_4434_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4434_, 0, v___x_4432_);
lean_closure_set(v___f_4434_, 1, v___x_4433_);
v___x_4435_ = 1;
v___x_4436_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4325_, v___x_4435_);
if (v___x_4436_ == 0)
{
lean_inc_ref(v_fileName_4427_);
lean_inc_ref(v_fileMap_4428_);
lean_inc(v_ref_4430_);
v___y_4418_ = v_ref_4430_;
v___y_4419_ = v_fileMap_4428_;
v___y_4420_ = v___f_4434_;
v___y_4421_ = v_fileName_4427_;
v___y_4422_ = v_suppressElabErrors_4431_;
v___y_4423_ = v___y_4426_;
v___y_4424_ = v___x_4436_;
goto v___jp_4417_;
}
else
{
lean_object* v___x_4437_; uint8_t v___x_4438_; 
v___x_4437_ = l_Lean_warningAsError;
v___x_4438_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(v_options_4429_, v___x_4437_);
lean_inc_ref(v_fileName_4427_);
lean_inc_ref(v_fileMap_4428_);
lean_inc(v_ref_4430_);
v___y_4418_ = v_ref_4430_;
v___y_4419_ = v_fileMap_4428_;
v___y_4420_ = v___f_4434_;
v___y_4421_ = v_fileName_4427_;
v___y_4422_ = v_suppressElabErrors_4431_;
v___y_4423_ = v___y_4426_;
v___y_4424_ = v___x_4438_;
goto v___jp_4417_;
}
}
else
{
lean_object* v___x_4439_; lean_object* v___x_4440_; 
lean_dec_ref(v___y_4329_);
lean_dec_ref(v_msgData_4324_);
v___x_4439_ = lean_box(0);
v___x_4440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4439_);
return v___x_4440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_4443_, lean_object* v_msgData_4444_, lean_object* v_severity_4445_, lean_object* v_isSilent_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_){
_start:
{
uint8_t v_severity_boxed_4452_; uint8_t v_isSilent_boxed_4453_; lean_object* v_res_4454_; 
v_severity_boxed_4452_ = lean_unbox(v_severity_4445_);
v_isSilent_boxed_4453_ = lean_unbox(v_isSilent_4446_);
v_res_4454_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(v_ref_4443_, v_msgData_4444_, v_severity_boxed_4452_, v_isSilent_boxed_4453_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_);
lean_dec(v___y_4450_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec(v_ref_4443_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(lean_object* v_msgData_4455_, uint8_t v_severity_4456_, uint8_t v_isSilent_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_){
_start:
{
lean_object* v_ref_4463_; lean_object* v___x_4464_; 
v_ref_4463_ = lean_ctor_get(v___y_4460_, 5);
lean_inc(v_ref_4463_);
v___x_4464_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(v_ref_4463_, v_msgData_4455_, v_severity_4456_, v_isSilent_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
lean_dec(v_ref_4463_);
return v___x_4464_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0___boxed(lean_object* v_msgData_4465_, lean_object* v_severity_4466_, lean_object* v_isSilent_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_){
_start:
{
uint8_t v_severity_boxed_4473_; uint8_t v_isSilent_boxed_4474_; lean_object* v_res_4475_; 
v_severity_boxed_4473_ = lean_unbox(v_severity_4466_);
v_isSilent_boxed_4474_ = lean_unbox(v_isSilent_4467_);
v_res_4475_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(v_msgData_4465_, v_severity_boxed_4473_, v_isSilent_boxed_4474_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_);
lean_dec(v___y_4471_);
lean_dec(v___y_4469_);
lean_dec_ref(v___y_4468_);
return v_res_4475_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(lean_object* v_msgData_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_){
_start:
{
uint8_t v___x_4482_; uint8_t v___x_4483_; lean_object* v___x_4484_; 
v___x_4482_ = 0;
v___x_4483_ = 0;
v___x_4484_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(v_msgData_4476_, v___x_4482_, v___x_4483_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_);
return v___x_4484_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0___boxed(lean_object* v_msgData_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_){
_start:
{
lean_object* v_res_4491_; 
v_res_4491_ = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(v_msgData_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_);
lean_dec(v___y_4489_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
return v_res_4491_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1(void){
_start:
{
lean_object* v___x_4493_; lean_object* v___x_4494_; 
v___x_4493_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0));
v___x_4494_ = l_Lean_stringToMessageData(v___x_4493_);
return v___x_4494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2(uint8_t v___x_4495_, lean_object* v___altIdx_4496_, lean_object* v_expAltType_4497_, lean_object* v___altFVars_4498_, lean_object* v_alt_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_){
_start:
{
lean_object* v___x_4505_; 
lean_inc(v___y_4503_);
lean_inc_ref(v___y_4502_);
lean_inc(v___y_4501_);
lean_inc_ref(v___y_4500_);
lean_inc_ref(v_alt_4499_);
v___x_4505_ = lean_infer_type(v_alt_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
if (lean_obj_tag(v___x_4505_) == 0)
{
lean_object* v_a_4506_; lean_object* v___x_4507_; 
v_a_4506_ = lean_ctor_get(v___x_4505_, 0);
lean_inc(v_a_4506_);
lean_dec_ref(v___x_4505_);
lean_inc(v___y_4503_);
lean_inc_ref(v___y_4502_);
lean_inc(v___y_4501_);
lean_inc_ref(v___y_4500_);
v___x_4507_ = l_Lean_Meta_mkEq(v_expAltType_4497_, v_a_4506_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
if (lean_obj_tag(v___x_4507_) == 0)
{
lean_object* v_a_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; 
v_a_4508_ = lean_ctor_get(v___x_4507_, 0);
lean_inc(v_a_4508_);
lean_dec_ref(v___x_4507_);
v___x_4509_ = lean_box(0);
lean_inc_ref(v___y_4500_);
v___x_4510_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4508_, v___x_4509_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
if (lean_obj_tag(v___x_4510_) == 0)
{
lean_object* v_a_4511_; lean_object* v___y_4513_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
v_a_4511_ = lean_ctor_get(v___x_4510_, 0);
lean_inc(v_a_4511_);
lean_dec_ref(v___x_4510_);
v___x_4523_ = l_Lean_Expr_mvarId_x21(v_a_4511_);
lean_inc(v___y_4503_);
lean_inc_ref(v___y_4502_);
lean_inc(v___y_4501_);
lean_inc_ref(v___y_4500_);
v___x_4524_ = l_Lean_Meta_Split_simpMatchTarget(v___x_4523_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
if (lean_obj_tag(v___x_4524_) == 0)
{
lean_object* v_a_4525_; lean_object* v___x_4526_; 
v_a_4525_ = lean_ctor_get(v___x_4524_, 0);
lean_inc(v_a_4525_);
lean_dec_ref(v___x_4524_);
lean_inc(v___y_4503_);
lean_inc_ref(v___y_4502_);
lean_inc(v___y_4501_);
lean_inc_ref(v___y_4500_);
lean_inc(v_a_4525_);
v___x_4526_ = l_Lean_MVarId_refl(v_a_4525_, v___x_4495_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
if (lean_obj_tag(v___x_4526_) == 0)
{
lean_dec(v_a_4525_);
v___y_4513_ = v___x_4526_;
goto v___jp_4512_;
}
else
{
lean_object* v_a_4527_; uint8_t v___y_4529_; uint8_t v___x_4542_; 
v_a_4527_ = lean_ctor_get(v___x_4526_, 0);
lean_inc(v_a_4527_);
v___x_4542_ = l_Lean_Exception_isInterrupt(v_a_4527_);
if (v___x_4542_ == 0)
{
uint8_t v___x_4543_; 
v___x_4543_ = l_Lean_Exception_isRuntime(v_a_4527_);
v___y_4529_ = v___x_4543_;
goto v___jp_4528_;
}
else
{
lean_dec(v_a_4527_);
v___y_4529_ = v___x_4542_;
goto v___jp_4528_;
}
v___jp_4528_:
{
if (v___y_4529_ == 0)
{
lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4540_; 
v_isSharedCheck_4540_ = !lean_is_exclusive(v___x_4526_);
if (v_isSharedCheck_4540_ == 0)
{
lean_object* v_unused_4541_; 
v_unused_4541_ = lean_ctor_get(v___x_4526_, 0);
lean_dec(v_unused_4541_);
v___x_4531_ = v___x_4526_;
v_isShared_4532_ = v_isSharedCheck_4540_;
goto v_resetjp_4530_;
}
else
{
lean_dec(v___x_4526_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4540_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v___x_4533_; lean_object* v___x_4535_; 
v___x_4533_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1, &l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1);
lean_inc(v_a_4525_);
if (v_isShared_4532_ == 0)
{
lean_ctor_set(v___x_4531_, 0, v_a_4525_);
v___x_4535_ = v___x_4531_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v_a_4525_);
v___x_4535_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4536_, 0, v___x_4533_);
lean_ctor_set(v___x_4536_, 1, v___x_4535_);
lean_inc_ref(v___y_4502_);
v___x_4537_ = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(v___x_4536_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
if (lean_obj_tag(v___x_4537_) == 0)
{
lean_object* v___x_4538_; 
lean_dec_ref(v___x_4537_);
lean_inc(v___y_4503_);
lean_inc_ref(v___y_4502_);
lean_inc(v___y_4501_);
lean_inc_ref(v___y_4500_);
v___x_4538_ = l_Lean_MVarId_admit(v_a_4525_, v___x_4495_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
v___y_4513_ = v___x_4538_;
goto v___jp_4512_;
}
else
{
lean_dec(v_a_4525_);
v___y_4513_ = v___x_4537_;
goto v___jp_4512_;
}
}
}
}
else
{
lean_dec(v_a_4525_);
v___y_4513_ = v___x_4526_;
goto v___jp_4512_;
}
}
}
}
else
{
lean_object* v_a_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4551_; 
lean_dec(v_a_4511_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec_ref(v_alt_4499_);
v_a_4544_ = lean_ctor_get(v___x_4524_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4524_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_4546_ = v___x_4524_;
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_a_4544_);
lean_dec(v___x_4524_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4549_; 
if (v_isShared_4547_ == 0)
{
v___x_4549_ = v___x_4546_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_a_4544_);
v___x_4549_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
return v___x_4549_;
}
}
}
v___jp_4512_:
{
if (lean_obj_tag(v___y_4513_) == 0)
{
lean_object* v___x_4514_; 
lean_dec_ref(v___y_4513_);
v___x_4514_ = l_Lean_Meta_mkEqMPR(v_a_4511_, v_alt_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
return v___x_4514_;
}
else
{
lean_object* v_a_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4522_; 
lean_dec(v_a_4511_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec_ref(v_alt_4499_);
v_a_4515_ = lean_ctor_get(v___y_4513_, 0);
v_isSharedCheck_4522_ = !lean_is_exclusive(v___y_4513_);
if (v_isSharedCheck_4522_ == 0)
{
v___x_4517_ = v___y_4513_;
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
else
{
lean_inc(v_a_4515_);
lean_dec(v___y_4513_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
lean_object* v___x_4520_; 
if (v_isShared_4518_ == 0)
{
v___x_4520_ = v___x_4517_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_a_4515_);
v___x_4520_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
return v___x_4520_;
}
}
}
}
}
else
{
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec_ref(v_alt_4499_);
return v___x_4510_;
}
}
else
{
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec_ref(v_alt_4499_);
return v___x_4507_;
}
}
else
{
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec_ref(v_alt_4499_);
lean_dec_ref(v_expAltType_4497_);
return v___x_4505_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___boxed(lean_object* v___x_4552_, lean_object* v___altIdx_4553_, lean_object* v_expAltType_4554_, lean_object* v___altFVars_4555_, lean_object* v_alt_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_){
_start:
{
uint8_t v___x_32599__boxed_4562_; lean_object* v_res_4563_; 
v___x_32599__boxed_4562_ = lean_unbox(v___x_4552_);
v_res_4563_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__2(v___x_32599__boxed_4562_, v___altIdx_4553_, v_expAltType_4554_, v___altFVars_4555_, v_alt_4556_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_);
lean_dec_ref(v___altFVars_4555_);
lean_dec(v___altIdx_4553_);
return v_res_4563_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(lean_object* v___x_4564_, lean_object* v_e_4565_){
_start:
{
uint8_t v___x_4566_; lean_object* v_d_4568_; lean_object* v_b_4569_; 
v___x_4566_ = l_Lean_Expr_hasFVar(v_e_4565_);
if (v___x_4566_ == 0)
{
return v___x_4566_;
}
else
{
switch(lean_obj_tag(v_e_4565_))
{
case 7:
{
lean_object* v_binderType_4572_; lean_object* v_body_4573_; 
v_binderType_4572_ = lean_ctor_get(v_e_4565_, 1);
v_body_4573_ = lean_ctor_get(v_e_4565_, 2);
v_d_4568_ = v_binderType_4572_;
v_b_4569_ = v_body_4573_;
goto v___jp_4567_;
}
case 6:
{
lean_object* v_binderType_4574_; lean_object* v_body_4575_; 
v_binderType_4574_ = lean_ctor_get(v_e_4565_, 1);
v_body_4575_ = lean_ctor_get(v_e_4565_, 2);
v_d_4568_ = v_binderType_4574_;
v_b_4569_ = v_body_4575_;
goto v___jp_4567_;
}
case 10:
{
lean_object* v_expr_4576_; 
v_expr_4576_ = lean_ctor_get(v_e_4565_, 1);
v_e_4565_ = v_expr_4576_;
goto _start;
}
case 8:
{
lean_object* v_type_4578_; lean_object* v_value_4579_; lean_object* v_body_4580_; uint8_t v___x_4581_; 
v_type_4578_ = lean_ctor_get(v_e_4565_, 1);
v_value_4579_ = lean_ctor_get(v_e_4565_, 2);
v_body_4580_ = lean_ctor_get(v_e_4565_, 3);
v___x_4581_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4564_, v_type_4578_);
if (v___x_4581_ == 0)
{
uint8_t v___x_4582_; 
v___x_4582_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4564_, v_value_4579_);
if (v___x_4582_ == 0)
{
v_e_4565_ = v_body_4580_;
goto _start;
}
else
{
return v___x_4566_;
}
}
else
{
return v___x_4566_;
}
}
case 5:
{
lean_object* v_fn_4584_; lean_object* v_arg_4585_; uint8_t v___x_4586_; 
v_fn_4584_ = lean_ctor_get(v_e_4565_, 0);
v_arg_4585_ = lean_ctor_get(v_e_4565_, 1);
v___x_4586_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4564_, v_fn_4584_);
if (v___x_4586_ == 0)
{
v_e_4565_ = v_arg_4585_;
goto _start;
}
else
{
return v___x_4566_;
}
}
case 11:
{
lean_object* v_struct_4588_; 
v_struct_4588_ = lean_ctor_get(v_e_4565_, 2);
v_e_4565_ = v_struct_4588_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4590_; lean_object* v___x_4591_; uint8_t v___x_4592_; 
v_fvarId_4590_ = lean_ctor_get(v_e_4565_, 0);
v___x_4591_ = l_Lean_Expr_fvarId_x21(v___x_4564_);
v___x_4592_ = l_Lean_instBEqFVarId_beq(v_fvarId_4590_, v___x_4591_);
lean_dec(v___x_4591_);
return v___x_4592_;
}
default: 
{
uint8_t v___x_4593_; 
v___x_4593_ = 0;
return v___x_4593_;
}
}
}
v___jp_4567_:
{
uint8_t v___x_4570_; 
v___x_4570_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4564_, v_d_4568_);
if (v___x_4570_ == 0)
{
v_e_4565_ = v_b_4569_;
goto _start;
}
else
{
return v___x_4566_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1___boxed(lean_object* v___x_4594_, lean_object* v_e_4595_){
_start:
{
uint8_t v_res_4596_; lean_object* v_r_4597_; 
v_res_4596_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4594_, v_e_4595_);
lean_dec_ref(v_e_4595_);
lean_dec_ref(v___x_4594_);
v_r_4597_ = lean_box(v_res_4596_);
return v_r_4597_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4599_; lean_object* v___x_4600_; 
v___x_4599_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__0));
v___x_4600_ = l_Lean_stringToMessageData(v___x_4599_);
return v___x_4600_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4602_; lean_object* v___x_4603_; 
v___x_4602_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__2));
v___x_4603_ = l_Lean_stringToMessageData(v___x_4602_);
return v___x_4603_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_4605_; lean_object* v___x_4606_; 
v___x_4605_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__4));
v___x_4606_ = l_Lean_stringToMessageData(v___x_4605_);
return v___x_4606_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(lean_object* v_a_4607_, lean_object* v_termAlt_4608_, lean_object* v_a_4609_, lean_object* v_b_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_){
_start:
{
lean_object* v_array_4616_; lean_object* v_start_4617_; lean_object* v_stop_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4646_; 
v_array_4616_ = lean_ctor_get(v_a_4609_, 0);
v_start_4617_ = lean_ctor_get(v_a_4609_, 1);
v_stop_4618_ = lean_ctor_get(v_a_4609_, 2);
v_isSharedCheck_4646_ = !lean_is_exclusive(v_a_4609_);
if (v_isSharedCheck_4646_ == 0)
{
v___x_4620_ = v_a_4609_;
v_isShared_4621_ = v_isSharedCheck_4646_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_stop_4618_);
lean_inc(v_start_4617_);
lean_inc(v_array_4616_);
lean_dec(v_a_4609_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4646_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
uint8_t v___x_4622_; 
v___x_4622_ = lean_nat_dec_lt(v_start_4617_, v_stop_4618_);
if (v___x_4622_ == 0)
{
lean_object* v___x_4623_; 
lean_del_object(v___x_4620_);
lean_dec(v_stop_4618_);
lean_dec(v_start_4617_);
lean_dec_ref(v_array_4616_);
lean_dec_ref(v_termAlt_4608_);
lean_dec_ref(v_a_4607_);
v___x_4623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4623_, 0, v_b_4610_);
return v___x_4623_;
}
else
{
lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4628_; 
v___x_4624_ = lean_box(0);
v___x_4625_ = lean_unsigned_to_nat(1u);
v___x_4626_ = lean_nat_add(v_start_4617_, v___x_4625_);
lean_inc_ref(v_array_4616_);
if (v_isShared_4621_ == 0)
{
lean_ctor_set(v___x_4620_, 1, v___x_4626_);
v___x_4628_ = v___x_4620_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4645_; 
v_reuseFailAlloc_4645_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_array_4616_);
lean_ctor_set(v_reuseFailAlloc_4645_, 1, v___x_4626_);
lean_ctor_set(v_reuseFailAlloc_4645_, 2, v_stop_4618_);
v___x_4628_ = v_reuseFailAlloc_4645_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
lean_object* v___x_4629_; uint8_t v___x_4630_; 
v___x_4629_ = lean_array_fget(v_array_4616_, v_start_4617_);
lean_dec(v_start_4617_);
lean_dec_ref(v_array_4616_);
v___x_4630_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4629_, v_a_4607_);
if (v___x_4630_ == 0)
{
lean_dec(v___x_4629_);
v_a_4609_ = v___x_4628_;
v_b_4610_ = v___x_4624_;
goto _start;
}
else
{
lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; 
v___x_4632_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1);
lean_inc_ref(v_a_4607_);
v___x_4633_ = l_Lean_MessageData_ofExpr(v_a_4607_);
v___x_4634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4634_, 0, v___x_4632_);
lean_ctor_set(v___x_4634_, 1, v___x_4633_);
v___x_4635_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3);
v___x_4636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4636_, 0, v___x_4634_);
lean_ctor_set(v___x_4636_, 1, v___x_4635_);
lean_inc_ref(v_termAlt_4608_);
v___x_4637_ = l_Lean_MessageData_ofExpr(v_termAlt_4608_);
v___x_4638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4638_, 0, v___x_4636_);
lean_ctor_set(v___x_4638_, 1, v___x_4637_);
v___x_4639_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5);
v___x_4640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4638_);
lean_ctor_set(v___x_4640_, 1, v___x_4639_);
v___x_4641_ = l_Lean_MessageData_ofExpr(v___x_4629_);
v___x_4642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4642_, 0, v___x_4640_);
lean_ctor_set(v___x_4642_, 1, v___x_4641_);
v___x_4643_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_4642_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_);
if (lean_obj_tag(v___x_4643_) == 0)
{
lean_dec_ref(v___x_4643_);
v_a_4609_ = v___x_4628_;
v_b_4610_ = v___x_4624_;
goto _start;
}
else
{
lean_dec_ref(v___x_4628_);
lean_dec_ref(v_termAlt_4608_);
lean_dec_ref(v_a_4607_);
return v___x_4643_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___boxed(lean_object* v_a_4647_, lean_object* v_termAlt_4648_, lean_object* v_a_4649_, lean_object* v_b_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_){
_start:
{
lean_object* v_res_4656_; 
v_res_4656_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_4647_, v_termAlt_4648_, v_a_4649_, v_b_4650_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_);
lean_dec(v___y_4654_);
lean_dec_ref(v___y_4653_);
lean_dec(v___y_4652_);
lean_dec_ref(v___y_4651_);
return v_res_4656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(lean_object* v_nExtra_4657_, lean_object* v_v_4658_, uint8_t v___x_4659_, uint8_t v___x_4660_, uint8_t v___x_4661_, lean_object* v_xs_4662_, lean_object* v_termAltBody_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_){
_start:
{
lean_object* v___x_4669_; 
lean_inc(v___y_4667_);
lean_inc_ref(v___y_4666_);
lean_inc(v___y_4665_);
lean_inc_ref(v___y_4664_);
v___x_4669_ = lean_infer_type(v_termAltBody_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_);
if (lean_obj_tag(v___x_4669_) == 0)
{
lean_object* v_a_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; 
v_a_4670_ = lean_ctor_get(v___x_4669_, 0);
lean_inc(v_a_4670_);
lean_dec_ref(v___x_4669_);
v___x_4671_ = lean_array_get_size(v_xs_4662_);
v___x_4672_ = lean_nat_sub(v___x_4671_, v_nExtra_4657_);
v___x_4673_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_4672_);
lean_inc_ref(v_xs_4662_);
v___x_4674_ = l_Array_toSubarray___redArg(v_xs_4662_, v___x_4673_, v___x_4672_);
v___x_4675_ = l_Array_toSubarray___redArg(v_xs_4662_, v___x_4672_, v___x_4671_);
v___x_4676_ = lean_box(0);
lean_inc(v_a_4670_);
v___x_4677_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_4670_, v_v_4658_, v___x_4675_, v___x_4676_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_);
if (lean_obj_tag(v___x_4677_) == 0)
{
lean_object* v___x_4678_; lean_object* v___x_4679_; 
lean_dec_ref(v___x_4677_);
v___x_4678_ = l_Subarray_copy___redArg(v___x_4674_);
v___x_4679_ = l_Lean_Meta_mkLambdaFVars(v___x_4678_, v_a_4670_, v___x_4659_, v___x_4660_, v___x_4659_, v___x_4660_, v___x_4661_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
lean_dec_ref(v___x_4678_);
return v___x_4679_;
}
else
{
lean_object* v_a_4680_; lean_object* v___x_4682_; uint8_t v_isShared_4683_; uint8_t v_isSharedCheck_4687_; 
lean_dec_ref(v___x_4674_);
lean_dec(v_a_4670_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
v_a_4680_ = lean_ctor_get(v___x_4677_, 0);
v_isSharedCheck_4687_ = !lean_is_exclusive(v___x_4677_);
if (v_isSharedCheck_4687_ == 0)
{
v___x_4682_ = v___x_4677_;
v_isShared_4683_ = v_isSharedCheck_4687_;
goto v_resetjp_4681_;
}
else
{
lean_inc(v_a_4680_);
lean_dec(v___x_4677_);
v___x_4682_ = lean_box(0);
v_isShared_4683_ = v_isSharedCheck_4687_;
goto v_resetjp_4681_;
}
v_resetjp_4681_:
{
lean_object* v___x_4685_; 
if (v_isShared_4683_ == 0)
{
v___x_4685_ = v___x_4682_;
goto v_reusejp_4684_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v_a_4680_);
v___x_4685_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4684_;
}
v_reusejp_4684_:
{
return v___x_4685_;
}
}
}
}
else
{
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
lean_dec_ref(v_xs_4662_);
lean_dec(v_v_4658_);
return v___x_4669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed(lean_object* v_nExtra_4688_, lean_object* v_v_4689_, lean_object* v___x_4690_, lean_object* v___x_4691_, lean_object* v___x_4692_, lean_object* v_xs_4693_, lean_object* v_termAltBody_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_){
_start:
{
uint8_t v___x_32888__boxed_4700_; uint8_t v___x_32889__boxed_4701_; uint8_t v___x_32890__boxed_4702_; lean_object* v_res_4703_; 
v___x_32888__boxed_4700_ = lean_unbox(v___x_4690_);
v___x_32889__boxed_4701_ = lean_unbox(v___x_4691_);
v___x_32890__boxed_4702_ = lean_unbox(v___x_4692_);
v_res_4703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(v_nExtra_4688_, v_v_4689_, v___x_32888__boxed_4700_, v___x_32889__boxed_4701_, v___x_32890__boxed_4702_, v_xs_4693_, v_termAltBody_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
lean_dec(v_nExtra_4688_);
return v_res_4703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(lean_object* v_nExtra_4704_, size_t v_sz_4705_, size_t v_i_4706_, lean_object* v_bs_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_){
_start:
{
uint8_t v___x_4713_; 
v___x_4713_ = lean_usize_dec_lt(v_i_4706_, v_sz_4705_);
if (v___x_4713_ == 0)
{
lean_object* v___x_4714_; 
lean_dec(v___y_4711_);
lean_dec_ref(v___y_4710_);
lean_dec(v___y_4709_);
lean_dec_ref(v___y_4708_);
lean_dec(v_nExtra_4704_);
v___x_4714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4714_, 0, v_bs_4707_);
return v___x_4714_;
}
else
{
uint8_t v___x_4715_; uint8_t v___x_4716_; lean_object* v_v_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___f_4721_; lean_object* v___x_4722_; 
v___x_4715_ = 0;
v___x_4716_ = 1;
v_v_4717_ = lean_array_uget_borrowed(v_bs_4707_, v_i_4706_);
v___x_4718_ = lean_box(v___x_4715_);
v___x_4719_ = lean_box(v___x_4713_);
v___x_4720_ = lean_box(v___x_4716_);
lean_inc(v_v_4717_);
lean_inc(v_nExtra_4704_);
v___f_4721_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4721_, 0, v_nExtra_4704_);
lean_closure_set(v___f_4721_, 1, v_v_4717_);
lean_closure_set(v___f_4721_, 2, v___x_4718_);
lean_closure_set(v___f_4721_, 3, v___x_4719_);
lean_closure_set(v___f_4721_, 4, v___x_4720_);
lean_inc(v___y_4711_);
lean_inc_ref(v___y_4710_);
lean_inc(v___y_4709_);
lean_inc_ref(v___y_4708_);
lean_inc(v_v_4717_);
v___x_4722_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_v_4717_, v___f_4721_, v___x_4715_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_);
if (lean_obj_tag(v___x_4722_) == 0)
{
lean_object* v_a_4723_; lean_object* v___x_4724_; lean_object* v_bs_x27_4725_; size_t v___x_4726_; size_t v___x_4727_; lean_object* v___x_4728_; 
v_a_4723_ = lean_ctor_get(v___x_4722_, 0);
lean_inc(v_a_4723_);
lean_dec_ref(v___x_4722_);
v___x_4724_ = lean_unsigned_to_nat(0u);
v_bs_x27_4725_ = lean_array_uset(v_bs_4707_, v_i_4706_, v___x_4724_);
v___x_4726_ = ((size_t)1ULL);
v___x_4727_ = lean_usize_add(v_i_4706_, v___x_4726_);
v___x_4728_ = lean_array_uset(v_bs_x27_4725_, v_i_4706_, v_a_4723_);
v_i_4706_ = v___x_4727_;
v_bs_4707_ = v___x_4728_;
goto _start;
}
else
{
lean_object* v_a_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4737_; 
lean_dec(v___y_4711_);
lean_dec_ref(v___y_4710_);
lean_dec(v___y_4709_);
lean_dec_ref(v___y_4708_);
lean_dec_ref(v_bs_4707_);
lean_dec(v_nExtra_4704_);
v_a_4730_ = lean_ctor_get(v___x_4722_, 0);
v_isSharedCheck_4737_ = !lean_is_exclusive(v___x_4722_);
if (v_isSharedCheck_4737_ == 0)
{
v___x_4732_ = v___x_4722_;
v_isShared_4733_ = v_isSharedCheck_4737_;
goto v_resetjp_4731_;
}
else
{
lean_inc(v_a_4730_);
lean_dec(v___x_4722_);
v___x_4732_ = lean_box(0);
v_isShared_4733_ = v_isSharedCheck_4737_;
goto v_resetjp_4731_;
}
v_resetjp_4731_:
{
lean_object* v___x_4735_; 
if (v_isShared_4733_ == 0)
{
v___x_4735_ = v___x_4732_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4736_; 
v_reuseFailAlloc_4736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4736_, 0, v_a_4730_);
v___x_4735_ = v_reuseFailAlloc_4736_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
return v___x_4735_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___boxed(lean_object* v_nExtra_4738_, lean_object* v_sz_4739_, lean_object* v_i_4740_, lean_object* v_bs_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_){
_start:
{
size_t v_sz_boxed_4747_; size_t v_i_boxed_4748_; lean_object* v_res_4749_; 
v_sz_boxed_4747_ = lean_unbox_usize(v_sz_4739_);
lean_dec(v_sz_4739_);
v_i_boxed_4748_ = lean_unbox_usize(v_i_4740_);
lean_dec(v_i_4740_);
v_res_4749_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(v_nExtra_4738_, v_sz_boxed_4747_, v_i_boxed_4748_, v_bs_4741_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_);
return v_res_4749_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0(void){
_start:
{
lean_object* v___x_4750_; lean_object* v___x_4751_; 
v___x_4750_ = lean_box(0);
v___x_4751_ = l_Lean_Expr_sort___override(v___x_4750_);
return v___x_4751_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1(void){
_start:
{
lean_object* v___x_4752_; lean_object* v___x_4753_; 
v___x_4752_ = lean_box(0);
v___x_4753_ = l_Lean_Level_succ___override(v___x_4752_);
return v___x_4753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3(lean_object* v_nExtra_4754_, uint8_t v___x_4755_, uint8_t v___x_4756_, lean_object* v_alts_4757_, lean_object* v_toMatcherInfo_4758_, lean_object* v_matcherName_4759_, lean_object* v_params_4760_, lean_object* v_matcherLevels_4761_, lean_object* v_motiveArgs_4762_, lean_object* v_body_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_){
_start:
{
lean_object* v___x_4769_; 
lean_inc(v___y_4767_);
lean_inc_ref(v___y_4766_);
lean_inc(v___y_4765_);
lean_inc_ref(v___y_4764_);
lean_inc(v_nExtra_4754_);
v___x_4769_ = l_Lean_Meta_arrowDomainsN(v_nExtra_4754_, v_body_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
if (lean_obj_tag(v___x_4769_) == 0)
{
lean_object* v_a_4770_; lean_object* v___x_4771_; uint8_t v___x_4772_; lean_object* v___x_4773_; 
v_a_4770_ = lean_ctor_get(v___x_4769_, 0);
lean_inc(v_a_4770_);
lean_dec_ref(v___x_4769_);
v___x_4771_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0, &l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0);
v___x_4772_ = 1;
v___x_4773_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_4762_, v___x_4771_, v___x_4755_, v___x_4756_, v___x_4755_, v___x_4756_, v___x_4772_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
if (lean_obj_tag(v___x_4773_) == 0)
{
lean_object* v_a_4774_; size_t v_sz_4775_; size_t v___x_4776_; lean_object* v___x_4777_; 
v_a_4774_ = lean_ctor_get(v___x_4773_, 0);
lean_inc(v_a_4774_);
lean_dec_ref(v___x_4773_);
v_sz_4775_ = lean_array_size(v_alts_4757_);
v___x_4776_ = ((size_t)0ULL);
lean_inc(v___y_4767_);
lean_inc_ref(v___y_4766_);
v___x_4777_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(v_nExtra_4754_, v_sz_4775_, v___x_4776_, v_alts_4757_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
if (lean_obj_tag(v___x_4777_) == 0)
{
lean_object* v_a_4778_; lean_object* v_matcherLevels_4780_; lean_object* v___y_4781_; lean_object* v___y_4782_; lean_object* v_uElimPos_x3f_4787_; 
v_a_4778_ = lean_ctor_get(v___x_4777_, 0);
lean_inc(v_a_4778_);
lean_dec_ref(v___x_4777_);
v_uElimPos_x3f_4787_ = lean_ctor_get(v_toMatcherInfo_4758_, 3);
if (lean_obj_tag(v_uElimPos_x3f_4787_) == 0)
{
v_matcherLevels_4780_ = v_matcherLevels_4761_;
v___y_4781_ = v___y_4766_;
v___y_4782_ = v___y_4767_;
goto v___jp_4779_;
}
else
{
lean_object* v_val_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; 
v_val_4788_ = lean_ctor_get(v_uElimPos_x3f_4787_, 0);
v___x_4789_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1, &l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1);
v___x_4790_ = lean_array_set(v_matcherLevels_4761_, v_val_4788_, v___x_4789_);
v_matcherLevels_4780_ = v___x_4790_;
v___y_4781_ = v___y_4766_;
v___y_4782_ = v___y_4767_;
goto v___jp_4779_;
}
v___jp_4779_:
{
lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; 
v___x_4783_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_4784_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4784_, 0, v_toMatcherInfo_4758_);
lean_ctor_set(v___x_4784_, 1, v_matcherName_4759_);
lean_ctor_set(v___x_4784_, 2, v_matcherLevels_4780_);
lean_ctor_set(v___x_4784_, 3, v_params_4760_);
lean_ctor_set(v___x_4784_, 4, v_a_4774_);
lean_ctor_set(v___x_4784_, 5, v_motiveArgs_4762_);
lean_ctor_set(v___x_4784_, 6, v_a_4778_);
lean_ctor_set(v___x_4784_, 7, v___x_4783_);
v___x_4785_ = l_Lean_Meta_MatcherApp_toExpr(v___x_4784_);
v___x_4786_ = l_Lean_mkArrowN(v_a_4770_, v___x_4785_, v___y_4781_, v___y_4782_);
lean_dec(v_a_4770_);
return v___x_4786_;
}
}
else
{
lean_object* v_a_4791_; lean_object* v___x_4793_; uint8_t v_isShared_4794_; uint8_t v_isSharedCheck_4798_; 
lean_dec(v_a_4774_);
lean_dec(v_a_4770_);
lean_dec(v___y_4767_);
lean_dec_ref(v___y_4766_);
lean_dec_ref(v_motiveArgs_4762_);
lean_dec_ref(v_matcherLevels_4761_);
lean_dec_ref(v_params_4760_);
lean_dec(v_matcherName_4759_);
lean_dec_ref(v_toMatcherInfo_4758_);
v_a_4791_ = lean_ctor_get(v___x_4777_, 0);
v_isSharedCheck_4798_ = !lean_is_exclusive(v___x_4777_);
if (v_isSharedCheck_4798_ == 0)
{
v___x_4793_ = v___x_4777_;
v_isShared_4794_ = v_isSharedCheck_4798_;
goto v_resetjp_4792_;
}
else
{
lean_inc(v_a_4791_);
lean_dec(v___x_4777_);
v___x_4793_ = lean_box(0);
v_isShared_4794_ = v_isSharedCheck_4798_;
goto v_resetjp_4792_;
}
v_resetjp_4792_:
{
lean_object* v___x_4796_; 
if (v_isShared_4794_ == 0)
{
v___x_4796_ = v___x_4793_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4797_; 
v_reuseFailAlloc_4797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4797_, 0, v_a_4791_);
v___x_4796_ = v_reuseFailAlloc_4797_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
return v___x_4796_;
}
}
}
}
else
{
lean_dec(v_a_4770_);
lean_dec(v___y_4767_);
lean_dec_ref(v___y_4766_);
lean_dec(v___y_4765_);
lean_dec_ref(v___y_4764_);
lean_dec_ref(v_motiveArgs_4762_);
lean_dec_ref(v_matcherLevels_4761_);
lean_dec_ref(v_params_4760_);
lean_dec(v_matcherName_4759_);
lean_dec_ref(v_toMatcherInfo_4758_);
lean_dec_ref(v_alts_4757_);
lean_dec(v_nExtra_4754_);
return v___x_4773_;
}
}
else
{
lean_object* v_a_4799_; lean_object* v___x_4801_; uint8_t v_isShared_4802_; uint8_t v_isSharedCheck_4806_; 
lean_dec(v___y_4767_);
lean_dec_ref(v___y_4766_);
lean_dec(v___y_4765_);
lean_dec_ref(v___y_4764_);
lean_dec_ref(v_motiveArgs_4762_);
lean_dec_ref(v_matcherLevels_4761_);
lean_dec_ref(v_params_4760_);
lean_dec(v_matcherName_4759_);
lean_dec_ref(v_toMatcherInfo_4758_);
lean_dec_ref(v_alts_4757_);
lean_dec(v_nExtra_4754_);
v_a_4799_ = lean_ctor_get(v___x_4769_, 0);
v_isSharedCheck_4806_ = !lean_is_exclusive(v___x_4769_);
if (v_isSharedCheck_4806_ == 0)
{
v___x_4801_ = v___x_4769_;
v_isShared_4802_ = v_isSharedCheck_4806_;
goto v_resetjp_4800_;
}
else
{
lean_inc(v_a_4799_);
lean_dec(v___x_4769_);
v___x_4801_ = lean_box(0);
v_isShared_4802_ = v_isSharedCheck_4806_;
goto v_resetjp_4800_;
}
v_resetjp_4800_:
{
lean_object* v___x_4804_; 
if (v_isShared_4802_ == 0)
{
v___x_4804_ = v___x_4801_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4805_; 
v_reuseFailAlloc_4805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_a_4799_);
v___x_4804_ = v_reuseFailAlloc_4805_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
return v___x_4804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed(lean_object* v_nExtra_4807_, lean_object* v___x_4808_, lean_object* v___x_4809_, lean_object* v_alts_4810_, lean_object* v_toMatcherInfo_4811_, lean_object* v_matcherName_4812_, lean_object* v_params_4813_, lean_object* v_matcherLevels_4814_, lean_object* v_motiveArgs_4815_, lean_object* v_body_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_){
_start:
{
uint8_t v___x_33023__boxed_4822_; uint8_t v___x_33024__boxed_4823_; lean_object* v_res_4824_; 
v___x_33023__boxed_4822_ = lean_unbox(v___x_4808_);
v___x_33024__boxed_4823_ = lean_unbox(v___x_4809_);
v_res_4824_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__3(v_nExtra_4807_, v___x_33023__boxed_4822_, v___x_33024__boxed_4823_, v_alts_4810_, v_toMatcherInfo_4811_, v_matcherName_4812_, v_params_4813_, v_matcherLevels_4814_, v_motiveArgs_4815_, v_body_4816_, v___y_4817_, v___y_4818_, v___y_4819_, v___y_4820_);
return v_res_4824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(lean_object* v_k_4825_, lean_object* v_ys_4826_, lean_object* v_args_4827_, lean_object* v___mask_4828_, lean_object* v___bodyType_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_){
_start:
{
lean_object* v___x_4835_; 
v___x_4835_ = lean_apply_7(v_k_4825_, v_ys_4826_, v_args_4827_, v___y_4830_, v___y_4831_, v___y_4832_, v___y_4833_, lean_box(0));
return v___x_4835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed(lean_object* v_k_4836_, lean_object* v_ys_4837_, lean_object* v_args_4838_, lean_object* v___mask_4839_, lean_object* v___bodyType_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_){
_start:
{
lean_object* v_res_4846_; 
v_res_4846_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(v_k_4836_, v_ys_4837_, v_args_4838_, v___mask_4839_, v___bodyType_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
lean_dec_ref(v___bodyType_4840_);
lean_dec_ref(v___mask_4839_);
return v_res_4846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(lean_object* v_origAltType_4847_, lean_object* v_altInfo_4848_, lean_object* v_k_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_){
_start:
{
lean_object* v___f_4855_; lean_object* v___x_4856_; 
v___f_4855_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_4855_, 0, v_k_4849_);
v___x_4856_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_origAltType_4847_, v_altInfo_4848_, v___f_4855_, v___y_4850_, v___y_4851_, v___y_4852_, v___y_4853_);
if (lean_obj_tag(v___x_4856_) == 0)
{
lean_object* v_a_4857_; lean_object* v___x_4859_; uint8_t v_isShared_4860_; uint8_t v_isSharedCheck_4864_; 
v_a_4857_ = lean_ctor_get(v___x_4856_, 0);
v_isSharedCheck_4864_ = !lean_is_exclusive(v___x_4856_);
if (v_isSharedCheck_4864_ == 0)
{
v___x_4859_ = v___x_4856_;
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
else
{
lean_inc(v_a_4857_);
lean_dec(v___x_4856_);
v___x_4859_ = lean_box(0);
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
v_resetjp_4858_:
{
lean_object* v___x_4862_; 
if (v_isShared_4860_ == 0)
{
v___x_4862_ = v___x_4859_;
goto v_reusejp_4861_;
}
else
{
lean_object* v_reuseFailAlloc_4863_; 
v_reuseFailAlloc_4863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4863_, 0, v_a_4857_);
v___x_4862_ = v_reuseFailAlloc_4863_;
goto v_reusejp_4861_;
}
v_reusejp_4861_:
{
return v___x_4862_;
}
}
}
else
{
lean_object* v_a_4865_; lean_object* v___x_4867_; uint8_t v_isShared_4868_; uint8_t v_isSharedCheck_4872_; 
v_a_4865_ = lean_ctor_get(v___x_4856_, 0);
v_isSharedCheck_4872_ = !lean_is_exclusive(v___x_4856_);
if (v_isSharedCheck_4872_ == 0)
{
v___x_4867_ = v___x_4856_;
v_isShared_4868_ = v_isSharedCheck_4872_;
goto v_resetjp_4866_;
}
else
{
lean_inc(v_a_4865_);
lean_dec(v___x_4856_);
v___x_4867_ = lean_box(0);
v_isShared_4868_ = v_isSharedCheck_4872_;
goto v_resetjp_4866_;
}
v_resetjp_4866_:
{
lean_object* v___x_4870_; 
if (v_isShared_4868_ == 0)
{
v___x_4870_ = v___x_4867_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4871_; 
v_reuseFailAlloc_4871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4871_, 0, v_a_4865_);
v___x_4870_ = v_reuseFailAlloc_4871_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
return v___x_4870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___boxed(lean_object* v_origAltType_4873_, lean_object* v_altInfo_4874_, lean_object* v_k_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_){
_start:
{
lean_object* v_res_4881_; 
v_res_4881_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v_origAltType_4873_, v_altInfo_4874_, v_k_4875_, v___y_4876_, v___y_4877_, v___y_4878_, v___y_4879_);
return v_res_4881_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(lean_object* v___x_4882_, lean_object* v___x_4883_, lean_object* v___f_4884_, lean_object* v_fst_4885_, lean_object* v___x_4886_, lean_object* v___x_4887_, lean_object* v___x_4888_, lean_object* v___x_4889_, lean_object* v___x_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_){
_start:
{
lean_object* v___x_4896_; 
v___x_4896_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v___x_4882_, v___x_4883_, v___f_4884_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
if (lean_obj_tag(v___x_4896_) == 0)
{
lean_object* v_a_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4911_; 
v_a_4897_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4911_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4911_ == 0)
{
v___x_4899_ = v___x_4896_;
v_isShared_4900_ = v_isSharedCheck_4911_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_a_4897_);
lean_dec(v___x_4896_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4911_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4909_; 
v___x_4901_ = lean_array_push(v_fst_4885_, v_a_4897_);
v___x_4902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4902_, 0, v___x_4886_);
lean_ctor_set(v___x_4902_, 1, v___x_4887_);
v___x_4903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4903_, 0, v___x_4888_);
lean_ctor_set(v___x_4903_, 1, v___x_4902_);
v___x_4904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4904_, 0, v___x_4889_);
lean_ctor_set(v___x_4904_, 1, v___x_4903_);
v___x_4905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4905_, 0, v___x_4890_);
lean_ctor_set(v___x_4905_, 1, v___x_4904_);
v___x_4906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4906_, 0, v___x_4901_);
lean_ctor_set(v___x_4906_, 1, v___x_4905_);
v___x_4907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4907_, 0, v___x_4906_);
if (v_isShared_4900_ == 0)
{
lean_ctor_set(v___x_4899_, 0, v___x_4907_);
v___x_4909_ = v___x_4899_;
goto v_reusejp_4908_;
}
else
{
lean_object* v_reuseFailAlloc_4910_; 
v_reuseFailAlloc_4910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4910_, 0, v___x_4907_);
v___x_4909_ = v_reuseFailAlloc_4910_;
goto v_reusejp_4908_;
}
v_reusejp_4908_:
{
return v___x_4909_;
}
}
}
else
{
lean_object* v_a_4912_; lean_object* v___x_4914_; uint8_t v_isShared_4915_; uint8_t v_isSharedCheck_4919_; 
lean_dec_ref(v___x_4890_);
lean_dec_ref(v___x_4889_);
lean_dec_ref(v___x_4888_);
lean_dec_ref(v___x_4887_);
lean_dec_ref(v___x_4886_);
lean_dec(v_fst_4885_);
v_a_4912_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4919_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4919_ == 0)
{
v___x_4914_ = v___x_4896_;
v_isShared_4915_ = v_isSharedCheck_4919_;
goto v_resetjp_4913_;
}
else
{
lean_inc(v_a_4912_);
lean_dec(v___x_4896_);
v___x_4914_ = lean_box(0);
v_isShared_4915_ = v_isSharedCheck_4919_;
goto v_resetjp_4913_;
}
v_resetjp_4913_:
{
lean_object* v___x_4917_; 
if (v_isShared_4915_ == 0)
{
v___x_4917_ = v___x_4914_;
goto v_reusejp_4916_;
}
else
{
lean_object* v_reuseFailAlloc_4918_; 
v_reuseFailAlloc_4918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4918_, 0, v_a_4912_);
v___x_4917_ = v_reuseFailAlloc_4918_;
goto v_reusejp_4916_;
}
v_reusejp_4916_:
{
return v___x_4917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed(lean_object* v___x_4920_, lean_object* v___x_4921_, lean_object* v___f_4922_, lean_object* v_fst_4923_, lean_object* v___x_4924_, lean_object* v___x_4925_, lean_object* v___x_4926_, lean_object* v___x_4927_, lean_object* v___x_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_){
_start:
{
lean_object* v_res_4934_; 
v_res_4934_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(v___x_4920_, v___x_4921_, v___f_4922_, v_fst_4923_, v___x_4924_, v___x_4925_, v___x_4926_, v___x_4927_, v___x_4928_, v___y_4929_, v___y_4930_, v___y_4931_, v___y_4932_);
return v_res_4934_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0(void){
_start:
{
lean_object* v___x_4935_; 
v___x_4935_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_4935_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(lean_object* v_msg_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_){
_start:
{
lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v_toApplicative_4948_; lean_object* v___x_4950_; uint8_t v_isShared_4951_; uint8_t v_isSharedCheck_5009_; 
v___x_4946_ = lean_obj_once(&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0, &l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0_once, _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0);
v___x_4947_ = l_ReaderT_instMonad___redArg(v___x_4946_);
v_toApplicative_4948_ = lean_ctor_get(v___x_4947_, 0);
v_isSharedCheck_5009_ = !lean_is_exclusive(v___x_4947_);
if (v_isSharedCheck_5009_ == 0)
{
lean_object* v_unused_5010_; 
v_unused_5010_ = lean_ctor_get(v___x_4947_, 1);
lean_dec(v_unused_5010_);
v___x_4950_ = v___x_4947_;
v_isShared_4951_ = v_isSharedCheck_5009_;
goto v_resetjp_4949_;
}
else
{
lean_inc(v_toApplicative_4948_);
lean_dec(v___x_4947_);
v___x_4950_ = lean_box(0);
v_isShared_4951_ = v_isSharedCheck_5009_;
goto v_resetjp_4949_;
}
v_resetjp_4949_:
{
lean_object* v_toFunctor_4952_; lean_object* v_toSeq_4953_; lean_object* v_toSeqLeft_4954_; lean_object* v_toSeqRight_4955_; lean_object* v___x_4957_; uint8_t v_isShared_4958_; uint8_t v_isSharedCheck_5007_; 
v_toFunctor_4952_ = lean_ctor_get(v_toApplicative_4948_, 0);
v_toSeq_4953_ = lean_ctor_get(v_toApplicative_4948_, 2);
v_toSeqLeft_4954_ = lean_ctor_get(v_toApplicative_4948_, 3);
v_toSeqRight_4955_ = lean_ctor_get(v_toApplicative_4948_, 4);
v_isSharedCheck_5007_ = !lean_is_exclusive(v_toApplicative_4948_);
if (v_isSharedCheck_5007_ == 0)
{
lean_object* v_unused_5008_; 
v_unused_5008_ = lean_ctor_get(v_toApplicative_4948_, 1);
lean_dec(v_unused_5008_);
v___x_4957_ = v_toApplicative_4948_;
v_isShared_4958_ = v_isSharedCheck_5007_;
goto v_resetjp_4956_;
}
else
{
lean_inc(v_toSeqRight_4955_);
lean_inc(v_toSeqLeft_4954_);
lean_inc(v_toSeq_4953_);
lean_inc(v_toFunctor_4952_);
lean_dec(v_toApplicative_4948_);
v___x_4957_ = lean_box(0);
v_isShared_4958_ = v_isSharedCheck_5007_;
goto v_resetjp_4956_;
}
v_resetjp_4956_:
{
lean_object* v___f_4959_; lean_object* v___f_4960_; lean_object* v___f_4961_; lean_object* v___f_4962_; lean_object* v___x_4963_; lean_object* v___f_4964_; lean_object* v___f_4965_; lean_object* v___f_4966_; lean_object* v___x_4968_; 
v___f_4959_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__1));
v___f_4960_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__2));
lean_inc_ref(v_toFunctor_4952_);
v___f_4961_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4961_, 0, v_toFunctor_4952_);
v___f_4962_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4962_, 0, v_toFunctor_4952_);
v___x_4963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4963_, 0, v___f_4961_);
lean_ctor_set(v___x_4963_, 1, v___f_4962_);
v___f_4964_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4964_, 0, v_toSeqRight_4955_);
v___f_4965_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4965_, 0, v_toSeqLeft_4954_);
v___f_4966_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4966_, 0, v_toSeq_4953_);
if (v_isShared_4958_ == 0)
{
lean_ctor_set(v___x_4957_, 4, v___f_4964_);
lean_ctor_set(v___x_4957_, 3, v___f_4965_);
lean_ctor_set(v___x_4957_, 2, v___f_4966_);
lean_ctor_set(v___x_4957_, 1, v___f_4959_);
lean_ctor_set(v___x_4957_, 0, v___x_4963_);
v___x_4968_ = v___x_4957_;
goto v_reusejp_4967_;
}
else
{
lean_object* v_reuseFailAlloc_5006_; 
v_reuseFailAlloc_5006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5006_, 0, v___x_4963_);
lean_ctor_set(v_reuseFailAlloc_5006_, 1, v___f_4959_);
lean_ctor_set(v_reuseFailAlloc_5006_, 2, v___f_4966_);
lean_ctor_set(v_reuseFailAlloc_5006_, 3, v___f_4965_);
lean_ctor_set(v_reuseFailAlloc_5006_, 4, v___f_4964_);
v___x_4968_ = v_reuseFailAlloc_5006_;
goto v_reusejp_4967_;
}
v_reusejp_4967_:
{
lean_object* v___x_4970_; 
if (v_isShared_4951_ == 0)
{
lean_ctor_set(v___x_4950_, 1, v___f_4960_);
lean_ctor_set(v___x_4950_, 0, v___x_4968_);
v___x_4970_ = v___x_4950_;
goto v_reusejp_4969_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5005_, 0, v___x_4968_);
lean_ctor_set(v_reuseFailAlloc_5005_, 1, v___f_4960_);
v___x_4970_ = v_reuseFailAlloc_5005_;
goto v_reusejp_4969_;
}
v_reusejp_4969_:
{
lean_object* v___x_4971_; lean_object* v_toApplicative_4972_; lean_object* v___x_4974_; uint8_t v_isShared_4975_; uint8_t v_isSharedCheck_5003_; 
v___x_4971_ = l_ReaderT_instMonad___redArg(v___x_4970_);
v_toApplicative_4972_ = lean_ctor_get(v___x_4971_, 0);
v_isSharedCheck_5003_ = !lean_is_exclusive(v___x_4971_);
if (v_isSharedCheck_5003_ == 0)
{
lean_object* v_unused_5004_; 
v_unused_5004_ = lean_ctor_get(v___x_4971_, 1);
lean_dec(v_unused_5004_);
v___x_4974_ = v___x_4971_;
v_isShared_4975_ = v_isSharedCheck_5003_;
goto v_resetjp_4973_;
}
else
{
lean_inc(v_toApplicative_4972_);
lean_dec(v___x_4971_);
v___x_4974_ = lean_box(0);
v_isShared_4975_ = v_isSharedCheck_5003_;
goto v_resetjp_4973_;
}
v_resetjp_4973_:
{
lean_object* v_toFunctor_4976_; lean_object* v_toSeq_4977_; lean_object* v_toSeqLeft_4978_; lean_object* v_toSeqRight_4979_; lean_object* v___x_4981_; uint8_t v_isShared_4982_; uint8_t v_isSharedCheck_5001_; 
v_toFunctor_4976_ = lean_ctor_get(v_toApplicative_4972_, 0);
v_toSeq_4977_ = lean_ctor_get(v_toApplicative_4972_, 2);
v_toSeqLeft_4978_ = lean_ctor_get(v_toApplicative_4972_, 3);
v_toSeqRight_4979_ = lean_ctor_get(v_toApplicative_4972_, 4);
v_isSharedCheck_5001_ = !lean_is_exclusive(v_toApplicative_4972_);
if (v_isSharedCheck_5001_ == 0)
{
lean_object* v_unused_5002_; 
v_unused_5002_ = lean_ctor_get(v_toApplicative_4972_, 1);
lean_dec(v_unused_5002_);
v___x_4981_ = v_toApplicative_4972_;
v_isShared_4982_ = v_isSharedCheck_5001_;
goto v_resetjp_4980_;
}
else
{
lean_inc(v_toSeqRight_4979_);
lean_inc(v_toSeqLeft_4978_);
lean_inc(v_toSeq_4977_);
lean_inc(v_toFunctor_4976_);
lean_dec(v_toApplicative_4972_);
v___x_4981_ = lean_box(0);
v_isShared_4982_ = v_isSharedCheck_5001_;
goto v_resetjp_4980_;
}
v_resetjp_4980_:
{
lean_object* v___f_4983_; lean_object* v___f_4984_; lean_object* v___f_4985_; lean_object* v___f_4986_; lean_object* v___x_4987_; lean_object* v___f_4988_; lean_object* v___f_4989_; lean_object* v___f_4990_; lean_object* v___x_4992_; 
v___f_4983_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3));
v___f_4984_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4));
lean_inc_ref(v_toFunctor_4976_);
v___f_4985_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4985_, 0, v_toFunctor_4976_);
v___f_4986_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4986_, 0, v_toFunctor_4976_);
v___x_4987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4987_, 0, v___f_4985_);
lean_ctor_set(v___x_4987_, 1, v___f_4986_);
v___f_4988_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4988_, 0, v_toSeqRight_4979_);
v___f_4989_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4989_, 0, v_toSeqLeft_4978_);
v___f_4990_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4990_, 0, v_toSeq_4977_);
if (v_isShared_4982_ == 0)
{
lean_ctor_set(v___x_4981_, 4, v___f_4988_);
lean_ctor_set(v___x_4981_, 3, v___f_4989_);
lean_ctor_set(v___x_4981_, 2, v___f_4990_);
lean_ctor_set(v___x_4981_, 1, v___f_4983_);
lean_ctor_set(v___x_4981_, 0, v___x_4987_);
v___x_4992_ = v___x_4981_;
goto v_reusejp_4991_;
}
else
{
lean_object* v_reuseFailAlloc_5000_; 
v_reuseFailAlloc_5000_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5000_, 0, v___x_4987_);
lean_ctor_set(v_reuseFailAlloc_5000_, 1, v___f_4983_);
lean_ctor_set(v_reuseFailAlloc_5000_, 2, v___f_4990_);
lean_ctor_set(v_reuseFailAlloc_5000_, 3, v___f_4989_);
lean_ctor_set(v_reuseFailAlloc_5000_, 4, v___f_4988_);
v___x_4992_ = v_reuseFailAlloc_5000_;
goto v_reusejp_4991_;
}
v_reusejp_4991_:
{
lean_object* v___x_4994_; 
if (v_isShared_4975_ == 0)
{
lean_ctor_set(v___x_4974_, 1, v___f_4984_);
lean_ctor_set(v___x_4974_, 0, v___x_4992_);
v___x_4994_ = v___x_4974_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v___x_4992_);
lean_ctor_set(v_reuseFailAlloc_4999_, 1, v___f_4984_);
v___x_4994_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_27743__overap_4997_; lean_object* v___x_4998_; 
v___x_4995_ = l_Lean_instInhabitedExpr;
v___x_4996_ = l_instInhabitedOfMonad___redArg(v___x_4994_, v___x_4995_);
v___x_27743__overap_4997_ = lean_panic_fn(v___x_4996_, v_msg_4940_);
v___x_4998_ = lean_apply_5(v___x_27743__overap_4997_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_, lean_box(0));
return v___x_4998_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___boxed(lean_object* v_msg_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_){
_start:
{
lean_object* v_res_5017_; 
v_res_5017_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(v_msg_5011_, v___y_5012_, v___y_5013_, v___y_5014_, v___y_5015_);
return v_res_5017_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(lean_object* v_args_5018_, lean_object* v_ys_5019_, lean_object* v_ys2_5020_, lean_object* v_ys3_5021_, lean_object* v_onAlt_5022_, lean_object* v_a_5023_, uint8_t v___x_5024_, uint8_t v_useSplitter_5025_, lean_object* v___x_5026_, lean_object* v_ys4_5027_, lean_object* v_altType_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_){
_start:
{
lean_object* v___y_5035_; lean_object* v___x_5045_; lean_object* v___x_5046_; 
lean_inc_ref(v_args_5018_);
v___x_5045_ = l_Array_append___redArg(v_args_5018_, v_ys3_5021_);
lean_inc(v___y_5032_);
lean_inc_ref(v___y_5031_);
lean_inc(v___y_5030_);
lean_inc_ref(v___y_5029_);
v___x_5046_ = l_Lean_Meta_instantiateLambda(v___x_5026_, v___x_5045_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_);
lean_dec_ref(v___x_5045_);
if (lean_obj_tag(v___x_5046_) == 0)
{
v___y_5035_ = v___x_5046_;
goto v___jp_5034_;
}
else
{
lean_object* v_a_5047_; uint8_t v___y_5049_; uint8_t v___x_5052_; 
v_a_5047_ = lean_ctor_get(v___x_5046_, 0);
lean_inc(v_a_5047_);
v___x_5052_ = l_Lean_Exception_isInterrupt(v_a_5047_);
if (v___x_5052_ == 0)
{
uint8_t v___x_5053_; 
v___x_5053_ = l_Lean_Exception_isRuntime(v_a_5047_);
v___y_5049_ = v___x_5053_;
goto v___jp_5048_;
}
else
{
lean_dec(v_a_5047_);
v___y_5049_ = v___x_5052_;
goto v___jp_5048_;
}
v___jp_5048_:
{
if (v___y_5049_ == 0)
{
lean_object* v___x_5050_; lean_object* v___x_5051_; 
lean_dec_ref(v___x_5046_);
v___x_5050_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2);
v___x_5051_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_5050_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_);
v___y_5035_ = v___x_5051_;
goto v___jp_5034_;
}
else
{
v___y_5035_ = v___x_5046_;
goto v___jp_5034_;
}
}
}
v___jp_5034_:
{
if (lean_obj_tag(v___y_5035_) == 0)
{
lean_object* v_a_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; 
v_a_5036_ = lean_ctor_get(v___y_5035_, 0);
lean_inc(v_a_5036_);
lean_dec_ref(v___y_5035_);
lean_inc_ref(v_ys4_5027_);
lean_inc_ref(v_ys3_5021_);
lean_inc_ref(v_ys2_5020_);
lean_inc_ref(v_ys_5019_);
v___x_5037_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5037_, 0, v_args_5018_);
lean_ctor_set(v___x_5037_, 1, v_ys_5019_);
lean_ctor_set(v___x_5037_, 2, v_ys2_5020_);
lean_ctor_set(v___x_5037_, 3, v_ys3_5021_);
lean_ctor_set(v___x_5037_, 4, v_ys4_5027_);
lean_inc(v___y_5032_);
lean_inc_ref(v___y_5031_);
lean_inc(v___y_5030_);
lean_inc_ref(v___y_5029_);
v___x_5038_ = lean_apply_9(v_onAlt_5022_, v_a_5023_, v_altType_5028_, v___x_5037_, v_a_5036_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_, lean_box(0));
if (lean_obj_tag(v___x_5038_) == 0)
{
lean_object* v_a_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; uint8_t v___x_5043_; lean_object* v___x_5044_; 
v_a_5039_ = lean_ctor_get(v___x_5038_, 0);
lean_inc(v_a_5039_);
lean_dec_ref(v___x_5038_);
v___x_5040_ = l_Array_append___redArg(v_ys_5019_, v_ys2_5020_);
lean_dec_ref(v_ys2_5020_);
v___x_5041_ = l_Array_append___redArg(v___x_5040_, v_ys3_5021_);
lean_dec_ref(v_ys3_5021_);
v___x_5042_ = l_Array_append___redArg(v___x_5041_, v_ys4_5027_);
lean_dec_ref(v_ys4_5027_);
v___x_5043_ = 1;
v___x_5044_ = l_Lean_Meta_mkLambdaFVars(v___x_5042_, v_a_5039_, v___x_5024_, v_useSplitter_5025_, v___x_5024_, v_useSplitter_5025_, v___x_5043_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_);
lean_dec(v___y_5032_);
lean_dec_ref(v___y_5031_);
lean_dec(v___y_5030_);
lean_dec_ref(v___y_5029_);
lean_dec_ref(v___x_5042_);
return v___x_5044_;
}
else
{
lean_dec(v___y_5032_);
lean_dec_ref(v___y_5031_);
lean_dec(v___y_5030_);
lean_dec_ref(v___y_5029_);
lean_dec_ref(v_ys4_5027_);
lean_dec_ref(v_ys3_5021_);
lean_dec_ref(v_ys2_5020_);
lean_dec_ref(v_ys_5019_);
return v___x_5038_;
}
}
else
{
lean_dec(v___y_5032_);
lean_dec_ref(v___y_5031_);
lean_dec(v___y_5030_);
lean_dec_ref(v___y_5029_);
lean_dec_ref(v_altType_5028_);
lean_dec_ref(v_ys4_5027_);
lean_dec(v_a_5023_);
lean_dec_ref(v_onAlt_5022_);
lean_dec_ref(v_ys3_5021_);
lean_dec_ref(v_ys2_5020_);
lean_dec_ref(v_ys_5019_);
lean_dec_ref(v_args_5018_);
return v___y_5035_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed(lean_object* v_args_5054_, lean_object* v_ys_5055_, lean_object* v_ys2_5056_, lean_object* v_ys3_5057_, lean_object* v_onAlt_5058_, lean_object* v_a_5059_, lean_object* v___x_5060_, lean_object* v_useSplitter_5061_, lean_object* v___x_5062_, lean_object* v_ys4_5063_, lean_object* v_altType_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_){
_start:
{
uint8_t v___x_33415__boxed_5070_; uint8_t v_useSplitter_boxed_5071_; lean_object* v_res_5072_; 
v___x_33415__boxed_5070_ = lean_unbox(v___x_5060_);
v_useSplitter_boxed_5071_ = lean_unbox(v_useSplitter_5061_);
v_res_5072_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(v_args_5054_, v_ys_5055_, v_ys2_5056_, v_ys3_5057_, v_onAlt_5058_, v_a_5059_, v___x_33415__boxed_5070_, v_useSplitter_boxed_5071_, v___x_5062_, v_ys4_5063_, v_altType_5064_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_);
return v_res_5072_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(lean_object* v_args_5073_, lean_object* v_ys_5074_, lean_object* v_ys2_5075_, lean_object* v_onAlt_5076_, lean_object* v_a_5077_, uint8_t v___x_5078_, uint8_t v_useSplitter_5079_, lean_object* v___x_5080_, lean_object* v_extraEqualities_5081_, lean_object* v_ys3_5082_, lean_object* v_altType_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_){
_start:
{
lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___f_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; 
v___x_5089_ = lean_box(v___x_5078_);
v___x_5090_ = lean_box(v_useSplitter_5079_);
v___f_5091_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed), 16, 9);
lean_closure_set(v___f_5091_, 0, v_args_5073_);
lean_closure_set(v___f_5091_, 1, v_ys_5074_);
lean_closure_set(v___f_5091_, 2, v_ys2_5075_);
lean_closure_set(v___f_5091_, 3, v_ys3_5082_);
lean_closure_set(v___f_5091_, 4, v_onAlt_5076_);
lean_closure_set(v___f_5091_, 5, v_a_5077_);
lean_closure_set(v___f_5091_, 6, v___x_5089_);
lean_closure_set(v___f_5091_, 7, v___x_5090_);
lean_closure_set(v___f_5091_, 8, v___x_5080_);
v___x_5092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5092_, 0, v_extraEqualities_5081_);
v___x_5093_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_5083_, v___x_5092_, v___f_5091_, v___x_5078_, v___x_5078_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_);
return v___x_5093_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed(lean_object* v_args_5094_, lean_object* v_ys_5095_, lean_object* v_ys2_5096_, lean_object* v_onAlt_5097_, lean_object* v_a_5098_, lean_object* v___x_5099_, lean_object* v_useSplitter_5100_, lean_object* v___x_5101_, lean_object* v_extraEqualities_5102_, lean_object* v_ys3_5103_, lean_object* v_altType_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_){
_start:
{
uint8_t v___x_33480__boxed_5110_; uint8_t v_useSplitter_boxed_5111_; lean_object* v_res_5112_; 
v___x_33480__boxed_5110_ = lean_unbox(v___x_5099_);
v_useSplitter_boxed_5111_ = lean_unbox(v_useSplitter_5100_);
v_res_5112_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(v_args_5094_, v_ys_5095_, v_ys2_5096_, v_onAlt_5097_, v_a_5098_, v___x_33480__boxed_5110_, v_useSplitter_boxed_5111_, v___x_5101_, v_extraEqualities_5102_, v_ys3_5103_, v_altType_5104_, v___y_5105_, v___y_5106_, v___y_5107_, v___y_5108_);
return v_res_5112_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(lean_object* v_args_5113_, lean_object* v_ys_5114_, lean_object* v_onAlt_5115_, lean_object* v_a_5116_, uint8_t v___x_5117_, uint8_t v_useSplitter_5118_, lean_object* v___x_5119_, lean_object* v_extraEqualities_5120_, lean_object* v_numDiscrEqs_5121_, lean_object* v_ys2_5122_, lean_object* v_altType_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_){
_start:
{
lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___f_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; 
v___x_5129_ = lean_box(v___x_5117_);
v___x_5130_ = lean_box(v_useSplitter_5118_);
v___f_5131_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_5131_, 0, v_args_5113_);
lean_closure_set(v___f_5131_, 1, v_ys_5114_);
lean_closure_set(v___f_5131_, 2, v_ys2_5122_);
lean_closure_set(v___f_5131_, 3, v_onAlt_5115_);
lean_closure_set(v___f_5131_, 4, v_a_5116_);
lean_closure_set(v___f_5131_, 5, v___x_5129_);
lean_closure_set(v___f_5131_, 6, v___x_5130_);
lean_closure_set(v___f_5131_, 7, v___x_5119_);
lean_closure_set(v___f_5131_, 8, v_extraEqualities_5120_);
v___x_5132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5132_, 0, v_numDiscrEqs_5121_);
v___x_5133_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_5123_, v___x_5132_, v___f_5131_, v___x_5117_, v___x_5117_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_);
return v___x_5133_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed(lean_object* v_args_5134_, lean_object* v_ys_5135_, lean_object* v_onAlt_5136_, lean_object* v_a_5137_, lean_object* v___x_5138_, lean_object* v_useSplitter_5139_, lean_object* v___x_5140_, lean_object* v_extraEqualities_5141_, lean_object* v_numDiscrEqs_5142_, lean_object* v_ys2_5143_, lean_object* v_altType_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_){
_start:
{
uint8_t v___x_33511__boxed_5150_; uint8_t v_useSplitter_boxed_5151_; lean_object* v_res_5152_; 
v___x_33511__boxed_5150_ = lean_unbox(v___x_5138_);
v_useSplitter_boxed_5151_ = lean_unbox(v_useSplitter_5139_);
v_res_5152_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(v_args_5134_, v_ys_5135_, v_onAlt_5136_, v_a_5137_, v___x_33511__boxed_5150_, v_useSplitter_boxed_5151_, v___x_5140_, v_extraEqualities_5141_, v_numDiscrEqs_5142_, v_ys2_5143_, v_altType_5144_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_);
return v_res_5152_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(lean_object* v___x_5153_, lean_object* v___x_5154_, lean_object* v_onAlt_5155_, lean_object* v_a_5156_, uint8_t v___x_5157_, uint8_t v_useSplitter_5158_, lean_object* v___x_5159_, lean_object* v_extraEqualities_5160_, lean_object* v_numDiscrEqs_5161_, uint8_t v_hasUnitThunk_5162_, lean_object* v___x_5163_, lean_object* v_ys_5164_, lean_object* v_args_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_){
_start:
{
lean_object* v_numFields_5171_; lean_object* v_numOverlaps_5172_; uint8_t v_hasUnitThunk_5173_; lean_object* v___x_5174_; uint8_t v___x_5175_; 
v_numFields_5171_ = lean_ctor_get(v___x_5153_, 0);
v_numOverlaps_5172_ = lean_ctor_get(v___x_5153_, 1);
v_hasUnitThunk_5173_ = lean_ctor_get_uint8(v___x_5153_, sizeof(void*)*2);
v___x_5174_ = lean_array_get_size(v_ys_5164_);
v___x_5175_ = lean_nat_dec_eq(v___x_5174_, v_numFields_5171_);
if (v___x_5175_ == 0)
{
lean_object* v___x_5176_; lean_object* v___x_5177_; 
lean_dec_ref(v_args_5165_);
lean_dec_ref(v_ys_5164_);
lean_dec(v_numDiscrEqs_5161_);
lean_dec(v_extraEqualities_5160_);
lean_dec_ref(v___x_5159_);
lean_dec(v_a_5156_);
lean_dec_ref(v_onAlt_5155_);
lean_dec_ref(v___x_5154_);
v___x_5176_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3);
v___x_5177_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(v___x_5176_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_);
return v___x_5177_;
}
else
{
lean_object* v___x_5178_; 
lean_inc(v___y_5169_);
lean_inc_ref(v___y_5168_);
lean_inc(v___y_5167_);
lean_inc_ref(v___y_5166_);
v___x_5178_ = l_Lean_Meta_instantiateForall(v___x_5154_, v_ys_5164_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_);
if (lean_obj_tag(v___x_5178_) == 0)
{
lean_object* v_a_5179_; lean_object* v___x_5181_; uint8_t v_isShared_5182_; uint8_t v_isSharedCheck_5208_; 
v_a_5179_ = lean_ctor_get(v___x_5178_, 0);
v_isSharedCheck_5208_ = !lean_is_exclusive(v___x_5178_);
if (v_isSharedCheck_5208_ == 0)
{
v___x_5181_ = v___x_5178_;
v_isShared_5182_ = v_isSharedCheck_5208_;
goto v_resetjp_5180_;
}
else
{
lean_inc(v_a_5179_);
lean_dec(v___x_5178_);
v___x_5181_ = lean_box(0);
v_isShared_5182_ = v_isSharedCheck_5208_;
goto v_resetjp_5180_;
}
v_resetjp_5180_:
{
lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___f_5185_; lean_object* v_altType_5187_; lean_object* v___y_5188_; lean_object* v___y_5189_; lean_object* v___y_5190_; lean_object* v___y_5191_; 
v___x_5183_ = lean_box(v___x_5157_);
v___x_5184_ = lean_box(v_useSplitter_5158_);
v___f_5185_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed), 16, 9);
lean_closure_set(v___f_5185_, 0, v_args_5165_);
lean_closure_set(v___f_5185_, 1, v_ys_5164_);
lean_closure_set(v___f_5185_, 2, v_onAlt_5155_);
lean_closure_set(v___f_5185_, 3, v_a_5156_);
lean_closure_set(v___f_5185_, 4, v___x_5183_);
lean_closure_set(v___f_5185_, 5, v___x_5184_);
lean_closure_set(v___f_5185_, 6, v___x_5159_);
lean_closure_set(v___f_5185_, 7, v_extraEqualities_5160_);
lean_closure_set(v___f_5185_, 8, v_numDiscrEqs_5161_);
if (v_hasUnitThunk_5162_ == 0)
{
v_altType_5187_ = v_a_5179_;
v___y_5188_ = v___y_5166_;
v___y_5189_ = v___y_5167_;
v___y_5190_ = v___y_5168_;
v___y_5191_ = v___y_5169_;
goto v___jp_5186_;
}
else
{
lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; 
v___x_5203_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2);
v___x_5204_ = lean_mk_empty_array_with_capacity(v___x_5163_);
v___x_5205_ = lean_array_push(v___x_5204_, v___x_5203_);
lean_inc(v___y_5169_);
lean_inc_ref(v___y_5168_);
lean_inc(v___y_5167_);
lean_inc_ref(v___y_5166_);
v___x_5206_ = l_Lean_Meta_instantiateForall(v_a_5179_, v___x_5205_, v___y_5166_, v___y_5167_, v___y_5168_, v___y_5169_);
lean_dec_ref(v___x_5205_);
if (lean_obj_tag(v___x_5206_) == 0)
{
lean_object* v_a_5207_; 
v_a_5207_ = lean_ctor_get(v___x_5206_, 0);
lean_inc(v_a_5207_);
lean_dec_ref(v___x_5206_);
v_altType_5187_ = v_a_5207_;
v___y_5188_ = v___y_5166_;
v___y_5189_ = v___y_5167_;
v___y_5190_ = v___y_5168_;
v___y_5191_ = v___y_5169_;
goto v___jp_5186_;
}
else
{
lean_dec_ref(v___f_5185_);
lean_del_object(v___x_5181_);
lean_dec(v___y_5169_);
lean_dec_ref(v___y_5168_);
lean_dec(v___y_5167_);
lean_dec_ref(v___y_5166_);
return v___x_5206_;
}
}
v___jp_5186_:
{
lean_object* v___x_5193_; 
lean_inc(v_numOverlaps_5172_);
if (v_isShared_5182_ == 0)
{
lean_ctor_set_tag(v___x_5181_, 1);
lean_ctor_set(v___x_5181_, 0, v_numOverlaps_5172_);
v___x_5193_ = v___x_5181_;
goto v_reusejp_5192_;
}
else
{
lean_object* v_reuseFailAlloc_5202_; 
v_reuseFailAlloc_5202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5202_, 0, v_numOverlaps_5172_);
v___x_5193_ = v_reuseFailAlloc_5202_;
goto v_reusejp_5192_;
}
v_reusejp_5192_:
{
lean_object* v___x_5194_; 
lean_inc(v___y_5191_);
lean_inc_ref(v___y_5190_);
lean_inc(v___y_5189_);
lean_inc_ref(v___y_5188_);
v___x_5194_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_5187_, v___x_5193_, v___f_5185_, v___x_5157_, v___x_5157_, v___y_5188_, v___y_5189_, v___y_5190_, v___y_5191_);
if (lean_obj_tag(v___x_5194_) == 0)
{
if (v_hasUnitThunk_5173_ == 0)
{
lean_dec(v___y_5191_);
lean_dec_ref(v___y_5190_);
lean_dec(v___y_5189_);
lean_dec_ref(v___y_5188_);
return v___x_5194_;
}
else
{
lean_object* v_a_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; 
v_a_5195_ = lean_ctor_get(v___x_5194_, 0);
lean_inc(v_a_5195_);
lean_dec_ref(v___x_5194_);
v___x_5196_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__2));
v___x_5197_ = lean_unsigned_to_nat(2u);
v___x_5198_ = lean_mk_empty_array_with_capacity(v___x_5197_);
lean_dec_ref(v___x_5198_);
v___x_5199_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__6);
v___x_5200_ = lean_array_push(v___x_5199_, v_a_5195_);
v___x_5201_ = l_Lean_Meta_mkAppM(v___x_5196_, v___x_5200_, v___y_5188_, v___y_5189_, v___y_5190_, v___y_5191_);
return v___x_5201_;
}
}
else
{
lean_dec(v___y_5191_);
lean_dec_ref(v___y_5190_);
lean_dec(v___y_5189_);
lean_dec_ref(v___y_5188_);
return v___x_5194_;
}
}
}
}
}
else
{
lean_dec(v___y_5169_);
lean_dec_ref(v___y_5168_);
lean_dec(v___y_5167_);
lean_dec_ref(v___y_5166_);
lean_dec_ref(v_args_5165_);
lean_dec_ref(v_ys_5164_);
lean_dec(v_numDiscrEqs_5161_);
lean_dec(v_extraEqualities_5160_);
lean_dec_ref(v___x_5159_);
lean_dec(v_a_5156_);
lean_dec_ref(v_onAlt_5155_);
return v___x_5178_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_5209_ = _args[0];
lean_object* v___x_5210_ = _args[1];
lean_object* v_onAlt_5211_ = _args[2];
lean_object* v_a_5212_ = _args[3];
lean_object* v___x_5213_ = _args[4];
lean_object* v_useSplitter_5214_ = _args[5];
lean_object* v___x_5215_ = _args[6];
lean_object* v_extraEqualities_5216_ = _args[7];
lean_object* v_numDiscrEqs_5217_ = _args[8];
lean_object* v_hasUnitThunk_5218_ = _args[9];
lean_object* v___x_5219_ = _args[10];
lean_object* v_ys_5220_ = _args[11];
lean_object* v_args_5221_ = _args[12];
lean_object* v___y_5222_ = _args[13];
lean_object* v___y_5223_ = _args[14];
lean_object* v___y_5224_ = _args[15];
lean_object* v___y_5225_ = _args[16];
lean_object* v___y_5226_ = _args[17];
_start:
{
uint8_t v___x_33576__boxed_5227_; uint8_t v_useSplitter_boxed_5228_; uint8_t v_hasUnitThunk_boxed_5229_; lean_object* v_res_5230_; 
v___x_33576__boxed_5227_ = lean_unbox(v___x_5213_);
v_useSplitter_boxed_5228_ = lean_unbox(v_useSplitter_5214_);
v_hasUnitThunk_boxed_5229_ = lean_unbox(v_hasUnitThunk_5218_);
v_res_5230_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(v___x_5209_, v___x_5210_, v_onAlt_5211_, v_a_5212_, v___x_33576__boxed_5227_, v_useSplitter_boxed_5228_, v___x_5215_, v_extraEqualities_5216_, v_numDiscrEqs_5217_, v_hasUnitThunk_boxed_5229_, v___x_5219_, v_ys_5220_, v_args_5221_, v___y_5222_, v___y_5223_, v___y_5224_, v___y_5225_);
lean_dec(v___x_5219_);
lean_dec_ref(v___x_5209_);
return v_res_5230_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(lean_object* v___x_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_){
_start:
{
lean_object* v___x_5237_; 
v___x_5237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5237_, 0, v___x_5231_);
return v___x_5237_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed(lean_object* v___x_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_){
_start:
{
lean_object* v_res_5244_; 
v_res_5244_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(v___x_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_);
lean_dec(v___y_5242_);
lean_dec_ref(v___y_5241_);
lean_dec(v___y_5240_);
lean_dec_ref(v___y_5239_);
return v_res_5244_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(lean_object* v_msg_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_){
_start:
{
lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v_toApplicative_5253_; lean_object* v___x_5255_; uint8_t v_isShared_5256_; uint8_t v_isSharedCheck_5314_; 
v___x_5251_ = lean_obj_once(&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0, &l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0_once, _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0);
v___x_5252_ = l_ReaderT_instMonad___redArg(v___x_5251_);
v_toApplicative_5253_ = lean_ctor_get(v___x_5252_, 0);
v_isSharedCheck_5314_ = !lean_is_exclusive(v___x_5252_);
if (v_isSharedCheck_5314_ == 0)
{
lean_object* v_unused_5315_; 
v_unused_5315_ = lean_ctor_get(v___x_5252_, 1);
lean_dec(v_unused_5315_);
v___x_5255_ = v___x_5252_;
v_isShared_5256_ = v_isSharedCheck_5314_;
goto v_resetjp_5254_;
}
else
{
lean_inc(v_toApplicative_5253_);
lean_dec(v___x_5252_);
v___x_5255_ = lean_box(0);
v_isShared_5256_ = v_isSharedCheck_5314_;
goto v_resetjp_5254_;
}
v_resetjp_5254_:
{
lean_object* v_toFunctor_5257_; lean_object* v_toSeq_5258_; lean_object* v_toSeqLeft_5259_; lean_object* v_toSeqRight_5260_; lean_object* v___x_5262_; uint8_t v_isShared_5263_; uint8_t v_isSharedCheck_5312_; 
v_toFunctor_5257_ = lean_ctor_get(v_toApplicative_5253_, 0);
v_toSeq_5258_ = lean_ctor_get(v_toApplicative_5253_, 2);
v_toSeqLeft_5259_ = lean_ctor_get(v_toApplicative_5253_, 3);
v_toSeqRight_5260_ = lean_ctor_get(v_toApplicative_5253_, 4);
v_isSharedCheck_5312_ = !lean_is_exclusive(v_toApplicative_5253_);
if (v_isSharedCheck_5312_ == 0)
{
lean_object* v_unused_5313_; 
v_unused_5313_ = lean_ctor_get(v_toApplicative_5253_, 1);
lean_dec(v_unused_5313_);
v___x_5262_ = v_toApplicative_5253_;
v_isShared_5263_ = v_isSharedCheck_5312_;
goto v_resetjp_5261_;
}
else
{
lean_inc(v_toSeqRight_5260_);
lean_inc(v_toSeqLeft_5259_);
lean_inc(v_toSeq_5258_);
lean_inc(v_toFunctor_5257_);
lean_dec(v_toApplicative_5253_);
v___x_5262_ = lean_box(0);
v_isShared_5263_ = v_isSharedCheck_5312_;
goto v_resetjp_5261_;
}
v_resetjp_5261_:
{
lean_object* v___f_5264_; lean_object* v___f_5265_; lean_object* v___f_5266_; lean_object* v___f_5267_; lean_object* v___x_5268_; lean_object* v___f_5269_; lean_object* v___f_5270_; lean_object* v___f_5271_; lean_object* v___x_5273_; 
v___f_5264_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__1));
v___f_5265_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__2));
lean_inc_ref(v_toFunctor_5257_);
v___f_5266_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5266_, 0, v_toFunctor_5257_);
v___f_5267_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5267_, 0, v_toFunctor_5257_);
v___x_5268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5268_, 0, v___f_5266_);
lean_ctor_set(v___x_5268_, 1, v___f_5267_);
v___f_5269_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5269_, 0, v_toSeqRight_5260_);
v___f_5270_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5270_, 0, v_toSeqLeft_5259_);
v___f_5271_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5271_, 0, v_toSeq_5258_);
if (v_isShared_5263_ == 0)
{
lean_ctor_set(v___x_5262_, 4, v___f_5269_);
lean_ctor_set(v___x_5262_, 3, v___f_5270_);
lean_ctor_set(v___x_5262_, 2, v___f_5271_);
lean_ctor_set(v___x_5262_, 1, v___f_5264_);
lean_ctor_set(v___x_5262_, 0, v___x_5268_);
v___x_5273_ = v___x_5262_;
goto v_reusejp_5272_;
}
else
{
lean_object* v_reuseFailAlloc_5311_; 
v_reuseFailAlloc_5311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5311_, 0, v___x_5268_);
lean_ctor_set(v_reuseFailAlloc_5311_, 1, v___f_5264_);
lean_ctor_set(v_reuseFailAlloc_5311_, 2, v___f_5271_);
lean_ctor_set(v_reuseFailAlloc_5311_, 3, v___f_5270_);
lean_ctor_set(v_reuseFailAlloc_5311_, 4, v___f_5269_);
v___x_5273_ = v_reuseFailAlloc_5311_;
goto v_reusejp_5272_;
}
v_reusejp_5272_:
{
lean_object* v___x_5275_; 
if (v_isShared_5256_ == 0)
{
lean_ctor_set(v___x_5255_, 1, v___f_5265_);
lean_ctor_set(v___x_5255_, 0, v___x_5273_);
v___x_5275_ = v___x_5255_;
goto v_reusejp_5274_;
}
else
{
lean_object* v_reuseFailAlloc_5310_; 
v_reuseFailAlloc_5310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5310_, 0, v___x_5273_);
lean_ctor_set(v_reuseFailAlloc_5310_, 1, v___f_5265_);
v___x_5275_ = v_reuseFailAlloc_5310_;
goto v_reusejp_5274_;
}
v_reusejp_5274_:
{
lean_object* v___x_5276_; lean_object* v_toApplicative_5277_; lean_object* v___x_5279_; uint8_t v_isShared_5280_; uint8_t v_isSharedCheck_5308_; 
v___x_5276_ = l_ReaderT_instMonad___redArg(v___x_5275_);
v_toApplicative_5277_ = lean_ctor_get(v___x_5276_, 0);
v_isSharedCheck_5308_ = !lean_is_exclusive(v___x_5276_);
if (v_isSharedCheck_5308_ == 0)
{
lean_object* v_unused_5309_; 
v_unused_5309_ = lean_ctor_get(v___x_5276_, 1);
lean_dec(v_unused_5309_);
v___x_5279_ = v___x_5276_;
v_isShared_5280_ = v_isSharedCheck_5308_;
goto v_resetjp_5278_;
}
else
{
lean_inc(v_toApplicative_5277_);
lean_dec(v___x_5276_);
v___x_5279_ = lean_box(0);
v_isShared_5280_ = v_isSharedCheck_5308_;
goto v_resetjp_5278_;
}
v_resetjp_5278_:
{
lean_object* v_toFunctor_5281_; lean_object* v_toSeq_5282_; lean_object* v_toSeqLeft_5283_; lean_object* v_toSeqRight_5284_; lean_object* v___x_5286_; uint8_t v_isShared_5287_; uint8_t v_isSharedCheck_5306_; 
v_toFunctor_5281_ = lean_ctor_get(v_toApplicative_5277_, 0);
v_toSeq_5282_ = lean_ctor_get(v_toApplicative_5277_, 2);
v_toSeqLeft_5283_ = lean_ctor_get(v_toApplicative_5277_, 3);
v_toSeqRight_5284_ = lean_ctor_get(v_toApplicative_5277_, 4);
v_isSharedCheck_5306_ = !lean_is_exclusive(v_toApplicative_5277_);
if (v_isSharedCheck_5306_ == 0)
{
lean_object* v_unused_5307_; 
v_unused_5307_ = lean_ctor_get(v_toApplicative_5277_, 1);
lean_dec(v_unused_5307_);
v___x_5286_ = v_toApplicative_5277_;
v_isShared_5287_ = v_isSharedCheck_5306_;
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
v_isShared_5287_ = v_isSharedCheck_5306_;
goto v_resetjp_5285_;
}
v_resetjp_5285_:
{
lean_object* v___f_5288_; lean_object* v___f_5289_; lean_object* v___f_5290_; lean_object* v___f_5291_; lean_object* v___x_5292_; lean_object* v___f_5293_; lean_object* v___f_5294_; lean_object* v___f_5295_; lean_object* v___x_5297_; 
v___f_5288_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3));
v___f_5289_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4));
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
lean_object* v_reuseFailAlloc_5305_; 
v_reuseFailAlloc_5305_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5305_, 0, v___x_5292_);
lean_ctor_set(v_reuseFailAlloc_5305_, 1, v___f_5288_);
lean_ctor_set(v_reuseFailAlloc_5305_, 2, v___f_5295_);
lean_ctor_set(v_reuseFailAlloc_5305_, 3, v___f_5294_);
lean_ctor_set(v_reuseFailAlloc_5305_, 4, v___f_5293_);
v___x_5297_ = v_reuseFailAlloc_5305_;
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
lean_object* v_reuseFailAlloc_5304_; 
v_reuseFailAlloc_5304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5304_, 0, v___x_5297_);
lean_ctor_set(v_reuseFailAlloc_5304_, 1, v___f_5289_);
v___x_5299_ = v_reuseFailAlloc_5304_;
goto v_reusejp_5298_;
}
v_reusejp_5298_:
{
lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_27731__overap_5302_; lean_object* v___x_5303_; 
v___x_5300_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7);
v___x_5301_ = l_instInhabitedOfMonad___redArg(v___x_5299_, v___x_5300_);
v___x_27731__overap_5302_ = lean_panic_fn(v___x_5301_, v_msg_5245_);
v___x_5303_ = lean_apply_5(v___x_27731__overap_5302_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_, lean_box(0));
return v___x_5303_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed(lean_object* v_msg_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_){
_start:
{
lean_object* v_res_5322_; 
v_res_5322_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(v_msg_5316_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_);
return v_res_5322_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(lean_object* v_upperBound_5323_, lean_object* v_onAlt_5324_, uint8_t v_useSplitter_5325_, lean_object* v_extraEqualities_5326_, lean_object* v_numDiscrEqs_5327_, lean_object* v_a_5328_, lean_object* v_b_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_){
_start:
{
lean_object* v___y_5336_; uint8_t v___x_5359_; 
v___x_5359_ = lean_nat_dec_lt(v_a_5328_, v_upperBound_5323_);
if (v___x_5359_ == 0)
{
lean_object* v___x_5360_; 
lean_dec(v___y_5333_);
lean_dec_ref(v___y_5332_);
lean_dec(v___y_5331_);
lean_dec_ref(v___y_5330_);
lean_dec(v_a_5328_);
lean_dec(v_numDiscrEqs_5327_);
lean_dec(v_extraEqualities_5326_);
lean_dec_ref(v_onAlt_5324_);
v___x_5360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5360_, 0, v_b_5329_);
return v___x_5360_;
}
else
{
lean_object* v_snd_5361_; lean_object* v_snd_5362_; lean_object* v_snd_5363_; lean_object* v_snd_5364_; lean_object* v_snd_5365_; lean_object* v_fst_5366_; lean_object* v___x_5368_; uint8_t v_isShared_5369_; uint8_t v_isSharedCheck_5572_; 
v_snd_5361_ = lean_ctor_get(v_b_5329_, 1);
lean_inc(v_snd_5361_);
v_snd_5362_ = lean_ctor_get(v_snd_5361_, 1);
lean_inc(v_snd_5362_);
v_snd_5363_ = lean_ctor_get(v_snd_5362_, 1);
lean_inc(v_snd_5363_);
v_snd_5364_ = lean_ctor_get(v_snd_5363_, 1);
lean_inc(v_snd_5364_);
v_snd_5365_ = lean_ctor_get(v_snd_5364_, 1);
lean_inc(v_snd_5365_);
v_fst_5366_ = lean_ctor_get(v_b_5329_, 0);
v_isSharedCheck_5572_ = !lean_is_exclusive(v_b_5329_);
if (v_isSharedCheck_5572_ == 0)
{
lean_object* v_unused_5573_; 
v_unused_5573_ = lean_ctor_get(v_b_5329_, 1);
lean_dec(v_unused_5573_);
v___x_5368_ = v_b_5329_;
v_isShared_5369_ = v_isSharedCheck_5572_;
goto v_resetjp_5367_;
}
else
{
lean_inc(v_fst_5366_);
lean_dec(v_b_5329_);
v___x_5368_ = lean_box(0);
v_isShared_5369_ = v_isSharedCheck_5572_;
goto v_resetjp_5367_;
}
v_resetjp_5367_:
{
lean_object* v_fst_5370_; lean_object* v___x_5372_; uint8_t v_isShared_5373_; uint8_t v_isSharedCheck_5570_; 
v_fst_5370_ = lean_ctor_get(v_snd_5361_, 0);
v_isSharedCheck_5570_ = !lean_is_exclusive(v_snd_5361_);
if (v_isSharedCheck_5570_ == 0)
{
lean_object* v_unused_5571_; 
v_unused_5571_ = lean_ctor_get(v_snd_5361_, 1);
lean_dec(v_unused_5571_);
v___x_5372_ = v_snd_5361_;
v_isShared_5373_ = v_isSharedCheck_5570_;
goto v_resetjp_5371_;
}
else
{
lean_inc(v_fst_5370_);
lean_dec(v_snd_5361_);
v___x_5372_ = lean_box(0);
v_isShared_5373_ = v_isSharedCheck_5570_;
goto v_resetjp_5371_;
}
v_resetjp_5371_:
{
lean_object* v_fst_5374_; lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5568_; 
v_fst_5374_ = lean_ctor_get(v_snd_5362_, 0);
v_isSharedCheck_5568_ = !lean_is_exclusive(v_snd_5362_);
if (v_isSharedCheck_5568_ == 0)
{
lean_object* v_unused_5569_; 
v_unused_5569_ = lean_ctor_get(v_snd_5362_, 1);
lean_dec(v_unused_5569_);
v___x_5376_ = v_snd_5362_;
v_isShared_5377_ = v_isSharedCheck_5568_;
goto v_resetjp_5375_;
}
else
{
lean_inc(v_fst_5374_);
lean_dec(v_snd_5362_);
v___x_5376_ = lean_box(0);
v_isShared_5377_ = v_isSharedCheck_5568_;
goto v_resetjp_5375_;
}
v_resetjp_5375_:
{
lean_object* v_fst_5378_; lean_object* v___x_5380_; uint8_t v_isShared_5381_; uint8_t v_isSharedCheck_5566_; 
v_fst_5378_ = lean_ctor_get(v_snd_5363_, 0);
v_isSharedCheck_5566_ = !lean_is_exclusive(v_snd_5363_);
if (v_isSharedCheck_5566_ == 0)
{
lean_object* v_unused_5567_; 
v_unused_5567_ = lean_ctor_get(v_snd_5363_, 1);
lean_dec(v_unused_5567_);
v___x_5380_ = v_snd_5363_;
v_isShared_5381_ = v_isSharedCheck_5566_;
goto v_resetjp_5379_;
}
else
{
lean_inc(v_fst_5378_);
lean_dec(v_snd_5363_);
v___x_5380_ = lean_box(0);
v_isShared_5381_ = v_isSharedCheck_5566_;
goto v_resetjp_5379_;
}
v_resetjp_5379_:
{
lean_object* v_fst_5382_; lean_object* v___x_5384_; uint8_t v_isShared_5385_; uint8_t v_isSharedCheck_5564_; 
v_fst_5382_ = lean_ctor_get(v_snd_5364_, 0);
v_isSharedCheck_5564_ = !lean_is_exclusive(v_snd_5364_);
if (v_isSharedCheck_5564_ == 0)
{
lean_object* v_unused_5565_; 
v_unused_5565_ = lean_ctor_get(v_snd_5364_, 1);
lean_dec(v_unused_5565_);
v___x_5384_ = v_snd_5364_;
v_isShared_5385_ = v_isSharedCheck_5564_;
goto v_resetjp_5383_;
}
else
{
lean_inc(v_fst_5382_);
lean_dec(v_snd_5364_);
v___x_5384_ = lean_box(0);
v_isShared_5385_ = v_isSharedCheck_5564_;
goto v_resetjp_5383_;
}
v_resetjp_5383_:
{
lean_object* v_array_5386_; lean_object* v_start_5387_; lean_object* v_stop_5388_; uint8_t v___x_5389_; 
v_array_5386_ = lean_ctor_get(v_snd_5365_, 0);
v_start_5387_ = lean_ctor_get(v_snd_5365_, 1);
v_stop_5388_ = lean_ctor_get(v_snd_5365_, 2);
v___x_5389_ = lean_nat_dec_lt(v_start_5387_, v_stop_5388_);
if (v___x_5389_ == 0)
{
lean_object* v___x_5391_; 
if (v_isShared_5385_ == 0)
{
v___x_5391_ = v___x_5384_;
goto v_reusejp_5390_;
}
else
{
lean_object* v_reuseFailAlloc_5406_; 
v_reuseFailAlloc_5406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5406_, 0, v_fst_5382_);
lean_ctor_set(v_reuseFailAlloc_5406_, 1, v_snd_5365_);
v___x_5391_ = v_reuseFailAlloc_5406_;
goto v_reusejp_5390_;
}
v_reusejp_5390_:
{
lean_object* v___x_5393_; 
if (v_isShared_5381_ == 0)
{
lean_ctor_set(v___x_5380_, 1, v___x_5391_);
v___x_5393_ = v___x_5380_;
goto v_reusejp_5392_;
}
else
{
lean_object* v_reuseFailAlloc_5405_; 
v_reuseFailAlloc_5405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5405_, 0, v_fst_5378_);
lean_ctor_set(v_reuseFailAlloc_5405_, 1, v___x_5391_);
v___x_5393_ = v_reuseFailAlloc_5405_;
goto v_reusejp_5392_;
}
v_reusejp_5392_:
{
lean_object* v___x_5395_; 
if (v_isShared_5377_ == 0)
{
lean_ctor_set(v___x_5376_, 1, v___x_5393_);
v___x_5395_ = v___x_5376_;
goto v_reusejp_5394_;
}
else
{
lean_object* v_reuseFailAlloc_5404_; 
v_reuseFailAlloc_5404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5404_, 0, v_fst_5374_);
lean_ctor_set(v_reuseFailAlloc_5404_, 1, v___x_5393_);
v___x_5395_ = v_reuseFailAlloc_5404_;
goto v_reusejp_5394_;
}
v_reusejp_5394_:
{
lean_object* v___x_5397_; 
if (v_isShared_5373_ == 0)
{
lean_ctor_set(v___x_5372_, 1, v___x_5395_);
v___x_5397_ = v___x_5372_;
goto v_reusejp_5396_;
}
else
{
lean_object* v_reuseFailAlloc_5403_; 
v_reuseFailAlloc_5403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5403_, 0, v_fst_5370_);
lean_ctor_set(v_reuseFailAlloc_5403_, 1, v___x_5395_);
v___x_5397_ = v_reuseFailAlloc_5403_;
goto v_reusejp_5396_;
}
v_reusejp_5396_:
{
lean_object* v___x_5399_; 
if (v_isShared_5369_ == 0)
{
lean_ctor_set(v___x_5368_, 1, v___x_5397_);
v___x_5399_ = v___x_5368_;
goto v_reusejp_5398_;
}
else
{
lean_object* v_reuseFailAlloc_5402_; 
v_reuseFailAlloc_5402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5402_, 0, v_fst_5366_);
lean_ctor_set(v_reuseFailAlloc_5402_, 1, v___x_5397_);
v___x_5399_ = v_reuseFailAlloc_5402_;
goto v_reusejp_5398_;
}
v_reusejp_5398_:
{
lean_object* v___x_5400_; lean_object* v___f_5401_; 
v___x_5400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5400_, 0, v___x_5399_);
v___f_5401_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5401_, 0, v___x_5400_);
v___y_5336_ = v___f_5401_;
goto v___jp_5335_;
}
}
}
}
}
}
else
{
lean_object* v___x_5408_; uint8_t v_isShared_5409_; uint8_t v_isSharedCheck_5560_; 
lean_inc(v_stop_5388_);
lean_inc(v_start_5387_);
lean_inc_ref(v_array_5386_);
v_isSharedCheck_5560_ = !lean_is_exclusive(v_snd_5365_);
if (v_isSharedCheck_5560_ == 0)
{
lean_object* v_unused_5561_; lean_object* v_unused_5562_; lean_object* v_unused_5563_; 
v_unused_5561_ = lean_ctor_get(v_snd_5365_, 2);
lean_dec(v_unused_5561_);
v_unused_5562_ = lean_ctor_get(v_snd_5365_, 1);
lean_dec(v_unused_5562_);
v_unused_5563_ = lean_ctor_get(v_snd_5365_, 0);
lean_dec(v_unused_5563_);
v___x_5408_ = v_snd_5365_;
v_isShared_5409_ = v_isSharedCheck_5560_;
goto v_resetjp_5407_;
}
else
{
lean_dec(v_snd_5365_);
v___x_5408_ = lean_box(0);
v_isShared_5409_ = v_isSharedCheck_5560_;
goto v_resetjp_5407_;
}
v_resetjp_5407_:
{
lean_object* v_array_5410_; lean_object* v_start_5411_; lean_object* v_stop_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5417_; 
v_array_5410_ = lean_ctor_get(v_fst_5382_, 0);
v_start_5411_ = lean_ctor_get(v_fst_5382_, 1);
v_stop_5412_ = lean_ctor_get(v_fst_5382_, 2);
v___x_5413_ = lean_array_fget(v_array_5386_, v_start_5387_);
v___x_5414_ = lean_unsigned_to_nat(1u);
v___x_5415_ = lean_nat_add(v_start_5387_, v___x_5414_);
lean_dec(v_start_5387_);
if (v_isShared_5409_ == 0)
{
lean_ctor_set(v___x_5408_, 1, v___x_5415_);
v___x_5417_ = v___x_5408_;
goto v_reusejp_5416_;
}
else
{
lean_object* v_reuseFailAlloc_5559_; 
v_reuseFailAlloc_5559_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5559_, 0, v_array_5386_);
lean_ctor_set(v_reuseFailAlloc_5559_, 1, v___x_5415_);
lean_ctor_set(v_reuseFailAlloc_5559_, 2, v_stop_5388_);
v___x_5417_ = v_reuseFailAlloc_5559_;
goto v_reusejp_5416_;
}
v_reusejp_5416_:
{
uint8_t v___x_5418_; 
v___x_5418_ = lean_nat_dec_lt(v_start_5411_, v_stop_5412_);
if (v___x_5418_ == 0)
{
lean_object* v___x_5420_; 
lean_dec(v___x_5413_);
if (v_isShared_5385_ == 0)
{
lean_ctor_set(v___x_5384_, 1, v___x_5417_);
v___x_5420_ = v___x_5384_;
goto v_reusejp_5419_;
}
else
{
lean_object* v_reuseFailAlloc_5435_; 
v_reuseFailAlloc_5435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_fst_5382_);
lean_ctor_set(v_reuseFailAlloc_5435_, 1, v___x_5417_);
v___x_5420_ = v_reuseFailAlloc_5435_;
goto v_reusejp_5419_;
}
v_reusejp_5419_:
{
lean_object* v___x_5422_; 
if (v_isShared_5381_ == 0)
{
lean_ctor_set(v___x_5380_, 1, v___x_5420_);
v___x_5422_ = v___x_5380_;
goto v_reusejp_5421_;
}
else
{
lean_object* v_reuseFailAlloc_5434_; 
v_reuseFailAlloc_5434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5434_, 0, v_fst_5378_);
lean_ctor_set(v_reuseFailAlloc_5434_, 1, v___x_5420_);
v___x_5422_ = v_reuseFailAlloc_5434_;
goto v_reusejp_5421_;
}
v_reusejp_5421_:
{
lean_object* v___x_5424_; 
if (v_isShared_5377_ == 0)
{
lean_ctor_set(v___x_5376_, 1, v___x_5422_);
v___x_5424_ = v___x_5376_;
goto v_reusejp_5423_;
}
else
{
lean_object* v_reuseFailAlloc_5433_; 
v_reuseFailAlloc_5433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5433_, 0, v_fst_5374_);
lean_ctor_set(v_reuseFailAlloc_5433_, 1, v___x_5422_);
v___x_5424_ = v_reuseFailAlloc_5433_;
goto v_reusejp_5423_;
}
v_reusejp_5423_:
{
lean_object* v___x_5426_; 
if (v_isShared_5373_ == 0)
{
lean_ctor_set(v___x_5372_, 1, v___x_5424_);
v___x_5426_ = v___x_5372_;
goto v_reusejp_5425_;
}
else
{
lean_object* v_reuseFailAlloc_5432_; 
v_reuseFailAlloc_5432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5432_, 0, v_fst_5370_);
lean_ctor_set(v_reuseFailAlloc_5432_, 1, v___x_5424_);
v___x_5426_ = v_reuseFailAlloc_5432_;
goto v_reusejp_5425_;
}
v_reusejp_5425_:
{
lean_object* v___x_5428_; 
if (v_isShared_5369_ == 0)
{
lean_ctor_set(v___x_5368_, 1, v___x_5426_);
v___x_5428_ = v___x_5368_;
goto v_reusejp_5427_;
}
else
{
lean_object* v_reuseFailAlloc_5431_; 
v_reuseFailAlloc_5431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5431_, 0, v_fst_5366_);
lean_ctor_set(v_reuseFailAlloc_5431_, 1, v___x_5426_);
v___x_5428_ = v_reuseFailAlloc_5431_;
goto v_reusejp_5427_;
}
v_reusejp_5427_:
{
lean_object* v___x_5429_; lean_object* v___f_5430_; 
v___x_5429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5429_, 0, v___x_5428_);
v___f_5430_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5430_, 0, v___x_5429_);
v___y_5336_ = v___f_5430_;
goto v___jp_5335_;
}
}
}
}
}
}
else
{
lean_object* v___x_5437_; uint8_t v_isShared_5438_; uint8_t v_isSharedCheck_5555_; 
lean_inc(v_stop_5412_);
lean_inc(v_start_5411_);
lean_inc_ref(v_array_5410_);
v_isSharedCheck_5555_ = !lean_is_exclusive(v_fst_5382_);
if (v_isSharedCheck_5555_ == 0)
{
lean_object* v_unused_5556_; lean_object* v_unused_5557_; lean_object* v_unused_5558_; 
v_unused_5556_ = lean_ctor_get(v_fst_5382_, 2);
lean_dec(v_unused_5556_);
v_unused_5557_ = lean_ctor_get(v_fst_5382_, 1);
lean_dec(v_unused_5557_);
v_unused_5558_ = lean_ctor_get(v_fst_5382_, 0);
lean_dec(v_unused_5558_);
v___x_5437_ = v_fst_5382_;
v_isShared_5438_ = v_isSharedCheck_5555_;
goto v_resetjp_5436_;
}
else
{
lean_dec(v_fst_5382_);
v___x_5437_ = lean_box(0);
v_isShared_5438_ = v_isSharedCheck_5555_;
goto v_resetjp_5436_;
}
v_resetjp_5436_:
{
lean_object* v_array_5439_; lean_object* v_start_5440_; lean_object* v_stop_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5445_; 
v_array_5439_ = lean_ctor_get(v_fst_5378_, 0);
v_start_5440_ = lean_ctor_get(v_fst_5378_, 1);
v_stop_5441_ = lean_ctor_get(v_fst_5378_, 2);
v___x_5442_ = lean_array_fget(v_array_5410_, v_start_5411_);
v___x_5443_ = lean_nat_add(v_start_5411_, v___x_5414_);
lean_dec(v_start_5411_);
if (v_isShared_5438_ == 0)
{
lean_ctor_set(v___x_5437_, 1, v___x_5443_);
v___x_5445_ = v___x_5437_;
goto v_reusejp_5444_;
}
else
{
lean_object* v_reuseFailAlloc_5554_; 
v_reuseFailAlloc_5554_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5554_, 0, v_array_5410_);
lean_ctor_set(v_reuseFailAlloc_5554_, 1, v___x_5443_);
lean_ctor_set(v_reuseFailAlloc_5554_, 2, v_stop_5412_);
v___x_5445_ = v_reuseFailAlloc_5554_;
goto v_reusejp_5444_;
}
v_reusejp_5444_:
{
uint8_t v___x_5446_; 
v___x_5446_ = lean_nat_dec_lt(v_start_5440_, v_stop_5441_);
if (v___x_5446_ == 0)
{
lean_object* v___x_5448_; 
lean_dec(v___x_5442_);
lean_dec(v___x_5413_);
if (v_isShared_5385_ == 0)
{
lean_ctor_set(v___x_5384_, 1, v___x_5417_);
lean_ctor_set(v___x_5384_, 0, v___x_5445_);
v___x_5448_ = v___x_5384_;
goto v_reusejp_5447_;
}
else
{
lean_object* v_reuseFailAlloc_5463_; 
v_reuseFailAlloc_5463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5463_, 0, v___x_5445_);
lean_ctor_set(v_reuseFailAlloc_5463_, 1, v___x_5417_);
v___x_5448_ = v_reuseFailAlloc_5463_;
goto v_reusejp_5447_;
}
v_reusejp_5447_:
{
lean_object* v___x_5450_; 
if (v_isShared_5381_ == 0)
{
lean_ctor_set(v___x_5380_, 1, v___x_5448_);
v___x_5450_ = v___x_5380_;
goto v_reusejp_5449_;
}
else
{
lean_object* v_reuseFailAlloc_5462_; 
v_reuseFailAlloc_5462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5462_, 0, v_fst_5378_);
lean_ctor_set(v_reuseFailAlloc_5462_, 1, v___x_5448_);
v___x_5450_ = v_reuseFailAlloc_5462_;
goto v_reusejp_5449_;
}
v_reusejp_5449_:
{
lean_object* v___x_5452_; 
if (v_isShared_5377_ == 0)
{
lean_ctor_set(v___x_5376_, 1, v___x_5450_);
v___x_5452_ = v___x_5376_;
goto v_reusejp_5451_;
}
else
{
lean_object* v_reuseFailAlloc_5461_; 
v_reuseFailAlloc_5461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5461_, 0, v_fst_5374_);
lean_ctor_set(v_reuseFailAlloc_5461_, 1, v___x_5450_);
v___x_5452_ = v_reuseFailAlloc_5461_;
goto v_reusejp_5451_;
}
v_reusejp_5451_:
{
lean_object* v___x_5454_; 
if (v_isShared_5373_ == 0)
{
lean_ctor_set(v___x_5372_, 1, v___x_5452_);
v___x_5454_ = v___x_5372_;
goto v_reusejp_5453_;
}
else
{
lean_object* v_reuseFailAlloc_5460_; 
v_reuseFailAlloc_5460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5460_, 0, v_fst_5370_);
lean_ctor_set(v_reuseFailAlloc_5460_, 1, v___x_5452_);
v___x_5454_ = v_reuseFailAlloc_5460_;
goto v_reusejp_5453_;
}
v_reusejp_5453_:
{
lean_object* v___x_5456_; 
if (v_isShared_5369_ == 0)
{
lean_ctor_set(v___x_5368_, 1, v___x_5454_);
v___x_5456_ = v___x_5368_;
goto v_reusejp_5455_;
}
else
{
lean_object* v_reuseFailAlloc_5459_; 
v_reuseFailAlloc_5459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5459_, 0, v_fst_5366_);
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
v___y_5336_ = v___f_5458_;
goto v___jp_5335_;
}
}
}
}
}
}
else
{
lean_object* v___x_5465_; uint8_t v_isShared_5466_; uint8_t v_isSharedCheck_5550_; 
lean_inc(v_stop_5441_);
lean_inc(v_start_5440_);
lean_inc_ref(v_array_5439_);
v_isSharedCheck_5550_ = !lean_is_exclusive(v_fst_5378_);
if (v_isSharedCheck_5550_ == 0)
{
lean_object* v_unused_5551_; lean_object* v_unused_5552_; lean_object* v_unused_5553_; 
v_unused_5551_ = lean_ctor_get(v_fst_5378_, 2);
lean_dec(v_unused_5551_);
v_unused_5552_ = lean_ctor_get(v_fst_5378_, 1);
lean_dec(v_unused_5552_);
v_unused_5553_ = lean_ctor_get(v_fst_5378_, 0);
lean_dec(v_unused_5553_);
v___x_5465_ = v_fst_5378_;
v_isShared_5466_ = v_isSharedCheck_5550_;
goto v_resetjp_5464_;
}
else
{
lean_dec(v_fst_5378_);
v___x_5465_ = lean_box(0);
v_isShared_5466_ = v_isSharedCheck_5550_;
goto v_resetjp_5464_;
}
v_resetjp_5464_:
{
lean_object* v_array_5467_; lean_object* v_start_5468_; lean_object* v_stop_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5473_; 
v_array_5467_ = lean_ctor_get(v_fst_5374_, 0);
v_start_5468_ = lean_ctor_get(v_fst_5374_, 1);
v_stop_5469_ = lean_ctor_get(v_fst_5374_, 2);
v___x_5470_ = lean_array_fget(v_array_5439_, v_start_5440_);
v___x_5471_ = lean_nat_add(v_start_5440_, v___x_5414_);
lean_dec(v_start_5440_);
if (v_isShared_5466_ == 0)
{
lean_ctor_set(v___x_5465_, 1, v___x_5471_);
v___x_5473_ = v___x_5465_;
goto v_reusejp_5472_;
}
else
{
lean_object* v_reuseFailAlloc_5549_; 
v_reuseFailAlloc_5549_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5549_, 0, v_array_5439_);
lean_ctor_set(v_reuseFailAlloc_5549_, 1, v___x_5471_);
lean_ctor_set(v_reuseFailAlloc_5549_, 2, v_stop_5441_);
v___x_5473_ = v_reuseFailAlloc_5549_;
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
lean_dec(v___x_5442_);
lean_dec(v___x_5413_);
if (v_isShared_5385_ == 0)
{
lean_ctor_set(v___x_5384_, 1, v___x_5417_);
lean_ctor_set(v___x_5384_, 0, v___x_5445_);
v___x_5476_ = v___x_5384_;
goto v_reusejp_5475_;
}
else
{
lean_object* v_reuseFailAlloc_5491_; 
v_reuseFailAlloc_5491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5491_, 0, v___x_5445_);
lean_ctor_set(v_reuseFailAlloc_5491_, 1, v___x_5417_);
v___x_5476_ = v_reuseFailAlloc_5491_;
goto v_reusejp_5475_;
}
v_reusejp_5475_:
{
lean_object* v___x_5478_; 
if (v_isShared_5381_ == 0)
{
lean_ctor_set(v___x_5380_, 1, v___x_5476_);
lean_ctor_set(v___x_5380_, 0, v___x_5473_);
v___x_5478_ = v___x_5380_;
goto v_reusejp_5477_;
}
else
{
lean_object* v_reuseFailAlloc_5490_; 
v_reuseFailAlloc_5490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5490_, 0, v___x_5473_);
lean_ctor_set(v_reuseFailAlloc_5490_, 1, v___x_5476_);
v___x_5478_ = v_reuseFailAlloc_5490_;
goto v_reusejp_5477_;
}
v_reusejp_5477_:
{
lean_object* v___x_5480_; 
if (v_isShared_5377_ == 0)
{
lean_ctor_set(v___x_5376_, 1, v___x_5478_);
v___x_5480_ = v___x_5376_;
goto v_reusejp_5479_;
}
else
{
lean_object* v_reuseFailAlloc_5489_; 
v_reuseFailAlloc_5489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5489_, 0, v_fst_5374_);
lean_ctor_set(v_reuseFailAlloc_5489_, 1, v___x_5478_);
v___x_5480_ = v_reuseFailAlloc_5489_;
goto v_reusejp_5479_;
}
v_reusejp_5479_:
{
lean_object* v___x_5482_; 
if (v_isShared_5373_ == 0)
{
lean_ctor_set(v___x_5372_, 1, v___x_5480_);
v___x_5482_ = v___x_5372_;
goto v_reusejp_5481_;
}
else
{
lean_object* v_reuseFailAlloc_5488_; 
v_reuseFailAlloc_5488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5488_, 0, v_fst_5370_);
lean_ctor_set(v_reuseFailAlloc_5488_, 1, v___x_5480_);
v___x_5482_ = v_reuseFailAlloc_5488_;
goto v_reusejp_5481_;
}
v_reusejp_5481_:
{
lean_object* v___x_5484_; 
if (v_isShared_5369_ == 0)
{
lean_ctor_set(v___x_5368_, 1, v___x_5482_);
v___x_5484_ = v___x_5368_;
goto v_reusejp_5483_;
}
else
{
lean_object* v_reuseFailAlloc_5487_; 
v_reuseFailAlloc_5487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5487_, 0, v_fst_5366_);
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
v___y_5336_ = v___f_5486_;
goto v___jp_5335_;
}
}
}
}
}
}
else
{
lean_object* v___x_5493_; uint8_t v_isShared_5494_; uint8_t v_isSharedCheck_5545_; 
lean_inc(v_stop_5469_);
lean_inc(v_start_5468_);
lean_inc_ref(v_array_5467_);
v_isSharedCheck_5545_ = !lean_is_exclusive(v_fst_5374_);
if (v_isSharedCheck_5545_ == 0)
{
lean_object* v_unused_5546_; lean_object* v_unused_5547_; lean_object* v_unused_5548_; 
v_unused_5546_ = lean_ctor_get(v_fst_5374_, 2);
lean_dec(v_unused_5546_);
v_unused_5547_ = lean_ctor_get(v_fst_5374_, 1);
lean_dec(v_unused_5547_);
v_unused_5548_ = lean_ctor_get(v_fst_5374_, 0);
lean_dec(v_unused_5548_);
v___x_5493_ = v_fst_5374_;
v_isShared_5494_ = v_isSharedCheck_5545_;
goto v_resetjp_5492_;
}
else
{
lean_dec(v_fst_5374_);
v___x_5493_ = lean_box(0);
v_isShared_5494_ = v_isSharedCheck_5545_;
goto v_resetjp_5492_;
}
v_resetjp_5492_:
{
lean_object* v_array_5495_; lean_object* v_start_5496_; lean_object* v_stop_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; lean_object* v___x_5501_; 
v_array_5495_ = lean_ctor_get(v_fst_5370_, 0);
v_start_5496_ = lean_ctor_get(v_fst_5370_, 1);
v_stop_5497_ = lean_ctor_get(v_fst_5370_, 2);
v___x_5498_ = lean_array_fget(v_array_5467_, v_start_5468_);
v___x_5499_ = lean_nat_add(v_start_5468_, v___x_5414_);
lean_dec(v_start_5468_);
if (v_isShared_5494_ == 0)
{
lean_ctor_set(v___x_5493_, 1, v___x_5499_);
v___x_5501_ = v___x_5493_;
goto v_reusejp_5500_;
}
else
{
lean_object* v_reuseFailAlloc_5544_; 
v_reuseFailAlloc_5544_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5544_, 0, v_array_5467_);
lean_ctor_set(v_reuseFailAlloc_5544_, 1, v___x_5499_);
lean_ctor_set(v_reuseFailAlloc_5544_, 2, v_stop_5469_);
v___x_5501_ = v_reuseFailAlloc_5544_;
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
lean_dec(v___x_5442_);
lean_dec(v___x_5413_);
if (v_isShared_5385_ == 0)
{
lean_ctor_set(v___x_5384_, 1, v___x_5417_);
lean_ctor_set(v___x_5384_, 0, v___x_5445_);
v___x_5504_ = v___x_5384_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5519_; 
v_reuseFailAlloc_5519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5519_, 0, v___x_5445_);
lean_ctor_set(v_reuseFailAlloc_5519_, 1, v___x_5417_);
v___x_5504_ = v_reuseFailAlloc_5519_;
goto v_reusejp_5503_;
}
v_reusejp_5503_:
{
lean_object* v___x_5506_; 
if (v_isShared_5381_ == 0)
{
lean_ctor_set(v___x_5380_, 1, v___x_5504_);
lean_ctor_set(v___x_5380_, 0, v___x_5473_);
v___x_5506_ = v___x_5380_;
goto v_reusejp_5505_;
}
else
{
lean_object* v_reuseFailAlloc_5518_; 
v_reuseFailAlloc_5518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5518_, 0, v___x_5473_);
lean_ctor_set(v_reuseFailAlloc_5518_, 1, v___x_5504_);
v___x_5506_ = v_reuseFailAlloc_5518_;
goto v_reusejp_5505_;
}
v_reusejp_5505_:
{
lean_object* v___x_5508_; 
if (v_isShared_5377_ == 0)
{
lean_ctor_set(v___x_5376_, 1, v___x_5506_);
lean_ctor_set(v___x_5376_, 0, v___x_5501_);
v___x_5508_ = v___x_5376_;
goto v_reusejp_5507_;
}
else
{
lean_object* v_reuseFailAlloc_5517_; 
v_reuseFailAlloc_5517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5517_, 0, v___x_5501_);
lean_ctor_set(v_reuseFailAlloc_5517_, 1, v___x_5506_);
v___x_5508_ = v_reuseFailAlloc_5517_;
goto v_reusejp_5507_;
}
v_reusejp_5507_:
{
lean_object* v___x_5510_; 
if (v_isShared_5373_ == 0)
{
lean_ctor_set(v___x_5372_, 1, v___x_5508_);
v___x_5510_ = v___x_5372_;
goto v_reusejp_5509_;
}
else
{
lean_object* v_reuseFailAlloc_5516_; 
v_reuseFailAlloc_5516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5516_, 0, v_fst_5370_);
lean_ctor_set(v_reuseFailAlloc_5516_, 1, v___x_5508_);
v___x_5510_ = v_reuseFailAlloc_5516_;
goto v_reusejp_5509_;
}
v_reusejp_5509_:
{
lean_object* v___x_5512_; 
if (v_isShared_5369_ == 0)
{
lean_ctor_set(v___x_5368_, 1, v___x_5510_);
v___x_5512_ = v___x_5368_;
goto v_reusejp_5511_;
}
else
{
lean_object* v_reuseFailAlloc_5515_; 
v_reuseFailAlloc_5515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5515_, 0, v_fst_5366_);
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
v___y_5336_ = v___f_5514_;
goto v___jp_5335_;
}
}
}
}
}
}
else
{
lean_object* v___x_5521_; uint8_t v_isShared_5522_; uint8_t v_isSharedCheck_5540_; 
lean_inc(v_stop_5497_);
lean_inc(v_start_5496_);
lean_inc_ref(v_array_5495_);
lean_del_object(v___x_5384_);
lean_del_object(v___x_5380_);
lean_del_object(v___x_5376_);
lean_del_object(v___x_5372_);
lean_del_object(v___x_5368_);
v_isSharedCheck_5540_ = !lean_is_exclusive(v_fst_5370_);
if (v_isSharedCheck_5540_ == 0)
{
lean_object* v_unused_5541_; lean_object* v_unused_5542_; lean_object* v_unused_5543_; 
v_unused_5541_ = lean_ctor_get(v_fst_5370_, 2);
lean_dec(v_unused_5541_);
v_unused_5542_ = lean_ctor_get(v_fst_5370_, 1);
lean_dec(v_unused_5542_);
v_unused_5543_ = lean_ctor_get(v_fst_5370_, 0);
lean_dec(v_unused_5543_);
v___x_5521_ = v_fst_5370_;
v_isShared_5522_ = v_isSharedCheck_5540_;
goto v_resetjp_5520_;
}
else
{
lean_dec(v_fst_5370_);
v___x_5521_ = lean_box(0);
v_isShared_5522_ = v_isSharedCheck_5540_;
goto v_resetjp_5520_;
}
v_resetjp_5520_:
{
lean_object* v_numOverlaps_5523_; uint8_t v_hasUnitThunk_5524_; lean_object* v___x_5525_; uint8_t v___x_5526_; 
v_numOverlaps_5523_ = lean_ctor_get(v___x_5498_, 1);
v_hasUnitThunk_5524_ = lean_ctor_get_uint8(v___x_5498_, sizeof(void*)*2);
v___x_5525_ = lean_unsigned_to_nat(0u);
v___x_5526_ = lean_nat_dec_eq(v_numOverlaps_5523_, v___x_5525_);
if (v___x_5526_ == 0)
{
lean_object* v___x_5527_; lean_object* v___x_5528_; 
lean_del_object(v___x_5521_);
lean_dec_ref(v___x_5501_);
lean_dec(v___x_5498_);
lean_dec(v_stop_5497_);
lean_dec(v_start_5496_);
lean_dec_ref(v_array_5495_);
lean_dec_ref(v___x_5473_);
lean_dec(v___x_5470_);
lean_dec_ref(v___x_5445_);
lean_dec(v___x_5442_);
lean_dec_ref(v___x_5417_);
lean_dec(v___x_5413_);
lean_dec(v_fst_5366_);
v___x_5527_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9);
v___x_5528_ = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed), 6, 1);
lean_closure_set(v___x_5528_, 0, v___x_5527_);
v___y_5336_ = v___x_5528_;
goto v___jp_5335_;
}
else
{
uint8_t v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; lean_object* v___f_5534_; lean_object* v___x_5535_; lean_object* v___x_5537_; 
v___x_5529_ = 0;
v___x_5530_ = lean_array_fget_borrowed(v_array_5495_, v_start_5496_);
v___x_5531_ = lean_box(v___x_5529_);
v___x_5532_ = lean_box(v_useSplitter_5325_);
v___x_5533_ = lean_box(v_hasUnitThunk_5524_);
lean_inc(v_numDiscrEqs_5327_);
lean_inc(v_extraEqualities_5326_);
lean_inc(v___x_5530_);
lean_inc(v_a_5328_);
lean_inc_ref(v_onAlt_5324_);
v___f_5534_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed), 18, 11);
lean_closure_set(v___f_5534_, 0, v___x_5470_);
lean_closure_set(v___f_5534_, 1, v___x_5413_);
lean_closure_set(v___f_5534_, 2, v_onAlt_5324_);
lean_closure_set(v___f_5534_, 3, v_a_5328_);
lean_closure_set(v___f_5534_, 4, v___x_5531_);
lean_closure_set(v___f_5534_, 5, v___x_5532_);
lean_closure_set(v___f_5534_, 6, v___x_5530_);
lean_closure_set(v___f_5534_, 7, v_extraEqualities_5326_);
lean_closure_set(v___f_5534_, 8, v_numDiscrEqs_5327_);
lean_closure_set(v___f_5534_, 9, v___x_5533_);
lean_closure_set(v___f_5534_, 10, v___x_5414_);
v___x_5535_ = lean_nat_add(v_start_5496_, v___x_5414_);
lean_dec(v_start_5496_);
if (v_isShared_5522_ == 0)
{
lean_ctor_set(v___x_5521_, 1, v___x_5535_);
v___x_5537_ = v___x_5521_;
goto v_reusejp_5536_;
}
else
{
lean_object* v_reuseFailAlloc_5539_; 
v_reuseFailAlloc_5539_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5539_, 0, v_array_5495_);
lean_ctor_set(v_reuseFailAlloc_5539_, 1, v___x_5535_);
lean_ctor_set(v_reuseFailAlloc_5539_, 2, v_stop_5497_);
v___x_5537_ = v_reuseFailAlloc_5539_;
goto v_reusejp_5536_;
}
v_reusejp_5536_:
{
lean_object* v___f_5538_; 
v___f_5538_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed), 14, 9);
lean_closure_set(v___f_5538_, 0, v___x_5442_);
lean_closure_set(v___f_5538_, 1, v___x_5498_);
lean_closure_set(v___f_5538_, 2, v___f_5534_);
lean_closure_set(v___f_5538_, 3, v_fst_5366_);
lean_closure_set(v___f_5538_, 4, v___x_5445_);
lean_closure_set(v___f_5538_, 5, v___x_5417_);
lean_closure_set(v___f_5538_, 6, v___x_5473_);
lean_closure_set(v___f_5538_, 7, v___x_5501_);
lean_closure_set(v___f_5538_, 8, v___x_5537_);
v___y_5336_ = v___f_5538_;
goto v___jp_5335_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_5335_:
{
lean_object* v___x_5337_; 
lean_inc(v___y_5333_);
lean_inc_ref(v___y_5332_);
lean_inc(v___y_5331_);
lean_inc_ref(v___y_5330_);
v___x_5337_ = lean_apply_5(v___y_5336_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_, lean_box(0));
if (lean_obj_tag(v___x_5337_) == 0)
{
lean_object* v_a_5338_; lean_object* v___x_5340_; uint8_t v_isShared_5341_; uint8_t v_isSharedCheck_5350_; 
v_a_5338_ = lean_ctor_get(v___x_5337_, 0);
v_isSharedCheck_5350_ = !lean_is_exclusive(v___x_5337_);
if (v_isSharedCheck_5350_ == 0)
{
v___x_5340_ = v___x_5337_;
v_isShared_5341_ = v_isSharedCheck_5350_;
goto v_resetjp_5339_;
}
else
{
lean_inc(v_a_5338_);
lean_dec(v___x_5337_);
v___x_5340_ = lean_box(0);
v_isShared_5341_ = v_isSharedCheck_5350_;
goto v_resetjp_5339_;
}
v_resetjp_5339_:
{
if (lean_obj_tag(v_a_5338_) == 0)
{
lean_object* v_a_5342_; lean_object* v___x_5344_; 
lean_dec(v___y_5333_);
lean_dec_ref(v___y_5332_);
lean_dec(v___y_5331_);
lean_dec_ref(v___y_5330_);
lean_dec(v_a_5328_);
lean_dec(v_numDiscrEqs_5327_);
lean_dec(v_extraEqualities_5326_);
lean_dec_ref(v_onAlt_5324_);
v_a_5342_ = lean_ctor_get(v_a_5338_, 0);
lean_inc(v_a_5342_);
lean_dec_ref(v_a_5338_);
if (v_isShared_5341_ == 0)
{
lean_ctor_set(v___x_5340_, 0, v_a_5342_);
v___x_5344_ = v___x_5340_;
goto v_reusejp_5343_;
}
else
{
lean_object* v_reuseFailAlloc_5345_; 
v_reuseFailAlloc_5345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5345_, 0, v_a_5342_);
v___x_5344_ = v_reuseFailAlloc_5345_;
goto v_reusejp_5343_;
}
v_reusejp_5343_:
{
return v___x_5344_;
}
}
else
{
lean_object* v_a_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; 
lean_del_object(v___x_5340_);
v_a_5346_ = lean_ctor_get(v_a_5338_, 0);
lean_inc(v_a_5346_);
lean_dec_ref(v_a_5338_);
v___x_5347_ = lean_unsigned_to_nat(1u);
v___x_5348_ = lean_nat_add(v_a_5328_, v___x_5347_);
lean_dec(v_a_5328_);
v_a_5328_ = v___x_5348_;
v_b_5329_ = v_a_5346_;
goto _start;
}
}
}
else
{
lean_object* v_a_5351_; lean_object* v___x_5353_; uint8_t v_isShared_5354_; uint8_t v_isSharedCheck_5358_; 
lean_dec(v___y_5333_);
lean_dec_ref(v___y_5332_);
lean_dec(v___y_5331_);
lean_dec_ref(v___y_5330_);
lean_dec(v_a_5328_);
lean_dec(v_numDiscrEqs_5327_);
lean_dec(v_extraEqualities_5326_);
lean_dec_ref(v_onAlt_5324_);
v_a_5351_ = lean_ctor_get(v___x_5337_, 0);
v_isSharedCheck_5358_ = !lean_is_exclusive(v___x_5337_);
if (v_isSharedCheck_5358_ == 0)
{
v___x_5353_ = v___x_5337_;
v_isShared_5354_ = v_isSharedCheck_5358_;
goto v_resetjp_5352_;
}
else
{
lean_inc(v_a_5351_);
lean_dec(v___x_5337_);
v___x_5353_ = lean_box(0);
v_isShared_5354_ = v_isSharedCheck_5358_;
goto v_resetjp_5352_;
}
v_resetjp_5352_:
{
lean_object* v___x_5356_; 
if (v_isShared_5354_ == 0)
{
v___x_5356_ = v___x_5353_;
goto v_reusejp_5355_;
}
else
{
lean_object* v_reuseFailAlloc_5357_; 
v_reuseFailAlloc_5357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5357_, 0, v_a_5351_);
v___x_5356_ = v_reuseFailAlloc_5357_;
goto v_reusejp_5355_;
}
v_reusejp_5355_:
{
return v___x_5356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___boxed(lean_object* v_upperBound_5574_, lean_object* v_onAlt_5575_, lean_object* v_useSplitter_5576_, lean_object* v_extraEqualities_5577_, lean_object* v_numDiscrEqs_5578_, lean_object* v_a_5579_, lean_object* v_b_5580_, lean_object* v___y_5581_, lean_object* v___y_5582_, lean_object* v___y_5583_, lean_object* v___y_5584_, lean_object* v___y_5585_){
_start:
{
uint8_t v_useSplitter_boxed_5586_; lean_object* v_res_5587_; 
v_useSplitter_boxed_5586_ = lean_unbox(v_useSplitter_5576_);
v_res_5587_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v_upperBound_5574_, v_onAlt_5575_, v_useSplitter_boxed_5586_, v_extraEqualities_5577_, v_numDiscrEqs_5578_, v_a_5579_, v_b_5580_, v___y_5581_, v___y_5582_, v___y_5583_, v___y_5584_);
lean_dec(v_upperBound_5574_);
return v_res_5587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(uint8_t v_addEqualities_5588_, lean_object* v_as_5589_, size_t v_sz_5590_, size_t v_i_5591_, lean_object* v_b_5592_, lean_object* v___y_5593_, lean_object* v___y_5594_, lean_object* v___y_5595_, lean_object* v___y_5596_){
_start:
{
lean_object* v_a_5599_; uint8_t v___x_5603_; 
v___x_5603_ = lean_usize_dec_lt(v_i_5591_, v_sz_5590_);
if (v___x_5603_ == 0)
{
lean_object* v___x_5604_; 
lean_dec(v___y_5596_);
lean_dec_ref(v___y_5595_);
lean_dec(v___y_5594_);
lean_dec_ref(v___y_5593_);
v___x_5604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5604_, 0, v_b_5592_);
return v___x_5604_;
}
else
{
lean_object* v_snd_5605_; lean_object* v_snd_5606_; lean_object* v_snd_5607_; lean_object* v_snd_5608_; lean_object* v_fst_5609_; lean_object* v___x_5611_; uint8_t v_isShared_5612_; uint8_t v_isSharedCheck_5755_; 
v_snd_5605_ = lean_ctor_get(v_b_5592_, 1);
lean_inc(v_snd_5605_);
v_snd_5606_ = lean_ctor_get(v_snd_5605_, 1);
lean_inc(v_snd_5606_);
v_snd_5607_ = lean_ctor_get(v_snd_5606_, 1);
lean_inc(v_snd_5607_);
v_snd_5608_ = lean_ctor_get(v_snd_5607_, 1);
lean_inc(v_snd_5608_);
v_fst_5609_ = lean_ctor_get(v_b_5592_, 0);
v_isSharedCheck_5755_ = !lean_is_exclusive(v_b_5592_);
if (v_isSharedCheck_5755_ == 0)
{
lean_object* v_unused_5756_; 
v_unused_5756_ = lean_ctor_get(v_b_5592_, 1);
lean_dec(v_unused_5756_);
v___x_5611_ = v_b_5592_;
v_isShared_5612_ = v_isSharedCheck_5755_;
goto v_resetjp_5610_;
}
else
{
lean_inc(v_fst_5609_);
lean_dec(v_b_5592_);
v___x_5611_ = lean_box(0);
v_isShared_5612_ = v_isSharedCheck_5755_;
goto v_resetjp_5610_;
}
v_resetjp_5610_:
{
lean_object* v_fst_5613_; lean_object* v___x_5615_; uint8_t v_isShared_5616_; uint8_t v_isSharedCheck_5753_; 
v_fst_5613_ = lean_ctor_get(v_snd_5605_, 0);
v_isSharedCheck_5753_ = !lean_is_exclusive(v_snd_5605_);
if (v_isSharedCheck_5753_ == 0)
{
lean_object* v_unused_5754_; 
v_unused_5754_ = lean_ctor_get(v_snd_5605_, 1);
lean_dec(v_unused_5754_);
v___x_5615_ = v_snd_5605_;
v_isShared_5616_ = v_isSharedCheck_5753_;
goto v_resetjp_5614_;
}
else
{
lean_inc(v_fst_5613_);
lean_dec(v_snd_5605_);
v___x_5615_ = lean_box(0);
v_isShared_5616_ = v_isSharedCheck_5753_;
goto v_resetjp_5614_;
}
v_resetjp_5614_:
{
lean_object* v_fst_5617_; lean_object* v___x_5619_; uint8_t v_isShared_5620_; uint8_t v_isSharedCheck_5751_; 
v_fst_5617_ = lean_ctor_get(v_snd_5606_, 0);
v_isSharedCheck_5751_ = !lean_is_exclusive(v_snd_5606_);
if (v_isSharedCheck_5751_ == 0)
{
lean_object* v_unused_5752_; 
v_unused_5752_ = lean_ctor_get(v_snd_5606_, 1);
lean_dec(v_unused_5752_);
v___x_5619_ = v_snd_5606_;
v_isShared_5620_ = v_isSharedCheck_5751_;
goto v_resetjp_5618_;
}
else
{
lean_inc(v_fst_5617_);
lean_dec(v_snd_5606_);
v___x_5619_ = lean_box(0);
v_isShared_5620_ = v_isSharedCheck_5751_;
goto v_resetjp_5618_;
}
v_resetjp_5618_:
{
lean_object* v_fst_5621_; lean_object* v___x_5623_; uint8_t v_isShared_5624_; uint8_t v_isSharedCheck_5749_; 
v_fst_5621_ = lean_ctor_get(v_snd_5607_, 0);
v_isSharedCheck_5749_ = !lean_is_exclusive(v_snd_5607_);
if (v_isSharedCheck_5749_ == 0)
{
lean_object* v_unused_5750_; 
v_unused_5750_ = lean_ctor_get(v_snd_5607_, 1);
lean_dec(v_unused_5750_);
v___x_5623_ = v_snd_5607_;
v_isShared_5624_ = v_isSharedCheck_5749_;
goto v_resetjp_5622_;
}
else
{
lean_inc(v_fst_5621_);
lean_dec(v_snd_5607_);
v___x_5623_ = lean_box(0);
v_isShared_5624_ = v_isSharedCheck_5749_;
goto v_resetjp_5622_;
}
v_resetjp_5622_:
{
lean_object* v_array_5625_; lean_object* v_start_5626_; lean_object* v_stop_5627_; uint8_t v___x_5628_; 
v_array_5625_ = lean_ctor_get(v_snd_5608_, 0);
v_start_5626_ = lean_ctor_get(v_snd_5608_, 1);
v_stop_5627_ = lean_ctor_get(v_snd_5608_, 2);
v___x_5628_ = lean_nat_dec_lt(v_start_5626_, v_stop_5627_);
if (v___x_5628_ == 0)
{
lean_object* v___x_5630_; 
lean_dec(v___y_5596_);
lean_dec_ref(v___y_5595_);
lean_dec(v___y_5594_);
lean_dec_ref(v___y_5593_);
if (v_isShared_5624_ == 0)
{
v___x_5630_ = v___x_5623_;
goto v_reusejp_5629_;
}
else
{
lean_object* v_reuseFailAlloc_5641_; 
v_reuseFailAlloc_5641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5641_, 0, v_fst_5621_);
lean_ctor_set(v_reuseFailAlloc_5641_, 1, v_snd_5608_);
v___x_5630_ = v_reuseFailAlloc_5641_;
goto v_reusejp_5629_;
}
v_reusejp_5629_:
{
lean_object* v___x_5632_; 
if (v_isShared_5620_ == 0)
{
lean_ctor_set(v___x_5619_, 1, v___x_5630_);
v___x_5632_ = v___x_5619_;
goto v_reusejp_5631_;
}
else
{
lean_object* v_reuseFailAlloc_5640_; 
v_reuseFailAlloc_5640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5640_, 0, v_fst_5617_);
lean_ctor_set(v_reuseFailAlloc_5640_, 1, v___x_5630_);
v___x_5632_ = v_reuseFailAlloc_5640_;
goto v_reusejp_5631_;
}
v_reusejp_5631_:
{
lean_object* v___x_5634_; 
if (v_isShared_5616_ == 0)
{
lean_ctor_set(v___x_5615_, 1, v___x_5632_);
v___x_5634_ = v___x_5615_;
goto v_reusejp_5633_;
}
else
{
lean_object* v_reuseFailAlloc_5639_; 
v_reuseFailAlloc_5639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5639_, 0, v_fst_5613_);
lean_ctor_set(v_reuseFailAlloc_5639_, 1, v___x_5632_);
v___x_5634_ = v_reuseFailAlloc_5639_;
goto v_reusejp_5633_;
}
v_reusejp_5633_:
{
lean_object* v___x_5636_; 
if (v_isShared_5612_ == 0)
{
lean_ctor_set(v___x_5611_, 1, v___x_5634_);
v___x_5636_ = v___x_5611_;
goto v_reusejp_5635_;
}
else
{
lean_object* v_reuseFailAlloc_5638_; 
v_reuseFailAlloc_5638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5638_, 0, v_fst_5609_);
lean_ctor_set(v_reuseFailAlloc_5638_, 1, v___x_5634_);
v___x_5636_ = v_reuseFailAlloc_5638_;
goto v_reusejp_5635_;
}
v_reusejp_5635_:
{
lean_object* v___x_5637_; 
v___x_5637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5637_, 0, v___x_5636_);
return v___x_5637_;
}
}
}
}
}
else
{
lean_object* v___x_5643_; uint8_t v_isShared_5644_; uint8_t v_isSharedCheck_5745_; 
lean_inc(v_stop_5627_);
lean_inc(v_start_5626_);
lean_inc_ref(v_array_5625_);
v_isSharedCheck_5745_ = !lean_is_exclusive(v_snd_5608_);
if (v_isSharedCheck_5745_ == 0)
{
lean_object* v_unused_5746_; lean_object* v_unused_5747_; lean_object* v_unused_5748_; 
v_unused_5746_ = lean_ctor_get(v_snd_5608_, 2);
lean_dec(v_unused_5746_);
v_unused_5747_ = lean_ctor_get(v_snd_5608_, 1);
lean_dec(v_unused_5747_);
v_unused_5748_ = lean_ctor_get(v_snd_5608_, 0);
lean_dec(v_unused_5748_);
v___x_5643_ = v_snd_5608_;
v_isShared_5644_ = v_isSharedCheck_5745_;
goto v_resetjp_5642_;
}
else
{
lean_dec(v_snd_5608_);
v___x_5643_ = lean_box(0);
v_isShared_5644_ = v_isSharedCheck_5745_;
goto v_resetjp_5642_;
}
v_resetjp_5642_:
{
lean_object* v_array_5645_; lean_object* v_start_5646_; lean_object* v_stop_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5652_; 
v_array_5645_ = lean_ctor_get(v_fst_5621_, 0);
v_start_5646_ = lean_ctor_get(v_fst_5621_, 1);
v_stop_5647_ = lean_ctor_get(v_fst_5621_, 2);
v___x_5648_ = lean_array_fget(v_array_5625_, v_start_5626_);
v___x_5649_ = lean_unsigned_to_nat(1u);
v___x_5650_ = lean_nat_add(v_start_5626_, v___x_5649_);
lean_dec(v_start_5626_);
if (v_isShared_5644_ == 0)
{
lean_ctor_set(v___x_5643_, 1, v___x_5650_);
v___x_5652_ = v___x_5643_;
goto v_reusejp_5651_;
}
else
{
lean_object* v_reuseFailAlloc_5744_; 
v_reuseFailAlloc_5744_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5744_, 0, v_array_5625_);
lean_ctor_set(v_reuseFailAlloc_5744_, 1, v___x_5650_);
lean_ctor_set(v_reuseFailAlloc_5744_, 2, v_stop_5627_);
v___x_5652_ = v_reuseFailAlloc_5744_;
goto v_reusejp_5651_;
}
v_reusejp_5651_:
{
uint8_t v___x_5653_; 
v___x_5653_ = lean_nat_dec_lt(v_start_5646_, v_stop_5647_);
if (v___x_5653_ == 0)
{
lean_object* v___x_5655_; 
lean_dec(v___x_5648_);
lean_dec(v___y_5596_);
lean_dec_ref(v___y_5595_);
lean_dec(v___y_5594_);
lean_dec_ref(v___y_5593_);
if (v_isShared_5624_ == 0)
{
lean_ctor_set(v___x_5623_, 1, v___x_5652_);
v___x_5655_ = v___x_5623_;
goto v_reusejp_5654_;
}
else
{
lean_object* v_reuseFailAlloc_5666_; 
v_reuseFailAlloc_5666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5666_, 0, v_fst_5621_);
lean_ctor_set(v_reuseFailAlloc_5666_, 1, v___x_5652_);
v___x_5655_ = v_reuseFailAlloc_5666_;
goto v_reusejp_5654_;
}
v_reusejp_5654_:
{
lean_object* v___x_5657_; 
if (v_isShared_5620_ == 0)
{
lean_ctor_set(v___x_5619_, 1, v___x_5655_);
v___x_5657_ = v___x_5619_;
goto v_reusejp_5656_;
}
else
{
lean_object* v_reuseFailAlloc_5665_; 
v_reuseFailAlloc_5665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5665_, 0, v_fst_5617_);
lean_ctor_set(v_reuseFailAlloc_5665_, 1, v___x_5655_);
v___x_5657_ = v_reuseFailAlloc_5665_;
goto v_reusejp_5656_;
}
v_reusejp_5656_:
{
lean_object* v___x_5659_; 
if (v_isShared_5616_ == 0)
{
lean_ctor_set(v___x_5615_, 1, v___x_5657_);
v___x_5659_ = v___x_5615_;
goto v_reusejp_5658_;
}
else
{
lean_object* v_reuseFailAlloc_5664_; 
v_reuseFailAlloc_5664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5664_, 0, v_fst_5613_);
lean_ctor_set(v_reuseFailAlloc_5664_, 1, v___x_5657_);
v___x_5659_ = v_reuseFailAlloc_5664_;
goto v_reusejp_5658_;
}
v_reusejp_5658_:
{
lean_object* v___x_5661_; 
if (v_isShared_5612_ == 0)
{
lean_ctor_set(v___x_5611_, 1, v___x_5659_);
v___x_5661_ = v___x_5611_;
goto v_reusejp_5660_;
}
else
{
lean_object* v_reuseFailAlloc_5663_; 
v_reuseFailAlloc_5663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5663_, 0, v_fst_5609_);
lean_ctor_set(v_reuseFailAlloc_5663_, 1, v___x_5659_);
v___x_5661_ = v_reuseFailAlloc_5663_;
goto v_reusejp_5660_;
}
v_reusejp_5660_:
{
lean_object* v___x_5662_; 
v___x_5662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5662_, 0, v___x_5661_);
return v___x_5662_;
}
}
}
}
}
else
{
lean_object* v___x_5668_; uint8_t v_isShared_5669_; uint8_t v_isSharedCheck_5740_; 
lean_inc(v_stop_5647_);
lean_inc(v_start_5646_);
lean_inc_ref(v_array_5645_);
v_isSharedCheck_5740_ = !lean_is_exclusive(v_fst_5621_);
if (v_isSharedCheck_5740_ == 0)
{
lean_object* v_unused_5741_; lean_object* v_unused_5742_; lean_object* v_unused_5743_; 
v_unused_5741_ = lean_ctor_get(v_fst_5621_, 2);
lean_dec(v_unused_5741_);
v_unused_5742_ = lean_ctor_get(v_fst_5621_, 1);
lean_dec(v_unused_5742_);
v_unused_5743_ = lean_ctor_get(v_fst_5621_, 0);
lean_dec(v_unused_5743_);
v___x_5668_ = v_fst_5621_;
v_isShared_5669_ = v_isSharedCheck_5740_;
goto v_resetjp_5667_;
}
else
{
lean_dec(v_fst_5621_);
v___x_5668_ = lean_box(0);
v_isShared_5669_ = v_isSharedCheck_5740_;
goto v_resetjp_5667_;
}
v_resetjp_5667_:
{
lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5673_; 
v___x_5670_ = lean_array_fget(v_array_5645_, v_start_5646_);
v___x_5671_ = lean_nat_add(v_start_5646_, v___x_5649_);
lean_dec(v_start_5646_);
if (v_isShared_5669_ == 0)
{
lean_ctor_set(v___x_5668_, 1, v___x_5671_);
v___x_5673_ = v___x_5668_;
goto v_reusejp_5672_;
}
else
{
lean_object* v_reuseFailAlloc_5739_; 
v_reuseFailAlloc_5739_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5739_, 0, v_array_5645_);
lean_ctor_set(v_reuseFailAlloc_5739_, 1, v___x_5671_);
lean_ctor_set(v_reuseFailAlloc_5739_, 2, v_stop_5647_);
v___x_5673_ = v_reuseFailAlloc_5739_;
goto v_reusejp_5672_;
}
v_reusejp_5672_:
{
if (v_addEqualities_5588_ == 0)
{
lean_dec(v___x_5670_);
goto v___jp_5674_;
}
else
{
if (lean_obj_tag(v___x_5648_) == 0)
{
lean_object* v_a_5690_; lean_object* v___x_5691_; 
lean_del_object(v___x_5623_);
lean_del_object(v___x_5619_);
lean_del_object(v___x_5615_);
lean_del_object(v___x_5611_);
v_a_5690_ = lean_array_uget_borrowed(v_as_5589_, v_i_5591_);
lean_inc(v___y_5596_);
lean_inc_ref(v___y_5595_);
lean_inc(v___y_5594_);
lean_inc_ref(v___y_5593_);
lean_inc(v_a_5690_);
v___x_5691_ = l_Lean_Meta_isProof(v_a_5690_, v___y_5593_, v___y_5594_, v___y_5595_, v___y_5596_);
if (lean_obj_tag(v___x_5691_) == 0)
{
lean_object* v_a_5692_; uint8_t v___x_5693_; 
v_a_5692_ = lean_ctor_get(v___x_5691_, 0);
lean_inc(v_a_5692_);
lean_dec_ref(v___x_5691_);
v___x_5693_ = lean_unbox(v_a_5692_);
lean_dec(v_a_5692_);
if (v___x_5693_ == 0)
{
lean_object* v___x_5694_; 
lean_inc(v___y_5596_);
lean_inc_ref(v___y_5595_);
lean_inc(v___y_5594_);
lean_inc_ref(v___y_5593_);
lean_inc(v_a_5690_);
v___x_5694_ = l_Lean_Meta_mkEqHEq(v___x_5670_, v_a_5690_, v___y_5593_, v___y_5594_, v___y_5595_, v___y_5596_);
if (lean_obj_tag(v___x_5694_) == 0)
{
lean_object* v_a_5695_; lean_object* v___x_5696_; 
v_a_5695_ = lean_ctor_get(v___x_5694_, 0);
lean_inc(v_a_5695_);
lean_dec_ref(v___x_5694_);
lean_inc(v___y_5596_);
lean_inc_ref(v___y_5595_);
lean_inc(v_a_5695_);
v___x_5696_ = l_Lean_mkArrow(v_a_5695_, v_fst_5609_, v___y_5595_, v___y_5596_);
if (lean_obj_tag(v___x_5696_) == 0)
{
lean_object* v_a_5697_; uint8_t v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; 
v_a_5697_ = lean_ctor_get(v___x_5696_, 0);
lean_inc(v_a_5697_);
lean_dec_ref(v___x_5696_);
v___x_5698_ = l_Lean_Expr_isHEq(v_a_5695_);
lean_dec(v_a_5695_);
v___x_5699_ = lean_box(v___x_5698_);
v___x_5700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5700_, 0, v___x_5699_);
v___x_5701_ = lean_array_push(v_fst_5613_, v___x_5700_);
v___x_5702_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9___closed__0));
v___x_5703_ = lean_array_push(v_fst_5617_, v___x_5702_);
v___x_5704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5704_, 0, v___x_5673_);
lean_ctor_set(v___x_5704_, 1, v___x_5652_);
v___x_5705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5705_, 0, v___x_5703_);
lean_ctor_set(v___x_5705_, 1, v___x_5704_);
v___x_5706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5706_, 0, v___x_5701_);
lean_ctor_set(v___x_5706_, 1, v___x_5705_);
v___x_5707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5707_, 0, v_a_5697_);
lean_ctor_set(v___x_5707_, 1, v___x_5706_);
v_a_5599_ = v___x_5707_;
goto v___jp_5598_;
}
else
{
lean_object* v_a_5708_; lean_object* v___x_5710_; uint8_t v_isShared_5711_; uint8_t v_isSharedCheck_5715_; 
lean_dec(v_a_5695_);
lean_dec_ref(v___x_5673_);
lean_dec_ref(v___x_5652_);
lean_dec(v_fst_5617_);
lean_dec(v_fst_5613_);
lean_dec(v___y_5596_);
lean_dec_ref(v___y_5595_);
lean_dec(v___y_5594_);
lean_dec_ref(v___y_5593_);
v_a_5708_ = lean_ctor_get(v___x_5696_, 0);
v_isSharedCheck_5715_ = !lean_is_exclusive(v___x_5696_);
if (v_isSharedCheck_5715_ == 0)
{
v___x_5710_ = v___x_5696_;
v_isShared_5711_ = v_isSharedCheck_5715_;
goto v_resetjp_5709_;
}
else
{
lean_inc(v_a_5708_);
lean_dec(v___x_5696_);
v___x_5710_ = lean_box(0);
v_isShared_5711_ = v_isSharedCheck_5715_;
goto v_resetjp_5709_;
}
v_resetjp_5709_:
{
lean_object* v___x_5713_; 
if (v_isShared_5711_ == 0)
{
v___x_5713_ = v___x_5710_;
goto v_reusejp_5712_;
}
else
{
lean_object* v_reuseFailAlloc_5714_; 
v_reuseFailAlloc_5714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5714_, 0, v_a_5708_);
v___x_5713_ = v_reuseFailAlloc_5714_;
goto v_reusejp_5712_;
}
v_reusejp_5712_:
{
return v___x_5713_;
}
}
}
}
else
{
lean_object* v_a_5716_; lean_object* v___x_5718_; uint8_t v_isShared_5719_; uint8_t v_isSharedCheck_5723_; 
lean_dec_ref(v___x_5673_);
lean_dec_ref(v___x_5652_);
lean_dec(v_fst_5617_);
lean_dec(v_fst_5613_);
lean_dec(v_fst_5609_);
lean_dec(v___y_5596_);
lean_dec_ref(v___y_5595_);
lean_dec(v___y_5594_);
lean_dec_ref(v___y_5593_);
v_a_5716_ = lean_ctor_get(v___x_5694_, 0);
v_isSharedCheck_5723_ = !lean_is_exclusive(v___x_5694_);
if (v_isSharedCheck_5723_ == 0)
{
v___x_5718_ = v___x_5694_;
v_isShared_5719_ = v_isSharedCheck_5723_;
goto v_resetjp_5717_;
}
else
{
lean_inc(v_a_5716_);
lean_dec(v___x_5694_);
v___x_5718_ = lean_box(0);
v_isShared_5719_ = v_isSharedCheck_5723_;
goto v_resetjp_5717_;
}
v_resetjp_5717_:
{
lean_object* v___x_5721_; 
if (v_isShared_5719_ == 0)
{
v___x_5721_ = v___x_5718_;
goto v_reusejp_5720_;
}
else
{
lean_object* v_reuseFailAlloc_5722_; 
v_reuseFailAlloc_5722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5722_, 0, v_a_5716_);
v___x_5721_ = v_reuseFailAlloc_5722_;
goto v_reusejp_5720_;
}
v_reusejp_5720_:
{
return v___x_5721_;
}
}
}
}
else
{
lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; 
lean_dec(v___x_5670_);
v___x_5724_ = lean_box(0);
v___x_5725_ = lean_array_push(v_fst_5613_, v___x_5724_);
v___x_5726_ = lean_array_push(v_fst_5617_, v___x_5648_);
v___x_5727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5727_, 0, v___x_5673_);
lean_ctor_set(v___x_5727_, 1, v___x_5652_);
v___x_5728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5728_, 0, v___x_5726_);
lean_ctor_set(v___x_5728_, 1, v___x_5727_);
v___x_5729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5729_, 0, v___x_5725_);
lean_ctor_set(v___x_5729_, 1, v___x_5728_);
v___x_5730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5730_, 0, v_fst_5609_);
lean_ctor_set(v___x_5730_, 1, v___x_5729_);
v_a_5599_ = v___x_5730_;
goto v___jp_5598_;
}
}
else
{
lean_object* v_a_5731_; lean_object* v___x_5733_; uint8_t v_isShared_5734_; uint8_t v_isSharedCheck_5738_; 
lean_dec_ref(v___x_5673_);
lean_dec(v___x_5670_);
lean_dec_ref(v___x_5652_);
lean_dec(v_fst_5617_);
lean_dec(v_fst_5613_);
lean_dec(v_fst_5609_);
lean_dec(v___y_5596_);
lean_dec_ref(v___y_5595_);
lean_dec(v___y_5594_);
lean_dec_ref(v___y_5593_);
v_a_5731_ = lean_ctor_get(v___x_5691_, 0);
v_isSharedCheck_5738_ = !lean_is_exclusive(v___x_5691_);
if (v_isSharedCheck_5738_ == 0)
{
v___x_5733_ = v___x_5691_;
v_isShared_5734_ = v_isSharedCheck_5738_;
goto v_resetjp_5732_;
}
else
{
lean_inc(v_a_5731_);
lean_dec(v___x_5691_);
v___x_5733_ = lean_box(0);
v_isShared_5734_ = v_isSharedCheck_5738_;
goto v_resetjp_5732_;
}
v_resetjp_5732_:
{
lean_object* v___x_5736_; 
if (v_isShared_5734_ == 0)
{
v___x_5736_ = v___x_5733_;
goto v_reusejp_5735_;
}
else
{
lean_object* v_reuseFailAlloc_5737_; 
v_reuseFailAlloc_5737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5737_, 0, v_a_5731_);
v___x_5736_ = v_reuseFailAlloc_5737_;
goto v_reusejp_5735_;
}
v_reusejp_5735_:
{
return v___x_5736_;
}
}
}
}
else
{
lean_dec(v___x_5670_);
goto v___jp_5674_;
}
}
v___jp_5674_:
{
lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5679_; 
v___x_5675_ = lean_box(0);
v___x_5676_ = lean_array_push(v_fst_5613_, v___x_5675_);
v___x_5677_ = lean_array_push(v_fst_5617_, v___x_5648_);
if (v_isShared_5624_ == 0)
{
lean_ctor_set(v___x_5623_, 1, v___x_5652_);
lean_ctor_set(v___x_5623_, 0, v___x_5673_);
v___x_5679_ = v___x_5623_;
goto v_reusejp_5678_;
}
else
{
lean_object* v_reuseFailAlloc_5689_; 
v_reuseFailAlloc_5689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5689_, 0, v___x_5673_);
lean_ctor_set(v_reuseFailAlloc_5689_, 1, v___x_5652_);
v___x_5679_ = v_reuseFailAlloc_5689_;
goto v_reusejp_5678_;
}
v_reusejp_5678_:
{
lean_object* v___x_5681_; 
if (v_isShared_5620_ == 0)
{
lean_ctor_set(v___x_5619_, 1, v___x_5679_);
lean_ctor_set(v___x_5619_, 0, v___x_5677_);
v___x_5681_ = v___x_5619_;
goto v_reusejp_5680_;
}
else
{
lean_object* v_reuseFailAlloc_5688_; 
v_reuseFailAlloc_5688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5688_, 0, v___x_5677_);
lean_ctor_set(v_reuseFailAlloc_5688_, 1, v___x_5679_);
v___x_5681_ = v_reuseFailAlloc_5688_;
goto v_reusejp_5680_;
}
v_reusejp_5680_:
{
lean_object* v___x_5683_; 
if (v_isShared_5616_ == 0)
{
lean_ctor_set(v___x_5615_, 1, v___x_5681_);
lean_ctor_set(v___x_5615_, 0, v___x_5676_);
v___x_5683_ = v___x_5615_;
goto v_reusejp_5682_;
}
else
{
lean_object* v_reuseFailAlloc_5687_; 
v_reuseFailAlloc_5687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5687_, 0, v___x_5676_);
lean_ctor_set(v_reuseFailAlloc_5687_, 1, v___x_5681_);
v___x_5683_ = v_reuseFailAlloc_5687_;
goto v_reusejp_5682_;
}
v_reusejp_5682_:
{
lean_object* v___x_5685_; 
if (v_isShared_5612_ == 0)
{
lean_ctor_set(v___x_5611_, 1, v___x_5683_);
v___x_5685_ = v___x_5611_;
goto v_reusejp_5684_;
}
else
{
lean_object* v_reuseFailAlloc_5686_; 
v_reuseFailAlloc_5686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5686_, 0, v_fst_5609_);
lean_ctor_set(v_reuseFailAlloc_5686_, 1, v___x_5683_);
v___x_5685_ = v_reuseFailAlloc_5686_;
goto v_reusejp_5684_;
}
v_reusejp_5684_:
{
v_a_5599_ = v___x_5685_;
goto v___jp_5598_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_5598_:
{
size_t v___x_5600_; size_t v___x_5601_; 
v___x_5600_ = ((size_t)1ULL);
v___x_5601_ = lean_usize_add(v_i_5591_, v___x_5600_);
v_i_5591_ = v___x_5601_;
v_b_5592_ = v_a_5599_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7___boxed(lean_object* v_addEqualities_5757_, lean_object* v_as_5758_, lean_object* v_sz_5759_, lean_object* v_i_5760_, lean_object* v_b_5761_, lean_object* v___y_5762_, lean_object* v___y_5763_, lean_object* v___y_5764_, lean_object* v___y_5765_, lean_object* v___y_5766_){
_start:
{
uint8_t v_addEqualities_boxed_5767_; size_t v_sz_boxed_5768_; size_t v_i_boxed_5769_; lean_object* v_res_5770_; 
v_addEqualities_boxed_5767_ = lean_unbox(v_addEqualities_5757_);
v_sz_boxed_5768_ = lean_unbox_usize(v_sz_5759_);
lean_dec(v_sz_5759_);
v_i_boxed_5769_ = lean_unbox_usize(v_i_5760_);
lean_dec(v_i_5760_);
v_res_5770_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(v_addEqualities_boxed_5767_, v_as_5758_, v_sz_boxed_5768_, v_i_boxed_5769_, v_b_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_);
lean_dec_ref(v_as_5758_);
return v_res_5770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(lean_object* v_onMotive_5771_, lean_object* v_toMatcherInfo_5772_, lean_object* v_a_5773_, uint8_t v_addEqualities_5774_, size_t v___x_5775_, lean_object* v_discrs_5776_, lean_object* v_motiveArgs_5777_, lean_object* v_motiveBody_5778_, lean_object* v___y_5779_, lean_object* v___y_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_){
_start:
{
lean_object* v___x_5876_; lean_object* v___x_5877_; uint8_t v___x_5878_; 
v___x_5876_ = lean_array_get_size(v_motiveArgs_5777_);
v___x_5877_ = lean_array_get_size(v_discrs_5776_);
v___x_5878_ = lean_nat_dec_eq(v___x_5876_, v___x_5877_);
if (v___x_5878_ == 0)
{
lean_object* v___x_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; lean_object* v_a_5887_; lean_object* v___x_5889_; uint8_t v_isShared_5890_; uint8_t v_isSharedCheck_5894_; 
lean_dec_ref(v_motiveBody_5778_);
lean_dec_ref(v_motiveArgs_5777_);
lean_dec_ref(v_a_5773_);
lean_dec_ref(v_toMatcherInfo_5772_);
lean_dec_ref(v_onMotive_5771_);
v___x_5879_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_5880_ = l_Nat_reprFast(v___x_5877_);
v___x_5881_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5881_, 0, v___x_5880_);
v___x_5882_ = l_Lean_MessageData_ofFormat(v___x_5881_);
v___x_5883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5883_, 0, v___x_5879_);
lean_ctor_set(v___x_5883_, 1, v___x_5882_);
v___x_5884_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_5885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5885_, 0, v___x_5883_);
lean_ctor_set(v___x_5885_, 1, v___x_5884_);
v___x_5886_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_5885_, v___y_5779_, v___y_5780_, v___y_5781_, v___y_5782_);
lean_dec(v___y_5782_);
lean_dec_ref(v___y_5781_);
lean_dec(v___y_5780_);
lean_dec_ref(v___y_5779_);
v_a_5887_ = lean_ctor_get(v___x_5886_, 0);
v_isSharedCheck_5894_ = !lean_is_exclusive(v___x_5886_);
if (v_isSharedCheck_5894_ == 0)
{
v___x_5889_ = v___x_5886_;
v_isShared_5890_ = v_isSharedCheck_5894_;
goto v_resetjp_5888_;
}
else
{
lean_inc(v_a_5887_);
lean_dec(v___x_5886_);
v___x_5889_ = lean_box(0);
v_isShared_5890_ = v_isSharedCheck_5894_;
goto v_resetjp_5888_;
}
v_resetjp_5888_:
{
lean_object* v___x_5892_; 
if (v_isShared_5890_ == 0)
{
v___x_5892_ = v___x_5889_;
goto v_reusejp_5891_;
}
else
{
lean_object* v_reuseFailAlloc_5893_; 
v_reuseFailAlloc_5893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5893_, 0, v_a_5887_);
v___x_5892_ = v_reuseFailAlloc_5893_;
goto v_reusejp_5891_;
}
v_reusejp_5891_:
{
return v___x_5892_;
}
}
}
else
{
goto v___jp_5784_;
}
v___jp_5784_:
{
lean_object* v___x_5785_; 
lean_inc(v___y_5782_);
lean_inc_ref(v___y_5781_);
lean_inc(v___y_5780_);
lean_inc_ref(v___y_5779_);
lean_inc_ref(v_motiveArgs_5777_);
v___x_5785_ = lean_apply_7(v_onMotive_5771_, v_motiveArgs_5777_, v_motiveBody_5778_, v___y_5779_, v___y_5780_, v___y_5781_, v___y_5782_, lean_box(0));
if (lean_obj_tag(v___x_5785_) == 0)
{
lean_object* v_a_5786_; lean_object* v_discrInfos_5787_; lean_object* v___x_5788_; lean_object* v_addHEqualities_5789_; lean_object* v___x_5790_; lean_object* v___x_5791_; lean_object* v___x_5792_; lean_object* v___x_5793_; lean_object* v___x_5794_; lean_object* v___x_5795_; lean_object* v___x_5796_; lean_object* v___x_5797_; size_t v_sz_5798_; lean_object* v___x_5799_; 
v_a_5786_ = lean_ctor_get(v___x_5785_, 0);
lean_inc(v_a_5786_);
lean_dec_ref(v___x_5785_);
v_discrInfos_5787_ = lean_ctor_get(v_toMatcherInfo_5772_, 4);
lean_inc_ref(v_discrInfos_5787_);
lean_dec_ref(v_toMatcherInfo_5772_);
v___x_5788_ = lean_unsigned_to_nat(0u);
v_addHEqualities_5789_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___closed__0));
v___x_5790_ = lean_array_get_size(v_a_5773_);
v___x_5791_ = l_Array_toSubarray___redArg(v_a_5773_, v___x_5788_, v___x_5790_);
v___x_5792_ = lean_array_get_size(v_discrInfos_5787_);
v___x_5793_ = l_Array_toSubarray___redArg(v_discrInfos_5787_, v___x_5788_, v___x_5792_);
v___x_5794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5794_, 0, v___x_5791_);
lean_ctor_set(v___x_5794_, 1, v___x_5793_);
v___x_5795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5795_, 0, v_addHEqualities_5789_);
lean_ctor_set(v___x_5795_, 1, v___x_5794_);
v___x_5796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5796_, 0, v_addHEqualities_5789_);
lean_ctor_set(v___x_5796_, 1, v___x_5795_);
v___x_5797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5797_, 0, v_a_5786_);
lean_ctor_set(v___x_5797_, 1, v___x_5796_);
v_sz_5798_ = lean_array_size(v_motiveArgs_5777_);
lean_inc(v___y_5782_);
lean_inc_ref(v___y_5781_);
lean_inc(v___y_5780_);
lean_inc_ref(v___y_5779_);
v___x_5799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(v_addEqualities_5774_, v_motiveArgs_5777_, v_sz_5798_, v___x_5775_, v___x_5797_, v___y_5779_, v___y_5780_, v___y_5781_, v___y_5782_);
if (lean_obj_tag(v___x_5799_) == 0)
{
lean_object* v_a_5800_; lean_object* v_snd_5801_; lean_object* v_snd_5802_; lean_object* v_fst_5803_; lean_object* v___x_5805_; uint8_t v_isShared_5806_; uint8_t v_isSharedCheck_5858_; 
v_a_5800_ = lean_ctor_get(v___x_5799_, 0);
lean_inc(v_a_5800_);
lean_dec_ref(v___x_5799_);
v_snd_5801_ = lean_ctor_get(v_a_5800_, 1);
lean_inc(v_snd_5801_);
v_snd_5802_ = lean_ctor_get(v_snd_5801_, 1);
lean_inc(v_snd_5802_);
v_fst_5803_ = lean_ctor_get(v_a_5800_, 0);
v_isSharedCheck_5858_ = !lean_is_exclusive(v_a_5800_);
if (v_isSharedCheck_5858_ == 0)
{
lean_object* v_unused_5859_; 
v_unused_5859_ = lean_ctor_get(v_a_5800_, 1);
lean_dec(v_unused_5859_);
v___x_5805_ = v_a_5800_;
v_isShared_5806_ = v_isSharedCheck_5858_;
goto v_resetjp_5804_;
}
else
{
lean_inc(v_fst_5803_);
lean_dec(v_a_5800_);
v___x_5805_ = lean_box(0);
v_isShared_5806_ = v_isSharedCheck_5858_;
goto v_resetjp_5804_;
}
v_resetjp_5804_:
{
lean_object* v_fst_5807_; lean_object* v___x_5809_; uint8_t v_isShared_5810_; uint8_t v_isSharedCheck_5856_; 
v_fst_5807_ = lean_ctor_get(v_snd_5801_, 0);
v_isSharedCheck_5856_ = !lean_is_exclusive(v_snd_5801_);
if (v_isSharedCheck_5856_ == 0)
{
lean_object* v_unused_5857_; 
v_unused_5857_ = lean_ctor_get(v_snd_5801_, 1);
lean_dec(v_unused_5857_);
v___x_5809_ = v_snd_5801_;
v_isShared_5810_ = v_isSharedCheck_5856_;
goto v_resetjp_5808_;
}
else
{
lean_inc(v_fst_5807_);
lean_dec(v_snd_5801_);
v___x_5809_ = lean_box(0);
v_isShared_5810_ = v_isSharedCheck_5856_;
goto v_resetjp_5808_;
}
v_resetjp_5808_:
{
lean_object* v_fst_5811_; lean_object* v___x_5813_; uint8_t v_isShared_5814_; uint8_t v_isSharedCheck_5854_; 
v_fst_5811_ = lean_ctor_get(v_snd_5802_, 0);
v_isSharedCheck_5854_ = !lean_is_exclusive(v_snd_5802_);
if (v_isSharedCheck_5854_ == 0)
{
lean_object* v_unused_5855_; 
v_unused_5855_ = lean_ctor_get(v_snd_5802_, 1);
lean_dec(v_unused_5855_);
v___x_5813_ = v_snd_5802_;
v_isShared_5814_ = v_isSharedCheck_5854_;
goto v_resetjp_5812_;
}
else
{
lean_inc(v_fst_5811_);
lean_dec(v_snd_5802_);
v___x_5813_ = lean_box(0);
v_isShared_5814_ = v_isSharedCheck_5854_;
goto v_resetjp_5812_;
}
v_resetjp_5812_:
{
uint8_t v___x_5815_; uint8_t v___x_5816_; uint8_t v___x_5817_; lean_object* v___x_5818_; 
v___x_5815_ = 0;
v___x_5816_ = 1;
v___x_5817_ = 1;
lean_inc(v_fst_5803_);
v___x_5818_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_5777_, v_fst_5803_, v___x_5815_, v___x_5816_, v___x_5815_, v___x_5816_, v___x_5817_, v___y_5779_, v___y_5780_, v___y_5781_, v___y_5782_);
lean_dec_ref(v_motiveArgs_5777_);
if (lean_obj_tag(v___x_5818_) == 0)
{
lean_object* v_a_5819_; lean_object* v___x_5820_; 
v_a_5819_ = lean_ctor_get(v___x_5818_, 0);
lean_inc(v_a_5819_);
lean_dec_ref(v___x_5818_);
v___x_5820_ = l_Lean_Meta_getLevel(v_fst_5803_, v___y_5779_, v___y_5780_, v___y_5781_, v___y_5782_);
if (lean_obj_tag(v___x_5820_) == 0)
{
lean_object* v_a_5821_; lean_object* v___x_5823_; uint8_t v_isShared_5824_; uint8_t v_isSharedCheck_5837_; 
v_a_5821_ = lean_ctor_get(v___x_5820_, 0);
v_isSharedCheck_5837_ = !lean_is_exclusive(v___x_5820_);
if (v_isSharedCheck_5837_ == 0)
{
v___x_5823_ = v___x_5820_;
v_isShared_5824_ = v_isSharedCheck_5837_;
goto v_resetjp_5822_;
}
else
{
lean_inc(v_a_5821_);
lean_dec(v___x_5820_);
v___x_5823_ = lean_box(0);
v_isShared_5824_ = v_isSharedCheck_5837_;
goto v_resetjp_5822_;
}
v_resetjp_5822_:
{
lean_object* v___x_5826_; 
if (v_isShared_5814_ == 0)
{
lean_ctor_set(v___x_5813_, 1, v_fst_5811_);
lean_ctor_set(v___x_5813_, 0, v_fst_5807_);
v___x_5826_ = v___x_5813_;
goto v_reusejp_5825_;
}
else
{
lean_object* v_reuseFailAlloc_5836_; 
v_reuseFailAlloc_5836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5836_, 0, v_fst_5807_);
lean_ctor_set(v_reuseFailAlloc_5836_, 1, v_fst_5811_);
v___x_5826_ = v_reuseFailAlloc_5836_;
goto v_reusejp_5825_;
}
v_reusejp_5825_:
{
lean_object* v___x_5828_; 
if (v_isShared_5810_ == 0)
{
lean_ctor_set(v___x_5809_, 1, v___x_5826_);
lean_ctor_set(v___x_5809_, 0, v_a_5821_);
v___x_5828_ = v___x_5809_;
goto v_reusejp_5827_;
}
else
{
lean_object* v_reuseFailAlloc_5835_; 
v_reuseFailAlloc_5835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5835_, 0, v_a_5821_);
lean_ctor_set(v_reuseFailAlloc_5835_, 1, v___x_5826_);
v___x_5828_ = v_reuseFailAlloc_5835_;
goto v_reusejp_5827_;
}
v_reusejp_5827_:
{
lean_object* v___x_5830_; 
if (v_isShared_5806_ == 0)
{
lean_ctor_set(v___x_5805_, 1, v___x_5828_);
lean_ctor_set(v___x_5805_, 0, v_a_5819_);
v___x_5830_ = v___x_5805_;
goto v_reusejp_5829_;
}
else
{
lean_object* v_reuseFailAlloc_5834_; 
v_reuseFailAlloc_5834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5834_, 0, v_a_5819_);
lean_ctor_set(v_reuseFailAlloc_5834_, 1, v___x_5828_);
v___x_5830_ = v_reuseFailAlloc_5834_;
goto v_reusejp_5829_;
}
v_reusejp_5829_:
{
lean_object* v___x_5832_; 
if (v_isShared_5824_ == 0)
{
lean_ctor_set(v___x_5823_, 0, v___x_5830_);
v___x_5832_ = v___x_5823_;
goto v_reusejp_5831_;
}
else
{
lean_object* v_reuseFailAlloc_5833_; 
v_reuseFailAlloc_5833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5833_, 0, v___x_5830_);
v___x_5832_ = v_reuseFailAlloc_5833_;
goto v_reusejp_5831_;
}
v_reusejp_5831_:
{
return v___x_5832_;
}
}
}
}
}
}
else
{
lean_object* v_a_5838_; lean_object* v___x_5840_; uint8_t v_isShared_5841_; uint8_t v_isSharedCheck_5845_; 
lean_dec(v_a_5819_);
lean_del_object(v___x_5813_);
lean_dec(v_fst_5811_);
lean_del_object(v___x_5809_);
lean_dec(v_fst_5807_);
lean_del_object(v___x_5805_);
v_a_5838_ = lean_ctor_get(v___x_5820_, 0);
v_isSharedCheck_5845_ = !lean_is_exclusive(v___x_5820_);
if (v_isSharedCheck_5845_ == 0)
{
v___x_5840_ = v___x_5820_;
v_isShared_5841_ = v_isSharedCheck_5845_;
goto v_resetjp_5839_;
}
else
{
lean_inc(v_a_5838_);
lean_dec(v___x_5820_);
v___x_5840_ = lean_box(0);
v_isShared_5841_ = v_isSharedCheck_5845_;
goto v_resetjp_5839_;
}
v_resetjp_5839_:
{
lean_object* v___x_5843_; 
if (v_isShared_5841_ == 0)
{
v___x_5843_ = v___x_5840_;
goto v_reusejp_5842_;
}
else
{
lean_object* v_reuseFailAlloc_5844_; 
v_reuseFailAlloc_5844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5844_, 0, v_a_5838_);
v___x_5843_ = v_reuseFailAlloc_5844_;
goto v_reusejp_5842_;
}
v_reusejp_5842_:
{
return v___x_5843_;
}
}
}
}
else
{
lean_object* v_a_5846_; lean_object* v___x_5848_; uint8_t v_isShared_5849_; uint8_t v_isSharedCheck_5853_; 
lean_del_object(v___x_5813_);
lean_dec(v_fst_5811_);
lean_del_object(v___x_5809_);
lean_dec(v_fst_5807_);
lean_del_object(v___x_5805_);
lean_dec(v_fst_5803_);
lean_dec(v___y_5782_);
lean_dec_ref(v___y_5781_);
lean_dec(v___y_5780_);
lean_dec_ref(v___y_5779_);
v_a_5846_ = lean_ctor_get(v___x_5818_, 0);
v_isSharedCheck_5853_ = !lean_is_exclusive(v___x_5818_);
if (v_isSharedCheck_5853_ == 0)
{
v___x_5848_ = v___x_5818_;
v_isShared_5849_ = v_isSharedCheck_5853_;
goto v_resetjp_5847_;
}
else
{
lean_inc(v_a_5846_);
lean_dec(v___x_5818_);
v___x_5848_ = lean_box(0);
v_isShared_5849_ = v_isSharedCheck_5853_;
goto v_resetjp_5847_;
}
v_resetjp_5847_:
{
lean_object* v___x_5851_; 
if (v_isShared_5849_ == 0)
{
v___x_5851_ = v___x_5848_;
goto v_reusejp_5850_;
}
else
{
lean_object* v_reuseFailAlloc_5852_; 
v_reuseFailAlloc_5852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5852_, 0, v_a_5846_);
v___x_5851_ = v_reuseFailAlloc_5852_;
goto v_reusejp_5850_;
}
v_reusejp_5850_:
{
return v___x_5851_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5860_; lean_object* v___x_5862_; uint8_t v_isShared_5863_; uint8_t v_isSharedCheck_5867_; 
lean_dec(v___y_5782_);
lean_dec_ref(v___y_5781_);
lean_dec(v___y_5780_);
lean_dec_ref(v___y_5779_);
lean_dec_ref(v_motiveArgs_5777_);
v_a_5860_ = lean_ctor_get(v___x_5799_, 0);
v_isSharedCheck_5867_ = !lean_is_exclusive(v___x_5799_);
if (v_isSharedCheck_5867_ == 0)
{
v___x_5862_ = v___x_5799_;
v_isShared_5863_ = v_isSharedCheck_5867_;
goto v_resetjp_5861_;
}
else
{
lean_inc(v_a_5860_);
lean_dec(v___x_5799_);
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
else
{
lean_object* v_a_5868_; lean_object* v___x_5870_; uint8_t v_isShared_5871_; uint8_t v_isSharedCheck_5875_; 
lean_dec(v___y_5782_);
lean_dec_ref(v___y_5781_);
lean_dec(v___y_5780_);
lean_dec_ref(v___y_5779_);
lean_dec_ref(v_motiveArgs_5777_);
lean_dec_ref(v_a_5773_);
lean_dec_ref(v_toMatcherInfo_5772_);
v_a_5868_ = lean_ctor_get(v___x_5785_, 0);
v_isSharedCheck_5875_ = !lean_is_exclusive(v___x_5785_);
if (v_isSharedCheck_5875_ == 0)
{
v___x_5870_ = v___x_5785_;
v_isShared_5871_ = v_isSharedCheck_5875_;
goto v_resetjp_5869_;
}
else
{
lean_inc(v_a_5868_);
lean_dec(v___x_5785_);
v___x_5870_ = lean_box(0);
v_isShared_5871_ = v_isSharedCheck_5875_;
goto v_resetjp_5869_;
}
v_resetjp_5869_:
{
lean_object* v___x_5873_; 
if (v_isShared_5871_ == 0)
{
v___x_5873_ = v___x_5870_;
goto v_reusejp_5872_;
}
else
{
lean_object* v_reuseFailAlloc_5874_; 
v_reuseFailAlloc_5874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5874_, 0, v_a_5868_);
v___x_5873_ = v_reuseFailAlloc_5874_;
goto v_reusejp_5872_;
}
v_reusejp_5872_:
{
return v___x_5873_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed(lean_object* v_onMotive_5895_, lean_object* v_toMatcherInfo_5896_, lean_object* v_a_5897_, lean_object* v_addEqualities_5898_, lean_object* v___x_5899_, lean_object* v_discrs_5900_, lean_object* v_motiveArgs_5901_, lean_object* v_motiveBody_5902_, lean_object* v___y_5903_, lean_object* v___y_5904_, lean_object* v___y_5905_, lean_object* v___y_5906_, lean_object* v___y_5907_){
_start:
{
uint8_t v_addEqualities_boxed_5908_; size_t v___x_34635__boxed_5909_; lean_object* v_res_5910_; 
v_addEqualities_boxed_5908_ = lean_unbox(v_addEqualities_5898_);
v___x_34635__boxed_5909_ = lean_unbox_usize(v___x_5899_);
lean_dec(v___x_5899_);
v_res_5910_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(v_onMotive_5895_, v_toMatcherInfo_5896_, v_a_5897_, v_addEqualities_boxed_5908_, v___x_34635__boxed_5909_, v_discrs_5900_, v_motiveArgs_5901_, v_motiveBody_5902_, v___y_5903_, v___y_5904_, v___y_5905_, v___y_5906_);
lean_dec_ref(v_discrs_5900_);
return v_res_5910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(lean_object* v_as_5911_, size_t v_sz_5912_, size_t v_i_5913_, lean_object* v_b_5914_, lean_object* v___y_5915_, lean_object* v___y_5916_, lean_object* v___y_5917_, lean_object* v___y_5918_){
_start:
{
lean_object* v_a_5921_; uint8_t v___x_5925_; 
v___x_5925_ = lean_usize_dec_lt(v_i_5913_, v_sz_5912_);
if (v___x_5925_ == 0)
{
lean_object* v___x_5926_; 
lean_dec(v___y_5918_);
lean_dec_ref(v___y_5917_);
lean_dec(v___y_5916_);
lean_dec_ref(v___y_5915_);
v___x_5926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5926_, 0, v_b_5914_);
return v___x_5926_;
}
else
{
lean_object* v_snd_5927_; lean_object* v_snd_5928_; lean_object* v_fst_5929_; lean_object* v___x_5931_; uint8_t v_isShared_5932_; uint8_t v_isSharedCheck_5989_; 
v_snd_5927_ = lean_ctor_get(v_b_5914_, 1);
lean_inc(v_snd_5927_);
v_snd_5928_ = lean_ctor_get(v_snd_5927_, 1);
lean_inc(v_snd_5928_);
v_fst_5929_ = lean_ctor_get(v_b_5914_, 0);
v_isSharedCheck_5989_ = !lean_is_exclusive(v_b_5914_);
if (v_isSharedCheck_5989_ == 0)
{
lean_object* v_unused_5990_; 
v_unused_5990_ = lean_ctor_get(v_b_5914_, 1);
lean_dec(v_unused_5990_);
v___x_5931_ = v_b_5914_;
v_isShared_5932_ = v_isSharedCheck_5989_;
goto v_resetjp_5930_;
}
else
{
lean_inc(v_fst_5929_);
lean_dec(v_b_5914_);
v___x_5931_ = lean_box(0);
v_isShared_5932_ = v_isSharedCheck_5989_;
goto v_resetjp_5930_;
}
v_resetjp_5930_:
{
lean_object* v_fst_5933_; lean_object* v___x_5935_; uint8_t v_isShared_5936_; uint8_t v_isSharedCheck_5987_; 
v_fst_5933_ = lean_ctor_get(v_snd_5927_, 0);
v_isSharedCheck_5987_ = !lean_is_exclusive(v_snd_5927_);
if (v_isSharedCheck_5987_ == 0)
{
lean_object* v_unused_5988_; 
v_unused_5988_ = lean_ctor_get(v_snd_5927_, 1);
lean_dec(v_unused_5988_);
v___x_5935_ = v_snd_5927_;
v_isShared_5936_ = v_isSharedCheck_5987_;
goto v_resetjp_5934_;
}
else
{
lean_inc(v_fst_5933_);
lean_dec(v_snd_5927_);
v___x_5935_ = lean_box(0);
v_isShared_5936_ = v_isSharedCheck_5987_;
goto v_resetjp_5934_;
}
v_resetjp_5934_:
{
lean_object* v_array_5937_; lean_object* v_start_5938_; lean_object* v_stop_5939_; uint8_t v___x_5940_; 
v_array_5937_ = lean_ctor_get(v_snd_5928_, 0);
v_start_5938_ = lean_ctor_get(v_snd_5928_, 1);
v_stop_5939_ = lean_ctor_get(v_snd_5928_, 2);
v___x_5940_ = lean_nat_dec_lt(v_start_5938_, v_stop_5939_);
if (v___x_5940_ == 0)
{
lean_object* v___x_5942_; 
lean_dec(v___y_5918_);
lean_dec_ref(v___y_5917_);
lean_dec(v___y_5916_);
lean_dec_ref(v___y_5915_);
if (v_isShared_5936_ == 0)
{
v___x_5942_ = v___x_5935_;
goto v_reusejp_5941_;
}
else
{
lean_object* v_reuseFailAlloc_5947_; 
v_reuseFailAlloc_5947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5947_, 0, v_fst_5933_);
lean_ctor_set(v_reuseFailAlloc_5947_, 1, v_snd_5928_);
v___x_5942_ = v_reuseFailAlloc_5947_;
goto v_reusejp_5941_;
}
v_reusejp_5941_:
{
lean_object* v___x_5944_; 
if (v_isShared_5932_ == 0)
{
lean_ctor_set(v___x_5931_, 1, v___x_5942_);
v___x_5944_ = v___x_5931_;
goto v_reusejp_5943_;
}
else
{
lean_object* v_reuseFailAlloc_5946_; 
v_reuseFailAlloc_5946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5946_, 0, v_fst_5929_);
lean_ctor_set(v_reuseFailAlloc_5946_, 1, v___x_5942_);
v___x_5944_ = v_reuseFailAlloc_5946_;
goto v_reusejp_5943_;
}
v_reusejp_5943_:
{
lean_object* v___x_5945_; 
v___x_5945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5945_, 0, v___x_5944_);
return v___x_5945_;
}
}
}
else
{
lean_object* v___x_5949_; uint8_t v_isShared_5950_; uint8_t v_isSharedCheck_5983_; 
lean_inc(v_stop_5939_);
lean_inc(v_start_5938_);
lean_inc_ref(v_array_5937_);
v_isSharedCheck_5983_ = !lean_is_exclusive(v_snd_5928_);
if (v_isSharedCheck_5983_ == 0)
{
lean_object* v_unused_5984_; lean_object* v_unused_5985_; lean_object* v_unused_5986_; 
v_unused_5984_ = lean_ctor_get(v_snd_5928_, 2);
lean_dec(v_unused_5984_);
v_unused_5985_ = lean_ctor_get(v_snd_5928_, 1);
lean_dec(v_unused_5985_);
v_unused_5986_ = lean_ctor_get(v_snd_5928_, 0);
lean_dec(v_unused_5986_);
v___x_5949_ = v_snd_5928_;
v_isShared_5950_ = v_isSharedCheck_5983_;
goto v_resetjp_5948_;
}
else
{
lean_dec(v_snd_5928_);
v___x_5949_ = lean_box(0);
v_isShared_5950_ = v_isSharedCheck_5983_;
goto v_resetjp_5948_;
}
v_resetjp_5948_:
{
lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5955_; 
v___x_5951_ = lean_array_fget(v_array_5937_, v_start_5938_);
v___x_5952_ = lean_unsigned_to_nat(1u);
v___x_5953_ = lean_nat_add(v_start_5938_, v___x_5952_);
lean_dec(v_start_5938_);
if (v_isShared_5950_ == 0)
{
lean_ctor_set(v___x_5949_, 1, v___x_5953_);
v___x_5955_ = v___x_5949_;
goto v_reusejp_5954_;
}
else
{
lean_object* v_reuseFailAlloc_5982_; 
v_reuseFailAlloc_5982_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5982_, 0, v_array_5937_);
lean_ctor_set(v_reuseFailAlloc_5982_, 1, v___x_5953_);
lean_ctor_set(v_reuseFailAlloc_5982_, 2, v_stop_5939_);
v___x_5955_ = v_reuseFailAlloc_5982_;
goto v_reusejp_5954_;
}
v_reusejp_5954_:
{
lean_object* v___y_5957_; 
if (lean_obj_tag(v___x_5951_) == 0)
{
lean_object* v___x_5975_; lean_object* v___x_5976_; 
lean_del_object(v___x_5935_);
lean_del_object(v___x_5931_);
v___x_5975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5975_, 0, v_fst_5933_);
lean_ctor_set(v___x_5975_, 1, v___x_5955_);
v___x_5976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5976_, 0, v_fst_5929_);
lean_ctor_set(v___x_5976_, 1, v___x_5975_);
v_a_5921_ = v___x_5976_;
goto v___jp_5920_;
}
else
{
lean_object* v_val_5977_; lean_object* v_a_5978_; uint8_t v___x_5979_; 
v_val_5977_ = lean_ctor_get(v___x_5951_, 0);
lean_inc(v_val_5977_);
lean_dec_ref(v___x_5951_);
v_a_5978_ = lean_array_uget_borrowed(v_as_5911_, v_i_5913_);
v___x_5979_ = lean_unbox(v_val_5977_);
lean_dec(v_val_5977_);
if (v___x_5979_ == 0)
{
lean_object* v___x_5980_; 
lean_inc(v___y_5918_);
lean_inc_ref(v___y_5917_);
lean_inc(v___y_5916_);
lean_inc_ref(v___y_5915_);
lean_inc(v_a_5978_);
v___x_5980_ = l_Lean_Meta_mkEqRefl(v_a_5978_, v___y_5915_, v___y_5916_, v___y_5917_, v___y_5918_);
v___y_5957_ = v___x_5980_;
goto v___jp_5956_;
}
else
{
lean_object* v___x_5981_; 
lean_inc(v___y_5918_);
lean_inc_ref(v___y_5917_);
lean_inc(v___y_5916_);
lean_inc_ref(v___y_5915_);
lean_inc(v_a_5978_);
v___x_5981_ = l_Lean_Meta_mkHEqRefl(v_a_5978_, v___y_5915_, v___y_5916_, v___y_5917_, v___y_5918_);
v___y_5957_ = v___x_5981_;
goto v___jp_5956_;
}
}
v___jp_5956_:
{
if (lean_obj_tag(v___y_5957_) == 0)
{
lean_object* v_a_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5962_; 
v_a_5958_ = lean_ctor_get(v___y_5957_, 0);
lean_inc(v_a_5958_);
lean_dec_ref(v___y_5957_);
v___x_5959_ = lean_array_push(v_fst_5929_, v_a_5958_);
v___x_5960_ = lean_nat_add(v_fst_5933_, v___x_5952_);
lean_dec(v_fst_5933_);
if (v_isShared_5936_ == 0)
{
lean_ctor_set(v___x_5935_, 1, v___x_5955_);
lean_ctor_set(v___x_5935_, 0, v___x_5960_);
v___x_5962_ = v___x_5935_;
goto v_reusejp_5961_;
}
else
{
lean_object* v_reuseFailAlloc_5966_; 
v_reuseFailAlloc_5966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5966_, 0, v___x_5960_);
lean_ctor_set(v_reuseFailAlloc_5966_, 1, v___x_5955_);
v___x_5962_ = v_reuseFailAlloc_5966_;
goto v_reusejp_5961_;
}
v_reusejp_5961_:
{
lean_object* v___x_5964_; 
if (v_isShared_5932_ == 0)
{
lean_ctor_set(v___x_5931_, 1, v___x_5962_);
lean_ctor_set(v___x_5931_, 0, v___x_5959_);
v___x_5964_ = v___x_5931_;
goto v_reusejp_5963_;
}
else
{
lean_object* v_reuseFailAlloc_5965_; 
v_reuseFailAlloc_5965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5965_, 0, v___x_5959_);
lean_ctor_set(v_reuseFailAlloc_5965_, 1, v___x_5962_);
v___x_5964_ = v_reuseFailAlloc_5965_;
goto v_reusejp_5963_;
}
v_reusejp_5963_:
{
v_a_5921_ = v___x_5964_;
goto v___jp_5920_;
}
}
}
else
{
lean_object* v_a_5967_; lean_object* v___x_5969_; uint8_t v_isShared_5970_; uint8_t v_isSharedCheck_5974_; 
lean_dec_ref(v___x_5955_);
lean_del_object(v___x_5935_);
lean_dec(v_fst_5933_);
lean_del_object(v___x_5931_);
lean_dec(v_fst_5929_);
lean_dec(v___y_5918_);
lean_dec_ref(v___y_5917_);
lean_dec(v___y_5916_);
lean_dec_ref(v___y_5915_);
v_a_5967_ = lean_ctor_get(v___y_5957_, 0);
v_isSharedCheck_5974_ = !lean_is_exclusive(v___y_5957_);
if (v_isSharedCheck_5974_ == 0)
{
v___x_5969_ = v___y_5957_;
v_isShared_5970_ = v_isSharedCheck_5974_;
goto v_resetjp_5968_;
}
else
{
lean_inc(v_a_5967_);
lean_dec(v___y_5957_);
v___x_5969_ = lean_box(0);
v_isShared_5970_ = v_isSharedCheck_5974_;
goto v_resetjp_5968_;
}
v_resetjp_5968_:
{
lean_object* v___x_5972_; 
if (v_isShared_5970_ == 0)
{
v___x_5972_ = v___x_5969_;
goto v_reusejp_5971_;
}
else
{
lean_object* v_reuseFailAlloc_5973_; 
v_reuseFailAlloc_5973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5973_, 0, v_a_5967_);
v___x_5972_ = v_reuseFailAlloc_5973_;
goto v_reusejp_5971_;
}
v_reusejp_5971_:
{
return v___x_5972_;
}
}
}
}
}
}
}
}
}
}
v___jp_5920_:
{
size_t v___x_5922_; size_t v___x_5923_; 
v___x_5922_ = ((size_t)1ULL);
v___x_5923_ = lean_usize_add(v_i_5913_, v___x_5922_);
v_i_5913_ = v___x_5923_;
v_b_5914_ = v_a_5921_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8___boxed(lean_object* v_as_5991_, lean_object* v_sz_5992_, lean_object* v_i_5993_, lean_object* v_b_5994_, lean_object* v___y_5995_, lean_object* v___y_5996_, lean_object* v___y_5997_, lean_object* v___y_5998_, lean_object* v___y_5999_){
_start:
{
size_t v_sz_boxed_6000_; size_t v_i_boxed_6001_; lean_object* v_res_6002_; 
v_sz_boxed_6000_ = lean_unbox_usize(v_sz_5992_);
lean_dec(v_sz_5992_);
v_i_boxed_6001_ = lean_unbox_usize(v_i_5993_);
lean_dec(v_i_5993_);
v_res_6002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(v_as_5991_, v_sz_boxed_6000_, v_i_boxed_6001_, v_b_5994_, v___y_5995_, v___y_5996_, v___y_5997_, v___y_5998_);
lean_dec_ref(v_as_5991_);
return v_res_6002_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(lean_object* v___x_6003_, lean_object* v___y_6004_, lean_object* v___y_6005_, lean_object* v___y_6006_, lean_object* v___y_6007_){
_start:
{
lean_object* v___x_6009_; 
v___x_6009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6009_, 0, v___x_6003_);
return v___x_6009_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed(lean_object* v___x_6010_, lean_object* v___y_6011_, lean_object* v___y_6012_, lean_object* v___y_6013_, lean_object* v___y_6014_, lean_object* v___y_6015_){
_start:
{
lean_object* v_res_6016_; 
v_res_6016_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(v___x_6010_, v___y_6011_, v___y_6012_, v___y_6013_, v___y_6014_);
lean_dec(v___y_6014_);
lean_dec_ref(v___y_6013_);
lean_dec(v___y_6012_);
lean_dec_ref(v___y_6011_);
return v_res_6016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(size_t v_sz_6017_, size_t v_i_6018_, lean_object* v_bs_6019_, lean_object* v___y_6020_, lean_object* v___y_6021_, lean_object* v___y_6022_){
_start:
{
uint8_t v___x_6024_; 
v___x_6024_ = lean_usize_dec_lt(v_i_6018_, v_sz_6017_);
if (v___x_6024_ == 0)
{
lean_object* v___x_6025_; 
lean_dec_ref(v___y_6020_);
v___x_6025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6025_, 0, v_bs_6019_);
return v___x_6025_;
}
else
{
lean_object* v_v_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; 
v_v_6026_ = lean_array_uget_borrowed(v_bs_6019_, v_i_6018_);
v___x_6027_ = l_Lean_Expr_fvarId_x21(v_v_6026_);
lean_inc_ref(v___y_6020_);
v___x_6028_ = l_Lean_FVarId_getUserName___redArg(v___x_6027_, v___y_6020_, v___y_6021_, v___y_6022_);
if (lean_obj_tag(v___x_6028_) == 0)
{
lean_object* v_a_6029_; lean_object* v___x_6030_; lean_object* v_bs_x27_6031_; size_t v___x_6032_; size_t v___x_6033_; lean_object* v___x_6034_; 
v_a_6029_ = lean_ctor_get(v___x_6028_, 0);
lean_inc(v_a_6029_);
lean_dec_ref(v___x_6028_);
v___x_6030_ = lean_unsigned_to_nat(0u);
v_bs_x27_6031_ = lean_array_uset(v_bs_6019_, v_i_6018_, v___x_6030_);
v___x_6032_ = ((size_t)1ULL);
v___x_6033_ = lean_usize_add(v_i_6018_, v___x_6032_);
v___x_6034_ = lean_array_uset(v_bs_x27_6031_, v_i_6018_, v_a_6029_);
v_i_6018_ = v___x_6033_;
v_bs_6019_ = v___x_6034_;
goto _start;
}
else
{
lean_object* v_a_6036_; lean_object* v___x_6038_; uint8_t v_isShared_6039_; uint8_t v_isSharedCheck_6043_; 
lean_dec_ref(v___y_6020_);
lean_dec_ref(v_bs_6019_);
v_a_6036_ = lean_ctor_get(v___x_6028_, 0);
v_isSharedCheck_6043_ = !lean_is_exclusive(v___x_6028_);
if (v_isSharedCheck_6043_ == 0)
{
v___x_6038_ = v___x_6028_;
v_isShared_6039_ = v_isSharedCheck_6043_;
goto v_resetjp_6037_;
}
else
{
lean_inc(v_a_6036_);
lean_dec(v___x_6028_);
v___x_6038_ = lean_box(0);
v_isShared_6039_ = v_isSharedCheck_6043_;
goto v_resetjp_6037_;
}
v_resetjp_6037_:
{
lean_object* v___x_6041_; 
if (v_isShared_6039_ == 0)
{
v___x_6041_ = v___x_6038_;
goto v_reusejp_6040_;
}
else
{
lean_object* v_reuseFailAlloc_6042_; 
v_reuseFailAlloc_6042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6042_, 0, v_a_6036_);
v___x_6041_ = v_reuseFailAlloc_6042_;
goto v_reusejp_6040_;
}
v_reusejp_6040_:
{
return v___x_6041_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg___boxed(lean_object* v_sz_6044_, lean_object* v_i_6045_, lean_object* v_bs_6046_, lean_object* v___y_6047_, lean_object* v___y_6048_, lean_object* v___y_6049_, lean_object* v___y_6050_){
_start:
{
size_t v_sz_boxed_6051_; size_t v_i_boxed_6052_; lean_object* v_res_6053_; 
v_sz_boxed_6051_ = lean_unbox_usize(v_sz_6044_);
lean_dec(v_sz_6044_);
v_i_boxed_6052_ = lean_unbox_usize(v_i_6045_);
lean_dec(v_i_6045_);
v_res_6053_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_boxed_6051_, v_i_boxed_6052_, v_bs_6046_, v___y_6047_, v___y_6048_, v___y_6049_);
lean_dec(v___y_6049_);
lean_dec_ref(v___y_6048_);
return v_res_6053_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(lean_object* v_xs_6054_, lean_object* v_x_6055_, lean_object* v___y_6056_, lean_object* v___y_6057_, lean_object* v___y_6058_, lean_object* v___y_6059_){
_start:
{
size_t v_sz_6061_; size_t v___x_6062_; lean_object* v___x_6063_; 
v_sz_6061_ = lean_array_size(v_xs_6054_);
v___x_6062_ = ((size_t)0ULL);
v___x_6063_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_6061_, v___x_6062_, v_xs_6054_, v___y_6056_, v___y_6058_, v___y_6059_);
return v___x_6063_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3___boxed(lean_object* v_xs_6064_, lean_object* v_x_6065_, lean_object* v___y_6066_, lean_object* v___y_6067_, lean_object* v___y_6068_, lean_object* v___y_6069_, lean_object* v___y_6070_){
_start:
{
lean_object* v_res_6071_; 
v_res_6071_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(v_xs_6064_, v_x_6065_, v___y_6066_, v___y_6067_, v___y_6068_, v___y_6069_);
lean_dec(v___y_6069_);
lean_dec_ref(v___y_6068_);
lean_dec(v___y_6067_);
lean_dec_ref(v_x_6065_);
return v_res_6071_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(lean_object* v___x_6072_, lean_object* v___x_6073_, lean_object* v___f_6074_, uint8_t v___x_6075_, lean_object* v_fst_6076_, lean_object* v___x_6077_, lean_object* v___x_6078_, lean_object* v___x_6079_, lean_object* v___y_6080_, lean_object* v___y_6081_, lean_object* v___y_6082_, lean_object* v___y_6083_){
_start:
{
lean_object* v___x_6085_; 
v___x_6085_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v___x_6072_, v___x_6073_, v___f_6074_, v___x_6075_, v___x_6075_, v___y_6080_, v___y_6081_, v___y_6082_, v___y_6083_);
if (lean_obj_tag(v___x_6085_) == 0)
{
lean_object* v_a_6086_; lean_object* v___x_6088_; uint8_t v_isShared_6089_; uint8_t v_isSharedCheck_6098_; 
v_a_6086_ = lean_ctor_get(v___x_6085_, 0);
v_isSharedCheck_6098_ = !lean_is_exclusive(v___x_6085_);
if (v_isSharedCheck_6098_ == 0)
{
v___x_6088_ = v___x_6085_;
v_isShared_6089_ = v_isSharedCheck_6098_;
goto v_resetjp_6087_;
}
else
{
lean_inc(v_a_6086_);
lean_dec(v___x_6085_);
v___x_6088_ = lean_box(0);
v_isShared_6089_ = v_isSharedCheck_6098_;
goto v_resetjp_6087_;
}
v_resetjp_6087_:
{
lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6096_; 
v___x_6090_ = lean_array_push(v_fst_6076_, v_a_6086_);
v___x_6091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6091_, 0, v___x_6077_);
lean_ctor_set(v___x_6091_, 1, v___x_6078_);
v___x_6092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6092_, 0, v___x_6079_);
lean_ctor_set(v___x_6092_, 1, v___x_6091_);
v___x_6093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6093_, 0, v___x_6090_);
lean_ctor_set(v___x_6093_, 1, v___x_6092_);
v___x_6094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6094_, 0, v___x_6093_);
if (v_isShared_6089_ == 0)
{
lean_ctor_set(v___x_6088_, 0, v___x_6094_);
v___x_6096_ = v___x_6088_;
goto v_reusejp_6095_;
}
else
{
lean_object* v_reuseFailAlloc_6097_; 
v_reuseFailAlloc_6097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6097_, 0, v___x_6094_);
v___x_6096_ = v_reuseFailAlloc_6097_;
goto v_reusejp_6095_;
}
v_reusejp_6095_:
{
return v___x_6096_;
}
}
}
else
{
lean_object* v_a_6099_; lean_object* v___x_6101_; uint8_t v_isShared_6102_; uint8_t v_isSharedCheck_6106_; 
lean_dec_ref(v___x_6079_);
lean_dec_ref(v___x_6078_);
lean_dec_ref(v___x_6077_);
lean_dec(v_fst_6076_);
v_a_6099_ = lean_ctor_get(v___x_6085_, 0);
v_isSharedCheck_6106_ = !lean_is_exclusive(v___x_6085_);
if (v_isSharedCheck_6106_ == 0)
{
v___x_6101_ = v___x_6085_;
v_isShared_6102_ = v_isSharedCheck_6106_;
goto v_resetjp_6100_;
}
else
{
lean_inc(v_a_6099_);
lean_dec(v___x_6085_);
v___x_6101_ = lean_box(0);
v_isShared_6102_ = v_isSharedCheck_6106_;
goto v_resetjp_6100_;
}
v_resetjp_6100_:
{
lean_object* v___x_6104_; 
if (v_isShared_6102_ == 0)
{
v___x_6104_ = v___x_6101_;
goto v_reusejp_6103_;
}
else
{
lean_object* v_reuseFailAlloc_6105_; 
v_reuseFailAlloc_6105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6105_, 0, v_a_6099_);
v___x_6104_ = v_reuseFailAlloc_6105_;
goto v_reusejp_6103_;
}
v_reusejp_6103_:
{
return v___x_6104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed(lean_object* v___x_6107_, lean_object* v___x_6108_, lean_object* v___f_6109_, lean_object* v___x_6110_, lean_object* v_fst_6111_, lean_object* v___x_6112_, lean_object* v___x_6113_, lean_object* v___x_6114_, lean_object* v___y_6115_, lean_object* v___y_6116_, lean_object* v___y_6117_, lean_object* v___y_6118_, lean_object* v___y_6119_){
_start:
{
uint8_t v___x_35098__boxed_6120_; lean_object* v_res_6121_; 
v___x_35098__boxed_6120_ = lean_unbox(v___x_6110_);
v_res_6121_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(v___x_6107_, v___x_6108_, v___f_6109_, v___x_35098__boxed_6120_, v_fst_6111_, v___x_6112_, v___x_6113_, v___x_6114_, v___y_6115_, v___y_6116_, v___y_6117_, v___y_6118_);
return v_res_6121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(lean_object* v_fvars_6122_, lean_object* v_names_6123_, lean_object* v_k_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_){
_start:
{
lean_object* v___x_6130_; 
v___x_6130_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_6122_, v_names_6123_, v_k_6124_, v___y_6125_, v___y_6126_, v___y_6127_, v___y_6128_);
if (lean_obj_tag(v___x_6130_) == 0)
{
lean_object* v_a_6131_; lean_object* v___x_6133_; uint8_t v_isShared_6134_; uint8_t v_isSharedCheck_6138_; 
v_a_6131_ = lean_ctor_get(v___x_6130_, 0);
v_isSharedCheck_6138_ = !lean_is_exclusive(v___x_6130_);
if (v_isSharedCheck_6138_ == 0)
{
v___x_6133_ = v___x_6130_;
v_isShared_6134_ = v_isSharedCheck_6138_;
goto v_resetjp_6132_;
}
else
{
lean_inc(v_a_6131_);
lean_dec(v___x_6130_);
v___x_6133_ = lean_box(0);
v_isShared_6134_ = v_isSharedCheck_6138_;
goto v_resetjp_6132_;
}
v_resetjp_6132_:
{
lean_object* v___x_6136_; 
if (v_isShared_6134_ == 0)
{
v___x_6136_ = v___x_6133_;
goto v_reusejp_6135_;
}
else
{
lean_object* v_reuseFailAlloc_6137_; 
v_reuseFailAlloc_6137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6137_, 0, v_a_6131_);
v___x_6136_ = v_reuseFailAlloc_6137_;
goto v_reusejp_6135_;
}
v_reusejp_6135_:
{
return v___x_6136_;
}
}
}
else
{
lean_object* v_a_6139_; lean_object* v___x_6141_; uint8_t v_isShared_6142_; uint8_t v_isSharedCheck_6146_; 
v_a_6139_ = lean_ctor_get(v___x_6130_, 0);
v_isSharedCheck_6146_ = !lean_is_exclusive(v___x_6130_);
if (v_isSharedCheck_6146_ == 0)
{
v___x_6141_ = v___x_6130_;
v_isShared_6142_ = v_isSharedCheck_6146_;
goto v_resetjp_6140_;
}
else
{
lean_inc(v_a_6139_);
lean_dec(v___x_6130_);
v___x_6141_ = lean_box(0);
v_isShared_6142_ = v_isSharedCheck_6146_;
goto v_resetjp_6140_;
}
v_resetjp_6140_:
{
lean_object* v___x_6144_; 
if (v_isShared_6142_ == 0)
{
v___x_6144_ = v___x_6141_;
goto v_reusejp_6143_;
}
else
{
lean_object* v_reuseFailAlloc_6145_; 
v_reuseFailAlloc_6145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6145_, 0, v_a_6139_);
v___x_6144_ = v_reuseFailAlloc_6145_;
goto v_reusejp_6143_;
}
v_reusejp_6143_:
{
return v___x_6144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg___boxed(lean_object* v_fvars_6147_, lean_object* v_names_6148_, lean_object* v_k_6149_, lean_object* v___y_6150_, lean_object* v___y_6151_, lean_object* v___y_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_){
_start:
{
lean_object* v_res_6155_; 
v_res_6155_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_fvars_6147_, v_names_6148_, v_k_6149_, v___y_6150_, v___y_6151_, v___y_6152_, v___y_6153_);
lean_dec_ref(v_names_6148_);
lean_dec_ref(v_fvars_6147_);
return v_res_6155_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(lean_object* v___x_6156_, lean_object* v_xs_6157_, lean_object* v_remaining_x27_6158_, lean_object* v_ys4_6159_, lean_object* v_onAlt_6160_, lean_object* v_a_6161_, lean_object* v_altType_6162_, uint8_t v___x_6163_, uint8_t v___x_6164_, lean_object* v___y_6165_, lean_object* v___y_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_){
_start:
{
lean_object* v___x_6170_; 
lean_inc(v___y_6168_);
lean_inc_ref(v___y_6167_);
lean_inc(v___y_6166_);
lean_inc_ref(v___y_6165_);
v___x_6170_ = l_Lean_Meta_instantiateLambda(v___x_6156_, v_xs_6157_, v___y_6165_, v___y_6166_, v___y_6167_, v___y_6168_);
if (lean_obj_tag(v___x_6170_) == 0)
{
lean_object* v_a_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; 
v_a_6171_ = lean_ctor_get(v___x_6170_, 0);
lean_inc(v_a_6171_);
lean_dec_ref(v___x_6170_);
lean_inc_ref(v_ys4_6159_);
lean_inc_ref(v_remaining_x27_6158_);
lean_inc_ref_n(v_xs_6157_, 2);
v___x_6172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6172_, 0, v_xs_6157_);
lean_ctor_set(v___x_6172_, 1, v_xs_6157_);
lean_ctor_set(v___x_6172_, 2, v_remaining_x27_6158_);
lean_ctor_set(v___x_6172_, 3, v_remaining_x27_6158_);
lean_ctor_set(v___x_6172_, 4, v_ys4_6159_);
lean_inc(v___y_6168_);
lean_inc_ref(v___y_6167_);
lean_inc(v___y_6166_);
lean_inc_ref(v___y_6165_);
v___x_6173_ = lean_apply_9(v_onAlt_6160_, v_a_6161_, v_altType_6162_, v___x_6172_, v_a_6171_, v___y_6165_, v___y_6166_, v___y_6167_, v___y_6168_, lean_box(0));
if (lean_obj_tag(v___x_6173_) == 0)
{
lean_object* v_a_6174_; lean_object* v___x_6175_; uint8_t v___x_6176_; lean_object* v___x_6177_; 
v_a_6174_ = lean_ctor_get(v___x_6173_, 0);
lean_inc(v_a_6174_);
lean_dec_ref(v___x_6173_);
v___x_6175_ = l_Array_append___redArg(v_xs_6157_, v_ys4_6159_);
lean_dec_ref(v_ys4_6159_);
v___x_6176_ = 1;
v___x_6177_ = l_Lean_Meta_mkLambdaFVars(v___x_6175_, v_a_6174_, v___x_6163_, v___x_6164_, v___x_6163_, v___x_6164_, v___x_6176_, v___y_6165_, v___y_6166_, v___y_6167_, v___y_6168_);
lean_dec(v___y_6168_);
lean_dec_ref(v___y_6167_);
lean_dec(v___y_6166_);
lean_dec_ref(v___y_6165_);
lean_dec_ref(v___x_6175_);
return v___x_6177_;
}
else
{
lean_dec(v___y_6168_);
lean_dec_ref(v___y_6167_);
lean_dec(v___y_6166_);
lean_dec_ref(v___y_6165_);
lean_dec_ref(v_ys4_6159_);
lean_dec_ref(v_xs_6157_);
return v___x_6173_;
}
}
else
{
lean_dec(v___y_6168_);
lean_dec_ref(v___y_6167_);
lean_dec(v___y_6166_);
lean_dec_ref(v___y_6165_);
lean_dec_ref(v_altType_6162_);
lean_dec(v_a_6161_);
lean_dec_ref(v_onAlt_6160_);
lean_dec_ref(v_ys4_6159_);
lean_dec_ref(v_remaining_x27_6158_);
lean_dec_ref(v_xs_6157_);
return v___x_6170_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed(lean_object* v___x_6178_, lean_object* v_xs_6179_, lean_object* v_remaining_x27_6180_, lean_object* v_ys4_6181_, lean_object* v_onAlt_6182_, lean_object* v_a_6183_, lean_object* v_altType_6184_, lean_object* v___x_6185_, lean_object* v___x_6186_, lean_object* v___y_6187_, lean_object* v___y_6188_, lean_object* v___y_6189_, lean_object* v___y_6190_, lean_object* v___y_6191_){
_start:
{
uint8_t v___x_35225__boxed_6192_; uint8_t v___x_35226__boxed_6193_; lean_object* v_res_6194_; 
v___x_35225__boxed_6192_ = lean_unbox(v___x_6185_);
v___x_35226__boxed_6193_ = lean_unbox(v___x_6186_);
v_res_6194_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(v___x_6178_, v_xs_6179_, v_remaining_x27_6180_, v_ys4_6181_, v_onAlt_6182_, v_a_6183_, v_altType_6184_, v___x_35225__boxed_6192_, v___x_35226__boxed_6193_, v___y_6187_, v___y_6188_, v___y_6189_, v___y_6190_);
return v_res_6194_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(lean_object* v___x_6195_, lean_object* v___f_6196_, uint8_t v___x_6197_, lean_object* v_xs_6198_, lean_object* v_remaining_x27_6199_, lean_object* v_onAlt_6200_, lean_object* v_a_6201_, uint8_t v___x_6202_, lean_object* v_ys4_6203_, lean_object* v_altType_6204_, lean_object* v___y_6205_, lean_object* v___y_6206_, lean_object* v___y_6207_, lean_object* v___y_6208_){
_start:
{
lean_object* v___x_6210_; 
lean_inc(v___y_6208_);
lean_inc_ref(v___y_6207_);
lean_inc(v___y_6206_);
lean_inc_ref(v___y_6205_);
lean_inc_ref(v___x_6195_);
v___x_6210_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v___x_6195_, v___f_6196_, v___x_6197_, v___y_6205_, v___y_6206_, v___y_6207_, v___y_6208_);
if (lean_obj_tag(v___x_6210_) == 0)
{
lean_object* v_a_6211_; lean_object* v___x_6212_; lean_object* v___x_6213_; lean_object* v___f_6214_; lean_object* v___x_6215_; 
v_a_6211_ = lean_ctor_get(v___x_6210_, 0);
lean_inc(v_a_6211_);
lean_dec_ref(v___x_6210_);
v___x_6212_ = lean_box(v___x_6197_);
v___x_6213_ = lean_box(v___x_6202_);
lean_inc_ref(v_xs_6198_);
v___f_6214_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_6214_, 0, v___x_6195_);
lean_closure_set(v___f_6214_, 1, v_xs_6198_);
lean_closure_set(v___f_6214_, 2, v_remaining_x27_6199_);
lean_closure_set(v___f_6214_, 3, v_ys4_6203_);
lean_closure_set(v___f_6214_, 4, v_onAlt_6200_);
lean_closure_set(v___f_6214_, 5, v_a_6201_);
lean_closure_set(v___f_6214_, 6, v_altType_6204_);
lean_closure_set(v___f_6214_, 7, v___x_6212_);
lean_closure_set(v___f_6214_, 8, v___x_6213_);
v___x_6215_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_xs_6198_, v_a_6211_, v___f_6214_, v___y_6205_, v___y_6206_, v___y_6207_, v___y_6208_);
lean_dec(v_a_6211_);
lean_dec_ref(v_xs_6198_);
return v___x_6215_;
}
else
{
lean_object* v_a_6216_; lean_object* v___x_6218_; uint8_t v_isShared_6219_; uint8_t v_isSharedCheck_6223_; 
lean_dec(v___y_6208_);
lean_dec_ref(v___y_6207_);
lean_dec(v___y_6206_);
lean_dec_ref(v___y_6205_);
lean_dec_ref(v_altType_6204_);
lean_dec_ref(v_ys4_6203_);
lean_dec(v_a_6201_);
lean_dec_ref(v_onAlt_6200_);
lean_dec_ref(v_remaining_x27_6199_);
lean_dec_ref(v_xs_6198_);
lean_dec_ref(v___x_6195_);
v_a_6216_ = lean_ctor_get(v___x_6210_, 0);
v_isSharedCheck_6223_ = !lean_is_exclusive(v___x_6210_);
if (v_isSharedCheck_6223_ == 0)
{
v___x_6218_ = v___x_6210_;
v_isShared_6219_ = v_isSharedCheck_6223_;
goto v_resetjp_6217_;
}
else
{
lean_inc(v_a_6216_);
lean_dec(v___x_6210_);
v___x_6218_ = lean_box(0);
v_isShared_6219_ = v_isSharedCheck_6223_;
goto v_resetjp_6217_;
}
v_resetjp_6217_:
{
lean_object* v___x_6221_; 
if (v_isShared_6219_ == 0)
{
v___x_6221_ = v___x_6218_;
goto v_reusejp_6220_;
}
else
{
lean_object* v_reuseFailAlloc_6222_; 
v_reuseFailAlloc_6222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6222_, 0, v_a_6216_);
v___x_6221_ = v_reuseFailAlloc_6222_;
goto v_reusejp_6220_;
}
v_reusejp_6220_:
{
return v___x_6221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed(lean_object* v___x_6224_, lean_object* v___f_6225_, lean_object* v___x_6226_, lean_object* v_xs_6227_, lean_object* v_remaining_x27_6228_, lean_object* v_onAlt_6229_, lean_object* v_a_6230_, lean_object* v___x_6231_, lean_object* v_ys4_6232_, lean_object* v_altType_6233_, lean_object* v___y_6234_, lean_object* v___y_6235_, lean_object* v___y_6236_, lean_object* v___y_6237_, lean_object* v___y_6238_){
_start:
{
uint8_t v___x_35268__boxed_6239_; uint8_t v___x_35269__boxed_6240_; lean_object* v_res_6241_; 
v___x_35268__boxed_6239_ = lean_unbox(v___x_6226_);
v___x_35269__boxed_6240_ = lean_unbox(v___x_6231_);
v_res_6241_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(v___x_6224_, v___f_6225_, v___x_35268__boxed_6239_, v_xs_6227_, v_remaining_x27_6228_, v_onAlt_6229_, v_a_6230_, v___x_35269__boxed_6240_, v_ys4_6232_, v_altType_6233_, v___y_6234_, v___y_6235_, v___y_6236_, v___y_6237_);
return v_res_6241_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(lean_object* v___x_6242_, lean_object* v___f_6243_, uint8_t v___x_6244_, lean_object* v_remaining_x27_6245_, lean_object* v_onAlt_6246_, lean_object* v_a_6247_, uint8_t v___x_6248_, lean_object* v_extraEqualities_6249_, lean_object* v_xs_6250_, lean_object* v_altType_6251_, lean_object* v___y_6252_, lean_object* v___y_6253_, lean_object* v___y_6254_, lean_object* v___y_6255_){
_start:
{
lean_object* v___x_6257_; lean_object* v___x_6258_; lean_object* v___f_6259_; lean_object* v___x_6260_; lean_object* v___x_6261_; 
v___x_6257_ = lean_box(v___x_6244_);
v___x_6258_ = lean_box(v___x_6248_);
v___f_6259_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed), 15, 8);
lean_closure_set(v___f_6259_, 0, v___x_6242_);
lean_closure_set(v___f_6259_, 1, v___f_6243_);
lean_closure_set(v___f_6259_, 2, v___x_6257_);
lean_closure_set(v___f_6259_, 3, v_xs_6250_);
lean_closure_set(v___f_6259_, 4, v_remaining_x27_6245_);
lean_closure_set(v___f_6259_, 5, v_onAlt_6246_);
lean_closure_set(v___f_6259_, 6, v_a_6247_);
lean_closure_set(v___f_6259_, 7, v___x_6258_);
v___x_6260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6260_, 0, v_extraEqualities_6249_);
v___x_6261_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_6251_, v___x_6260_, v___f_6259_, v___x_6244_, v___x_6244_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_);
return v___x_6261_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed(lean_object* v___x_6262_, lean_object* v___f_6263_, lean_object* v___x_6264_, lean_object* v_remaining_x27_6265_, lean_object* v_onAlt_6266_, lean_object* v_a_6267_, lean_object* v___x_6268_, lean_object* v_extraEqualities_6269_, lean_object* v_xs_6270_, lean_object* v_altType_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_, lean_object* v___y_6274_, lean_object* v___y_6275_, lean_object* v___y_6276_){
_start:
{
uint8_t v___x_35323__boxed_6277_; uint8_t v___x_35324__boxed_6278_; lean_object* v_res_6279_; 
v___x_35323__boxed_6277_ = lean_unbox(v___x_6264_);
v___x_35324__boxed_6278_ = lean_unbox(v___x_6268_);
v_res_6279_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(v___x_6262_, v___f_6263_, v___x_35323__boxed_6277_, v_remaining_x27_6265_, v_onAlt_6266_, v_a_6267_, v___x_35324__boxed_6278_, v_extraEqualities_6269_, v_xs_6270_, v_altType_6271_, v___y_6272_, v___y_6273_, v___y_6274_, v___y_6275_);
return v_res_6279_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(lean_object* v_upperBound_6281_, lean_object* v_onAlt_6282_, lean_object* v_extraEqualities_6283_, lean_object* v_a_6284_, lean_object* v_b_6285_, lean_object* v___y_6286_, lean_object* v___y_6287_, lean_object* v___y_6288_, lean_object* v___y_6289_){
_start:
{
lean_object* v___y_6292_; uint8_t v___x_6315_; 
v___x_6315_ = lean_nat_dec_lt(v_a_6284_, v_upperBound_6281_);
if (v___x_6315_ == 0)
{
lean_object* v___x_6316_; 
lean_dec(v___y_6289_);
lean_dec_ref(v___y_6288_);
lean_dec(v___y_6287_);
lean_dec_ref(v___y_6286_);
lean_dec(v_a_6284_);
lean_dec(v_extraEqualities_6283_);
lean_dec_ref(v_onAlt_6282_);
v___x_6316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6316_, 0, v_b_6285_);
return v___x_6316_;
}
else
{
lean_object* v_snd_6317_; lean_object* v_snd_6318_; lean_object* v_snd_6319_; lean_object* v_fst_6320_; lean_object* v___x_6322_; uint8_t v_isShared_6323_; uint8_t v_isSharedCheck_6427_; 
v_snd_6317_ = lean_ctor_get(v_b_6285_, 1);
lean_inc(v_snd_6317_);
v_snd_6318_ = lean_ctor_get(v_snd_6317_, 1);
lean_inc(v_snd_6318_);
v_snd_6319_ = lean_ctor_get(v_snd_6318_, 1);
lean_inc(v_snd_6319_);
v_fst_6320_ = lean_ctor_get(v_b_6285_, 0);
v_isSharedCheck_6427_ = !lean_is_exclusive(v_b_6285_);
if (v_isSharedCheck_6427_ == 0)
{
lean_object* v_unused_6428_; 
v_unused_6428_ = lean_ctor_get(v_b_6285_, 1);
lean_dec(v_unused_6428_);
v___x_6322_ = v_b_6285_;
v_isShared_6323_ = v_isSharedCheck_6427_;
goto v_resetjp_6321_;
}
else
{
lean_inc(v_fst_6320_);
lean_dec(v_b_6285_);
v___x_6322_ = lean_box(0);
v_isShared_6323_ = v_isSharedCheck_6427_;
goto v_resetjp_6321_;
}
v_resetjp_6321_:
{
lean_object* v_fst_6324_; lean_object* v___x_6326_; uint8_t v_isShared_6327_; uint8_t v_isSharedCheck_6425_; 
v_fst_6324_ = lean_ctor_get(v_snd_6317_, 0);
v_isSharedCheck_6425_ = !lean_is_exclusive(v_snd_6317_);
if (v_isSharedCheck_6425_ == 0)
{
lean_object* v_unused_6426_; 
v_unused_6426_ = lean_ctor_get(v_snd_6317_, 1);
lean_dec(v_unused_6426_);
v___x_6326_ = v_snd_6317_;
v_isShared_6327_ = v_isSharedCheck_6425_;
goto v_resetjp_6325_;
}
else
{
lean_inc(v_fst_6324_);
lean_dec(v_snd_6317_);
v___x_6326_ = lean_box(0);
v_isShared_6327_ = v_isSharedCheck_6425_;
goto v_resetjp_6325_;
}
v_resetjp_6325_:
{
lean_object* v_fst_6328_; lean_object* v___x_6330_; uint8_t v_isShared_6331_; uint8_t v_isSharedCheck_6423_; 
v_fst_6328_ = lean_ctor_get(v_snd_6318_, 0);
v_isSharedCheck_6423_ = !lean_is_exclusive(v_snd_6318_);
if (v_isSharedCheck_6423_ == 0)
{
lean_object* v_unused_6424_; 
v_unused_6424_ = lean_ctor_get(v_snd_6318_, 1);
lean_dec(v_unused_6424_);
v___x_6330_ = v_snd_6318_;
v_isShared_6331_ = v_isSharedCheck_6423_;
goto v_resetjp_6329_;
}
else
{
lean_inc(v_fst_6328_);
lean_dec(v_snd_6318_);
v___x_6330_ = lean_box(0);
v_isShared_6331_ = v_isSharedCheck_6423_;
goto v_resetjp_6329_;
}
v_resetjp_6329_:
{
lean_object* v_array_6332_; lean_object* v_start_6333_; lean_object* v_stop_6334_; uint8_t v___x_6335_; 
v_array_6332_ = lean_ctor_get(v_snd_6319_, 0);
v_start_6333_ = lean_ctor_get(v_snd_6319_, 1);
v_stop_6334_ = lean_ctor_get(v_snd_6319_, 2);
v___x_6335_ = lean_nat_dec_lt(v_start_6333_, v_stop_6334_);
if (v___x_6335_ == 0)
{
lean_object* v___x_6337_; 
if (v_isShared_6331_ == 0)
{
v___x_6337_ = v___x_6330_;
goto v_reusejp_6336_;
}
else
{
lean_object* v_reuseFailAlloc_6346_; 
v_reuseFailAlloc_6346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6346_, 0, v_fst_6328_);
lean_ctor_set(v_reuseFailAlloc_6346_, 1, v_snd_6319_);
v___x_6337_ = v_reuseFailAlloc_6346_;
goto v_reusejp_6336_;
}
v_reusejp_6336_:
{
lean_object* v___x_6339_; 
if (v_isShared_6327_ == 0)
{
lean_ctor_set(v___x_6326_, 1, v___x_6337_);
v___x_6339_ = v___x_6326_;
goto v_reusejp_6338_;
}
else
{
lean_object* v_reuseFailAlloc_6345_; 
v_reuseFailAlloc_6345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6345_, 0, v_fst_6324_);
lean_ctor_set(v_reuseFailAlloc_6345_, 1, v___x_6337_);
v___x_6339_ = v_reuseFailAlloc_6345_;
goto v_reusejp_6338_;
}
v_reusejp_6338_:
{
lean_object* v___x_6341_; 
if (v_isShared_6323_ == 0)
{
lean_ctor_set(v___x_6322_, 1, v___x_6339_);
v___x_6341_ = v___x_6322_;
goto v_reusejp_6340_;
}
else
{
lean_object* v_reuseFailAlloc_6344_; 
v_reuseFailAlloc_6344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6344_, 0, v_fst_6320_);
lean_ctor_set(v_reuseFailAlloc_6344_, 1, v___x_6339_);
v___x_6341_ = v_reuseFailAlloc_6344_;
goto v_reusejp_6340_;
}
v_reusejp_6340_:
{
lean_object* v___x_6342_; lean_object* v___f_6343_; 
v___x_6342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6342_, 0, v___x_6341_);
v___f_6343_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6343_, 0, v___x_6342_);
v___y_6292_ = v___f_6343_;
goto v___jp_6291_;
}
}
}
}
else
{
lean_object* v___x_6348_; uint8_t v_isShared_6349_; uint8_t v_isSharedCheck_6419_; 
lean_inc(v_stop_6334_);
lean_inc(v_start_6333_);
lean_inc_ref(v_array_6332_);
v_isSharedCheck_6419_ = !lean_is_exclusive(v_snd_6319_);
if (v_isSharedCheck_6419_ == 0)
{
lean_object* v_unused_6420_; lean_object* v_unused_6421_; lean_object* v_unused_6422_; 
v_unused_6420_ = lean_ctor_get(v_snd_6319_, 2);
lean_dec(v_unused_6420_);
v_unused_6421_ = lean_ctor_get(v_snd_6319_, 1);
lean_dec(v_unused_6421_);
v_unused_6422_ = lean_ctor_get(v_snd_6319_, 0);
lean_dec(v_unused_6422_);
v___x_6348_ = v_snd_6319_;
v_isShared_6349_ = v_isSharedCheck_6419_;
goto v_resetjp_6347_;
}
else
{
lean_dec(v_snd_6319_);
v___x_6348_ = lean_box(0);
v_isShared_6349_ = v_isSharedCheck_6419_;
goto v_resetjp_6347_;
}
v_resetjp_6347_:
{
lean_object* v_array_6350_; lean_object* v_start_6351_; lean_object* v_stop_6352_; lean_object* v___x_6353_; lean_object* v___x_6354_; lean_object* v___x_6355_; lean_object* v___x_6357_; 
v_array_6350_ = lean_ctor_get(v_fst_6328_, 0);
v_start_6351_ = lean_ctor_get(v_fst_6328_, 1);
v_stop_6352_ = lean_ctor_get(v_fst_6328_, 2);
v___x_6353_ = lean_array_fget(v_array_6332_, v_start_6333_);
v___x_6354_ = lean_unsigned_to_nat(1u);
v___x_6355_ = lean_nat_add(v_start_6333_, v___x_6354_);
lean_dec(v_start_6333_);
if (v_isShared_6349_ == 0)
{
lean_ctor_set(v___x_6348_, 1, v___x_6355_);
v___x_6357_ = v___x_6348_;
goto v_reusejp_6356_;
}
else
{
lean_object* v_reuseFailAlloc_6418_; 
v_reuseFailAlloc_6418_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6418_, 0, v_array_6332_);
lean_ctor_set(v_reuseFailAlloc_6418_, 1, v___x_6355_);
lean_ctor_set(v_reuseFailAlloc_6418_, 2, v_stop_6334_);
v___x_6357_ = v_reuseFailAlloc_6418_;
goto v_reusejp_6356_;
}
v_reusejp_6356_:
{
uint8_t v___x_6358_; 
v___x_6358_ = lean_nat_dec_lt(v_start_6351_, v_stop_6352_);
if (v___x_6358_ == 0)
{
lean_object* v___x_6360_; 
lean_dec(v___x_6353_);
if (v_isShared_6331_ == 0)
{
lean_ctor_set(v___x_6330_, 1, v___x_6357_);
v___x_6360_ = v___x_6330_;
goto v_reusejp_6359_;
}
else
{
lean_object* v_reuseFailAlloc_6369_; 
v_reuseFailAlloc_6369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6369_, 0, v_fst_6328_);
lean_ctor_set(v_reuseFailAlloc_6369_, 1, v___x_6357_);
v___x_6360_ = v_reuseFailAlloc_6369_;
goto v_reusejp_6359_;
}
v_reusejp_6359_:
{
lean_object* v___x_6362_; 
if (v_isShared_6327_ == 0)
{
lean_ctor_set(v___x_6326_, 1, v___x_6360_);
v___x_6362_ = v___x_6326_;
goto v_reusejp_6361_;
}
else
{
lean_object* v_reuseFailAlloc_6368_; 
v_reuseFailAlloc_6368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6368_, 0, v_fst_6324_);
lean_ctor_set(v_reuseFailAlloc_6368_, 1, v___x_6360_);
v___x_6362_ = v_reuseFailAlloc_6368_;
goto v_reusejp_6361_;
}
v_reusejp_6361_:
{
lean_object* v___x_6364_; 
if (v_isShared_6323_ == 0)
{
lean_ctor_set(v___x_6322_, 1, v___x_6362_);
v___x_6364_ = v___x_6322_;
goto v_reusejp_6363_;
}
else
{
lean_object* v_reuseFailAlloc_6367_; 
v_reuseFailAlloc_6367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6367_, 0, v_fst_6320_);
lean_ctor_set(v_reuseFailAlloc_6367_, 1, v___x_6362_);
v___x_6364_ = v_reuseFailAlloc_6367_;
goto v_reusejp_6363_;
}
v_reusejp_6363_:
{
lean_object* v___x_6365_; lean_object* v___f_6366_; 
v___x_6365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6365_, 0, v___x_6364_);
v___f_6366_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6366_, 0, v___x_6365_);
v___y_6292_ = v___f_6366_;
goto v___jp_6291_;
}
}
}
}
else
{
lean_object* v___x_6371_; uint8_t v_isShared_6372_; uint8_t v_isSharedCheck_6414_; 
lean_inc(v_stop_6352_);
lean_inc(v_start_6351_);
lean_inc_ref(v_array_6350_);
v_isSharedCheck_6414_ = !lean_is_exclusive(v_fst_6328_);
if (v_isSharedCheck_6414_ == 0)
{
lean_object* v_unused_6415_; lean_object* v_unused_6416_; lean_object* v_unused_6417_; 
v_unused_6415_ = lean_ctor_get(v_fst_6328_, 2);
lean_dec(v_unused_6415_);
v_unused_6416_ = lean_ctor_get(v_fst_6328_, 1);
lean_dec(v_unused_6416_);
v_unused_6417_ = lean_ctor_get(v_fst_6328_, 0);
lean_dec(v_unused_6417_);
v___x_6371_ = v_fst_6328_;
v_isShared_6372_ = v_isSharedCheck_6414_;
goto v_resetjp_6370_;
}
else
{
lean_dec(v_fst_6328_);
v___x_6371_ = lean_box(0);
v_isShared_6372_ = v_isSharedCheck_6414_;
goto v_resetjp_6370_;
}
v_resetjp_6370_:
{
lean_object* v_array_6373_; lean_object* v_start_6374_; lean_object* v_stop_6375_; lean_object* v___x_6376_; lean_object* v___x_6377_; lean_object* v___x_6379_; 
v_array_6373_ = lean_ctor_get(v_fst_6324_, 0);
v_start_6374_ = lean_ctor_get(v_fst_6324_, 1);
v_stop_6375_ = lean_ctor_get(v_fst_6324_, 2);
v___x_6376_ = lean_array_fget(v_array_6350_, v_start_6351_);
v___x_6377_ = lean_nat_add(v_start_6351_, v___x_6354_);
lean_dec(v_start_6351_);
if (v_isShared_6372_ == 0)
{
lean_ctor_set(v___x_6371_, 1, v___x_6377_);
v___x_6379_ = v___x_6371_;
goto v_reusejp_6378_;
}
else
{
lean_object* v_reuseFailAlloc_6413_; 
v_reuseFailAlloc_6413_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6413_, 0, v_array_6350_);
lean_ctor_set(v_reuseFailAlloc_6413_, 1, v___x_6377_);
lean_ctor_set(v_reuseFailAlloc_6413_, 2, v_stop_6352_);
v___x_6379_ = v_reuseFailAlloc_6413_;
goto v_reusejp_6378_;
}
v_reusejp_6378_:
{
uint8_t v___x_6380_; 
v___x_6380_ = lean_nat_dec_lt(v_start_6374_, v_stop_6375_);
if (v___x_6380_ == 0)
{
lean_object* v___x_6382_; 
lean_dec(v___x_6376_);
lean_dec(v___x_6353_);
if (v_isShared_6331_ == 0)
{
lean_ctor_set(v___x_6330_, 1, v___x_6357_);
lean_ctor_set(v___x_6330_, 0, v___x_6379_);
v___x_6382_ = v___x_6330_;
goto v_reusejp_6381_;
}
else
{
lean_object* v_reuseFailAlloc_6391_; 
v_reuseFailAlloc_6391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6391_, 0, v___x_6379_);
lean_ctor_set(v_reuseFailAlloc_6391_, 1, v___x_6357_);
v___x_6382_ = v_reuseFailAlloc_6391_;
goto v_reusejp_6381_;
}
v_reusejp_6381_:
{
lean_object* v___x_6384_; 
if (v_isShared_6327_ == 0)
{
lean_ctor_set(v___x_6326_, 1, v___x_6382_);
v___x_6384_ = v___x_6326_;
goto v_reusejp_6383_;
}
else
{
lean_object* v_reuseFailAlloc_6390_; 
v_reuseFailAlloc_6390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6390_, 0, v_fst_6324_);
lean_ctor_set(v_reuseFailAlloc_6390_, 1, v___x_6382_);
v___x_6384_ = v_reuseFailAlloc_6390_;
goto v_reusejp_6383_;
}
v_reusejp_6383_:
{
lean_object* v___x_6386_; 
if (v_isShared_6323_ == 0)
{
lean_ctor_set(v___x_6322_, 1, v___x_6384_);
v___x_6386_ = v___x_6322_;
goto v_reusejp_6385_;
}
else
{
lean_object* v_reuseFailAlloc_6389_; 
v_reuseFailAlloc_6389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6389_, 0, v_fst_6320_);
lean_ctor_set(v_reuseFailAlloc_6389_, 1, v___x_6384_);
v___x_6386_ = v_reuseFailAlloc_6389_;
goto v_reusejp_6385_;
}
v_reusejp_6385_:
{
lean_object* v___x_6387_; lean_object* v___f_6388_; 
v___x_6387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6387_, 0, v___x_6386_);
v___f_6388_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6388_, 0, v___x_6387_);
v___y_6292_ = v___f_6388_;
goto v___jp_6291_;
}
}
}
}
else
{
lean_object* v___x_6393_; uint8_t v_isShared_6394_; uint8_t v_isSharedCheck_6409_; 
lean_inc(v_stop_6375_);
lean_inc(v_start_6374_);
lean_inc_ref(v_array_6373_);
lean_del_object(v___x_6330_);
lean_del_object(v___x_6326_);
lean_del_object(v___x_6322_);
v_isSharedCheck_6409_ = !lean_is_exclusive(v_fst_6324_);
if (v_isSharedCheck_6409_ == 0)
{
lean_object* v_unused_6410_; lean_object* v_unused_6411_; lean_object* v_unused_6412_; 
v_unused_6410_ = lean_ctor_get(v_fst_6324_, 2);
lean_dec(v_unused_6410_);
v_unused_6411_ = lean_ctor_get(v_fst_6324_, 1);
lean_dec(v_unused_6411_);
v_unused_6412_ = lean_ctor_get(v_fst_6324_, 0);
lean_dec(v_unused_6412_);
v___x_6393_ = v_fst_6324_;
v_isShared_6394_ = v_isSharedCheck_6409_;
goto v_resetjp_6392_;
}
else
{
lean_dec(v_fst_6324_);
v___x_6393_ = lean_box(0);
v_isShared_6394_ = v_isSharedCheck_6409_;
goto v_resetjp_6392_;
}
v_resetjp_6392_:
{
lean_object* v___f_6395_; uint8_t v___x_6396_; lean_object* v_remaining_x27_6397_; lean_object* v___x_6398_; lean_object* v___x_6399_; lean_object* v___x_6400_; lean_object* v___f_6401_; lean_object* v___x_6402_; lean_object* v___x_6404_; 
v___f_6395_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___closed__0));
v___x_6396_ = 0;
v_remaining_x27_6397_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_6398_ = lean_array_fget_borrowed(v_array_6373_, v_start_6374_);
v___x_6399_ = lean_box(v___x_6396_);
v___x_6400_ = lean_box(v___x_6380_);
lean_inc(v_extraEqualities_6283_);
lean_inc(v_a_6284_);
lean_inc_ref(v_onAlt_6282_);
lean_inc(v___x_6398_);
v___f_6401_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed), 15, 8);
lean_closure_set(v___f_6401_, 0, v___x_6398_);
lean_closure_set(v___f_6401_, 1, v___f_6395_);
lean_closure_set(v___f_6401_, 2, v___x_6399_);
lean_closure_set(v___f_6401_, 3, v_remaining_x27_6397_);
lean_closure_set(v___f_6401_, 4, v_onAlt_6282_);
lean_closure_set(v___f_6401_, 5, v_a_6284_);
lean_closure_set(v___f_6401_, 6, v___x_6400_);
lean_closure_set(v___f_6401_, 7, v_extraEqualities_6283_);
v___x_6402_ = lean_nat_add(v_start_6374_, v___x_6354_);
lean_dec(v_start_6374_);
if (v_isShared_6394_ == 0)
{
lean_ctor_set(v___x_6393_, 1, v___x_6402_);
v___x_6404_ = v___x_6393_;
goto v_reusejp_6403_;
}
else
{
lean_object* v_reuseFailAlloc_6408_; 
v_reuseFailAlloc_6408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6408_, 0, v_array_6373_);
lean_ctor_set(v_reuseFailAlloc_6408_, 1, v___x_6402_);
lean_ctor_set(v_reuseFailAlloc_6408_, 2, v_stop_6375_);
v___x_6404_ = v_reuseFailAlloc_6408_;
goto v_reusejp_6403_;
}
v_reusejp_6403_:
{
lean_object* v___x_6405_; lean_object* v___x_6406_; lean_object* v___f_6407_; 
v___x_6405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6405_, 0, v___x_6376_);
v___x_6406_ = lean_box(v___x_6396_);
v___f_6407_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed), 13, 8);
lean_closure_set(v___f_6407_, 0, v___x_6353_);
lean_closure_set(v___f_6407_, 1, v___x_6405_);
lean_closure_set(v___f_6407_, 2, v___f_6401_);
lean_closure_set(v___f_6407_, 3, v___x_6406_);
lean_closure_set(v___f_6407_, 4, v_fst_6320_);
lean_closure_set(v___f_6407_, 5, v___x_6379_);
lean_closure_set(v___f_6407_, 6, v___x_6357_);
lean_closure_set(v___f_6407_, 7, v___x_6404_);
v___y_6292_ = v___f_6407_;
goto v___jp_6291_;
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_6291_:
{
lean_object* v___x_6293_; 
lean_inc(v___y_6289_);
lean_inc_ref(v___y_6288_);
lean_inc(v___y_6287_);
lean_inc_ref(v___y_6286_);
v___x_6293_ = lean_apply_5(v___y_6292_, v___y_6286_, v___y_6287_, v___y_6288_, v___y_6289_, lean_box(0));
if (lean_obj_tag(v___x_6293_) == 0)
{
lean_object* v_a_6294_; lean_object* v___x_6296_; uint8_t v_isShared_6297_; uint8_t v_isSharedCheck_6306_; 
v_a_6294_ = lean_ctor_get(v___x_6293_, 0);
v_isSharedCheck_6306_ = !lean_is_exclusive(v___x_6293_);
if (v_isSharedCheck_6306_ == 0)
{
v___x_6296_ = v___x_6293_;
v_isShared_6297_ = v_isSharedCheck_6306_;
goto v_resetjp_6295_;
}
else
{
lean_inc(v_a_6294_);
lean_dec(v___x_6293_);
v___x_6296_ = lean_box(0);
v_isShared_6297_ = v_isSharedCheck_6306_;
goto v_resetjp_6295_;
}
v_resetjp_6295_:
{
if (lean_obj_tag(v_a_6294_) == 0)
{
lean_object* v_a_6298_; lean_object* v___x_6300_; 
lean_dec(v___y_6289_);
lean_dec_ref(v___y_6288_);
lean_dec(v___y_6287_);
lean_dec_ref(v___y_6286_);
lean_dec(v_a_6284_);
lean_dec(v_extraEqualities_6283_);
lean_dec_ref(v_onAlt_6282_);
v_a_6298_ = lean_ctor_get(v_a_6294_, 0);
lean_inc(v_a_6298_);
lean_dec_ref(v_a_6294_);
if (v_isShared_6297_ == 0)
{
lean_ctor_set(v___x_6296_, 0, v_a_6298_);
v___x_6300_ = v___x_6296_;
goto v_reusejp_6299_;
}
else
{
lean_object* v_reuseFailAlloc_6301_; 
v_reuseFailAlloc_6301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6301_, 0, v_a_6298_);
v___x_6300_ = v_reuseFailAlloc_6301_;
goto v_reusejp_6299_;
}
v_reusejp_6299_:
{
return v___x_6300_;
}
}
else
{
lean_object* v_a_6302_; lean_object* v___x_6303_; lean_object* v___x_6304_; 
lean_del_object(v___x_6296_);
v_a_6302_ = lean_ctor_get(v_a_6294_, 0);
lean_inc(v_a_6302_);
lean_dec_ref(v_a_6294_);
v___x_6303_ = lean_unsigned_to_nat(1u);
v___x_6304_ = lean_nat_add(v_a_6284_, v___x_6303_);
lean_dec(v_a_6284_);
v_a_6284_ = v___x_6304_;
v_b_6285_ = v_a_6302_;
goto _start;
}
}
}
else
{
lean_object* v_a_6307_; lean_object* v___x_6309_; uint8_t v_isShared_6310_; uint8_t v_isSharedCheck_6314_; 
lean_dec(v___y_6289_);
lean_dec_ref(v___y_6288_);
lean_dec(v___y_6287_);
lean_dec_ref(v___y_6286_);
lean_dec(v_a_6284_);
lean_dec(v_extraEqualities_6283_);
lean_dec_ref(v_onAlt_6282_);
v_a_6307_ = lean_ctor_get(v___x_6293_, 0);
v_isSharedCheck_6314_ = !lean_is_exclusive(v___x_6293_);
if (v_isSharedCheck_6314_ == 0)
{
v___x_6309_ = v___x_6293_;
v_isShared_6310_ = v_isSharedCheck_6314_;
goto v_resetjp_6308_;
}
else
{
lean_inc(v_a_6307_);
lean_dec(v___x_6293_);
v___x_6309_ = lean_box(0);
v_isShared_6310_ = v_isSharedCheck_6314_;
goto v_resetjp_6308_;
}
v_resetjp_6308_:
{
lean_object* v___x_6312_; 
if (v_isShared_6310_ == 0)
{
v___x_6312_ = v___x_6309_;
goto v_reusejp_6311_;
}
else
{
lean_object* v_reuseFailAlloc_6313_; 
v_reuseFailAlloc_6313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6313_, 0, v_a_6307_);
v___x_6312_ = v_reuseFailAlloc_6313_;
goto v_reusejp_6311_;
}
v_reusejp_6311_:
{
return v___x_6312_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___boxed(lean_object* v_upperBound_6429_, lean_object* v_onAlt_6430_, lean_object* v_extraEqualities_6431_, lean_object* v_a_6432_, lean_object* v_b_6433_, lean_object* v___y_6434_, lean_object* v___y_6435_, lean_object* v___y_6436_, lean_object* v___y_6437_, lean_object* v___y_6438_){
_start:
{
lean_object* v_res_6439_; 
v_res_6439_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v_upperBound_6429_, v_onAlt_6430_, v_extraEqualities_6431_, v_a_6432_, v_b_6433_, v___y_6434_, v___y_6435_, v___y_6436_, v___y_6437_);
lean_dec(v_upperBound_6429_);
return v_res_6439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(lean_object* v_onParams_6440_, size_t v_sz_6441_, size_t v_i_6442_, lean_object* v_bs_6443_, lean_object* v___y_6444_, lean_object* v___y_6445_, lean_object* v___y_6446_, lean_object* v___y_6447_){
_start:
{
uint8_t v___x_6449_; 
v___x_6449_ = lean_usize_dec_lt(v_i_6442_, v_sz_6441_);
if (v___x_6449_ == 0)
{
lean_object* v___x_6450_; 
lean_dec(v___y_6447_);
lean_dec_ref(v___y_6446_);
lean_dec(v___y_6445_);
lean_dec_ref(v___y_6444_);
lean_dec_ref(v_onParams_6440_);
v___x_6450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6450_, 0, v_bs_6443_);
return v___x_6450_;
}
else
{
lean_object* v_v_6451_; lean_object* v___x_6452_; 
v_v_6451_ = lean_array_uget_borrowed(v_bs_6443_, v_i_6442_);
lean_inc_ref(v_onParams_6440_);
lean_inc(v___y_6447_);
lean_inc_ref(v___y_6446_);
lean_inc(v___y_6445_);
lean_inc_ref(v___y_6444_);
lean_inc(v_v_6451_);
v___x_6452_ = lean_apply_6(v_onParams_6440_, v_v_6451_, v___y_6444_, v___y_6445_, v___y_6446_, v___y_6447_, lean_box(0));
if (lean_obj_tag(v___x_6452_) == 0)
{
lean_object* v_a_6453_; lean_object* v___x_6454_; lean_object* v_bs_x27_6455_; size_t v___x_6456_; size_t v___x_6457_; lean_object* v___x_6458_; 
v_a_6453_ = lean_ctor_get(v___x_6452_, 0);
lean_inc(v_a_6453_);
lean_dec_ref(v___x_6452_);
v___x_6454_ = lean_unsigned_to_nat(0u);
v_bs_x27_6455_ = lean_array_uset(v_bs_6443_, v_i_6442_, v___x_6454_);
v___x_6456_ = ((size_t)1ULL);
v___x_6457_ = lean_usize_add(v_i_6442_, v___x_6456_);
v___x_6458_ = lean_array_uset(v_bs_x27_6455_, v_i_6442_, v_a_6453_);
v_i_6442_ = v___x_6457_;
v_bs_6443_ = v___x_6458_;
goto _start;
}
else
{
lean_object* v_a_6460_; lean_object* v___x_6462_; uint8_t v_isShared_6463_; uint8_t v_isSharedCheck_6467_; 
lean_dec(v___y_6447_);
lean_dec_ref(v___y_6446_);
lean_dec(v___y_6445_);
lean_dec_ref(v___y_6444_);
lean_dec_ref(v_bs_6443_);
lean_dec_ref(v_onParams_6440_);
v_a_6460_ = lean_ctor_get(v___x_6452_, 0);
v_isSharedCheck_6467_ = !lean_is_exclusive(v___x_6452_);
if (v_isSharedCheck_6467_ == 0)
{
v___x_6462_ = v___x_6452_;
v_isShared_6463_ = v_isSharedCheck_6467_;
goto v_resetjp_6461_;
}
else
{
lean_inc(v_a_6460_);
lean_dec(v___x_6452_);
v___x_6462_ = lean_box(0);
v_isShared_6463_ = v_isSharedCheck_6467_;
goto v_resetjp_6461_;
}
v_resetjp_6461_:
{
lean_object* v___x_6465_; 
if (v_isShared_6463_ == 0)
{
v___x_6465_ = v___x_6462_;
goto v_reusejp_6464_;
}
else
{
lean_object* v_reuseFailAlloc_6466_; 
v_reuseFailAlloc_6466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6466_, 0, v_a_6460_);
v___x_6465_ = v_reuseFailAlloc_6466_;
goto v_reusejp_6464_;
}
v_reusejp_6464_:
{
return v___x_6465_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6___boxed(lean_object* v_onParams_6468_, lean_object* v_sz_6469_, lean_object* v_i_6470_, lean_object* v_bs_6471_, lean_object* v___y_6472_, lean_object* v___y_6473_, lean_object* v___y_6474_, lean_object* v___y_6475_, lean_object* v___y_6476_){
_start:
{
size_t v_sz_boxed_6477_; size_t v_i_boxed_6478_; lean_object* v_res_6479_; 
v_sz_boxed_6477_ = lean_unbox_usize(v_sz_6469_);
lean_dec(v_sz_6469_);
v_i_boxed_6478_ = lean_unbox_usize(v_i_6470_);
lean_dec(v_i_6470_);
v_res_6479_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6468_, v_sz_boxed_6477_, v_i_boxed_6478_, v_bs_6471_, v___y_6472_, v___y_6473_, v___y_6474_, v___y_6475_);
return v_res_6479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(lean_object* v_declName_6480_, lean_object* v___y_6481_){
_start:
{
lean_object* v___x_6483_; lean_object* v_env_6484_; lean_object* v___x_6485_; lean_object* v___x_6486_; 
v___x_6483_ = lean_st_ref_get(v___y_6481_);
v_env_6484_ = lean_ctor_get(v___x_6483_, 0);
lean_inc_ref(v_env_6484_);
lean_dec(v___x_6483_);
v___x_6485_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_6484_, v_declName_6480_);
v___x_6486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6486_, 0, v___x_6485_);
return v___x_6486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg___boxed(lean_object* v_declName_6487_, lean_object* v___y_6488_, lean_object* v___y_6489_){
_start:
{
lean_object* v_res_6490_; 
v_res_6490_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_declName_6487_, v___y_6488_);
lean_dec(v___y_6488_);
return v_res_6490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(lean_object* v_matcherApp_6493_, uint8_t v_useSplitter_6494_, uint8_t v_addEqualities_6495_, lean_object* v_onParams_6496_, lean_object* v_onMotive_6497_, lean_object* v_onAlt_6498_, lean_object* v_onRemaining_6499_, lean_object* v___y_6500_, lean_object* v___y_6501_, lean_object* v___y_6502_, lean_object* v___y_6503_){
_start:
{
lean_object* v___x_6505_; lean_object* v_env_6506_; lean_object* v_toMatcherInfo_6507_; lean_object* v_matcherName_6508_; lean_object* v_matcherLevels_6509_; lean_object* v_params_6510_; lean_object* v_motive_6511_; lean_object* v_discrs_6512_; lean_object* v_alts_6513_; lean_object* v_remaining_6514_; lean_object* v___y_6516_; lean_object* v___y_6517_; lean_object* v___y_6518_; lean_object* v___y_6519_; lean_object* v___y_6520_; lean_object* v___y_6521_; lean_object* v___y_6522_; lean_object* v___y_6523_; lean_object* v___y_6524_; lean_object* v___y_6525_; lean_object* v___y_6526_; lean_object* v___y_6527_; lean_object* v___y_6528_; uint8_t v_isCasesOn_6611_; lean_object* v___y_6613_; lean_object* v___y_6614_; lean_object* v___y_6615_; lean_object* v___y_6616_; lean_object* v___y_6617_; lean_object* v___y_6618_; size_t v___y_6619_; lean_object* v_matcherLevels_6620_; lean_object* v___y_6621_; lean_object* v___y_6622_; lean_object* v___y_6623_; lean_object* v___y_6624_; lean_object* v_numDiscrEqs_6815_; lean_object* v___y_6816_; lean_object* v___y_6817_; lean_object* v___y_6818_; lean_object* v___y_6819_; 
v___x_6505_ = lean_st_ref_get(v___y_6503_);
v_env_6506_ = lean_ctor_get(v___x_6505_, 0);
lean_inc_ref(v_env_6506_);
lean_dec(v___x_6505_);
v_toMatcherInfo_6507_ = lean_ctor_get(v_matcherApp_6493_, 0);
lean_inc_ref(v_toMatcherInfo_6507_);
v_matcherName_6508_ = lean_ctor_get(v_matcherApp_6493_, 1);
lean_inc(v_matcherName_6508_);
v_matcherLevels_6509_ = lean_ctor_get(v_matcherApp_6493_, 2);
v_params_6510_ = lean_ctor_get(v_matcherApp_6493_, 3);
v_motive_6511_ = lean_ctor_get(v_matcherApp_6493_, 4);
v_discrs_6512_ = lean_ctor_get(v_matcherApp_6493_, 5);
v_alts_6513_ = lean_ctor_get(v_matcherApp_6493_, 6);
lean_inc_ref(v_alts_6513_);
v_remaining_6514_ = lean_ctor_get(v_matcherApp_6493_, 7);
lean_inc_ref(v_remaining_6514_);
lean_inc(v_matcherName_6508_);
v_isCasesOn_6611_ = l_Lean_isCasesOnRecursor(v_env_6506_, v_matcherName_6508_);
if (v_isCasesOn_6611_ == 0)
{
lean_object* v___x_6869_; lean_object* v_a_6870_; 
lean_inc(v_matcherName_6508_);
v___x_6869_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_matcherName_6508_, v___y_6503_);
v_a_6870_ = lean_ctor_get(v___x_6869_, 0);
lean_inc(v_a_6870_);
lean_dec_ref(v___x_6869_);
if (lean_obj_tag(v_a_6870_) == 0)
{
lean_object* v___x_6871_; lean_object* v___x_6872_; lean_object* v___x_6873_; lean_object* v___x_6874_; lean_object* v___x_6875_; lean_object* v___x_6876_; lean_object* v_a_6877_; lean_object* v___x_6879_; uint8_t v_isShared_6880_; uint8_t v_isSharedCheck_6884_; 
lean_dec_ref(v_remaining_6514_);
lean_dec_ref(v_alts_6513_);
lean_dec_ref(v_toMatcherInfo_6507_);
lean_dec_ref(v_onRemaining_6499_);
lean_dec_ref(v_onAlt_6498_);
lean_dec_ref(v_onMotive_6497_);
lean_dec_ref(v_onParams_6496_);
lean_dec_ref(v_matcherApp_6493_);
v___x_6871_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1);
v___x_6872_ = l_Lean_MessageData_ofName(v_matcherName_6508_);
v___x_6873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6873_, 0, v___x_6871_);
lean_ctor_set(v___x_6873_, 1, v___x_6872_);
v___x_6874_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3);
v___x_6875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6875_, 0, v___x_6873_);
lean_ctor_set(v___x_6875_, 1, v___x_6874_);
v___x_6876_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_6875_, v___y_6500_, v___y_6501_, v___y_6502_, v___y_6503_);
lean_dec(v___y_6503_);
lean_dec_ref(v___y_6502_);
lean_dec(v___y_6501_);
lean_dec_ref(v___y_6500_);
v_a_6877_ = lean_ctor_get(v___x_6876_, 0);
v_isSharedCheck_6884_ = !lean_is_exclusive(v___x_6876_);
if (v_isSharedCheck_6884_ == 0)
{
v___x_6879_ = v___x_6876_;
v_isShared_6880_ = v_isSharedCheck_6884_;
goto v_resetjp_6878_;
}
else
{
lean_inc(v_a_6877_);
lean_dec(v___x_6876_);
v___x_6879_ = lean_box(0);
v_isShared_6880_ = v_isSharedCheck_6884_;
goto v_resetjp_6878_;
}
v_resetjp_6878_:
{
lean_object* v___x_6882_; 
if (v_isShared_6880_ == 0)
{
v___x_6882_ = v___x_6879_;
goto v_reusejp_6881_;
}
else
{
lean_object* v_reuseFailAlloc_6883_; 
v_reuseFailAlloc_6883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6883_, 0, v_a_6877_);
v___x_6882_ = v_reuseFailAlloc_6883_;
goto v_reusejp_6881_;
}
v_reusejp_6881_:
{
return v___x_6882_;
}
}
}
else
{
lean_object* v_val_6885_; lean_object* v___x_6886_; 
v_val_6885_ = lean_ctor_get(v_a_6870_, 0);
lean_inc(v_val_6885_);
lean_dec_ref(v_a_6870_);
v___x_6886_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_6885_);
lean_dec(v_val_6885_);
v_numDiscrEqs_6815_ = v___x_6886_;
v___y_6816_ = v___y_6500_;
v___y_6817_ = v___y_6501_;
v___y_6818_ = v___y_6502_;
v___y_6819_ = v___y_6503_;
goto v___jp_6814_;
}
}
else
{
lean_object* v___x_6887_; 
v___x_6887_ = lean_unsigned_to_nat(0u);
v_numDiscrEqs_6815_ = v___x_6887_;
v___y_6816_ = v___y_6500_;
v___y_6817_ = v___y_6501_;
v___y_6818_ = v___y_6502_;
v___y_6819_ = v___y_6503_;
goto v___jp_6814_;
}
v___jp_6515_:
{
lean_object* v___x_6529_; lean_object* v___x_6530_; lean_object* v_aux_6531_; lean_object* v_aux_6532_; lean_object* v_aux_6533_; lean_object* v___x_6534_; lean_object* v___x_6535_; lean_object* v___x_6536_; lean_object* v___f_6537_; lean_object* v___x_6538_; lean_object* v___x_6539_; 
lean_inc_ref(v___y_6524_);
v___x_6529_ = lean_array_to_list(v___y_6524_);
lean_inc(v_matcherName_6508_);
v___x_6530_ = l_Lean_mkConst(v_matcherName_6508_, v___x_6529_);
v_aux_6531_ = l_Lean_mkAppN(v___x_6530_, v___y_6528_);
lean_inc_ref(v___y_6519_);
v_aux_6532_ = l_Lean_Expr_app___override(v_aux_6531_, v___y_6519_);
v_aux_6533_ = l_Lean_mkAppN(v_aux_6532_, v___y_6527_);
v___x_6534_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__1);
lean_inc_ref(v_aux_6533_);
v___x_6535_ = l_Lean_indentExpr(v_aux_6533_);
v___x_6536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6536_, 0, v___x_6534_);
lean_ctor_set(v___x_6536_, 1, v___x_6535_);
v___f_6537_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6537_, 0, v___x_6536_);
lean_inc_ref(v_aux_6533_);
v___x_6538_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(v___x_6538_, 0, v_aux_6533_);
lean_inc(v___y_6518_);
lean_inc_ref(v___y_6522_);
lean_inc(v___y_6521_);
lean_inc_ref(v___y_6525_);
v___x_6539_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6538_, v___f_6537_, v___y_6525_, v___y_6521_, v___y_6522_, v___y_6518_);
if (lean_obj_tag(v___x_6539_) == 0)
{
lean_object* v___x_6540_; lean_object* v___x_6541_; 
lean_dec_ref(v___x_6539_);
v___x_6540_ = lean_array_get_size(v_alts_6513_);
lean_inc(v___y_6518_);
lean_inc_ref(v___y_6522_);
lean_inc(v___y_6521_);
lean_inc_ref(v___y_6525_);
v___x_6541_ = l_Lean_Meta_inferArgumentTypesN(v___x_6540_, v_aux_6533_, v___y_6525_, v___y_6521_, v___y_6522_, v___y_6518_);
if (lean_obj_tag(v___x_6541_) == 0)
{
lean_object* v_a_6542_; lean_object* v___x_6543_; lean_object* v___x_6544_; lean_object* v___x_6545_; lean_object* v___x_6546_; lean_object* v___x_6547_; lean_object* v___x_6548_; lean_object* v___x_6549_; lean_object* v___x_6550_; lean_object* v___x_6551_; lean_object* v___x_6552_; 
v_a_6542_ = lean_ctor_get(v___x_6541_, 0);
lean_inc(v_a_6542_);
lean_dec_ref(v___x_6541_);
v___x_6543_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_6493_);
v___x_6544_ = lean_array_get_size(v___x_6543_);
v___x_6545_ = lean_array_get_size(v_a_6542_);
lean_inc(v___y_6526_);
v___x_6546_ = l_Array_toSubarray___redArg(v_alts_6513_, v___y_6526_, v___x_6540_);
lean_inc(v___y_6526_);
v___x_6547_ = l_Array_toSubarray___redArg(v___x_6543_, v___y_6526_, v___x_6544_);
lean_inc(v___y_6526_);
v___x_6548_ = l_Array_toSubarray___redArg(v_a_6542_, v___y_6526_, v___x_6545_);
v___x_6549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6549_, 0, v___x_6547_);
lean_ctor_set(v___x_6549_, 1, v___x_6548_);
v___x_6550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6550_, 0, v___x_6546_);
lean_ctor_set(v___x_6550_, 1, v___x_6549_);
v___x_6551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6551_, 0, v___y_6517_);
lean_ctor_set(v___x_6551_, 1, v___x_6550_);
lean_inc(v___y_6518_);
lean_inc_ref(v___y_6522_);
lean_inc(v___y_6521_);
lean_inc_ref(v___y_6525_);
v___x_6552_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v___x_6540_, v_onAlt_6498_, v___y_6516_, v___y_6526_, v___x_6551_, v___y_6525_, v___y_6521_, v___y_6522_, v___y_6518_);
if (lean_obj_tag(v___x_6552_) == 0)
{
lean_object* v_a_6553_; lean_object* v_fst_6554_; lean_object* v___x_6555_; 
v_a_6553_ = lean_ctor_get(v___x_6552_, 0);
lean_inc(v_a_6553_);
lean_dec_ref(v___x_6552_);
v_fst_6554_ = lean_ctor_get(v_a_6553_, 0);
lean_inc(v_fst_6554_);
lean_dec(v_a_6553_);
v___x_6555_ = lean_apply_6(v_onRemaining_6499_, v_remaining_6514_, v___y_6525_, v___y_6521_, v___y_6522_, v___y_6518_, lean_box(0));
if (lean_obj_tag(v___x_6555_) == 0)
{
lean_object* v_a_6556_; lean_object* v___x_6558_; uint8_t v_isShared_6559_; uint8_t v_isSharedCheck_6578_; 
v_a_6556_ = lean_ctor_get(v___x_6555_, 0);
v_isSharedCheck_6578_ = !lean_is_exclusive(v___x_6555_);
if (v_isSharedCheck_6578_ == 0)
{
v___x_6558_ = v___x_6555_;
v_isShared_6559_ = v_isSharedCheck_6578_;
goto v_resetjp_6557_;
}
else
{
lean_inc(v_a_6556_);
lean_dec(v___x_6555_);
v___x_6558_ = lean_box(0);
v_isShared_6559_ = v_isSharedCheck_6578_;
goto v_resetjp_6557_;
}
v_resetjp_6557_:
{
lean_object* v_numParams_6560_; lean_object* v_numDiscrs_6561_; lean_object* v_altInfos_6562_; lean_object* v_uElimPos_x3f_6563_; lean_object* v_overlaps_6564_; lean_object* v___x_6566_; uint8_t v_isShared_6567_; uint8_t v_isSharedCheck_6576_; 
v_numParams_6560_ = lean_ctor_get(v_toMatcherInfo_6507_, 0);
v_numDiscrs_6561_ = lean_ctor_get(v_toMatcherInfo_6507_, 1);
v_altInfos_6562_ = lean_ctor_get(v_toMatcherInfo_6507_, 2);
v_uElimPos_x3f_6563_ = lean_ctor_get(v_toMatcherInfo_6507_, 3);
v_overlaps_6564_ = lean_ctor_get(v_toMatcherInfo_6507_, 5);
v_isSharedCheck_6576_ = !lean_is_exclusive(v_toMatcherInfo_6507_);
if (v_isSharedCheck_6576_ == 0)
{
lean_object* v_unused_6577_; 
v_unused_6577_ = lean_ctor_get(v_toMatcherInfo_6507_, 4);
lean_dec(v_unused_6577_);
v___x_6566_ = v_toMatcherInfo_6507_;
v_isShared_6567_ = v_isSharedCheck_6576_;
goto v_resetjp_6565_;
}
else
{
lean_inc(v_overlaps_6564_);
lean_inc(v_uElimPos_x3f_6563_);
lean_inc(v_altInfos_6562_);
lean_inc(v_numDiscrs_6561_);
lean_inc(v_numParams_6560_);
lean_dec(v_toMatcherInfo_6507_);
v___x_6566_ = lean_box(0);
v_isShared_6567_ = v_isSharedCheck_6576_;
goto v_resetjp_6565_;
}
v_resetjp_6565_:
{
lean_object* v_remaining_x27_6568_; lean_object* v___x_6570_; 
v_remaining_x27_6568_ = l_Array_append___redArg(v___y_6520_, v_a_6556_);
lean_dec(v_a_6556_);
if (v_isShared_6567_ == 0)
{
lean_ctor_set(v___x_6566_, 4, v___y_6523_);
v___x_6570_ = v___x_6566_;
goto v_reusejp_6569_;
}
else
{
lean_object* v_reuseFailAlloc_6575_; 
v_reuseFailAlloc_6575_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6575_, 0, v_numParams_6560_);
lean_ctor_set(v_reuseFailAlloc_6575_, 1, v_numDiscrs_6561_);
lean_ctor_set(v_reuseFailAlloc_6575_, 2, v_altInfos_6562_);
lean_ctor_set(v_reuseFailAlloc_6575_, 3, v_uElimPos_x3f_6563_);
lean_ctor_set(v_reuseFailAlloc_6575_, 4, v___y_6523_);
lean_ctor_set(v_reuseFailAlloc_6575_, 5, v_overlaps_6564_);
v___x_6570_ = v_reuseFailAlloc_6575_;
goto v_reusejp_6569_;
}
v_reusejp_6569_:
{
lean_object* v___x_6571_; lean_object* v___x_6573_; 
v___x_6571_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6571_, 0, v___x_6570_);
lean_ctor_set(v___x_6571_, 1, v_matcherName_6508_);
lean_ctor_set(v___x_6571_, 2, v___y_6524_);
lean_ctor_set(v___x_6571_, 3, v___y_6528_);
lean_ctor_set(v___x_6571_, 4, v___y_6519_);
lean_ctor_set(v___x_6571_, 5, v___y_6527_);
lean_ctor_set(v___x_6571_, 6, v_fst_6554_);
lean_ctor_set(v___x_6571_, 7, v_remaining_x27_6568_);
if (v_isShared_6559_ == 0)
{
lean_ctor_set(v___x_6558_, 0, v___x_6571_);
v___x_6573_ = v___x_6558_;
goto v_reusejp_6572_;
}
else
{
lean_object* v_reuseFailAlloc_6574_; 
v_reuseFailAlloc_6574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6574_, 0, v___x_6571_);
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
}
else
{
lean_object* v_a_6579_; lean_object* v___x_6581_; uint8_t v_isShared_6582_; uint8_t v_isSharedCheck_6586_; 
lean_dec(v_fst_6554_);
lean_dec_ref(v___y_6528_);
lean_dec_ref(v___y_6527_);
lean_dec_ref(v___y_6524_);
lean_dec_ref(v___y_6523_);
lean_dec(v___y_6520_);
lean_dec_ref(v___y_6519_);
lean_dec(v_matcherName_6508_);
lean_dec_ref(v_toMatcherInfo_6507_);
v_a_6579_ = lean_ctor_get(v___x_6555_, 0);
v_isSharedCheck_6586_ = !lean_is_exclusive(v___x_6555_);
if (v_isSharedCheck_6586_ == 0)
{
v___x_6581_ = v___x_6555_;
v_isShared_6582_ = v_isSharedCheck_6586_;
goto v_resetjp_6580_;
}
else
{
lean_inc(v_a_6579_);
lean_dec(v___x_6555_);
v___x_6581_ = lean_box(0);
v_isShared_6582_ = v_isSharedCheck_6586_;
goto v_resetjp_6580_;
}
v_resetjp_6580_:
{
lean_object* v___x_6584_; 
if (v_isShared_6582_ == 0)
{
v___x_6584_ = v___x_6581_;
goto v_reusejp_6583_;
}
else
{
lean_object* v_reuseFailAlloc_6585_; 
v_reuseFailAlloc_6585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6585_, 0, v_a_6579_);
v___x_6584_ = v_reuseFailAlloc_6585_;
goto v_reusejp_6583_;
}
v_reusejp_6583_:
{
return v___x_6584_;
}
}
}
}
else
{
lean_object* v_a_6587_; lean_object* v___x_6589_; uint8_t v_isShared_6590_; uint8_t v_isSharedCheck_6594_; 
lean_dec_ref(v___y_6528_);
lean_dec_ref(v___y_6527_);
lean_dec_ref(v___y_6525_);
lean_dec_ref(v___y_6524_);
lean_dec_ref(v___y_6523_);
lean_dec_ref(v___y_6522_);
lean_dec(v___y_6521_);
lean_dec(v___y_6520_);
lean_dec_ref(v___y_6519_);
lean_dec(v___y_6518_);
lean_dec_ref(v_remaining_6514_);
lean_dec(v_matcherName_6508_);
lean_dec_ref(v_toMatcherInfo_6507_);
lean_dec_ref(v_onRemaining_6499_);
v_a_6587_ = lean_ctor_get(v___x_6552_, 0);
v_isSharedCheck_6594_ = !lean_is_exclusive(v___x_6552_);
if (v_isSharedCheck_6594_ == 0)
{
v___x_6589_ = v___x_6552_;
v_isShared_6590_ = v_isSharedCheck_6594_;
goto v_resetjp_6588_;
}
else
{
lean_inc(v_a_6587_);
lean_dec(v___x_6552_);
v___x_6589_ = lean_box(0);
v_isShared_6590_ = v_isSharedCheck_6594_;
goto v_resetjp_6588_;
}
v_resetjp_6588_:
{
lean_object* v___x_6592_; 
if (v_isShared_6590_ == 0)
{
v___x_6592_ = v___x_6589_;
goto v_reusejp_6591_;
}
else
{
lean_object* v_reuseFailAlloc_6593_; 
v_reuseFailAlloc_6593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6593_, 0, v_a_6587_);
v___x_6592_ = v_reuseFailAlloc_6593_;
goto v_reusejp_6591_;
}
v_reusejp_6591_:
{
return v___x_6592_;
}
}
}
}
else
{
lean_object* v_a_6595_; lean_object* v___x_6597_; uint8_t v_isShared_6598_; uint8_t v_isSharedCheck_6602_; 
lean_dec_ref(v___y_6528_);
lean_dec_ref(v___y_6527_);
lean_dec(v___y_6526_);
lean_dec_ref(v___y_6525_);
lean_dec_ref(v___y_6524_);
lean_dec_ref(v___y_6523_);
lean_dec_ref(v___y_6522_);
lean_dec(v___y_6521_);
lean_dec(v___y_6520_);
lean_dec_ref(v___y_6519_);
lean_dec(v___y_6518_);
lean_dec_ref(v___y_6517_);
lean_dec(v___y_6516_);
lean_dec_ref(v_remaining_6514_);
lean_dec_ref(v_alts_6513_);
lean_dec(v_matcherName_6508_);
lean_dec_ref(v_toMatcherInfo_6507_);
lean_dec_ref(v_onRemaining_6499_);
lean_dec_ref(v_onAlt_6498_);
lean_dec_ref(v_matcherApp_6493_);
v_a_6595_ = lean_ctor_get(v___x_6541_, 0);
v_isSharedCheck_6602_ = !lean_is_exclusive(v___x_6541_);
if (v_isSharedCheck_6602_ == 0)
{
v___x_6597_ = v___x_6541_;
v_isShared_6598_ = v_isSharedCheck_6602_;
goto v_resetjp_6596_;
}
else
{
lean_inc(v_a_6595_);
lean_dec(v___x_6541_);
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
lean_dec_ref(v_aux_6533_);
lean_dec_ref(v___y_6528_);
lean_dec_ref(v___y_6527_);
lean_dec(v___y_6526_);
lean_dec_ref(v___y_6525_);
lean_dec_ref(v___y_6524_);
lean_dec_ref(v___y_6523_);
lean_dec_ref(v___y_6522_);
lean_dec(v___y_6521_);
lean_dec(v___y_6520_);
lean_dec_ref(v___y_6519_);
lean_dec(v___y_6518_);
lean_dec_ref(v___y_6517_);
lean_dec(v___y_6516_);
lean_dec_ref(v_remaining_6514_);
lean_dec_ref(v_alts_6513_);
lean_dec(v_matcherName_6508_);
lean_dec_ref(v_toMatcherInfo_6507_);
lean_dec_ref(v_onRemaining_6499_);
lean_dec_ref(v_onAlt_6498_);
lean_dec_ref(v_matcherApp_6493_);
v_a_6603_ = lean_ctor_get(v___x_6539_, 0);
v_isSharedCheck_6610_ = !lean_is_exclusive(v___x_6539_);
if (v_isSharedCheck_6610_ == 0)
{
v___x_6605_ = v___x_6539_;
v_isShared_6606_ = v_isSharedCheck_6610_;
goto v_resetjp_6604_;
}
else
{
lean_inc(v_a_6603_);
lean_dec(v___x_6539_);
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
v___jp_6612_:
{
lean_object* v___x_6625_; lean_object* v_remaining_x27_6626_; lean_object* v___x_6627_; lean_object* v___x_6628_; lean_object* v___x_6629_; lean_object* v___x_6630_; lean_object* v___x_6631_; lean_object* v___x_6632_; size_t v_sz_6633_; lean_object* v___x_6634_; 
v___x_6625_ = lean_unsigned_to_nat(0u);
v_remaining_x27_6626_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_6627_ = l_Array_reverse___redArg(v___y_6613_);
v___x_6628_ = lean_array_get_size(v___x_6627_);
v___x_6629_ = l_Array_toSubarray___redArg(v___x_6627_, v___x_6625_, v___x_6628_);
lean_inc_ref(v___y_6617_);
v___x_6630_ = l_Array_reverse___redArg(v___y_6617_);
v___x_6631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6631_, 0, v___x_6625_);
lean_ctor_set(v___x_6631_, 1, v___x_6629_);
v___x_6632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6632_, 0, v_remaining_x27_6626_);
lean_ctor_set(v___x_6632_, 1, v___x_6631_);
v_sz_6633_ = lean_array_size(v___x_6630_);
lean_inc(v___y_6624_);
lean_inc_ref(v___y_6623_);
lean_inc(v___y_6622_);
lean_inc_ref(v___y_6621_);
v___x_6634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(v___x_6630_, v_sz_6633_, v___y_6619_, v___x_6632_, v___y_6621_, v___y_6622_, v___y_6623_, v___y_6624_);
lean_dec_ref(v___x_6630_);
if (lean_obj_tag(v___x_6634_) == 0)
{
lean_object* v_a_6635_; lean_object* v_snd_6636_; 
v_a_6635_ = lean_ctor_get(v___x_6634_, 0);
lean_inc(v_a_6635_);
lean_dec_ref(v___x_6634_);
v_snd_6636_ = lean_ctor_get(v_a_6635_, 1);
lean_inc(v_snd_6636_);
if (v_useSplitter_6494_ == 0)
{
lean_object* v_fst_6637_; lean_object* v_fst_6638_; 
lean_dec(v___y_6614_);
v_fst_6637_ = lean_ctor_get(v_a_6635_, 0);
lean_inc(v_fst_6637_);
lean_dec(v_a_6635_);
v_fst_6638_ = lean_ctor_get(v_snd_6636_, 0);
lean_inc(v_fst_6638_);
lean_dec(v_snd_6636_);
v___y_6516_ = v_fst_6638_;
v___y_6517_ = v_remaining_x27_6626_;
v___y_6518_ = v___y_6624_;
v___y_6519_ = v___y_6616_;
v___y_6520_ = v_fst_6637_;
v___y_6521_ = v___y_6622_;
v___y_6522_ = v___y_6623_;
v___y_6523_ = v___y_6615_;
v___y_6524_ = v_matcherLevels_6620_;
v___y_6525_ = v___y_6621_;
v___y_6526_ = v___x_6625_;
v___y_6527_ = v___y_6617_;
v___y_6528_ = v___y_6618_;
goto v___jp_6515_;
}
else
{
if (v_isCasesOn_6611_ == 0)
{
lean_object* v___x_6640_; uint8_t v_isShared_6641_; uint8_t v_isSharedCheck_6795_; 
v_isSharedCheck_6795_ = !lean_is_exclusive(v_matcherApp_6493_);
if (v_isSharedCheck_6795_ == 0)
{
lean_object* v_unused_6796_; lean_object* v_unused_6797_; lean_object* v_unused_6798_; lean_object* v_unused_6799_; lean_object* v_unused_6800_; lean_object* v_unused_6801_; lean_object* v_unused_6802_; lean_object* v_unused_6803_; 
v_unused_6796_ = lean_ctor_get(v_matcherApp_6493_, 7);
lean_dec(v_unused_6796_);
v_unused_6797_ = lean_ctor_get(v_matcherApp_6493_, 6);
lean_dec(v_unused_6797_);
v_unused_6798_ = lean_ctor_get(v_matcherApp_6493_, 5);
lean_dec(v_unused_6798_);
v_unused_6799_ = lean_ctor_get(v_matcherApp_6493_, 4);
lean_dec(v_unused_6799_);
v_unused_6800_ = lean_ctor_get(v_matcherApp_6493_, 3);
lean_dec(v_unused_6800_);
v_unused_6801_ = lean_ctor_get(v_matcherApp_6493_, 2);
lean_dec(v_unused_6801_);
v_unused_6802_ = lean_ctor_get(v_matcherApp_6493_, 1);
lean_dec(v_unused_6802_);
v_unused_6803_ = lean_ctor_get(v_matcherApp_6493_, 0);
lean_dec(v_unused_6803_);
v___x_6640_ = v_matcherApp_6493_;
v_isShared_6641_ = v_isSharedCheck_6795_;
goto v_resetjp_6639_;
}
else
{
lean_dec(v_matcherApp_6493_);
v___x_6640_ = lean_box(0);
v_isShared_6641_ = v_isSharedCheck_6795_;
goto v_resetjp_6639_;
}
v_resetjp_6639_:
{
lean_object* v_fst_6642_; lean_object* v___x_6644_; uint8_t v_isShared_6645_; uint8_t v_isSharedCheck_6793_; 
v_fst_6642_ = lean_ctor_get(v_a_6635_, 0);
v_isSharedCheck_6793_ = !lean_is_exclusive(v_a_6635_);
if (v_isSharedCheck_6793_ == 0)
{
lean_object* v_unused_6794_; 
v_unused_6794_ = lean_ctor_get(v_a_6635_, 1);
lean_dec(v_unused_6794_);
v___x_6644_ = v_a_6635_;
v_isShared_6645_ = v_isSharedCheck_6793_;
goto v_resetjp_6643_;
}
else
{
lean_inc(v_fst_6642_);
lean_dec(v_a_6635_);
v___x_6644_ = lean_box(0);
v_isShared_6645_ = v_isSharedCheck_6793_;
goto v_resetjp_6643_;
}
v_resetjp_6643_:
{
lean_object* v_fst_6646_; lean_object* v___x_6648_; uint8_t v_isShared_6649_; uint8_t v_isSharedCheck_6791_; 
v_fst_6646_ = lean_ctor_get(v_snd_6636_, 0);
v_isSharedCheck_6791_ = !lean_is_exclusive(v_snd_6636_);
if (v_isSharedCheck_6791_ == 0)
{
lean_object* v_unused_6792_; 
v_unused_6792_ = lean_ctor_get(v_snd_6636_, 1);
lean_dec(v_unused_6792_);
v___x_6648_ = v_snd_6636_;
v_isShared_6649_ = v_isSharedCheck_6791_;
goto v_resetjp_6647_;
}
else
{
lean_inc(v_fst_6646_);
lean_dec(v_snd_6636_);
v___x_6648_ = lean_box(0);
v_isShared_6649_ = v_isSharedCheck_6791_;
goto v_resetjp_6647_;
}
v_resetjp_6647_:
{
lean_object* v___x_6650_; lean_object* v___x_6651_; lean_object* v_aux1_6652_; lean_object* v_aux1_6653_; lean_object* v_aux1_6654_; lean_object* v___x_6655_; lean_object* v___x_6656_; lean_object* v___x_6657_; lean_object* v___x_6658_; lean_object* v___x_6659_; lean_object* v___f_6660_; lean_object* v___x_6661_; lean_object* v___x_6662_; 
lean_inc_ref(v_matcherLevels_6620_);
v___x_6650_ = lean_array_to_list(v_matcherLevels_6620_);
lean_inc(v___x_6650_);
lean_inc(v_matcherName_6508_);
v___x_6651_ = l_Lean_mkConst(v_matcherName_6508_, v___x_6650_);
v_aux1_6652_ = l_Lean_mkAppN(v___x_6651_, v___y_6618_);
lean_inc_ref(v___y_6616_);
v_aux1_6653_ = l_Lean_Expr_app___override(v_aux1_6652_, v___y_6616_);
v_aux1_6654_ = l_Lean_mkAppN(v_aux1_6653_, v___y_6617_);
v___x_6655_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__3);
lean_inc_ref(v_aux1_6654_);
v___x_6656_ = l_Lean_indentExpr(v_aux1_6654_);
v___x_6657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6657_, 0, v___x_6655_);
lean_ctor_set(v___x_6657_, 1, v___x_6656_);
v___x_6658_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__5);
v___x_6659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6659_, 0, v___x_6657_);
lean_ctor_set(v___x_6659_, 1, v___x_6658_);
v___f_6660_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6660_, 0, v___x_6659_);
lean_inc_ref(v_aux1_6654_);
v___x_6661_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(v___x_6661_, 0, v_aux1_6654_);
lean_inc(v___y_6624_);
lean_inc_ref(v___y_6623_);
lean_inc(v___y_6622_);
lean_inc_ref(v___y_6621_);
v___x_6662_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6661_, v___f_6660_, v___y_6621_, v___y_6622_, v___y_6623_, v___y_6624_);
if (lean_obj_tag(v___x_6662_) == 0)
{
lean_object* v___x_6663_; lean_object* v___x_6664_; 
lean_dec_ref(v___x_6662_);
v___x_6663_ = lean_array_get_size(v_alts_6513_);
lean_inc(v___y_6624_);
lean_inc_ref(v___y_6623_);
lean_inc(v___y_6622_);
lean_inc_ref(v___y_6621_);
v___x_6664_ = l_Lean_Meta_inferArgumentTypesN(v___x_6663_, v_aux1_6654_, v___y_6621_, v___y_6622_, v___y_6623_, v___y_6624_);
if (lean_obj_tag(v___x_6664_) == 0)
{
lean_object* v_a_6665_; lean_object* v___x_6666_; 
v_a_6665_ = lean_ctor_get(v___x_6664_, 0);
lean_inc(v_a_6665_);
lean_dec_ref(v___x_6664_);
lean_inc(v___y_6624_);
lean_inc_ref(v___y_6623_);
lean_inc(v___y_6622_);
lean_inc_ref(v___y_6621_);
v___x_6666_ = lean_get_match_equations_for(v_matcherName_6508_, v___y_6621_, v___y_6622_, v___y_6623_, v___y_6624_);
if (lean_obj_tag(v___x_6666_) == 0)
{
lean_object* v_a_6667_; lean_object* v_splitterName_6668_; lean_object* v_splitterMatchInfo_6669_; lean_object* v___x_6670_; lean_object* v_aux2_6671_; lean_object* v_aux2_6672_; lean_object* v_aux2_6673_; lean_object* v___x_6674_; lean_object* v___x_6675_; lean_object* v___x_6676_; lean_object* v___x_6677_; lean_object* v___f_6678_; lean_object* v___x_6679_; lean_object* v___x_6680_; 
v_a_6667_ = lean_ctor_get(v___x_6666_, 0);
lean_inc(v_a_6667_);
lean_dec_ref(v___x_6666_);
v_splitterName_6668_ = lean_ctor_get(v_a_6667_, 1);
lean_inc(v_splitterName_6668_);
v_splitterMatchInfo_6669_ = lean_ctor_get(v_a_6667_, 2);
lean_inc_ref(v_splitterMatchInfo_6669_);
lean_dec(v_a_6667_);
lean_inc(v_splitterName_6668_);
v___x_6670_ = l_Lean_mkConst(v_splitterName_6668_, v___x_6650_);
v_aux2_6671_ = l_Lean_mkAppN(v___x_6670_, v___y_6618_);
lean_inc_ref(v___y_6616_);
v_aux2_6672_ = l_Lean_Expr_app___override(v_aux2_6671_, v___y_6616_);
v_aux2_6673_ = l_Lean_mkAppN(v_aux2_6672_, v___y_6617_);
v___x_6674_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1);
lean_inc_ref(v_aux2_6673_);
v___x_6675_ = l_Lean_indentExpr(v_aux2_6673_);
v___x_6676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6676_, 0, v___x_6674_);
lean_ctor_set(v___x_6676_, 1, v___x_6675_);
v___x_6677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6677_, 0, v___x_6676_);
lean_ctor_set(v___x_6677_, 1, v___x_6658_);
v___f_6678_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6678_, 0, v___x_6677_);
lean_inc_ref(v_aux2_6673_);
v___x_6679_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(v___x_6679_, 0, v_aux2_6673_);
lean_inc(v___y_6624_);
lean_inc_ref(v___y_6623_);
lean_inc(v___y_6622_);
lean_inc_ref(v___y_6621_);
v___x_6680_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6679_, v___f_6678_, v___y_6621_, v___y_6622_, v___y_6623_, v___y_6624_);
if (lean_obj_tag(v___x_6680_) == 0)
{
lean_object* v___x_6681_; 
lean_dec_ref(v___x_6680_);
lean_inc(v___y_6624_);
lean_inc_ref(v___y_6623_);
lean_inc(v___y_6622_);
lean_inc_ref(v___y_6621_);
v___x_6681_ = l_Lean_Meta_inferArgumentTypesN(v___x_6663_, v_aux2_6673_, v___y_6621_, v___y_6622_, v___y_6623_, v___y_6624_);
if (lean_obj_tag(v___x_6681_) == 0)
{
lean_object* v_a_6682_; lean_object* v_numParams_6683_; lean_object* v_numDiscrs_6684_; lean_object* v_altInfos_6685_; lean_object* v_uElimPos_x3f_6686_; lean_object* v_overlaps_6687_; lean_object* v_altInfos_6688_; lean_object* v___x_6690_; uint8_t v_isShared_6691_; uint8_t v_isSharedCheck_6745_; 
v_a_6682_ = lean_ctor_get(v___x_6681_, 0);
lean_inc(v_a_6682_);
lean_dec_ref(v___x_6681_);
v_numParams_6683_ = lean_ctor_get(v_toMatcherInfo_6507_, 0);
lean_inc(v_numParams_6683_);
v_numDiscrs_6684_ = lean_ctor_get(v_toMatcherInfo_6507_, 1);
lean_inc(v_numDiscrs_6684_);
v_altInfos_6685_ = lean_ctor_get(v_toMatcherInfo_6507_, 2);
lean_inc_ref(v_altInfos_6685_);
v_uElimPos_x3f_6686_ = lean_ctor_get(v_toMatcherInfo_6507_, 3);
lean_inc(v_uElimPos_x3f_6686_);
v_overlaps_6687_ = lean_ctor_get(v_toMatcherInfo_6507_, 5);
lean_inc_ref(v_overlaps_6687_);
lean_dec_ref(v_toMatcherInfo_6507_);
v_altInfos_6688_ = lean_ctor_get(v_splitterMatchInfo_6669_, 2);
v_isSharedCheck_6745_ = !lean_is_exclusive(v_splitterMatchInfo_6669_);
if (v_isSharedCheck_6745_ == 0)
{
lean_object* v_unused_6746_; lean_object* v_unused_6747_; lean_object* v_unused_6748_; lean_object* v_unused_6749_; lean_object* v_unused_6750_; 
v_unused_6746_ = lean_ctor_get(v_splitterMatchInfo_6669_, 5);
lean_dec(v_unused_6746_);
v_unused_6747_ = lean_ctor_get(v_splitterMatchInfo_6669_, 4);
lean_dec(v_unused_6747_);
v_unused_6748_ = lean_ctor_get(v_splitterMatchInfo_6669_, 3);
lean_dec(v_unused_6748_);
v_unused_6749_ = lean_ctor_get(v_splitterMatchInfo_6669_, 1);
lean_dec(v_unused_6749_);
v_unused_6750_ = lean_ctor_get(v_splitterMatchInfo_6669_, 0);
lean_dec(v_unused_6750_);
v___x_6690_ = v_splitterMatchInfo_6669_;
v_isShared_6691_ = v_isSharedCheck_6745_;
goto v_resetjp_6689_;
}
else
{
lean_inc(v_altInfos_6688_);
lean_dec(v_splitterMatchInfo_6669_);
v___x_6690_ = lean_box(0);
v_isShared_6691_ = v_isSharedCheck_6745_;
goto v_resetjp_6689_;
}
v_resetjp_6689_:
{
lean_object* v___x_6692_; lean_object* v___x_6693_; lean_object* v___x_6694_; lean_object* v___x_6695_; lean_object* v___x_6696_; lean_object* v___x_6697_; lean_object* v___x_6698_; lean_object* v___x_6699_; lean_object* v___x_6700_; lean_object* v___x_6702_; 
v___x_6692_ = lean_array_get_size(v_altInfos_6685_);
v___x_6693_ = lean_array_get_size(v_altInfos_6688_);
v___x_6694_ = lean_array_get_size(v_a_6665_);
v___x_6695_ = lean_array_get_size(v_a_6682_);
v___x_6696_ = l_Array_toSubarray___redArg(v_alts_6513_, v___x_6625_, v___x_6663_);
lean_inc_ref(v_altInfos_6685_);
v___x_6697_ = l_Array_toSubarray___redArg(v_altInfos_6685_, v___x_6625_, v___x_6692_);
v___x_6698_ = l_Array_toSubarray___redArg(v_altInfos_6688_, v___x_6625_, v___x_6693_);
v___x_6699_ = l_Array_toSubarray___redArg(v_a_6665_, v___x_6625_, v___x_6694_);
v___x_6700_ = l_Array_toSubarray___redArg(v_a_6682_, v___x_6625_, v___x_6695_);
if (v_isShared_6649_ == 0)
{
lean_ctor_set(v___x_6648_, 1, v___x_6700_);
lean_ctor_set(v___x_6648_, 0, v___x_6699_);
v___x_6702_ = v___x_6648_;
goto v_reusejp_6701_;
}
else
{
lean_object* v_reuseFailAlloc_6744_; 
v_reuseFailAlloc_6744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6744_, 0, v___x_6699_);
lean_ctor_set(v_reuseFailAlloc_6744_, 1, v___x_6700_);
v___x_6702_ = v_reuseFailAlloc_6744_;
goto v_reusejp_6701_;
}
v_reusejp_6701_:
{
lean_object* v___x_6704_; 
if (v_isShared_6645_ == 0)
{
lean_ctor_set(v___x_6644_, 1, v___x_6702_);
lean_ctor_set(v___x_6644_, 0, v___x_6698_);
v___x_6704_ = v___x_6644_;
goto v_reusejp_6703_;
}
else
{
lean_object* v_reuseFailAlloc_6743_; 
v_reuseFailAlloc_6743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6743_, 0, v___x_6698_);
lean_ctor_set(v_reuseFailAlloc_6743_, 1, v___x_6702_);
v___x_6704_ = v_reuseFailAlloc_6743_;
goto v_reusejp_6703_;
}
v_reusejp_6703_:
{
lean_object* v___x_6705_; lean_object* v___x_6706_; lean_object* v___x_6707_; lean_object* v___x_6708_; 
v___x_6705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6705_, 0, v___x_6697_);
lean_ctor_set(v___x_6705_, 1, v___x_6704_);
v___x_6706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6706_, 0, v___x_6696_);
lean_ctor_set(v___x_6706_, 1, v___x_6705_);
v___x_6707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6707_, 0, v_remaining_x27_6626_);
lean_ctor_set(v___x_6707_, 1, v___x_6706_);
lean_inc(v___y_6624_);
lean_inc_ref(v___y_6623_);
lean_inc(v___y_6622_);
lean_inc_ref(v___y_6621_);
v___x_6708_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v___x_6663_, v_onAlt_6498_, v_useSplitter_6494_, v_fst_6646_, v___y_6614_, v___x_6625_, v___x_6707_, v___y_6621_, v___y_6622_, v___y_6623_, v___y_6624_);
if (lean_obj_tag(v___x_6708_) == 0)
{
lean_object* v_a_6709_; lean_object* v_fst_6710_; lean_object* v___x_6711_; 
v_a_6709_ = lean_ctor_get(v___x_6708_, 0);
lean_inc(v_a_6709_);
lean_dec_ref(v___x_6708_);
v_fst_6710_ = lean_ctor_get(v_a_6709_, 0);
lean_inc(v_fst_6710_);
lean_dec(v_a_6709_);
v___x_6711_ = lean_apply_6(v_onRemaining_6499_, v_remaining_6514_, v___y_6621_, v___y_6622_, v___y_6623_, v___y_6624_, lean_box(0));
if (lean_obj_tag(v___x_6711_) == 0)
{
lean_object* v_a_6712_; lean_object* v___x_6714_; uint8_t v_isShared_6715_; uint8_t v_isSharedCheck_6726_; 
v_a_6712_ = lean_ctor_get(v___x_6711_, 0);
v_isSharedCheck_6726_ = !lean_is_exclusive(v___x_6711_);
if (v_isSharedCheck_6726_ == 0)
{
v___x_6714_ = v___x_6711_;
v_isShared_6715_ = v_isSharedCheck_6726_;
goto v_resetjp_6713_;
}
else
{
lean_inc(v_a_6712_);
lean_dec(v___x_6711_);
v___x_6714_ = lean_box(0);
v_isShared_6715_ = v_isSharedCheck_6726_;
goto v_resetjp_6713_;
}
v_resetjp_6713_:
{
lean_object* v_remaining_x27_6716_; lean_object* v___x_6718_; 
v_remaining_x27_6716_ = l_Array_append___redArg(v_fst_6642_, v_a_6712_);
lean_dec(v_a_6712_);
if (v_isShared_6691_ == 0)
{
lean_ctor_set(v___x_6690_, 5, v_overlaps_6687_);
lean_ctor_set(v___x_6690_, 4, v___y_6615_);
lean_ctor_set(v___x_6690_, 3, v_uElimPos_x3f_6686_);
lean_ctor_set(v___x_6690_, 2, v_altInfos_6685_);
lean_ctor_set(v___x_6690_, 1, v_numDiscrs_6684_);
lean_ctor_set(v___x_6690_, 0, v_numParams_6683_);
v___x_6718_ = v___x_6690_;
goto v_reusejp_6717_;
}
else
{
lean_object* v_reuseFailAlloc_6725_; 
v_reuseFailAlloc_6725_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6725_, 0, v_numParams_6683_);
lean_ctor_set(v_reuseFailAlloc_6725_, 1, v_numDiscrs_6684_);
lean_ctor_set(v_reuseFailAlloc_6725_, 2, v_altInfos_6685_);
lean_ctor_set(v_reuseFailAlloc_6725_, 3, v_uElimPos_x3f_6686_);
lean_ctor_set(v_reuseFailAlloc_6725_, 4, v___y_6615_);
lean_ctor_set(v_reuseFailAlloc_6725_, 5, v_overlaps_6687_);
v___x_6718_ = v_reuseFailAlloc_6725_;
goto v_reusejp_6717_;
}
v_reusejp_6717_:
{
lean_object* v___x_6720_; 
if (v_isShared_6641_ == 0)
{
lean_ctor_set(v___x_6640_, 7, v_remaining_x27_6716_);
lean_ctor_set(v___x_6640_, 6, v_fst_6710_);
lean_ctor_set(v___x_6640_, 5, v___y_6617_);
lean_ctor_set(v___x_6640_, 4, v___y_6616_);
lean_ctor_set(v___x_6640_, 3, v___y_6618_);
lean_ctor_set(v___x_6640_, 2, v_matcherLevels_6620_);
lean_ctor_set(v___x_6640_, 1, v_splitterName_6668_);
lean_ctor_set(v___x_6640_, 0, v___x_6718_);
v___x_6720_ = v___x_6640_;
goto v_reusejp_6719_;
}
else
{
lean_object* v_reuseFailAlloc_6724_; 
v_reuseFailAlloc_6724_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_6724_, 0, v___x_6718_);
lean_ctor_set(v_reuseFailAlloc_6724_, 1, v_splitterName_6668_);
lean_ctor_set(v_reuseFailAlloc_6724_, 2, v_matcherLevels_6620_);
lean_ctor_set(v_reuseFailAlloc_6724_, 3, v___y_6618_);
lean_ctor_set(v_reuseFailAlloc_6724_, 4, v___y_6616_);
lean_ctor_set(v_reuseFailAlloc_6724_, 5, v___y_6617_);
lean_ctor_set(v_reuseFailAlloc_6724_, 6, v_fst_6710_);
lean_ctor_set(v_reuseFailAlloc_6724_, 7, v_remaining_x27_6716_);
v___x_6720_ = v_reuseFailAlloc_6724_;
goto v_reusejp_6719_;
}
v_reusejp_6719_:
{
lean_object* v___x_6722_; 
if (v_isShared_6715_ == 0)
{
lean_ctor_set(v___x_6714_, 0, v___x_6720_);
v___x_6722_ = v___x_6714_;
goto v_reusejp_6721_;
}
else
{
lean_object* v_reuseFailAlloc_6723_; 
v_reuseFailAlloc_6723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6723_, 0, v___x_6720_);
v___x_6722_ = v_reuseFailAlloc_6723_;
goto v_reusejp_6721_;
}
v_reusejp_6721_:
{
return v___x_6722_;
}
}
}
}
}
else
{
lean_object* v_a_6727_; lean_object* v___x_6729_; uint8_t v_isShared_6730_; uint8_t v_isSharedCheck_6734_; 
lean_dec(v_fst_6710_);
lean_del_object(v___x_6690_);
lean_dec_ref(v_overlaps_6687_);
lean_dec(v_uElimPos_x3f_6686_);
lean_dec_ref(v_altInfos_6685_);
lean_dec(v_numDiscrs_6684_);
lean_dec(v_numParams_6683_);
lean_dec(v_splitterName_6668_);
lean_dec(v_fst_6642_);
lean_del_object(v___x_6640_);
lean_dec_ref(v_matcherLevels_6620_);
lean_dec_ref(v___y_6618_);
lean_dec_ref(v___y_6617_);
lean_dec_ref(v___y_6616_);
lean_dec_ref(v___y_6615_);
v_a_6727_ = lean_ctor_get(v___x_6711_, 0);
v_isSharedCheck_6734_ = !lean_is_exclusive(v___x_6711_);
if (v_isSharedCheck_6734_ == 0)
{
v___x_6729_ = v___x_6711_;
v_isShared_6730_ = v_isSharedCheck_6734_;
goto v_resetjp_6728_;
}
else
{
lean_inc(v_a_6727_);
lean_dec(v___x_6711_);
v___x_6729_ = lean_box(0);
v_isShared_6730_ = v_isSharedCheck_6734_;
goto v_resetjp_6728_;
}
v_resetjp_6728_:
{
lean_object* v___x_6732_; 
if (v_isShared_6730_ == 0)
{
v___x_6732_ = v___x_6729_;
goto v_reusejp_6731_;
}
else
{
lean_object* v_reuseFailAlloc_6733_; 
v_reuseFailAlloc_6733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6733_, 0, v_a_6727_);
v___x_6732_ = v_reuseFailAlloc_6733_;
goto v_reusejp_6731_;
}
v_reusejp_6731_:
{
return v___x_6732_;
}
}
}
}
else
{
lean_object* v_a_6735_; lean_object* v___x_6737_; uint8_t v_isShared_6738_; uint8_t v_isSharedCheck_6742_; 
lean_del_object(v___x_6690_);
lean_dec_ref(v_overlaps_6687_);
lean_dec(v_uElimPos_x3f_6686_);
lean_dec_ref(v_altInfos_6685_);
lean_dec(v_numDiscrs_6684_);
lean_dec(v_numParams_6683_);
lean_dec(v_splitterName_6668_);
lean_dec(v_fst_6642_);
lean_del_object(v___x_6640_);
lean_dec(v___y_6624_);
lean_dec_ref(v___y_6623_);
lean_dec(v___y_6622_);
lean_dec_ref(v___y_6621_);
lean_dec_ref(v_matcherLevels_6620_);
lean_dec_ref(v___y_6618_);
lean_dec_ref(v___y_6617_);
lean_dec_ref(v___y_6616_);
lean_dec_ref(v___y_6615_);
lean_dec_ref(v_remaining_6514_);
lean_dec_ref(v_onRemaining_6499_);
v_a_6735_ = lean_ctor_get(v___x_6708_, 0);
v_isSharedCheck_6742_ = !lean_is_exclusive(v___x_6708_);
if (v_isSharedCheck_6742_ == 0)
{
v___x_6737_ = v___x_6708_;
v_isShared_6738_ = v_isSharedCheck_6742_;
goto v_resetjp_6736_;
}
else
{
lean_inc(v_a_6735_);
lean_dec(v___x_6708_);
v___x_6737_ = lean_box(0);
v_isShared_6738_ = v_isSharedCheck_6742_;
goto v_resetjp_6736_;
}
v_resetjp_6736_:
{
lean_object* v___x_6740_; 
if (v_isShared_6738_ == 0)
{
v___x_6740_ = v___x_6737_;
goto v_reusejp_6739_;
}
else
{
lean_object* v_reuseFailAlloc_6741_; 
v_reuseFailAlloc_6741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6741_, 0, v_a_6735_);
v___x_6740_ = v_reuseFailAlloc_6741_;
goto v_reusejp_6739_;
}
v_reusejp_6739_:
{
return v___x_6740_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_6751_; lean_object* v___x_6753_; uint8_t v_isShared_6754_; uint8_t v_isSharedCheck_6758_; 
lean_dec_ref(v_splitterMatchInfo_6669_);
lean_dec(v_splitterName_6668_);
lean_dec(v_a_6665_);
lean_del_object(v___x_6648_);
lean_dec(v_fst_6646_);
lean_del_object(v___x_6644_);
lean_dec(v_fst_6642_);
lean_del_object(v___x_6640_);
lean_dec(v___y_6624_);
lean_dec_ref(v___y_6623_);
lean_dec(v___y_6622_);
lean_dec_ref(v___y_6621_);
lean_dec_ref(v_matcherLevels_6620_);
lean_dec_ref(v___y_6618_);
lean_dec_ref(v___y_6617_);
lean_dec_ref(v___y_6616_);
lean_dec_ref(v___y_6615_);
lean_dec(v___y_6614_);
lean_dec_ref(v_remaining_6514_);
lean_dec_ref(v_alts_6513_);
lean_dec_ref(v_toMatcherInfo_6507_);
lean_dec_ref(v_onRemaining_6499_);
lean_dec_ref(v_onAlt_6498_);
v_a_6751_ = lean_ctor_get(v___x_6681_, 0);
v_isSharedCheck_6758_ = !lean_is_exclusive(v___x_6681_);
if (v_isSharedCheck_6758_ == 0)
{
v___x_6753_ = v___x_6681_;
v_isShared_6754_ = v_isSharedCheck_6758_;
goto v_resetjp_6752_;
}
else
{
lean_inc(v_a_6751_);
lean_dec(v___x_6681_);
v___x_6753_ = lean_box(0);
v_isShared_6754_ = v_isSharedCheck_6758_;
goto v_resetjp_6752_;
}
v_resetjp_6752_:
{
lean_object* v___x_6756_; 
if (v_isShared_6754_ == 0)
{
v___x_6756_ = v___x_6753_;
goto v_reusejp_6755_;
}
else
{
lean_object* v_reuseFailAlloc_6757_; 
v_reuseFailAlloc_6757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6757_, 0, v_a_6751_);
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
else
{
lean_object* v_a_6759_; lean_object* v___x_6761_; uint8_t v_isShared_6762_; uint8_t v_isSharedCheck_6766_; 
lean_dec_ref(v_aux2_6673_);
lean_dec_ref(v_splitterMatchInfo_6669_);
lean_dec(v_splitterName_6668_);
lean_dec(v_a_6665_);
lean_del_object(v___x_6648_);
lean_dec(v_fst_6646_);
lean_del_object(v___x_6644_);
lean_dec(v_fst_6642_);
lean_del_object(v___x_6640_);
lean_dec(v___y_6624_);
lean_dec_ref(v___y_6623_);
lean_dec(v___y_6622_);
lean_dec_ref(v___y_6621_);
lean_dec_ref(v_matcherLevels_6620_);
lean_dec_ref(v___y_6618_);
lean_dec_ref(v___y_6617_);
lean_dec_ref(v___y_6616_);
lean_dec_ref(v___y_6615_);
lean_dec(v___y_6614_);
lean_dec_ref(v_remaining_6514_);
lean_dec_ref(v_alts_6513_);
lean_dec_ref(v_toMatcherInfo_6507_);
lean_dec_ref(v_onRemaining_6499_);
lean_dec_ref(v_onAlt_6498_);
v_a_6759_ = lean_ctor_get(v___x_6680_, 0);
v_isSharedCheck_6766_ = !lean_is_exclusive(v___x_6680_);
if (v_isSharedCheck_6766_ == 0)
{
v___x_6761_ = v___x_6680_;
v_isShared_6762_ = v_isSharedCheck_6766_;
goto v_resetjp_6760_;
}
else
{
lean_inc(v_a_6759_);
lean_dec(v___x_6680_);
v___x_6761_ = lean_box(0);
v_isShared_6762_ = v_isSharedCheck_6766_;
goto v_resetjp_6760_;
}
v_resetjp_6760_:
{
lean_object* v___x_6764_; 
if (v_isShared_6762_ == 0)
{
v___x_6764_ = v___x_6761_;
goto v_reusejp_6763_;
}
else
{
lean_object* v_reuseFailAlloc_6765_; 
v_reuseFailAlloc_6765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6765_, 0, v_a_6759_);
v___x_6764_ = v_reuseFailAlloc_6765_;
goto v_reusejp_6763_;
}
v_reusejp_6763_:
{
return v___x_6764_;
}
}
}
}
else
{
lean_object* v_a_6767_; lean_object* v___x_6769_; uint8_t v_isShared_6770_; uint8_t v_isSharedCheck_6774_; 
lean_dec(v_a_6665_);
lean_dec(v___x_6650_);
lean_del_object(v___x_6648_);
lean_dec(v_fst_6646_);
lean_del_object(v___x_6644_);
lean_dec(v_fst_6642_);
lean_del_object(v___x_6640_);
lean_dec(v___y_6624_);
lean_dec_ref(v___y_6623_);
lean_dec(v___y_6622_);
lean_dec_ref(v___y_6621_);
lean_dec_ref(v_matcherLevels_6620_);
lean_dec_ref(v___y_6618_);
lean_dec_ref(v___y_6617_);
lean_dec_ref(v___y_6616_);
lean_dec_ref(v___y_6615_);
lean_dec(v___y_6614_);
lean_dec_ref(v_remaining_6514_);
lean_dec_ref(v_alts_6513_);
lean_dec_ref(v_toMatcherInfo_6507_);
lean_dec_ref(v_onRemaining_6499_);
lean_dec_ref(v_onAlt_6498_);
v_a_6767_ = lean_ctor_get(v___x_6666_, 0);
v_isSharedCheck_6774_ = !lean_is_exclusive(v___x_6666_);
if (v_isSharedCheck_6774_ == 0)
{
v___x_6769_ = v___x_6666_;
v_isShared_6770_ = v_isSharedCheck_6774_;
goto v_resetjp_6768_;
}
else
{
lean_inc(v_a_6767_);
lean_dec(v___x_6666_);
v___x_6769_ = lean_box(0);
v_isShared_6770_ = v_isSharedCheck_6774_;
goto v_resetjp_6768_;
}
v_resetjp_6768_:
{
lean_object* v___x_6772_; 
if (v_isShared_6770_ == 0)
{
v___x_6772_ = v___x_6769_;
goto v_reusejp_6771_;
}
else
{
lean_object* v_reuseFailAlloc_6773_; 
v_reuseFailAlloc_6773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6773_, 0, v_a_6767_);
v___x_6772_ = v_reuseFailAlloc_6773_;
goto v_reusejp_6771_;
}
v_reusejp_6771_:
{
return v___x_6772_;
}
}
}
}
else
{
lean_object* v_a_6775_; lean_object* v___x_6777_; uint8_t v_isShared_6778_; uint8_t v_isSharedCheck_6782_; 
lean_dec(v___x_6650_);
lean_del_object(v___x_6648_);
lean_dec(v_fst_6646_);
lean_del_object(v___x_6644_);
lean_dec(v_fst_6642_);
lean_del_object(v___x_6640_);
lean_dec(v___y_6624_);
lean_dec_ref(v___y_6623_);
lean_dec(v___y_6622_);
lean_dec_ref(v___y_6621_);
lean_dec_ref(v_matcherLevels_6620_);
lean_dec_ref(v___y_6618_);
lean_dec_ref(v___y_6617_);
lean_dec_ref(v___y_6616_);
lean_dec_ref(v___y_6615_);
lean_dec(v___y_6614_);
lean_dec_ref(v_remaining_6514_);
lean_dec_ref(v_alts_6513_);
lean_dec(v_matcherName_6508_);
lean_dec_ref(v_toMatcherInfo_6507_);
lean_dec_ref(v_onRemaining_6499_);
lean_dec_ref(v_onAlt_6498_);
v_a_6775_ = lean_ctor_get(v___x_6664_, 0);
v_isSharedCheck_6782_ = !lean_is_exclusive(v___x_6664_);
if (v_isSharedCheck_6782_ == 0)
{
v___x_6777_ = v___x_6664_;
v_isShared_6778_ = v_isSharedCheck_6782_;
goto v_resetjp_6776_;
}
else
{
lean_inc(v_a_6775_);
lean_dec(v___x_6664_);
v___x_6777_ = lean_box(0);
v_isShared_6778_ = v_isSharedCheck_6782_;
goto v_resetjp_6776_;
}
v_resetjp_6776_:
{
lean_object* v___x_6780_; 
if (v_isShared_6778_ == 0)
{
v___x_6780_ = v___x_6777_;
goto v_reusejp_6779_;
}
else
{
lean_object* v_reuseFailAlloc_6781_; 
v_reuseFailAlloc_6781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6781_, 0, v_a_6775_);
v___x_6780_ = v_reuseFailAlloc_6781_;
goto v_reusejp_6779_;
}
v_reusejp_6779_:
{
return v___x_6780_;
}
}
}
}
else
{
lean_object* v_a_6783_; lean_object* v___x_6785_; uint8_t v_isShared_6786_; uint8_t v_isSharedCheck_6790_; 
lean_dec_ref(v_aux1_6654_);
lean_dec(v___x_6650_);
lean_del_object(v___x_6648_);
lean_dec(v_fst_6646_);
lean_del_object(v___x_6644_);
lean_dec(v_fst_6642_);
lean_del_object(v___x_6640_);
lean_dec(v___y_6624_);
lean_dec_ref(v___y_6623_);
lean_dec(v___y_6622_);
lean_dec_ref(v___y_6621_);
lean_dec_ref(v_matcherLevels_6620_);
lean_dec_ref(v___y_6618_);
lean_dec_ref(v___y_6617_);
lean_dec_ref(v___y_6616_);
lean_dec_ref(v___y_6615_);
lean_dec(v___y_6614_);
lean_dec_ref(v_remaining_6514_);
lean_dec_ref(v_alts_6513_);
lean_dec(v_matcherName_6508_);
lean_dec_ref(v_toMatcherInfo_6507_);
lean_dec_ref(v_onRemaining_6499_);
lean_dec_ref(v_onAlt_6498_);
v_a_6783_ = lean_ctor_get(v___x_6662_, 0);
v_isSharedCheck_6790_ = !lean_is_exclusive(v___x_6662_);
if (v_isSharedCheck_6790_ == 0)
{
v___x_6785_ = v___x_6662_;
v_isShared_6786_ = v_isSharedCheck_6790_;
goto v_resetjp_6784_;
}
else
{
lean_inc(v_a_6783_);
lean_dec(v___x_6662_);
v___x_6785_ = lean_box(0);
v_isShared_6786_ = v_isSharedCheck_6790_;
goto v_resetjp_6784_;
}
v_resetjp_6784_:
{
lean_object* v___x_6788_; 
if (v_isShared_6786_ == 0)
{
v___x_6788_ = v___x_6785_;
goto v_reusejp_6787_;
}
else
{
lean_object* v_reuseFailAlloc_6789_; 
v_reuseFailAlloc_6789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6789_, 0, v_a_6783_);
v___x_6788_ = v_reuseFailAlloc_6789_;
goto v_reusejp_6787_;
}
v_reusejp_6787_:
{
return v___x_6788_;
}
}
}
}
}
}
}
else
{
lean_object* v_fst_6804_; lean_object* v_fst_6805_; 
lean_dec(v___y_6614_);
v_fst_6804_ = lean_ctor_get(v_a_6635_, 0);
lean_inc(v_fst_6804_);
lean_dec(v_a_6635_);
v_fst_6805_ = lean_ctor_get(v_snd_6636_, 0);
lean_inc(v_fst_6805_);
lean_dec(v_snd_6636_);
v___y_6516_ = v_fst_6805_;
v___y_6517_ = v_remaining_x27_6626_;
v___y_6518_ = v___y_6624_;
v___y_6519_ = v___y_6616_;
v___y_6520_ = v_fst_6804_;
v___y_6521_ = v___y_6622_;
v___y_6522_ = v___y_6623_;
v___y_6523_ = v___y_6615_;
v___y_6524_ = v_matcherLevels_6620_;
v___y_6525_ = v___y_6621_;
v___y_6526_ = v___x_6625_;
v___y_6527_ = v___y_6617_;
v___y_6528_ = v___y_6618_;
goto v___jp_6515_;
}
}
}
else
{
lean_object* v_a_6806_; lean_object* v___x_6808_; uint8_t v_isShared_6809_; uint8_t v_isSharedCheck_6813_; 
lean_dec(v___y_6624_);
lean_dec_ref(v___y_6623_);
lean_dec(v___y_6622_);
lean_dec_ref(v___y_6621_);
lean_dec_ref(v_matcherLevels_6620_);
lean_dec_ref(v___y_6618_);
lean_dec_ref(v___y_6617_);
lean_dec_ref(v___y_6616_);
lean_dec_ref(v___y_6615_);
lean_dec(v___y_6614_);
lean_dec_ref(v_remaining_6514_);
lean_dec_ref(v_alts_6513_);
lean_dec(v_matcherName_6508_);
lean_dec_ref(v_toMatcherInfo_6507_);
lean_dec_ref(v_onRemaining_6499_);
lean_dec_ref(v_onAlt_6498_);
lean_dec_ref(v_matcherApp_6493_);
v_a_6806_ = lean_ctor_get(v___x_6634_, 0);
v_isSharedCheck_6813_ = !lean_is_exclusive(v___x_6634_);
if (v_isSharedCheck_6813_ == 0)
{
v___x_6808_ = v___x_6634_;
v_isShared_6809_ = v_isSharedCheck_6813_;
goto v_resetjp_6807_;
}
else
{
lean_inc(v_a_6806_);
lean_dec(v___x_6634_);
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
v___jp_6814_:
{
size_t v_sz_6820_; size_t v___x_6821_; lean_object* v___x_6822_; 
v_sz_6820_ = lean_array_size(v_params_6510_);
v___x_6821_ = ((size_t)0ULL);
lean_inc(v___y_6819_);
lean_inc_ref(v___y_6818_);
lean_inc(v___y_6817_);
lean_inc_ref(v___y_6816_);
lean_inc_ref(v_params_6510_);
lean_inc_ref(v_onParams_6496_);
v___x_6822_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6496_, v_sz_6820_, v___x_6821_, v_params_6510_, v___y_6816_, v___y_6817_, v___y_6818_, v___y_6819_);
if (lean_obj_tag(v___x_6822_) == 0)
{
lean_object* v_a_6823_; size_t v_sz_6824_; lean_object* v___x_6825_; 
v_a_6823_ = lean_ctor_get(v___x_6822_, 0);
lean_inc(v_a_6823_);
lean_dec_ref(v___x_6822_);
v_sz_6824_ = lean_array_size(v_discrs_6512_);
lean_inc(v___y_6819_);
lean_inc_ref(v___y_6818_);
lean_inc(v___y_6817_);
lean_inc_ref(v___y_6816_);
lean_inc_ref(v_discrs_6512_);
v___x_6825_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6496_, v_sz_6824_, v___x_6821_, v_discrs_6512_, v___y_6816_, v___y_6817_, v___y_6818_, v___y_6819_);
if (lean_obj_tag(v___x_6825_) == 0)
{
lean_object* v_a_6826_; lean_object* v___x_6827_; lean_object* v___x_6828_; lean_object* v___f_6829_; uint8_t v___x_6830_; lean_object* v___x_6831_; 
v_a_6826_ = lean_ctor_get(v___x_6825_, 0);
lean_inc(v_a_6826_);
lean_dec_ref(v___x_6825_);
v___x_6827_ = lean_box(v_addEqualities_6495_);
v___x_6828_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed__const__1));
lean_inc_ref(v_discrs_6512_);
lean_inc(v_a_6826_);
lean_inc_ref(v_toMatcherInfo_6507_);
v___f_6829_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed), 13, 6);
lean_closure_set(v___f_6829_, 0, v_onMotive_6497_);
lean_closure_set(v___f_6829_, 1, v_toMatcherInfo_6507_);
lean_closure_set(v___f_6829_, 2, v_a_6826_);
lean_closure_set(v___f_6829_, 3, v___x_6827_);
lean_closure_set(v___f_6829_, 4, v___x_6828_);
lean_closure_set(v___f_6829_, 5, v_discrs_6512_);
v___x_6830_ = 0;
lean_inc(v___y_6819_);
lean_inc_ref(v___y_6818_);
lean_inc(v___y_6817_);
lean_inc_ref(v___y_6816_);
lean_inc_ref(v_motive_6511_);
v___x_6831_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_6511_, v___f_6829_, v___x_6830_, v___y_6816_, v___y_6817_, v___y_6818_, v___y_6819_);
if (lean_obj_tag(v___x_6831_) == 0)
{
lean_object* v_a_6832_; lean_object* v_snd_6833_; lean_object* v_snd_6834_; lean_object* v_uElimPos_x3f_6835_; 
v_a_6832_ = lean_ctor_get(v___x_6831_, 0);
lean_inc(v_a_6832_);
lean_dec_ref(v___x_6831_);
v_snd_6833_ = lean_ctor_get(v_a_6832_, 1);
v_snd_6834_ = lean_ctor_get(v_snd_6833_, 1);
lean_inc(v_snd_6834_);
v_uElimPos_x3f_6835_ = lean_ctor_get(v_toMatcherInfo_6507_, 3);
if (lean_obj_tag(v_uElimPos_x3f_6835_) == 0)
{
lean_object* v_fst_6836_; lean_object* v_fst_6837_; lean_object* v_snd_6838_; 
v_fst_6836_ = lean_ctor_get(v_a_6832_, 0);
lean_inc(v_fst_6836_);
lean_dec(v_a_6832_);
v_fst_6837_ = lean_ctor_get(v_snd_6834_, 0);
lean_inc(v_fst_6837_);
v_snd_6838_ = lean_ctor_get(v_snd_6834_, 1);
lean_inc(v_snd_6838_);
lean_dec(v_snd_6834_);
lean_inc_ref(v_matcherLevels_6509_);
v___y_6613_ = v_fst_6837_;
v___y_6614_ = v_numDiscrEqs_6815_;
v___y_6615_ = v_snd_6838_;
v___y_6616_ = v_fst_6836_;
v___y_6617_ = v_a_6826_;
v___y_6618_ = v_a_6823_;
v___y_6619_ = v___x_6821_;
v_matcherLevels_6620_ = v_matcherLevels_6509_;
v___y_6621_ = v___y_6816_;
v___y_6622_ = v___y_6817_;
v___y_6623_ = v___y_6818_;
v___y_6624_ = v___y_6819_;
goto v___jp_6612_;
}
else
{
lean_object* v_fst_6839_; lean_object* v_fst_6840_; lean_object* v_fst_6841_; lean_object* v_snd_6842_; lean_object* v_val_6843_; lean_object* v___x_6844_; 
lean_inc(v_snd_6833_);
v_fst_6839_ = lean_ctor_get(v_a_6832_, 0);
lean_inc(v_fst_6839_);
lean_dec(v_a_6832_);
v_fst_6840_ = lean_ctor_get(v_snd_6833_, 0);
lean_inc(v_fst_6840_);
lean_dec(v_snd_6833_);
v_fst_6841_ = lean_ctor_get(v_snd_6834_, 0);
lean_inc(v_fst_6841_);
v_snd_6842_ = lean_ctor_get(v_snd_6834_, 1);
lean_inc(v_snd_6842_);
lean_dec(v_snd_6834_);
v_val_6843_ = lean_ctor_get(v_uElimPos_x3f_6835_, 0);
lean_inc_ref(v_matcherLevels_6509_);
v___x_6844_ = lean_array_set(v_matcherLevels_6509_, v_val_6843_, v_fst_6840_);
v___y_6613_ = v_fst_6841_;
v___y_6614_ = v_numDiscrEqs_6815_;
v___y_6615_ = v_snd_6842_;
v___y_6616_ = v_fst_6839_;
v___y_6617_ = v_a_6826_;
v___y_6618_ = v_a_6823_;
v___y_6619_ = v___x_6821_;
v_matcherLevels_6620_ = v___x_6844_;
v___y_6621_ = v___y_6816_;
v___y_6622_ = v___y_6817_;
v___y_6623_ = v___y_6818_;
v___y_6624_ = v___y_6819_;
goto v___jp_6612_;
}
}
else
{
lean_object* v_a_6845_; lean_object* v___x_6847_; uint8_t v_isShared_6848_; uint8_t v_isSharedCheck_6852_; 
lean_dec(v_a_6826_);
lean_dec(v_a_6823_);
lean_dec(v___y_6819_);
lean_dec_ref(v___y_6818_);
lean_dec(v___y_6817_);
lean_dec_ref(v___y_6816_);
lean_dec(v_numDiscrEqs_6815_);
lean_dec_ref(v_remaining_6514_);
lean_dec_ref(v_alts_6513_);
lean_dec(v_matcherName_6508_);
lean_dec_ref(v_toMatcherInfo_6507_);
lean_dec_ref(v_onRemaining_6499_);
lean_dec_ref(v_onAlt_6498_);
lean_dec_ref(v_matcherApp_6493_);
v_a_6845_ = lean_ctor_get(v___x_6831_, 0);
v_isSharedCheck_6852_ = !lean_is_exclusive(v___x_6831_);
if (v_isSharedCheck_6852_ == 0)
{
v___x_6847_ = v___x_6831_;
v_isShared_6848_ = v_isSharedCheck_6852_;
goto v_resetjp_6846_;
}
else
{
lean_inc(v_a_6845_);
lean_dec(v___x_6831_);
v___x_6847_ = lean_box(0);
v_isShared_6848_ = v_isSharedCheck_6852_;
goto v_resetjp_6846_;
}
v_resetjp_6846_:
{
lean_object* v___x_6850_; 
if (v_isShared_6848_ == 0)
{
v___x_6850_ = v___x_6847_;
goto v_reusejp_6849_;
}
else
{
lean_object* v_reuseFailAlloc_6851_; 
v_reuseFailAlloc_6851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6851_, 0, v_a_6845_);
v___x_6850_ = v_reuseFailAlloc_6851_;
goto v_reusejp_6849_;
}
v_reusejp_6849_:
{
return v___x_6850_;
}
}
}
}
else
{
lean_object* v_a_6853_; lean_object* v___x_6855_; uint8_t v_isShared_6856_; uint8_t v_isSharedCheck_6860_; 
lean_dec(v_a_6823_);
lean_dec(v___y_6819_);
lean_dec_ref(v___y_6818_);
lean_dec(v___y_6817_);
lean_dec_ref(v___y_6816_);
lean_dec(v_numDiscrEqs_6815_);
lean_dec_ref(v_remaining_6514_);
lean_dec_ref(v_alts_6513_);
lean_dec(v_matcherName_6508_);
lean_dec_ref(v_toMatcherInfo_6507_);
lean_dec_ref(v_onRemaining_6499_);
lean_dec_ref(v_onAlt_6498_);
lean_dec_ref(v_onMotive_6497_);
lean_dec_ref(v_matcherApp_6493_);
v_a_6853_ = lean_ctor_get(v___x_6825_, 0);
v_isSharedCheck_6860_ = !lean_is_exclusive(v___x_6825_);
if (v_isSharedCheck_6860_ == 0)
{
v___x_6855_ = v___x_6825_;
v_isShared_6856_ = v_isSharedCheck_6860_;
goto v_resetjp_6854_;
}
else
{
lean_inc(v_a_6853_);
lean_dec(v___x_6825_);
v___x_6855_ = lean_box(0);
v_isShared_6856_ = v_isSharedCheck_6860_;
goto v_resetjp_6854_;
}
v_resetjp_6854_:
{
lean_object* v___x_6858_; 
if (v_isShared_6856_ == 0)
{
v___x_6858_ = v___x_6855_;
goto v_reusejp_6857_;
}
else
{
lean_object* v_reuseFailAlloc_6859_; 
v_reuseFailAlloc_6859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6859_, 0, v_a_6853_);
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
else
{
lean_object* v_a_6861_; lean_object* v___x_6863_; uint8_t v_isShared_6864_; uint8_t v_isSharedCheck_6868_; 
lean_dec(v___y_6819_);
lean_dec_ref(v___y_6818_);
lean_dec(v___y_6817_);
lean_dec_ref(v___y_6816_);
lean_dec(v_numDiscrEqs_6815_);
lean_dec_ref(v_remaining_6514_);
lean_dec_ref(v_alts_6513_);
lean_dec(v_matcherName_6508_);
lean_dec_ref(v_toMatcherInfo_6507_);
lean_dec_ref(v_onRemaining_6499_);
lean_dec_ref(v_onAlt_6498_);
lean_dec_ref(v_onMotive_6497_);
lean_dec_ref(v_onParams_6496_);
lean_dec_ref(v_matcherApp_6493_);
v_a_6861_ = lean_ctor_get(v___x_6822_, 0);
v_isSharedCheck_6868_ = !lean_is_exclusive(v___x_6822_);
if (v_isSharedCheck_6868_ == 0)
{
v___x_6863_ = v___x_6822_;
v_isShared_6864_ = v_isSharedCheck_6868_;
goto v_resetjp_6862_;
}
else
{
lean_inc(v_a_6861_);
lean_dec(v___x_6822_);
v___x_6863_ = lean_box(0);
v_isShared_6864_ = v_isSharedCheck_6868_;
goto v_resetjp_6862_;
}
v_resetjp_6862_:
{
lean_object* v___x_6866_; 
if (v_isShared_6864_ == 0)
{
v___x_6866_ = v___x_6863_;
goto v_reusejp_6865_;
}
else
{
lean_object* v_reuseFailAlloc_6867_; 
v_reuseFailAlloc_6867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6867_, 0, v_a_6861_);
v___x_6866_ = v_reuseFailAlloc_6867_;
goto v_reusejp_6865_;
}
v_reusejp_6865_:
{
return v___x_6866_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed(lean_object* v_matcherApp_6888_, lean_object* v_useSplitter_6889_, lean_object* v_addEqualities_6890_, lean_object* v_onParams_6891_, lean_object* v_onMotive_6892_, lean_object* v_onAlt_6893_, lean_object* v_onRemaining_6894_, lean_object* v___y_6895_, lean_object* v___y_6896_, lean_object* v___y_6897_, lean_object* v___y_6898_, lean_object* v___y_6899_){
_start:
{
uint8_t v_useSplitter_boxed_6900_; uint8_t v_addEqualities_boxed_6901_; lean_object* v_res_6902_; 
v_useSplitter_boxed_6900_ = lean_unbox(v_useSplitter_6889_);
v_addEqualities_boxed_6901_ = lean_unbox(v_addEqualities_6890_);
v_res_6902_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(v_matcherApp_6888_, v_useSplitter_boxed_6900_, v_addEqualities_boxed_6901_, v_onParams_6891_, v_onMotive_6892_, v_onAlt_6893_, v_onRemaining_6894_, v___y_6895_, v___y_6896_, v___y_6897_, v___y_6898_);
return v_res_6902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType(lean_object* v_matcherApp_6908_, lean_object* v_a_6909_, lean_object* v_a_6910_, lean_object* v_a_6911_, lean_object* v_a_6912_){
_start:
{
lean_object* v_toMatcherInfo_6914_; lean_object* v_matcherName_6915_; lean_object* v_matcherLevels_6916_; lean_object* v_params_6917_; lean_object* v_alts_6918_; lean_object* v_remaining_6919_; lean_object* v___f_6920_; lean_object* v___f_6921_; lean_object* v_nExtra_6922_; uint8_t v___x_6923_; lean_object* v___f_6924_; uint8_t v___x_6925_; lean_object* v___x_6926_; lean_object* v___x_6927_; lean_object* v___f_6928_; lean_object* v___x_6929_; 
v_toMatcherInfo_6914_ = lean_ctor_get(v_matcherApp_6908_, 0);
v_matcherName_6915_ = lean_ctor_get(v_matcherApp_6908_, 1);
v_matcherLevels_6916_ = lean_ctor_get(v_matcherApp_6908_, 2);
v_params_6917_ = lean_ctor_get(v_matcherApp_6908_, 3);
v_alts_6918_ = lean_ctor_get(v_matcherApp_6908_, 6);
v_remaining_6919_ = lean_ctor_get(v_matcherApp_6908_, 7);
v___f_6920_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__0));
v___f_6921_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__1));
v_nExtra_6922_ = lean_array_get_size(v_remaining_6919_);
v___x_6923_ = 1;
v___f_6924_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__2));
v___x_6925_ = 0;
v___x_6926_ = lean_box(v___x_6925_);
v___x_6927_ = lean_box(v___x_6923_);
lean_inc_ref(v_matcherLevels_6916_);
lean_inc_ref(v_params_6917_);
lean_inc(v_matcherName_6915_);
lean_inc_ref(v_toMatcherInfo_6914_);
lean_inc_ref(v_alts_6918_);
v___f_6928_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed), 15, 8);
lean_closure_set(v___f_6928_, 0, v_nExtra_6922_);
lean_closure_set(v___f_6928_, 1, v___x_6926_);
lean_closure_set(v___f_6928_, 2, v___x_6927_);
lean_closure_set(v___f_6928_, 3, v_alts_6918_);
lean_closure_set(v___f_6928_, 4, v_toMatcherInfo_6914_);
lean_closure_set(v___f_6928_, 5, v_matcherName_6915_);
lean_closure_set(v___f_6928_, 6, v_params_6917_);
lean_closure_set(v___f_6928_, 7, v_matcherLevels_6916_);
v___x_6929_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(v_matcherApp_6908_, v___x_6923_, v___x_6925_, v___f_6920_, v___f_6928_, v___f_6924_, v___f_6921_, v_a_6909_, v_a_6910_, v_a_6911_, v_a_6912_);
return v___x_6929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___boxed(lean_object* v_matcherApp_6930_, lean_object* v_a_6931_, lean_object* v_a_6932_, lean_object* v_a_6933_, lean_object* v_a_6934_, lean_object* v_a_6935_){
_start:
{
lean_object* v_res_6936_; 
v_res_6936_ = l_Lean_Meta_MatcherApp_inferMatchType(v_matcherApp_6930_, v_a_6931_, v_a_6932_, v_a_6933_, v_a_6934_);
return v_res_6936_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(lean_object* v_a_6937_, lean_object* v_termAlt_6938_, lean_object* v_inst_6939_, lean_object* v_R_6940_, lean_object* v_a_6941_, lean_object* v_b_6942_, lean_object* v_c_6943_, lean_object* v___y_6944_, lean_object* v___y_6945_, lean_object* v___y_6946_, lean_object* v___y_6947_){
_start:
{
lean_object* v___x_6949_; 
v___x_6949_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_6937_, v_termAlt_6938_, v_a_6941_, v_b_6942_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
return v___x_6949_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___boxed(lean_object* v_a_6950_, lean_object* v_termAlt_6951_, lean_object* v_inst_6952_, lean_object* v_R_6953_, lean_object* v_a_6954_, lean_object* v_b_6955_, lean_object* v_c_6956_, lean_object* v___y_6957_, lean_object* v___y_6958_, lean_object* v___y_6959_, lean_object* v___y_6960_, lean_object* v___y_6961_){
_start:
{
lean_object* v_res_6962_; 
v_res_6962_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(v_a_6950_, v_termAlt_6951_, v_inst_6952_, v_R_6953_, v_a_6954_, v_b_6955_, v_c_6956_, v___y_6957_, v___y_6958_, v___y_6959_, v___y_6960_);
lean_dec(v___y_6960_);
lean_dec_ref(v___y_6959_);
lean_dec(v___y_6958_);
lean_dec_ref(v___y_6957_);
return v_res_6962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(lean_object* v_00_u03b1_6963_, lean_object* v_fvars_6964_, lean_object* v_names_6965_, lean_object* v_k_6966_, lean_object* v___y_6967_, lean_object* v___y_6968_, lean_object* v___y_6969_, lean_object* v___y_6970_){
_start:
{
lean_object* v___x_6972_; 
v___x_6972_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_fvars_6964_, v_names_6965_, v_k_6966_, v___y_6967_, v___y_6968_, v___y_6969_, v___y_6970_);
return v___x_6972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___boxed(lean_object* v_00_u03b1_6973_, lean_object* v_fvars_6974_, lean_object* v_names_6975_, lean_object* v_k_6976_, lean_object* v___y_6977_, lean_object* v___y_6978_, lean_object* v___y_6979_, lean_object* v___y_6980_, lean_object* v___y_6981_){
_start:
{
lean_object* v_res_6982_; 
v_res_6982_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(v_00_u03b1_6973_, v_fvars_6974_, v_names_6975_, v_k_6976_, v___y_6977_, v___y_6978_, v___y_6979_, v___y_6980_);
lean_dec_ref(v_names_6975_);
lean_dec_ref(v_fvars_6974_);
return v_res_6982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(lean_object* v_00_u03b1_6983_, lean_object* v_origAltType_6984_, lean_object* v_altInfo_6985_, lean_object* v_k_6986_, lean_object* v___y_6987_, lean_object* v___y_6988_, lean_object* v___y_6989_, lean_object* v___y_6990_){
_start:
{
lean_object* v___x_6992_; 
v___x_6992_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v_origAltType_6984_, v_altInfo_6985_, v_k_6986_, v___y_6987_, v___y_6988_, v___y_6989_, v___y_6990_);
return v___x_6992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___boxed(lean_object* v_00_u03b1_6993_, lean_object* v_origAltType_6994_, lean_object* v_altInfo_6995_, lean_object* v_k_6996_, lean_object* v___y_6997_, lean_object* v___y_6998_, lean_object* v___y_6999_, lean_object* v___y_7000_, lean_object* v___y_7001_){
_start:
{
lean_object* v_res_7002_; 
v_res_7002_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(v_00_u03b1_6993_, v_origAltType_6994_, v_altInfo_6995_, v_k_6996_, v___y_6997_, v___y_6998_, v___y_6999_, v___y_7000_);
return v_res_7002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(lean_object* v_declName_7003_, lean_object* v___y_7004_, lean_object* v___y_7005_, lean_object* v___y_7006_, lean_object* v___y_7007_){
_start:
{
lean_object* v___x_7009_; 
v___x_7009_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_declName_7003_, v___y_7007_);
return v___x_7009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___boxed(lean_object* v_declName_7010_, lean_object* v___y_7011_, lean_object* v___y_7012_, lean_object* v___y_7013_, lean_object* v___y_7014_, lean_object* v___y_7015_){
_start:
{
lean_object* v_res_7016_; 
v_res_7016_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(v_declName_7010_, v___y_7011_, v___y_7012_, v___y_7013_, v___y_7014_);
lean_dec(v___y_7014_);
lean_dec_ref(v___y_7013_);
lean_dec(v___y_7012_);
lean_dec_ref(v___y_7011_);
return v_res_7016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(size_t v_sz_7017_, size_t v_i_7018_, lean_object* v_bs_7019_, lean_object* v___y_7020_, lean_object* v___y_7021_, lean_object* v___y_7022_, lean_object* v___y_7023_){
_start:
{
lean_object* v___x_7025_; 
v___x_7025_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_7017_, v_i_7018_, v_bs_7019_, v___y_7020_, v___y_7022_, v___y_7023_);
return v___x_7025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___boxed(lean_object* v_sz_7026_, lean_object* v_i_7027_, lean_object* v_bs_7028_, lean_object* v___y_7029_, lean_object* v___y_7030_, lean_object* v___y_7031_, lean_object* v___y_7032_, lean_object* v___y_7033_){
_start:
{
size_t v_sz_boxed_7034_; size_t v_i_boxed_7035_; lean_object* v_res_7036_; 
v_sz_boxed_7034_ = lean_unbox_usize(v_sz_7026_);
lean_dec(v_sz_7026_);
v_i_boxed_7035_ = lean_unbox_usize(v_i_7027_);
lean_dec(v_i_7027_);
v_res_7036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(v_sz_boxed_7034_, v_i_boxed_7035_, v_bs_7028_, v___y_7029_, v___y_7030_, v___y_7031_, v___y_7032_);
lean_dec(v___y_7032_);
lean_dec_ref(v___y_7031_);
lean_dec(v___y_7030_);
return v_res_7036_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(lean_object* v_upperBound_7037_, lean_object* v_onAlt_7038_, lean_object* v_extraEqualities_7039_, lean_object* v_inst_7040_, lean_object* v_R_7041_, lean_object* v_a_7042_, lean_object* v_b_7043_, lean_object* v_c_7044_, lean_object* v___y_7045_, lean_object* v___y_7046_, lean_object* v___y_7047_, lean_object* v___y_7048_){
_start:
{
lean_object* v___x_7050_; 
v___x_7050_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v_upperBound_7037_, v_onAlt_7038_, v_extraEqualities_7039_, v_a_7042_, v_b_7043_, v___y_7045_, v___y_7046_, v___y_7047_, v___y_7048_);
return v___x_7050_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___boxed(lean_object* v_upperBound_7051_, lean_object* v_onAlt_7052_, lean_object* v_extraEqualities_7053_, lean_object* v_inst_7054_, lean_object* v_R_7055_, lean_object* v_a_7056_, lean_object* v_b_7057_, lean_object* v_c_7058_, lean_object* v___y_7059_, lean_object* v___y_7060_, lean_object* v___y_7061_, lean_object* v___y_7062_, lean_object* v___y_7063_){
_start:
{
lean_object* v_res_7064_; 
v_res_7064_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(v_upperBound_7051_, v_onAlt_7052_, v_extraEqualities_7053_, v_inst_7054_, v_R_7055_, v_a_7056_, v_b_7057_, v_c_7058_, v___y_7059_, v___y_7060_, v___y_7061_, v___y_7062_);
lean_dec(v_upperBound_7051_);
return v_res_7064_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(lean_object* v_upperBound_7065_, lean_object* v_onAlt_7066_, uint8_t v_useSplitter_7067_, lean_object* v_extraEqualities_7068_, lean_object* v_numDiscrEqs_7069_, lean_object* v_inst_7070_, lean_object* v_R_7071_, lean_object* v_a_7072_, lean_object* v_b_7073_, lean_object* v_c_7074_, lean_object* v___y_7075_, lean_object* v___y_7076_, lean_object* v___y_7077_, lean_object* v___y_7078_){
_start:
{
lean_object* v___x_7080_; 
v___x_7080_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v_upperBound_7065_, v_onAlt_7066_, v_useSplitter_7067_, v_extraEqualities_7068_, v_numDiscrEqs_7069_, v_a_7072_, v_b_7073_, v___y_7075_, v___y_7076_, v___y_7077_, v___y_7078_);
return v___x_7080_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___boxed(lean_object* v_upperBound_7081_, lean_object* v_onAlt_7082_, lean_object* v_useSplitter_7083_, lean_object* v_extraEqualities_7084_, lean_object* v_numDiscrEqs_7085_, lean_object* v_inst_7086_, lean_object* v_R_7087_, lean_object* v_a_7088_, lean_object* v_b_7089_, lean_object* v_c_7090_, lean_object* v___y_7091_, lean_object* v___y_7092_, lean_object* v___y_7093_, lean_object* v___y_7094_, lean_object* v___y_7095_){
_start:
{
uint8_t v_useSplitter_boxed_7096_; lean_object* v_res_7097_; 
v_useSplitter_boxed_7096_ = lean_unbox(v_useSplitter_7083_);
v_res_7097_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(v_upperBound_7081_, v_onAlt_7082_, v_useSplitter_boxed_7096_, v_extraEqualities_7084_, v_numDiscrEqs_7085_, v_inst_7086_, v_R_7087_, v_a_7088_, v_b_7089_, v_c_7090_, v___y_7091_, v___y_7092_, v___y_7093_, v___y_7094_);
lean_dec(v_upperBound_7081_);
return v_res_7097_;
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
