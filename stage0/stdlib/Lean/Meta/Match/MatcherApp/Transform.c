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
uint8_t v___x_4705__boxed_235_; uint8_t v_refined_boxed_236_; lean_object* v_res_237_; 
v___x_4705__boxed_235_ = lean_unbox(v___x_224_);
v_refined_boxed_236_ = lean_unbox(v_refined_226_);
v_res_237_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(v_alt_223_, v___x_4705__boxed_235_, v_xs_225_, v_refined_boxed_236_, v_unrefinedArgType_227_, v_x_228_, v_x_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
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
v___x_319_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_a_316_, v___x_317_, v___f_309_, v___x_318_, v___x_318_, v___y_314_, v___y_313_, v___y_312_, v___y_311_);
return v___x_319_;
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
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
lean_dec_ref(v___y_333_);
v___x_335_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2);
v___x_336_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_335_, v___y_332_, v___y_331_, v___y_330_, v___y_329_);
v___y_311_ = v___y_329_;
v___y_312_ = v___y_330_;
v___y_313_ = v___y_331_;
v___y_314_ = v___y_332_;
v___y_315_ = v___x_336_;
goto v___jp_310_;
}
else
{
v___y_311_ = v___y_329_;
v___y_312_ = v___y_330_;
v___y_313_ = v___y_331_;
v___y_314_ = v___y_332_;
v___y_315_ = v___y_333_;
goto v___jp_310_;
}
}
v___jp_337_:
{
lean_object* v___x_338_; 
v___x_338_ = l_Lean_Meta_instantiateForall(v_binderType_298_, v_xs_300_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
lean_dec_ref(v_xs_300_);
if (lean_obj_tag(v___x_338_) == 0)
{
v___y_311_ = v___y_305_;
v___y_312_ = v___y_304_;
v___y_313_ = v___y_303_;
v___y_314_ = v___y_302_;
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
v___y_330_ = v___y_304_;
v___y_331_ = v___y_303_;
v___y_332_ = v___y_302_;
v___y_333_ = v___x_338_;
v___y_334_ = v___x_341_;
goto v___jp_328_;
}
else
{
lean_dec(v_a_339_);
v___y_329_ = v___y_305_;
v___y_330_ = v___y_304_;
v___y_331_ = v___y_303_;
v___y_332_ = v___y_302_;
v___y_333_ = v___x_338_;
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
uint8_t v___x_4929__boxed_372_; uint8_t v_refined_boxed_373_; lean_object* v_res_374_; 
v___x_4929__boxed_372_ = lean_unbox(v___x_360_);
v_refined_boxed_373_ = lean_unbox(v_refined_361_);
v_res_374_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(v___x_4929__boxed_372_, v_refined_boxed_373_, v_unrefinedArgType_362_, v_binderType_363_, v_numParams_364_, v_xs_365_, v_alt_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
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
return v___x_395_;
}
else
{
lean_object* v___x_396_; 
v___x_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_396_, 0, v_alts_384_);
return v___x_396_;
}
}
else
{
lean_object* v___x_397_; 
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
lean_inc_n(v_numParams_403_, 2);
lean_inc_ref(v_unrefinedArgType_381_);
v___f_406_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed), 12, 5);
lean_closure_set(v___f_406_, 0, v___x_404_);
lean_closure_set(v___f_406_, 1, v___x_405_);
lean_closure_set(v___f_406_, 2, v_unrefinedArgType_381_);
lean_closure_set(v___f_406_, 3, v_binderType_399_);
lean_closure_set(v___f_406_, 4, v_numParams_403_);
v___x_407_ = 0;
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
return v___x_427_;
}
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
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
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
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
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
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
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0(lean_object* v_matcherApp_574_, lean_object* v_e_575_, lean_object* v_discrs_576_, lean_object* v_toMatcherInfo_577_, lean_object* v_alts_578_, lean_object* v_remaining_579_, lean_object* v_matcherName_580_, lean_object* v_params_581_, lean_object* v_matcherLevels_582_, lean_object* v_motiveArgs_583_, lean_object* v_motiveBody_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
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
lean_dec_ref(v_params_581_);
lean_dec(v_matcherName_580_);
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
v___x_606_ = lean_infer_type(v___y_598_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref(v___x_606_);
v___x_608_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_574_);
v___x_609_ = lean_unsigned_to_nat(0u);
v___x_610_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(v___y_597_, v_a_607_, v___x_608_, v___y_593_, v___y_591_, v___x_609_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
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
v___x_618_ = l_Array_append___redArg(v___x_617_, v___y_596_);
v___x_619_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_619_, 0, v___y_592_);
lean_ctor_set(v___x_619_, 1, v___y_600_);
lean_ctor_set(v___x_619_, 2, v___y_599_);
lean_ctor_set(v___x_619_, 3, v___y_601_);
lean_ctor_set(v___x_619_, 4, v___y_594_);
lean_ctor_set(v___x_619_, 5, v___y_595_);
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
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec_ref(v___y_595_);
lean_dec_ref(v___y_594_);
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
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec_ref(v___y_597_);
lean_dec_ref(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec_ref(v___y_593_);
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
v___x_657_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_583_, v___y_643_, v___x_654_, v___x_655_, v___x_654_, v___x_655_, v___x_656_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc_n(v_a_658_, 2);
lean_dec_ref(v___x_657_);
lean_inc_ref(v_matcherLevels_649_);
v___x_659_ = lean_array_to_list(v_matcherLevels_649_);
lean_inc(v___y_647_);
v___x_660_ = l_Lean_mkConst(v___y_647_, v___x_659_);
v___x_661_ = l_Lean_mkAppN(v___x_660_, v___y_648_);
v___x_662_ = l_Lean_Expr_app___override(v___x_661_, v_a_658_);
v___x_663_ = l_Lean_mkAppN(v___x_662_, v___y_644_);
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
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec_ref(v___y_644_);
lean_dec_ref(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec_ref(v_e_575_);
lean_dec_ref(v_matcherApp_574_);
v___x_667_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1);
v___x_668_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_667_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
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
v___y_592_ = v___y_642_;
v___y_593_ = v___y_641_;
v___y_594_ = v_a_658_;
v___y_595_ = v___y_644_;
v___y_596_ = v___y_645_;
v___y_597_ = v___y_646_;
v___y_598_ = v___x_663_;
v___y_599_ = v_matcherLevels_649_;
v___y_600_ = v___y_647_;
v___y_601_ = v___y_648_;
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
lean_dec_ref(v_matcherLevels_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec_ref(v___y_644_);
lean_dec_ref(v___y_642_);
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
lean_dec_ref(v_matcherLevels_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec_ref(v___y_644_);
lean_dec_ref(v___y_642_);
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
lean_inc_n(v_a_699_, 2);
lean_dec_ref(v___x_698_);
v___x_700_ = lean_array_get_size(v_discrs_576_);
v___x_701_ = l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(v_discrs_576_, v_motiveArgs_583_, v___x_700_, v_a_699_);
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
v___y_642_ = v_toMatcherInfo_577_;
v___y_643_ = v_a_704_;
v___y_644_ = v_discrs_576_;
v___y_645_ = v_remaining_579_;
v___y_646_ = v_a_699_;
v___y_647_ = v_matcherName_580_;
v___y_648_ = v_params_581_;
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
lean_inc_n(v_a_705_, 2);
lean_dec_ref(v___x_702_);
v_val_706_ = lean_ctor_get(v_uElimPos_x3f_703_, 0);
v___x_707_ = l_Lean_Meta_getLevel(v_a_705_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_709_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref(v___x_707_);
v___x_709_ = lean_array_set(v_matcherLevels_582_, v_val_706_, v_a_708_);
v___y_641_ = v_alts_578_;
v___y_642_ = v_toMatcherInfo_577_;
v___y_643_ = v_a_705_;
v___y_644_ = v_discrs_576_;
v___y_645_ = v_remaining_579_;
v___y_646_ = v_a_699_;
v___y_647_ = v_matcherName_580_;
v___y_648_ = v_params_581_;
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
lean_dec_ref(v_matcherLevels_582_);
lean_dec_ref(v_params_581_);
lean_dec(v_matcherName_580_);
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
lean_dec_ref(v_matcherLevels_582_);
lean_dec_ref(v_params_581_);
lean_dec(v_matcherName_580_);
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
lean_dec_ref(v_motiveBody_584_);
lean_dec_ref(v_matcherLevels_582_);
lean_dec_ref(v_params_581_);
lean_dec(v_matcherName_580_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___boxed(lean_object* v_matcherApp_753_, lean_object* v_e_754_, lean_object* v_discrs_755_, lean_object* v_toMatcherInfo_756_, lean_object* v_alts_757_, lean_object* v_remaining_758_, lean_object* v_matcherName_759_, lean_object* v_params_760_, lean_object* v_matcherLevels_761_, lean_object* v_motiveArgs_762_, lean_object* v_motiveBody_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_Meta_MatcherApp_addArg___lam__0(v_matcherApp_753_, v_e_754_, v_discrs_755_, v_toMatcherInfo_756_, v_alts_757_, v_remaining_758_, v_matcherName_759_, v_params_760_, v_matcherLevels_761_, v_motiveArgs_762_, v_motiveBody_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
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
lean_closure_set(v___f_785_, 6, v_matcherName_778_);
lean_closure_set(v___f_785_, 7, v_params_780_);
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
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
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
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
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
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
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
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
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
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
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
uint8_t v___x_4259__boxed_985_; uint8_t v___x_4260__boxed_986_; uint8_t v___x_4261__boxed_987_; lean_object* v_res_988_; 
v___x_4259__boxed_985_ = lean_unbox(v___x_974_);
v___x_4260__boxed_986_ = lean_unbox(v___x_975_);
v___x_4261__boxed_987_ = lean_unbox(v___x_976_);
v_res_988_ = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0(v___x_4259__boxed_985_, v___x_4260__boxed_986_, v___x_4261__boxed_987_, v_a_977_, v_fvs_978_, v_body_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
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
lean_inc_n(v_a_1006_, 2);
v___f_1010_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1010_, 0, v___x_1007_);
lean_closure_set(v___f_1010_, 1, v___x_1008_);
lean_closure_set(v___f_1010_, 2, v___x_1009_);
lean_closure_set(v___f_1010_, 3, v_a_1006_);
v_b_1011_ = lean_array_fget_borrowed(v_bs_990_, v_i_991_);
v___x_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1012_, 0, v_a_1006_);
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
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
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
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
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
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
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
lean_object* v___y_1119_; lean_object* v___y_1120_; uint8_t v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v_matcherLevels_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___x_1217_; lean_object* v___x_1218_; uint8_t v___x_1219_; 
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
v___x_1126_ = lean_infer_type(v___y_1120_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1128_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
lean_inc(v_a_1127_);
lean_dec_ref(v___x_1126_);
v___x_1128_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg(v_a_1127_, v___y_1119_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
return v___x_1128_;
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_dec_ref(v___y_1119_);
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
v___x_1150_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_1111_, v___y_1141_, v___x_1147_, v___x_1148_, v___x_1147_, v___x_1148_, v___x_1149_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_a_1151_);
lean_dec_ref(v___x_1150_);
v___x_1152_ = lean_array_to_list(v_matcherLevels_1142_);
v___x_1153_ = l_Lean_mkConst(v___y_1140_, v___x_1152_);
v___x_1154_ = l_Lean_mkAppN(v___x_1153_, v___y_1138_);
v___x_1155_ = l_Lean_Expr_app___override(v___x_1154_, v_a_1151_);
v___x_1156_ = l_Lean_mkAppN(v___x_1155_, v___y_1139_);
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
v___y_1119_ = v___f_1104_;
v___y_1120_ = v___x_1156_;
v___y_1121_ = v___x_1147_;
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
lean_dec_ref(v_matcherLevels_1142_);
lean_dec(v___y_1140_);
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
v___x_1192_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(v_discrs_1105_, v_motiveArgs_1111_, v___x_1191_, v_e_1106_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1194_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc_n(v_a_1193_, 2);
lean_dec_ref(v___x_1192_);
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
v___y_1139_ = v_discrs_1105_;
v___y_1140_ = v_matcherName_1109_;
v___y_1141_ = v_a_1196_;
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
v___y_1139_ = v_discrs_1105_;
v___y_1140_ = v_matcherName_1109_;
v___y_1141_ = v_a_1197_;
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
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
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
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
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
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
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
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
lean_dec(v_a_1336_);
lean_dec_ref(v_a_1335_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(lean_object* v_lctx_1341_, lean_object* v_x_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v_keyedConfig_1348_; uint8_t v_trackZetaDelta_1349_; lean_object* v_zetaDeltaSet_1350_; lean_object* v_localInstances_1351_; lean_object* v_defEqCtx_x3f_1352_; lean_object* v_synthPendingDepth_1353_; lean_object* v_canUnfold_x3f_1354_; uint8_t v_univApprox_1355_; uint8_t v_inTypeClassResolution_1356_; uint8_t v_cacheInferType_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
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
lean_inc(v_canUnfold_x3f_1354_);
lean_inc(v_synthPendingDepth_1353_);
lean_inc(v_defEqCtx_x3f_1352_);
lean_inc_ref(v_localInstances_1351_);
lean_inc(v_zetaDeltaSet_1350_);
lean_inc_ref(v_keyedConfig_1348_);
v___x_1358_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1358_, 0, v_keyedConfig_1348_);
lean_ctor_set(v___x_1358_, 1, v_zetaDeltaSet_1350_);
lean_ctor_set(v___x_1358_, 2, v_lctx_1341_);
lean_ctor_set(v___x_1358_, 3, v_localInstances_1351_);
lean_ctor_set(v___x_1358_, 4, v_defEqCtx_x3f_1352_);
lean_ctor_set(v___x_1358_, 5, v_synthPendingDepth_1353_);
lean_ctor_set(v___x_1358_, 6, v_canUnfold_x3f_1354_);
lean_ctor_set_uint8(v___x_1358_, sizeof(void*)*7, v_trackZetaDelta_1349_);
lean_ctor_set_uint8(v___x_1358_, sizeof(void*)*7 + 1, v_univApprox_1355_);
lean_ctor_set_uint8(v___x_1358_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1356_);
lean_ctor_set_uint8(v___x_1358_, sizeof(void*)*7 + 3, v_cacheInferType_1357_);
lean_inc(v___y_1346_);
lean_inc_ref(v___y_1345_);
lean_inc(v___y_1344_);
v___x_1359_ = lean_apply_5(v_x_1342_, v___x_1358_, v___y_1344_, v___y_1345_, v___y_1346_, lean_box(0));
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg___boxed(lean_object* v_lctx_1360_, lean_object* v_x_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1360_, v_x_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(lean_object* v_00_u03b1_1368_, lean_object* v_lctx_1369_, lean_object* v_x_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1369_, v_x_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___boxed(lean_object* v_00_u03b1_1377_, lean_object* v_lctx_1378_, lean_object* v_x_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(v_00_u03b1_1377_, v_lctx_1378_, v_x_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(lean_object* v_as_1386_, size_t v_i_1387_, size_t v_stop_1388_, lean_object* v_b_1389_){
_start:
{
uint8_t v___x_1390_; 
v___x_1390_ = lean_usize_dec_eq(v_i_1387_, v_stop_1388_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; lean_object* v_fst_1392_; lean_object* v_snd_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; size_t v___x_1396_; size_t v___x_1397_; 
v___x_1391_ = lean_array_uget_borrowed(v_as_1386_, v_i_1387_);
v_fst_1392_ = lean_ctor_get(v___x_1391_, 0);
v_snd_1393_ = lean_ctor_get(v___x_1391_, 1);
v___x_1394_ = l_Lean_Expr_fvarId_x21(v_fst_1392_);
lean_inc(v_snd_1393_);
v___x_1395_ = l_Lean_LocalContext_setUserName(v_b_1389_, v___x_1394_, v_snd_1393_);
v___x_1396_ = ((size_t)1ULL);
v___x_1397_ = lean_usize_add(v_i_1387_, v___x_1396_);
v_i_1387_ = v___x_1397_;
v_b_1389_ = v___x_1395_;
goto _start;
}
else
{
return v_b_1389_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1___boxed(lean_object* v_as_1399_, lean_object* v_i_1400_, lean_object* v_stop_1401_, lean_object* v_b_1402_){
_start:
{
size_t v_i_boxed_1403_; size_t v_stop_boxed_1404_; lean_object* v_res_1405_; 
v_i_boxed_1403_ = lean_unbox_usize(v_i_1400_);
lean_dec(v_i_1400_);
v_stop_boxed_1404_ = lean_unbox_usize(v_stop_1401_);
lean_dec(v_stop_1401_);
v_res_1405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(v_as_1399_, v_i_boxed_1403_, v_stop_boxed_1404_, v_b_1402_);
lean_dec_ref(v_as_1399_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(lean_object* v_fvars_1406_, lean_object* v_names_1407_, lean_object* v_k_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v_lctx_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v_lctx_1414_ = lean_ctor_get(v_a_1409_, 2);
v___x_1415_ = l_Array_zip___redArg(v_fvars_1406_, v_names_1407_);
v___x_1416_ = lean_unsigned_to_nat(0u);
v___x_1417_ = lean_array_get_size(v___x_1415_);
v___x_1418_ = lean_nat_dec_lt(v___x_1416_, v___x_1417_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; 
lean_dec_ref(v___x_1415_);
lean_inc_ref(v_lctx_1414_);
v___x_1419_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1414_, v_k_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_);
return v___x_1419_;
}
else
{
uint8_t v___x_1420_; 
v___x_1420_ = lean_nat_dec_le(v___x_1417_, v___x_1417_);
if (v___x_1420_ == 0)
{
if (v___x_1418_ == 0)
{
lean_object* v___x_1421_; 
lean_dec_ref(v___x_1415_);
lean_inc_ref(v_lctx_1414_);
v___x_1421_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1414_, v_k_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_);
return v___x_1421_;
}
else
{
size_t v___x_1422_; size_t v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1422_ = ((size_t)0ULL);
v___x_1423_ = lean_usize_of_nat(v___x_1417_);
lean_inc_ref(v_lctx_1414_);
v___x_1424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(v___x_1415_, v___x_1422_, v___x_1423_, v_lctx_1414_);
lean_dec_ref(v___x_1415_);
v___x_1425_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v___x_1424_, v_k_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_);
return v___x_1425_;
}
}
else
{
size_t v___x_1426_; size_t v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1426_ = ((size_t)0ULL);
v___x_1427_ = lean_usize_of_nat(v___x_1417_);
lean_inc_ref(v_lctx_1414_);
v___x_1428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(v___x_1415_, v___x_1426_, v___x_1427_, v_lctx_1414_);
lean_dec_ref(v___x_1415_);
v___x_1429_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v___x_1428_, v_k_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_);
return v___x_1429_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg___boxed(lean_object* v_fvars_1430_, lean_object* v_names_1431_, lean_object* v_k_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_1430_, v_names_1431_, v_k_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_a_1434_);
lean_dec_ref(v_a_1433_);
lean_dec_ref(v_names_1431_);
lean_dec_ref(v_fvars_1430_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl(lean_object* v_00_u03b1_1439_, lean_object* v_fvars_1440_, lean_object* v_names_1441_, lean_object* v_k_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_1440_, v_names_1441_, v_k_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___boxed(lean_object* v_00_u03b1_1449_, lean_object* v_fvars_1450_, lean_object* v_names_1451_, lean_object* v_k_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl(v_00_u03b1_1449_, v_fvars_1450_, v_names_1451_, v_k_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_);
lean_dec(v_a_1456_);
lean_dec_ref(v_a_1455_);
lean_dec(v_a_1454_);
lean_dec_ref(v_a_1453_);
lean_dec_ref(v_names_1451_);
lean_dec_ref(v_fvars_1450_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0(lean_object* v_k_1459_, lean_object* v_fvars_1460_, lean_object* v_names_1461_, lean_object* v_runInBase_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = lean_apply_2(v_runInBase_1462_, lean_box(0), v_k_1459_);
v___x_1469_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_1460_, v_names_1461_, v___x_1468_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0___boxed(lean_object* v_k_1470_, lean_object* v_fvars_1471_, lean_object* v_names_1472_, lean_object* v_runInBase_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0(v_k_1470_, v_fvars_1471_, v_names_1472_, v_runInBase_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec_ref(v_names_1472_);
lean_dec_ref(v_fvars_1471_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg(lean_object* v_inst_1480_, lean_object* v_inst_1481_, lean_object* v_fvars_1482_, lean_object* v_names_1483_, lean_object* v_k_1484_){
_start:
{
lean_object* v_toBind_1485_; lean_object* v_liftWith_1486_; lean_object* v_restoreM_1487_; lean_object* v___f_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v_toBind_1485_ = lean_ctor_get(v_inst_1481_, 1);
lean_inc(v_toBind_1485_);
lean_dec_ref(v_inst_1481_);
v_liftWith_1486_ = lean_ctor_get(v_inst_1480_, 0);
lean_inc(v_liftWith_1486_);
v_restoreM_1487_ = lean_ctor_get(v_inst_1480_, 1);
lean_inc(v_restoreM_1487_);
lean_dec_ref(v_inst_1480_);
v___f_1488_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1488_, 0, v_k_1484_);
lean_closure_set(v___f_1488_, 1, v_fvars_1482_);
lean_closure_set(v___f_1488_, 2, v_names_1483_);
v___x_1489_ = lean_apply_2(v_liftWith_1486_, lean_box(0), v___f_1488_);
v___x_1490_ = lean_apply_1(v_restoreM_1487_, lean_box(0));
v___x_1491_ = lean_apply_4(v_toBind_1485_, lean_box(0), lean_box(0), v___x_1489_, v___x_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames(lean_object* v_n_1492_, lean_object* v_inst_1493_, lean_object* v_inst_1494_, lean_object* v_00_u03b1_1495_, lean_object* v_fvars_1496_, lean_object* v_names_1497_, lean_object* v_k_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_Meta_MatcherApp_withUserNames___redArg(v_inst_1493_, v_inst_1494_, v_fvars_1496_, v_names_1497_, v_k_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0(lean_object* v_k_1500_, lean_object* v_runInBase_1501_, lean_object* v_ys_1502_, lean_object* v_args_1503_, lean_object* v___mask_1504_, lean_object* v___bodyType_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = lean_apply_2(v_k_1500_, v_ys_1502_, v_args_1503_);
lean_inc(v___y_1509_);
lean_inc_ref(v___y_1508_);
lean_inc(v___y_1507_);
lean_inc_ref(v___y_1506_);
v___x_1512_ = lean_apply_7(v_runInBase_1501_, lean_box(0), v___x_1511_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, lean_box(0));
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0___boxed(lean_object* v_k_1513_, lean_object* v_runInBase_1514_, lean_object* v_ys_1515_, lean_object* v_args_1516_, lean_object* v___mask_1517_, lean_object* v___bodyType_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0(v_k_1513_, v_runInBase_1514_, v_ys_1515_, v_args_1516_, v___mask_1517_, v___bodyType_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec_ref(v___bodyType_1518_);
lean_dec_ref(v___mask_1517_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1(lean_object* v_k_1525_, lean_object* v_origAltType_1526_, lean_object* v_altInfo_1527_, lean_object* v_runInBase_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v___f_1534_; lean_object* v___x_1535_; 
v___f_1534_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1534_, 0, v_k_1525_);
lean_closure_set(v___f_1534_, 1, v_runInBase_1528_);
v___x_1535_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_origAltType_1526_, v_altInfo_1527_, v___f_1534_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1___boxed(lean_object* v_k_1536_, lean_object* v_origAltType_1537_, lean_object* v_altInfo_1538_, lean_object* v_runInBase_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1(v_k_1536_, v_origAltType_1537_, v_altInfo_1538_, v_runInBase_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(lean_object* v_inst_1546_, lean_object* v_inst_1547_, lean_object* v_origAltType_1548_, lean_object* v_altInfo_1549_, lean_object* v_k_1550_){
_start:
{
lean_object* v_toBind_1551_; lean_object* v_liftWith_1552_; lean_object* v_restoreM_1553_; lean_object* v___f_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v_toBind_1551_ = lean_ctor_get(v_inst_1546_, 1);
lean_inc(v_toBind_1551_);
lean_dec_ref(v_inst_1546_);
v_liftWith_1552_ = lean_ctor_get(v_inst_1547_, 0);
lean_inc(v_liftWith_1552_);
v_restoreM_1553_ = lean_ctor_get(v_inst_1547_, 1);
lean_inc(v_restoreM_1553_);
lean_dec_ref(v_inst_1547_);
v___f_1554_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1___boxed), 9, 3);
lean_closure_set(v___f_1554_, 0, v_k_1550_);
lean_closure_set(v___f_1554_, 1, v_origAltType_1548_);
lean_closure_set(v___f_1554_, 2, v_altInfo_1549_);
v___x_1555_ = lean_apply_2(v_liftWith_1552_, lean_box(0), v___f_1554_);
v___x_1556_ = lean_apply_1(v_restoreM_1553_, lean_box(0));
v___x_1557_ = lean_apply_4(v_toBind_1551_, lean_box(0), lean_box(0), v___x_1555_, v___x_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27(lean_object* v_n_1558_, lean_object* v_inst_1559_, lean_object* v_inst_1560_, lean_object* v_00_u03b1_1561_, lean_object* v_origAltType_1562_, lean_object* v_altInfo_1563_, lean_object* v_k_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(v_inst_1559_, v_inst_1560_, v_origAltType_1562_, v_altInfo_1563_, v_k_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_TransformAltFVars_altParams(lean_object* v_fvars_1566_){
_start:
{
lean_object* v_args_1567_; lean_object* v_discrEqs_1568_; lean_object* v___x_1569_; 
v_args_1567_ = lean_ctor_get(v_fvars_1566_, 0);
lean_inc_ref(v_args_1567_);
v_discrEqs_1568_ = lean_ctor_get(v_fvars_1566_, 3);
lean_inc_ref(v_discrEqs_1568_);
lean_dec_ref(v_fvars_1566_);
v___x_1569_ = l_Array_append___redArg(v_args_1567_, v_discrEqs_1568_);
lean_dec_ref(v_discrEqs_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_TransformAltFVars_all(lean_object* v_fvars_1570_){
_start:
{
lean_object* v_fields_1571_; lean_object* v_overlaps_1572_; lean_object* v_discrEqs_1573_; lean_object* v_extraEqs_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v_fields_1571_ = lean_ctor_get(v_fvars_1570_, 1);
lean_inc_ref(v_fields_1571_);
v_overlaps_1572_ = lean_ctor_get(v_fvars_1570_, 2);
lean_inc_ref(v_overlaps_1572_);
v_discrEqs_1573_ = lean_ctor_get(v_fvars_1570_, 3);
lean_inc_ref(v_discrEqs_1573_);
v_extraEqs_1574_ = lean_ctor_get(v_fvars_1570_, 4);
lean_inc_ref(v_extraEqs_1574_);
lean_dec_ref(v_fvars_1570_);
v___x_1575_ = l_Array_append___redArg(v_fields_1571_, v_overlaps_1572_);
lean_dec_ref(v_overlaps_1572_);
v___x_1576_ = l_Array_append___redArg(v___x_1575_, v_discrEqs_1573_);
lean_dec_ref(v_discrEqs_1573_);
v___x_1577_ = l_Array_append___redArg(v___x_1576_, v_extraEqs_1574_);
lean_dec_ref(v_extraEqs_1574_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0(lean_object* v_inst_1578_, lean_object* v_inst_1579_, lean_object* v_x_1580_){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2);
v___x_1582_ = l_Lean_throwError___redArg(v_inst_1578_, v_inst_1579_, v___x_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed(lean_object* v_inst_1583_, lean_object* v_inst_1584_, lean_object* v_x_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__0(v_inst_1583_, v_inst_1584_, v_x_1585_);
lean_dec_ref(v_x_1585_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1(lean_object* v_inst_1587_, lean_object* v_x_1588_){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1589_ = l_Lean_Expr_fvarId_x21(v_x_1588_);
v___x_1590_ = lean_alloc_closure((void*)(l_Lean_FVarId_getUserName___boxed), 6, 1);
lean_closure_set(v___x_1590_, 0, v___x_1589_);
v___x_1591_ = lean_apply_2(v_inst_1587_, lean_box(0), v___x_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed(lean_object* v_inst_1592_, lean_object* v_x_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__1(v_inst_1592_, v_x_1593_);
lean_dec_ref(v_x_1593_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2(lean_object* v_inst_1595_, lean_object* v___f_1596_, lean_object* v_xs_1597_, lean_object* v_x_1598_){
_start:
{
size_t v_sz_1599_; size_t v___x_1600_; lean_object* v___x_1601_; 
v_sz_1599_ = lean_array_size(v_xs_1597_);
v___x_1600_ = ((size_t)0ULL);
v___x_1601_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1595_, v___f_1596_, v_sz_1599_, v___x_1600_, v_xs_1597_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed(lean_object* v_inst_1602_, lean_object* v___f_1603_, lean_object* v_xs_1604_, lean_object* v_x_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__2(v_inst_1602_, v___f_1603_, v_xs_1604_, v_x_1605_);
lean_dec_ref(v_x_1605_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__3(lean_object* v_toPure_1607_, lean_object* v_____do__lift_1608_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = lean_apply_2(v_toPure_1607_, lean_box(0), v_____do__lift_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__4(lean_object* v_toPure_1610_, lean_object* v_____do__lift_1611_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_apply_2(v_toPure_1610_, lean_box(0), v_____do__lift_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__5(lean_object* v_fst_1613_, lean_object* v_fst_1614_, lean_object* v___x_1615_, lean_object* v___x_1616_, lean_object* v_toPure_1617_, lean_object* v_____do__lift_1618_){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1619_ = lean_array_push(v_fst_1613_, v_____do__lift_1618_);
v___x_1620_ = lean_nat_add(v_fst_1614_, v___x_1615_);
v___x_1621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
lean_ctor_set(v___x_1621_, 1, v___x_1616_);
v___x_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1619_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1622_);
v___x_1624_ = lean_apply_2(v_toPure_1617_, lean_box(0), v___x_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__5___boxed(lean_object* v_fst_1625_, lean_object* v_fst_1626_, lean_object* v___x_1627_, lean_object* v___x_1628_, lean_object* v_toPure_1629_, lean_object* v_____do__lift_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__5(v_fst_1625_, v_fst_1626_, v___x_1627_, v___x_1628_, v_toPure_1629_, v_____do__lift_1630_);
lean_dec(v___x_1627_);
lean_dec(v_fst_1626_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6(uint8_t v_val_1632_, lean_object* v_a_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
if (v_val_1632_ == 0)
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_Meta_mkEqRefl(v_a_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
return v___x_1639_;
}
else
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Lean_Meta_mkHEqRefl(v_a_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
return v___x_1640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed(lean_object* v_val_1641_, lean_object* v_a_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
uint8_t v_val_14308__boxed_1648_; lean_object* v_res_1649_; 
v_val_14308__boxed_1648_ = lean_unbox(v_val_1641_);
v_res_1649_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__6(v_val_14308__boxed_1648_, v_a_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7(lean_object* v_toPure_1650_, lean_object* v_inst_1651_, lean_object* v_toBind_1652_, lean_object* v_a_1653_, lean_object* v_x_1654_, lean_object* v___y_1655_){
_start:
{
lean_object* v_snd_1656_; lean_object* v_snd_1657_; lean_object* v_fst_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1706_; 
v_snd_1656_ = lean_ctor_get(v___y_1655_, 1);
lean_inc(v_snd_1656_);
v_snd_1657_ = lean_ctor_get(v_snd_1656_, 1);
lean_inc(v_snd_1657_);
v_fst_1658_ = lean_ctor_get(v___y_1655_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___y_1655_);
if (v_isSharedCheck_1706_ == 0)
{
lean_object* v_unused_1707_; 
v_unused_1707_ = lean_ctor_get(v___y_1655_, 1);
lean_dec(v_unused_1707_);
v___x_1660_ = v___y_1655_;
v_isShared_1661_ = v_isSharedCheck_1706_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_fst_1658_);
lean_dec(v___y_1655_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1706_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v_fst_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1704_; 
v_fst_1662_ = lean_ctor_get(v_snd_1656_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v_snd_1656_);
if (v_isSharedCheck_1704_ == 0)
{
lean_object* v_unused_1705_; 
v_unused_1705_ = lean_ctor_get(v_snd_1656_, 1);
lean_dec(v_unused_1705_);
v___x_1664_ = v_snd_1656_;
v_isShared_1665_ = v_isSharedCheck_1704_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_fst_1662_);
lean_dec(v_snd_1656_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1704_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v_array_1666_; lean_object* v_start_1667_; lean_object* v_stop_1668_; uint8_t v___x_1669_; 
v_array_1666_ = lean_ctor_get(v_snd_1657_, 0);
v_start_1667_ = lean_ctor_get(v_snd_1657_, 1);
v_stop_1668_ = lean_ctor_get(v_snd_1657_, 2);
v___x_1669_ = lean_nat_dec_lt(v_start_1667_, v_stop_1668_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1671_; 
lean_dec_ref(v_a_1653_);
lean_dec(v_toBind_1652_);
lean_dec(v_inst_1651_);
if (v_isShared_1665_ == 0)
{
v___x_1671_ = v___x_1664_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_fst_1662_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v_snd_1657_);
v___x_1671_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_object* v___x_1673_; 
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 1, v___x_1671_);
v___x_1673_ = v___x_1660_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_fst_1658_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v___x_1671_);
v___x_1673_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
v___x_1675_ = lean_apply_2(v_toPure_1650_, lean_box(0), v___x_1674_);
return v___x_1675_;
}
}
}
else
{
lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1700_; 
lean_inc(v_stop_1668_);
lean_inc(v_start_1667_);
lean_inc_ref(v_array_1666_);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_snd_1657_);
if (v_isSharedCheck_1700_ == 0)
{
lean_object* v_unused_1701_; lean_object* v_unused_1702_; lean_object* v_unused_1703_; 
v_unused_1701_ = lean_ctor_get(v_snd_1657_, 2);
lean_dec(v_unused_1701_);
v_unused_1702_ = lean_ctor_get(v_snd_1657_, 1);
lean_dec(v_unused_1702_);
v_unused_1703_ = lean_ctor_get(v_snd_1657_, 0);
lean_dec(v_unused_1703_);
v___x_1679_ = v_snd_1657_;
v_isShared_1680_ = v_isSharedCheck_1700_;
goto v_resetjp_1678_;
}
else
{
lean_dec(v_snd_1657_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1700_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1681_ = lean_array_fget(v_array_1666_, v_start_1667_);
v___x_1682_ = lean_unsigned_to_nat(1u);
v___x_1683_ = lean_nat_add(v_start_1667_, v___x_1682_);
lean_dec(v_start_1667_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 1, v___x_1683_);
v___x_1685_ = v___x_1679_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_array_1666_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v___x_1683_);
lean_ctor_set(v_reuseFailAlloc_1699_, 2, v_stop_1668_);
v___x_1685_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v___x_1687_; 
lean_dec_ref(v_a_1653_);
lean_dec(v_toBind_1652_);
lean_dec(v_inst_1651_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 1, v___x_1685_);
v___x_1687_ = v___x_1664_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_fst_1662_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1689_; 
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 1, v___x_1687_);
v___x_1689_ = v___x_1660_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_fst_1658_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
v___x_1691_ = lean_apply_2(v_toPure_1650_, lean_box(0), v___x_1690_);
return v___x_1691_;
}
}
}
else
{
lean_object* v_val_1694_; lean_object* v___f_1695_; lean_object* v___f_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
lean_del_object(v___x_1664_);
lean_del_object(v___x_1660_);
v_val_1694_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_val_1694_);
lean_dec_ref(v___x_1681_);
v___f_1695_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_1695_, 0, v_fst_1658_);
lean_closure_set(v___f_1695_, 1, v_fst_1662_);
lean_closure_set(v___f_1695_, 2, v___x_1682_);
lean_closure_set(v___f_1695_, 3, v___x_1685_);
lean_closure_set(v___f_1695_, 4, v_toPure_1650_);
v___f_1696_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed), 7, 2);
lean_closure_set(v___f_1696_, 0, v_val_1694_);
lean_closure_set(v___f_1696_, 1, v_a_1653_);
v___x_1697_ = lean_apply_2(v_inst_1651_, lean_box(0), v___f_1696_);
v___x_1698_ = lean_apply_4(v_toBind_1652_, lean_box(0), lean_box(0), v___x_1697_, v___f_1695_);
return v___x_1698_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8(lean_object* v_heq_1708_, lean_object* v_fst_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Lean_mkArrow(v_heq_1708_, v_fst_1709_, v___y_1712_, v___y_1713_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed(lean_object* v_heq_1716_, lean_object* v_fst_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__8(v_heq_1716_, v_fst_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9(lean_object* v_heq_1726_, lean_object* v_fst_1727_, lean_object* v_fst_1728_, lean_object* v___x_1729_, lean_object* v___x_1730_, lean_object* v_toPure_1731_, lean_object* v_motiveBody_x27_1732_){
_start:
{
uint8_t v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1733_ = l_Lean_Expr_isHEq(v_heq_1726_);
v___x_1734_ = lean_box(v___x_1733_);
v___x_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1734_);
v___x_1736_ = lean_array_push(v_fst_1727_, v___x_1735_);
v___x_1737_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9___closed__0));
v___x_1738_ = lean_array_push(v_fst_1728_, v___x_1737_);
v___x_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1729_);
lean_ctor_set(v___x_1739_, 1, v___x_1730_);
v___x_1740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1738_);
lean_ctor_set(v___x_1740_, 1, v___x_1739_);
v___x_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1736_);
lean_ctor_set(v___x_1741_, 1, v___x_1740_);
v___x_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1742_, 0, v_motiveBody_x27_1732_);
lean_ctor_set(v___x_1742_, 1, v___x_1741_);
v___x_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
v___x_1744_ = lean_apply_2(v_toPure_1731_, lean_box(0), v___x_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9___boxed(lean_object* v_heq_1745_, lean_object* v_fst_1746_, lean_object* v_fst_1747_, lean_object* v___x_1748_, lean_object* v___x_1749_, lean_object* v_toPure_1750_, lean_object* v_motiveBody_x27_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__9(v_heq_1745_, v_fst_1746_, v_fst_1747_, v___x_1748_, v___x_1749_, v_toPure_1750_, v_motiveBody_x27_1751_);
lean_dec_ref(v_heq_1745_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10(lean_object* v_fst_1753_, lean_object* v_fst_1754_, lean_object* v_fst_1755_, lean_object* v___x_1756_, lean_object* v___x_1757_, lean_object* v_toPure_1758_, lean_object* v_inst_1759_, lean_object* v_toBind_1760_, lean_object* v_heq_1761_){
_start:
{
lean_object* v___f_1762_; lean_object* v___f_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_inc_ref(v_heq_1761_);
v___f_1762_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed), 7, 2);
lean_closure_set(v___f_1762_, 0, v_heq_1761_);
lean_closure_set(v___f_1762_, 1, v_fst_1753_);
v___f_1763_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9___boxed), 7, 6);
lean_closure_set(v___f_1763_, 0, v_heq_1761_);
lean_closure_set(v___f_1763_, 1, v_fst_1754_);
lean_closure_set(v___f_1763_, 2, v_fst_1755_);
lean_closure_set(v___f_1763_, 3, v___x_1756_);
lean_closure_set(v___f_1763_, 4, v___x_1757_);
lean_closure_set(v___f_1763_, 5, v_toPure_1758_);
v___x_1764_ = lean_apply_2(v_inst_1759_, lean_box(0), v___f_1762_);
v___x_1765_ = lean_apply_4(v_toBind_1760_, lean_box(0), lean_box(0), v___x_1764_, v___f_1763_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11(lean_object* v___x_1766_, lean_object* v_a_1767_, lean_object* v_inst_1768_, lean_object* v_toBind_1769_, lean_object* v___f_1770_, lean_object* v_fst_1771_, lean_object* v_fst_1772_, lean_object* v___x_1773_, lean_object* v___x_1774_, lean_object* v___x_1775_, lean_object* v_fst_1776_, lean_object* v_toPure_1777_, uint8_t v_____do__lift_1778_){
_start:
{
if (v_____do__lift_1778_ == 0)
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
lean_dec(v_toPure_1777_);
lean_dec(v_fst_1776_);
lean_dec_ref(v___x_1775_);
lean_dec_ref(v___x_1774_);
lean_dec(v___x_1773_);
lean_dec(v_fst_1772_);
lean_dec(v_fst_1771_);
v___x_1779_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEqHEq___boxed), 7, 2);
lean_closure_set(v___x_1779_, 0, v___x_1766_);
lean_closure_set(v___x_1779_, 1, v_a_1767_);
v___x_1780_ = lean_apply_2(v_inst_1768_, lean_box(0), v___x_1779_);
v___x_1781_ = lean_apply_4(v_toBind_1769_, lean_box(0), lean_box(0), v___x_1780_, v___f_1770_);
return v___x_1781_;
}
else
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
lean_dec(v___f_1770_);
lean_dec(v_toBind_1769_);
lean_dec(v_inst_1768_);
lean_dec_ref(v_a_1767_);
lean_dec_ref(v___x_1766_);
v___x_1782_ = lean_box(0);
v___x_1783_ = lean_array_push(v_fst_1771_, v___x_1782_);
v___x_1784_ = lean_array_push(v_fst_1772_, v___x_1773_);
v___x_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1774_);
lean_ctor_set(v___x_1785_, 1, v___x_1775_);
v___x_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1784_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
v___x_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1783_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1788_, 0, v_fst_1776_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
v___x_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1788_);
v___x_1790_ = lean_apply_2(v_toPure_1777_, lean_box(0), v___x_1789_);
return v___x_1790_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed(lean_object* v___x_1791_, lean_object* v_a_1792_, lean_object* v_inst_1793_, lean_object* v_toBind_1794_, lean_object* v___f_1795_, lean_object* v_fst_1796_, lean_object* v_fst_1797_, lean_object* v___x_1798_, lean_object* v___x_1799_, lean_object* v___x_1800_, lean_object* v_fst_1801_, lean_object* v_toPure_1802_, lean_object* v_____do__lift_1803_){
_start:
{
uint8_t v_____do__lift_14499__boxed_1804_; lean_object* v_res_1805_; 
v_____do__lift_14499__boxed_1804_ = lean_unbox(v_____do__lift_1803_);
v_res_1805_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__11(v___x_1791_, v_a_1792_, v_inst_1793_, v_toBind_1794_, v___f_1795_, v_fst_1796_, v_fst_1797_, v___x_1798_, v___x_1799_, v___x_1800_, v_fst_1801_, v_toPure_1802_, v_____do__lift_14499__boxed_1804_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12(lean_object* v_toPure_1806_, uint8_t v_addEqualities_1807_, lean_object* v_inst_1808_, lean_object* v_toBind_1809_, lean_object* v_a_1810_, lean_object* v_x_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_snd_1813_; lean_object* v_snd_1814_; lean_object* v_snd_1815_; lean_object* v_snd_1816_; lean_object* v_fst_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1923_; 
v_snd_1813_ = lean_ctor_get(v___y_1812_, 1);
lean_inc(v_snd_1813_);
v_snd_1814_ = lean_ctor_get(v_snd_1813_, 1);
lean_inc(v_snd_1814_);
v_snd_1815_ = lean_ctor_get(v_snd_1814_, 1);
lean_inc(v_snd_1815_);
v_snd_1816_ = lean_ctor_get(v_snd_1815_, 1);
lean_inc(v_snd_1816_);
v_fst_1817_ = lean_ctor_get(v___y_1812_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___y_1812_);
if (v_isSharedCheck_1923_ == 0)
{
lean_object* v_unused_1924_; 
v_unused_1924_ = lean_ctor_get(v___y_1812_, 1);
lean_dec(v_unused_1924_);
v___x_1819_ = v___y_1812_;
v_isShared_1820_ = v_isSharedCheck_1923_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_fst_1817_);
lean_dec(v___y_1812_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1923_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v_fst_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1921_; 
v_fst_1821_ = lean_ctor_get(v_snd_1813_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v_snd_1813_);
if (v_isSharedCheck_1921_ == 0)
{
lean_object* v_unused_1922_; 
v_unused_1922_ = lean_ctor_get(v_snd_1813_, 1);
lean_dec(v_unused_1922_);
v___x_1823_ = v_snd_1813_;
v_isShared_1824_ = v_isSharedCheck_1921_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_fst_1821_);
lean_dec(v_snd_1813_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1921_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v_fst_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1919_; 
v_fst_1825_ = lean_ctor_get(v_snd_1814_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v_snd_1814_);
if (v_isSharedCheck_1919_ == 0)
{
lean_object* v_unused_1920_; 
v_unused_1920_ = lean_ctor_get(v_snd_1814_, 1);
lean_dec(v_unused_1920_);
v___x_1827_ = v_snd_1814_;
v_isShared_1828_ = v_isSharedCheck_1919_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_fst_1825_);
lean_dec(v_snd_1814_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1919_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v_fst_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1917_; 
v_fst_1829_ = lean_ctor_get(v_snd_1815_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_snd_1815_);
if (v_isSharedCheck_1917_ == 0)
{
lean_object* v_unused_1918_; 
v_unused_1918_ = lean_ctor_get(v_snd_1815_, 1);
lean_dec(v_unused_1918_);
v___x_1831_ = v_snd_1815_;
v_isShared_1832_ = v_isSharedCheck_1917_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_fst_1829_);
lean_dec(v_snd_1815_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1917_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v_array_1833_; lean_object* v_start_1834_; lean_object* v_stop_1835_; uint8_t v___x_1836_; 
v_array_1833_ = lean_ctor_get(v_snd_1816_, 0);
v_start_1834_ = lean_ctor_get(v_snd_1816_, 1);
v_stop_1835_ = lean_ctor_get(v_snd_1816_, 2);
v___x_1836_ = lean_nat_dec_lt(v_start_1834_, v_stop_1835_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1838_; 
lean_dec_ref(v_a_1810_);
lean_dec(v_toBind_1809_);
lean_dec(v_inst_1808_);
if (v_isShared_1832_ == 0)
{
v___x_1838_ = v___x_1831_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_fst_1829_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_snd_1816_);
v___x_1838_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
lean_object* v___x_1840_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 1, v___x_1838_);
v___x_1840_ = v___x_1827_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_fst_1825_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v___x_1842_; 
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 1, v___x_1840_);
v___x_1842_ = v___x_1823_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_fst_1821_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1844_; 
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 1, v___x_1842_);
v___x_1844_ = v___x_1819_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_fst_1817_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
v___x_1846_ = lean_apply_2(v_toPure_1806_, lean_box(0), v___x_1845_);
return v___x_1846_;
}
}
}
}
}
else
{
lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1913_; 
lean_inc(v_stop_1835_);
lean_inc(v_start_1834_);
lean_inc_ref(v_array_1833_);
v_isSharedCheck_1913_ = !lean_is_exclusive(v_snd_1816_);
if (v_isSharedCheck_1913_ == 0)
{
lean_object* v_unused_1914_; lean_object* v_unused_1915_; lean_object* v_unused_1916_; 
v_unused_1914_ = lean_ctor_get(v_snd_1816_, 2);
lean_dec(v_unused_1914_);
v_unused_1915_ = lean_ctor_get(v_snd_1816_, 1);
lean_dec(v_unused_1915_);
v_unused_1916_ = lean_ctor_get(v_snd_1816_, 0);
lean_dec(v_unused_1916_);
v___x_1852_ = v_snd_1816_;
v_isShared_1853_ = v_isSharedCheck_1913_;
goto v_resetjp_1851_;
}
else
{
lean_dec(v_snd_1816_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1913_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v_array_1854_; lean_object* v_start_1855_; lean_object* v_stop_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1861_; 
v_array_1854_ = lean_ctor_get(v_fst_1829_, 0);
v_start_1855_ = lean_ctor_get(v_fst_1829_, 1);
v_stop_1856_ = lean_ctor_get(v_fst_1829_, 2);
v___x_1857_ = lean_array_fget(v_array_1833_, v_start_1834_);
v___x_1858_ = lean_unsigned_to_nat(1u);
v___x_1859_ = lean_nat_add(v_start_1834_, v___x_1858_);
lean_dec(v_start_1834_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 1, v___x_1859_);
v___x_1861_ = v___x_1852_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_array_1833_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v___x_1859_);
lean_ctor_set(v_reuseFailAlloc_1912_, 2, v_stop_1835_);
v___x_1861_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
uint8_t v___x_1862_; 
v___x_1862_ = lean_nat_dec_lt(v_start_1855_, v_stop_1856_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1864_; 
lean_dec(v___x_1857_);
lean_dec_ref(v_a_1810_);
lean_dec(v_toBind_1809_);
lean_dec(v_inst_1808_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 1, v___x_1861_);
v___x_1864_ = v___x_1831_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_fst_1829_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v___x_1861_);
v___x_1864_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1866_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 1, v___x_1864_);
v___x_1866_ = v___x_1827_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_fst_1825_);
lean_ctor_set(v_reuseFailAlloc_1875_, 1, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
lean_object* v___x_1868_; 
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 1, v___x_1866_);
v___x_1868_ = v___x_1823_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_fst_1821_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v___x_1866_);
v___x_1868_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
lean_object* v___x_1870_; 
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 1, v___x_1868_);
v___x_1870_ = v___x_1819_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_fst_1817_);
lean_ctor_set(v_reuseFailAlloc_1873_, 1, v___x_1868_);
v___x_1870_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
v___x_1872_ = lean_apply_2(v_toPure_1806_, lean_box(0), v___x_1871_);
return v___x_1872_;
}
}
}
}
}
else
{
lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1908_; 
lean_inc(v_stop_1856_);
lean_inc(v_start_1855_);
lean_inc_ref(v_array_1854_);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_fst_1829_);
if (v_isSharedCheck_1908_ == 0)
{
lean_object* v_unused_1909_; lean_object* v_unused_1910_; lean_object* v_unused_1911_; 
v_unused_1909_ = lean_ctor_get(v_fst_1829_, 2);
lean_dec(v_unused_1909_);
v_unused_1910_ = lean_ctor_get(v_fst_1829_, 1);
lean_dec(v_unused_1910_);
v_unused_1911_ = lean_ctor_get(v_fst_1829_, 0);
lean_dec(v_unused_1911_);
v___x_1878_ = v_fst_1829_;
v_isShared_1879_ = v_isSharedCheck_1908_;
goto v_resetjp_1877_;
}
else
{
lean_dec(v_fst_1829_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1908_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1883_; 
v___x_1880_ = lean_array_fget(v_array_1854_, v_start_1855_);
v___x_1881_ = lean_nat_add(v_start_1855_, v___x_1858_);
lean_dec(v_start_1855_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 1, v___x_1881_);
v___x_1883_ = v___x_1878_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_array_1854_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v___x_1881_);
lean_ctor_set(v_reuseFailAlloc_1907_, 2, v_stop_1856_);
v___x_1883_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
if (v_addEqualities_1807_ == 0)
{
lean_dec(v___x_1880_);
lean_dec_ref(v_a_1810_);
lean_dec(v_toBind_1809_);
lean_dec(v_inst_1808_);
goto v___jp_1884_;
}
else
{
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v___f_1902_; lean_object* v___f_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
lean_del_object(v___x_1831_);
lean_del_object(v___x_1827_);
lean_del_object(v___x_1823_);
lean_del_object(v___x_1819_);
lean_inc_n(v_toBind_1809_, 2);
lean_inc_n(v_inst_1808_, 2);
lean_inc(v_toPure_1806_);
lean_inc_ref(v___x_1861_);
lean_inc_ref(v___x_1883_);
lean_inc(v_fst_1825_);
lean_inc(v_fst_1821_);
lean_inc(v_fst_1817_);
v___f_1902_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__10), 9, 8);
lean_closure_set(v___f_1902_, 0, v_fst_1817_);
lean_closure_set(v___f_1902_, 1, v_fst_1821_);
lean_closure_set(v___f_1902_, 2, v_fst_1825_);
lean_closure_set(v___f_1902_, 3, v___x_1883_);
lean_closure_set(v___f_1902_, 4, v___x_1861_);
lean_closure_set(v___f_1902_, 5, v_toPure_1806_);
lean_closure_set(v___f_1902_, 6, v_inst_1808_);
lean_closure_set(v___f_1902_, 7, v_toBind_1809_);
lean_inc_ref(v_a_1810_);
v___f_1903_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_1903_, 0, v___x_1880_);
lean_closure_set(v___f_1903_, 1, v_a_1810_);
lean_closure_set(v___f_1903_, 2, v_inst_1808_);
lean_closure_set(v___f_1903_, 3, v_toBind_1809_);
lean_closure_set(v___f_1903_, 4, v___f_1902_);
lean_closure_set(v___f_1903_, 5, v_fst_1821_);
lean_closure_set(v___f_1903_, 6, v_fst_1825_);
lean_closure_set(v___f_1903_, 7, v___x_1857_);
lean_closure_set(v___f_1903_, 8, v___x_1883_);
lean_closure_set(v___f_1903_, 9, v___x_1861_);
lean_closure_set(v___f_1903_, 10, v_fst_1817_);
lean_closure_set(v___f_1903_, 11, v_toPure_1806_);
v___x_1904_ = lean_alloc_closure((void*)(l_Lean_Meta_isProof___boxed), 6, 1);
lean_closure_set(v___x_1904_, 0, v_a_1810_);
v___x_1905_ = lean_apply_2(v_inst_1808_, lean_box(0), v___x_1904_);
v___x_1906_ = lean_apply_4(v_toBind_1809_, lean_box(0), lean_box(0), v___x_1905_, v___f_1903_);
return v___x_1906_;
}
else
{
lean_dec(v___x_1880_);
lean_dec_ref(v_a_1810_);
lean_dec(v_toBind_1809_);
lean_dec(v_inst_1808_);
goto v___jp_1884_;
}
}
v___jp_1884_:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1885_ = lean_box(0);
v___x_1886_ = lean_array_push(v_fst_1821_, v___x_1885_);
v___x_1887_ = lean_array_push(v_fst_1825_, v___x_1857_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 1, v___x_1861_);
lean_ctor_set(v___x_1831_, 0, v___x_1883_);
v___x_1889_ = v___x_1831_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1883_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v___x_1861_);
v___x_1889_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1891_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 1, v___x_1889_);
lean_ctor_set(v___x_1827_, 0, v___x_1887_);
v___x_1891_ = v___x_1827_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v___x_1889_);
v___x_1891_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
lean_object* v___x_1893_; 
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 1, v___x_1891_);
lean_ctor_set(v___x_1823_, 0, v___x_1886_);
v___x_1893_ = v___x_1823_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1886_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
lean_object* v___x_1895_; 
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 1, v___x_1893_);
v___x_1895_ = v___x_1819_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_fst_1817_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
v___x_1897_ = lean_apply_2(v_toPure_1806_, lean_box(0), v___x_1896_);
return v___x_1897_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12___boxed(lean_object* v_toPure_1925_, lean_object* v_addEqualities_1926_, lean_object* v_inst_1927_, lean_object* v_toBind_1928_, lean_object* v_a_1929_, lean_object* v_x_1930_, lean_object* v___y_1931_){
_start:
{
uint8_t v_addEqualities_boxed_1932_; lean_object* v_res_1933_; 
v_addEqualities_boxed_1932_ = lean_unbox(v_addEqualities_1926_);
v_res_1933_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__12(v_toPure_1925_, v_addEqualities_boxed_1932_, v_inst_1927_, v_toBind_1928_, v_a_1929_, v_x_1930_, v___y_1931_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__13(lean_object* v_fst_1934_, lean_object* v_fst_1935_, lean_object* v_____do__lift_1936_, lean_object* v_toPure_1937_, lean_object* v_____do__lift_1938_){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1939_, 0, v_fst_1934_);
lean_ctor_set(v___x_1939_, 1, v_fst_1935_);
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v_____do__lift_1938_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1941_, 0, v_____do__lift_1936_);
lean_ctor_set(v___x_1941_, 1, v___x_1940_);
v___x_1942_ = lean_apply_2(v_toPure_1937_, lean_box(0), v___x_1941_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__14(lean_object* v_fst_1943_, lean_object* v_fst_1944_, lean_object* v_toPure_1945_, lean_object* v_fst_1946_, lean_object* v_inst_1947_, lean_object* v_toBind_1948_, lean_object* v_____do__lift_1949_){
_start:
{
lean_object* v___f_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___f_1950_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__13), 5, 4);
lean_closure_set(v___f_1950_, 0, v_fst_1943_);
lean_closure_set(v___f_1950_, 1, v_fst_1944_);
lean_closure_set(v___f_1950_, 2, v_____do__lift_1949_);
lean_closure_set(v___f_1950_, 3, v_toPure_1945_);
v___x_1951_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1951_, 0, v_fst_1946_);
v___x_1952_ = lean_apply_2(v_inst_1947_, lean_box(0), v___x_1951_);
v___x_1953_ = lean_apply_4(v_toBind_1948_, lean_box(0), lean_box(0), v___x_1952_, v___f_1950_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__15(lean_object* v_toPure_1954_, lean_object* v_inst_1955_, lean_object* v_toBind_1956_, lean_object* v_motiveArgs_1957_, lean_object* v_____s_1958_){
_start:
{
lean_object* v_snd_1959_; lean_object* v_snd_1960_; lean_object* v_fst_1961_; lean_object* v_fst_1962_; lean_object* v_fst_1963_; lean_object* v___f_1964_; uint8_t v___x_1965_; uint8_t v___x_1966_; uint8_t v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v_snd_1959_ = lean_ctor_get(v_____s_1958_, 1);
lean_inc(v_snd_1959_);
v_snd_1960_ = lean_ctor_get(v_snd_1959_, 1);
lean_inc(v_snd_1960_);
v_fst_1961_ = lean_ctor_get(v_____s_1958_, 0);
lean_inc_n(v_fst_1961_, 2);
lean_dec_ref(v_____s_1958_);
v_fst_1962_ = lean_ctor_get(v_snd_1959_, 0);
lean_inc(v_fst_1962_);
lean_dec(v_snd_1959_);
v_fst_1963_ = lean_ctor_get(v_snd_1960_, 0);
lean_inc(v_fst_1963_);
lean_dec(v_snd_1960_);
lean_inc(v_toBind_1956_);
lean_inc(v_inst_1955_);
v___f_1964_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14), 7, 6);
lean_closure_set(v___f_1964_, 0, v_fst_1962_);
lean_closure_set(v___f_1964_, 1, v_fst_1963_);
lean_closure_set(v___f_1964_, 2, v_toPure_1954_);
lean_closure_set(v___f_1964_, 3, v_fst_1961_);
lean_closure_set(v___f_1964_, 4, v_inst_1955_);
lean_closure_set(v___f_1964_, 5, v_toBind_1956_);
v___x_1965_ = 0;
v___x_1966_ = 1;
v___x_1967_ = 1;
v___x_1968_ = lean_box(v___x_1965_);
v___x_1969_ = lean_box(v___x_1966_);
v___x_1970_ = lean_box(v___x_1965_);
v___x_1971_ = lean_box(v___x_1966_);
v___x_1972_ = lean_box(v___x_1967_);
v___x_1973_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1973_, 0, v_motiveArgs_1957_);
lean_closure_set(v___x_1973_, 1, v_fst_1961_);
lean_closure_set(v___x_1973_, 2, v___x_1968_);
lean_closure_set(v___x_1973_, 3, v___x_1969_);
lean_closure_set(v___x_1973_, 4, v___x_1970_);
lean_closure_set(v___x_1973_, 5, v___x_1971_);
lean_closure_set(v___x_1973_, 6, v___x_1972_);
v___x_1974_ = lean_apply_2(v_inst_1955_, lean_box(0), v___x_1973_);
v___x_1975_ = lean_apply_4(v_toBind_1956_, lean_box(0), lean_box(0), v___x_1974_, v___f_1964_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__16(lean_object* v_toMatcherInfo_1978_, lean_object* v_discrs_x27_1979_, lean_object* v_motiveArgs_1980_, lean_object* v_inst_1981_, lean_object* v___f_1982_, lean_object* v_toBind_1983_, lean_object* v___f_1984_, lean_object* v_motiveBody_x27_1985_){
_start:
{
lean_object* v_discrInfos_1986_; lean_object* v___x_1987_; lean_object* v_addHEqualities_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; size_t v_sz_1997_; size_t v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v_discrInfos_1986_ = lean_ctor_get(v_toMatcherInfo_1978_, 4);
lean_inc_ref(v_discrInfos_1986_);
lean_dec_ref(v_toMatcherInfo_1978_);
v___x_1987_ = lean_unsigned_to_nat(0u);
v_addHEqualities_1988_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___closed__0));
v___x_1989_ = lean_array_get_size(v_discrs_x27_1979_);
v___x_1990_ = l_Array_toSubarray___redArg(v_discrs_x27_1979_, v___x_1987_, v___x_1989_);
v___x_1991_ = lean_array_get_size(v_discrInfos_1986_);
v___x_1992_ = l_Array_toSubarray___redArg(v_discrInfos_1986_, v___x_1987_, v___x_1991_);
v___x_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1990_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1994_, 0, v_addHEqualities_1988_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___x_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1995_, 0, v_addHEqualities_1988_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v___x_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1996_, 0, v_motiveBody_x27_1985_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v_sz_1997_ = lean_array_size(v_motiveArgs_1980_);
v___x_1998_ = ((size_t)0ULL);
v___x_1999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1981_, v_motiveArgs_1980_, v___f_1982_, v_sz_1997_, v___x_1998_, v___x_1996_);
v___x_2000_ = lean_apply_4(v_toBind_1983_, lean_box(0), lean_box(0), v___x_1999_, v___f_1984_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__17(lean_object* v_onMotive_2001_, lean_object* v_motiveArgs_2002_, lean_object* v_motiveBody_2003_, lean_object* v_toBind_2004_, lean_object* v___f_2005_, lean_object* v_____r_2006_){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = lean_apply_2(v_onMotive_2001_, v_motiveArgs_2002_, v_motiveBody_2003_);
v___x_2008_ = lean_apply_4(v_toBind_2004_, lean_box(0), lean_box(0), v___x_2007_, v___f_2005_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__18(lean_object* v___f_2009_, lean_object* v_____r_2010_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_apply_1(v___f_2009_, v_____r_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19(lean_object* v_toPure_2012_, lean_object* v_inst_2013_, lean_object* v_toBind_2014_, lean_object* v_toMatcherInfo_2015_, lean_object* v_discrs_x27_2016_, lean_object* v_inst_2017_, lean_object* v___f_2018_, lean_object* v_onMotive_2019_, lean_object* v_discrs_2020_, lean_object* v_inst_2021_, lean_object* v_motiveArgs_2022_, lean_object* v_motiveBody_2023_){
_start:
{
lean_object* v___f_2024_; lean_object* v___f_2025_; lean_object* v___f_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; uint8_t v___x_2029_; 
lean_inc_ref_n(v_motiveArgs_2022_, 3);
lean_inc_n(v_toBind_2014_, 3);
v___f_2024_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__15), 5, 4);
lean_closure_set(v___f_2024_, 0, v_toPure_2012_);
lean_closure_set(v___f_2024_, 1, v_inst_2013_);
lean_closure_set(v___f_2024_, 2, v_toBind_2014_);
lean_closure_set(v___f_2024_, 3, v_motiveArgs_2022_);
lean_inc_ref(v_inst_2017_);
v___f_2025_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16), 8, 7);
lean_closure_set(v___f_2025_, 0, v_toMatcherInfo_2015_);
lean_closure_set(v___f_2025_, 1, v_discrs_x27_2016_);
lean_closure_set(v___f_2025_, 2, v_motiveArgs_2022_);
lean_closure_set(v___f_2025_, 3, v_inst_2017_);
lean_closure_set(v___f_2025_, 4, v___f_2018_);
lean_closure_set(v___f_2025_, 5, v_toBind_2014_);
lean_closure_set(v___f_2025_, 6, v___f_2024_);
lean_inc_ref(v___f_2025_);
lean_inc_ref(v_motiveBody_2023_);
lean_inc(v_onMotive_2019_);
v___f_2026_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__17), 6, 5);
lean_closure_set(v___f_2026_, 0, v_onMotive_2019_);
lean_closure_set(v___f_2026_, 1, v_motiveArgs_2022_);
lean_closure_set(v___f_2026_, 2, v_motiveBody_2023_);
lean_closure_set(v___f_2026_, 3, v_toBind_2014_);
lean_closure_set(v___f_2026_, 4, v___f_2025_);
v___x_2027_ = lean_array_get_size(v_motiveArgs_2022_);
v___x_2028_ = lean_array_get_size(v_discrs_2020_);
v___x_2029_ = lean_nat_dec_eq(v___x_2027_, v___x_2028_);
if (v___x_2029_ == 0)
{
lean_object* v___f_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
lean_dec_ref(v___f_2025_);
lean_dec_ref(v_motiveBody_2023_);
lean_dec_ref(v_motiveArgs_2022_);
lean_dec(v_onMotive_2019_);
v___f_2030_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__18), 2, 1);
lean_closure_set(v___f_2030_, 0, v___f_2026_);
v___x_2031_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_2032_ = l_Nat_reprFast(v___x_2028_);
v___x_2033_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
v___x_2034_ = l_Lean_MessageData_ofFormat(v___x_2033_);
v___x_2035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2031_);
lean_ctor_set(v___x_2035_, 1, v___x_2034_);
v___x_2036_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_2037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2035_);
lean_ctor_set(v___x_2037_, 1, v___x_2036_);
v___x_2038_ = l_Lean_throwError___redArg(v_inst_2017_, v_inst_2021_, v___x_2037_);
v___x_2039_ = lean_apply_4(v_toBind_2014_, lean_box(0), lean_box(0), v___x_2038_, v___f_2030_);
return v___x_2039_;
}
else
{
lean_object* v___x_2040_; lean_object* v___x_2041_; 
lean_dec_ref(v___f_2026_);
lean_dec_ref(v_inst_2021_);
lean_dec_ref(v_inst_2017_);
v___x_2040_ = lean_box(0);
v___x_2041_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__17(v_onMotive_2019_, v_motiveArgs_2022_, v_motiveBody_2023_, v_toBind_2014_, v___f_2025_, v___x_2040_);
return v___x_2041_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19___boxed(lean_object* v_toPure_2042_, lean_object* v_inst_2043_, lean_object* v_toBind_2044_, lean_object* v_toMatcherInfo_2045_, lean_object* v_discrs_x27_2046_, lean_object* v_inst_2047_, lean_object* v___f_2048_, lean_object* v_onMotive_2049_, lean_object* v_discrs_2050_, lean_object* v_inst_2051_, lean_object* v_motiveArgs_2052_, lean_object* v_motiveBody_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__19(v_toPure_2042_, v_inst_2043_, v_toBind_2044_, v_toMatcherInfo_2045_, v_discrs_x27_2046_, v_inst_2047_, v___f_2048_, v_onMotive_2049_, v_discrs_2050_, v_inst_2051_, v_motiveArgs_2052_, v_motiveBody_2053_);
lean_dec_ref(v_discrs_2050_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20(lean_object* v_fst_2055_, lean_object* v_numParams_2056_, lean_object* v_numDiscrs_2057_, lean_object* v_altInfos_2058_, lean_object* v_uElimPos_x3f_2059_, lean_object* v_snd_2060_, lean_object* v_overlaps_2061_, lean_object* v_matcherName_2062_, lean_object* v_matcherLevels_2063_, lean_object* v_params_x27_2064_, lean_object* v_fst_2065_, lean_object* v_discrs_x27_2066_, lean_object* v_fst_2067_, lean_object* v_toPure_2068_, lean_object* v_____do__lift_2069_){
_start:
{
lean_object* v_remaining_x27_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v_remaining_x27_2070_ = l_Array_append___redArg(v_fst_2055_, v_____do__lift_2069_);
v___x_2071_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2071_, 0, v_numParams_2056_);
lean_ctor_set(v___x_2071_, 1, v_numDiscrs_2057_);
lean_ctor_set(v___x_2071_, 2, v_altInfos_2058_);
lean_ctor_set(v___x_2071_, 3, v_uElimPos_x3f_2059_);
lean_ctor_set(v___x_2071_, 4, v_snd_2060_);
lean_ctor_set(v___x_2071_, 5, v_overlaps_2061_);
v___x_2072_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
lean_ctor_set(v___x_2072_, 1, v_matcherName_2062_);
lean_ctor_set(v___x_2072_, 2, v_matcherLevels_2063_);
lean_ctor_set(v___x_2072_, 3, v_params_x27_2064_);
lean_ctor_set(v___x_2072_, 4, v_fst_2065_);
lean_ctor_set(v___x_2072_, 5, v_discrs_x27_2066_);
lean_ctor_set(v___x_2072_, 6, v_fst_2067_);
lean_ctor_set(v___x_2072_, 7, v_remaining_x27_2070_);
v___x_2073_ = lean_apply_2(v_toPure_2068_, lean_box(0), v___x_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20___boxed(lean_object* v_fst_2074_, lean_object* v_numParams_2075_, lean_object* v_numDiscrs_2076_, lean_object* v_altInfos_2077_, lean_object* v_uElimPos_x3f_2078_, lean_object* v_snd_2079_, lean_object* v_overlaps_2080_, lean_object* v_matcherName_2081_, lean_object* v_matcherLevels_2082_, lean_object* v_params_x27_2083_, lean_object* v_fst_2084_, lean_object* v_discrs_x27_2085_, lean_object* v_fst_2086_, lean_object* v_toPure_2087_, lean_object* v_____do__lift_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__20(v_fst_2074_, v_numParams_2075_, v_numDiscrs_2076_, v_altInfos_2077_, v_uElimPos_x3f_2078_, v_snd_2079_, v_overlaps_2080_, v_matcherName_2081_, v_matcherLevels_2082_, v_params_x27_2083_, v_fst_2084_, v_discrs_x27_2085_, v_fst_2086_, v_toPure_2087_, v_____do__lift_2088_);
lean_dec_ref(v_____do__lift_2088_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21(lean_object* v_fst_2090_, lean_object* v_numParams_2091_, lean_object* v_numDiscrs_2092_, lean_object* v_altInfos_2093_, lean_object* v_uElimPos_x3f_2094_, lean_object* v_snd_2095_, lean_object* v_overlaps_2096_, lean_object* v_matcherName_2097_, lean_object* v_matcherLevels_2098_, lean_object* v_params_x27_2099_, lean_object* v_fst_2100_, lean_object* v_discrs_x27_2101_, lean_object* v_toPure_2102_, lean_object* v_onRemaining_2103_, lean_object* v_remaining_2104_, lean_object* v_toBind_2105_, lean_object* v_____s_2106_){
_start:
{
lean_object* v_fst_2107_; lean_object* v___f_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v_fst_2107_ = lean_ctor_get(v_____s_2106_, 0);
lean_inc(v_fst_2107_);
lean_dec_ref(v_____s_2106_);
v___f_2108_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__20___boxed), 15, 14);
lean_closure_set(v___f_2108_, 0, v_fst_2090_);
lean_closure_set(v___f_2108_, 1, v_numParams_2091_);
lean_closure_set(v___f_2108_, 2, v_numDiscrs_2092_);
lean_closure_set(v___f_2108_, 3, v_altInfos_2093_);
lean_closure_set(v___f_2108_, 4, v_uElimPos_x3f_2094_);
lean_closure_set(v___f_2108_, 5, v_snd_2095_);
lean_closure_set(v___f_2108_, 6, v_overlaps_2096_);
lean_closure_set(v___f_2108_, 7, v_matcherName_2097_);
lean_closure_set(v___f_2108_, 8, v_matcherLevels_2098_);
lean_closure_set(v___f_2108_, 9, v_params_x27_2099_);
lean_closure_set(v___f_2108_, 10, v_fst_2100_);
lean_closure_set(v___f_2108_, 11, v_discrs_x27_2101_);
lean_closure_set(v___f_2108_, 12, v_fst_2107_);
lean_closure_set(v___f_2108_, 13, v_toPure_2102_);
v___x_2109_ = lean_apply_1(v_onRemaining_2103_, v_remaining_2104_);
v___x_2110_ = lean_apply_4(v_toBind_2105_, lean_box(0), lean_box(0), v___x_2109_, v___f_2108_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed(lean_object** _args){
lean_object* v_fst_2111_ = _args[0];
lean_object* v_numParams_2112_ = _args[1];
lean_object* v_numDiscrs_2113_ = _args[2];
lean_object* v_altInfos_2114_ = _args[3];
lean_object* v_uElimPos_x3f_2115_ = _args[4];
lean_object* v_snd_2116_ = _args[5];
lean_object* v_overlaps_2117_ = _args[6];
lean_object* v_matcherName_2118_ = _args[7];
lean_object* v_matcherLevels_2119_ = _args[8];
lean_object* v_params_x27_2120_ = _args[9];
lean_object* v_fst_2121_ = _args[10];
lean_object* v_discrs_x27_2122_ = _args[11];
lean_object* v_toPure_2123_ = _args[12];
lean_object* v_onRemaining_2124_ = _args[13];
lean_object* v_remaining_2125_ = _args[14];
lean_object* v_toBind_2126_ = _args[15];
lean_object* v_____s_2127_ = _args[16];
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__21(v_fst_2111_, v_numParams_2112_, v_numDiscrs_2113_, v_altInfos_2114_, v_uElimPos_x3f_2115_, v_snd_2116_, v_overlaps_2117_, v_matcherName_2118_, v_matcherLevels_2119_, v_params_x27_2120_, v_fst_2121_, v_discrs_x27_2122_, v_toPure_2123_, v_onRemaining_2124_, v_remaining_2125_, v_toBind_2126_, v_____s_2127_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22(lean_object* v_toPure_2129_, lean_object* v_next_2130_, lean_object* v_G_2131_, lean_object* v_____do__lift_2132_){
_start:
{
if (lean_obj_tag(v_____do__lift_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2134_; 
lean_dec(v_G_2131_);
v_a_2133_ = lean_ctor_get(v_____do__lift_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref(v_____do__lift_2132_);
v___x_2134_ = lean_apply_2(v_toPure_2129_, lean_box(0), v_a_2133_);
return v___x_2134_;
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
lean_dec(v_toPure_2129_);
v_a_2135_ = lean_ctor_get(v_____do__lift_2132_, 0);
lean_inc(v_a_2135_);
lean_dec_ref(v_____do__lift_2132_);
v___x_2136_ = lean_unsigned_to_nat(1u);
v___x_2137_ = lean_nat_add(v_next_2130_, v___x_2136_);
v___x_2138_ = lean_apply_4(v_G_2131_, v___x_2137_, v_a_2135_, lean_box(0), lean_box(0));
return v___x_2138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22___boxed(lean_object* v_toPure_2139_, lean_object* v_next_2140_, lean_object* v_G_2141_, lean_object* v_____do__lift_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__22(v_toPure_2139_, v_next_2140_, v_G_2141_, v_____do__lift_2142_);
lean_dec(v_next_2140_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23(lean_object* v_xs_2144_, lean_object* v_ys4_2145_, uint8_t v___x_2146_, uint8_t v___x_2147_, lean_object* v_inst_2148_, lean_object* v_alt_x27_2149_){
_start:
{
lean_object* v___x_2150_; uint8_t v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2150_ = l_Array_append___redArg(v_xs_2144_, v_ys4_2145_);
v___x_2151_ = 1;
v___x_2152_ = lean_box(v___x_2146_);
v___x_2153_ = lean_box(v___x_2147_);
v___x_2154_ = lean_box(v___x_2146_);
v___x_2155_ = lean_box(v___x_2147_);
v___x_2156_ = lean_box(v___x_2151_);
v___x_2157_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_2157_, 0, v___x_2150_);
lean_closure_set(v___x_2157_, 1, v_alt_x27_2149_);
lean_closure_set(v___x_2157_, 2, v___x_2152_);
lean_closure_set(v___x_2157_, 3, v___x_2153_);
lean_closure_set(v___x_2157_, 4, v___x_2154_);
lean_closure_set(v___x_2157_, 5, v___x_2155_);
lean_closure_set(v___x_2157_, 6, v___x_2156_);
v___x_2158_ = lean_apply_2(v_inst_2148_, lean_box(0), v___x_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed(lean_object* v_xs_2159_, lean_object* v_ys4_2160_, lean_object* v___x_2161_, lean_object* v___x_2162_, lean_object* v_inst_2163_, lean_object* v_alt_x27_2164_){
_start:
{
uint8_t v___x_14944__boxed_2165_; uint8_t v___x_14945__boxed_2166_; lean_object* v_res_2167_; 
v___x_14944__boxed_2165_ = lean_unbox(v___x_2161_);
v___x_14945__boxed_2166_ = lean_unbox(v___x_2162_);
v_res_2167_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__23(v_xs_2159_, v_ys4_2160_, v___x_14944__boxed_2165_, v___x_14945__boxed_2166_, v_inst_2163_, v_alt_x27_2164_);
lean_dec_ref(v_ys4_2160_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__24(lean_object* v_xs_2168_, lean_object* v_remaining_x27_2169_, lean_object* v_ys4_2170_, lean_object* v_onAlt_2171_, lean_object* v_next_2172_, lean_object* v_altType_2173_, lean_object* v_toBind_2174_, lean_object* v___f_2175_, lean_object* v_alt_2176_){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
lean_inc_ref(v_remaining_x27_2169_);
lean_inc_ref(v_xs_2168_);
v___x_2177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2177_, 0, v_xs_2168_);
lean_ctor_set(v___x_2177_, 1, v_xs_2168_);
lean_ctor_set(v___x_2177_, 2, v_remaining_x27_2169_);
lean_ctor_set(v___x_2177_, 3, v_remaining_x27_2169_);
lean_ctor_set(v___x_2177_, 4, v_ys4_2170_);
v___x_2178_ = lean_apply_4(v_onAlt_2171_, v_next_2172_, v_altType_2173_, v___x_2177_, v_alt_2176_);
v___x_2179_ = lean_apply_4(v_toBind_2174_, lean_box(0), lean_box(0), v___x_2178_, v___f_2175_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25(lean_object* v___x_2180_, lean_object* v_xs_2181_, lean_object* v_inst_2182_, lean_object* v_toBind_2183_, lean_object* v___f_2184_, lean_object* v_inst_2185_, lean_object* v_inst_2186_, lean_object* v_names_2187_){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_inc_ref(v_xs_2181_);
v___x_2188_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLambda___boxed), 7, 2);
lean_closure_set(v___x_2188_, 0, v___x_2180_);
lean_closure_set(v___x_2188_, 1, v_xs_2181_);
v___x_2189_ = lean_apply_2(v_inst_2182_, lean_box(0), v___x_2188_);
v___x_2190_ = lean_apply_4(v_toBind_2183_, lean_box(0), lean_box(0), v___x_2189_, v___f_2184_);
v___x_2191_ = l_Lean_Meta_MatcherApp_withUserNames___redArg(v_inst_2185_, v_inst_2186_, v_xs_2181_, v_names_2187_, v___x_2190_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26(lean_object* v_xs_2192_, uint8_t v___x_2193_, uint8_t v___x_2194_, lean_object* v_inst_2195_, lean_object* v_remaining_x27_2196_, lean_object* v_onAlt_2197_, lean_object* v_next_2198_, lean_object* v_toBind_2199_, lean_object* v___x_2200_, lean_object* v_inst_2201_, lean_object* v_inst_2202_, lean_object* v___f_2203_, lean_object* v_ys4_2204_, lean_object* v_altType_2205_){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___f_2208_; lean_object* v___f_2209_; lean_object* v___f_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2206_ = lean_box(v___x_2193_);
v___x_2207_ = lean_box(v___x_2194_);
lean_inc(v_inst_2195_);
lean_inc_ref(v_ys4_2204_);
lean_inc_ref_n(v_xs_2192_, 2);
v___f_2208_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed), 6, 5);
lean_closure_set(v___f_2208_, 0, v_xs_2192_);
lean_closure_set(v___f_2208_, 1, v_ys4_2204_);
lean_closure_set(v___f_2208_, 2, v___x_2206_);
lean_closure_set(v___f_2208_, 3, v___x_2207_);
lean_closure_set(v___f_2208_, 4, v_inst_2195_);
lean_inc_n(v_toBind_2199_, 2);
v___f_2209_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__24), 9, 8);
lean_closure_set(v___f_2209_, 0, v_xs_2192_);
lean_closure_set(v___f_2209_, 1, v_remaining_x27_2196_);
lean_closure_set(v___f_2209_, 2, v_ys4_2204_);
lean_closure_set(v___f_2209_, 3, v_onAlt_2197_);
lean_closure_set(v___f_2209_, 4, v_next_2198_);
lean_closure_set(v___f_2209_, 5, v_altType_2205_);
lean_closure_set(v___f_2209_, 6, v_toBind_2199_);
lean_closure_set(v___f_2209_, 7, v___f_2208_);
lean_inc_ref(v_inst_2202_);
lean_inc_ref(v_inst_2201_);
lean_inc_ref(v___x_2200_);
v___f_2210_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__25), 8, 7);
lean_closure_set(v___f_2210_, 0, v___x_2200_);
lean_closure_set(v___f_2210_, 1, v_xs_2192_);
lean_closure_set(v___f_2210_, 2, v_inst_2195_);
lean_closure_set(v___f_2210_, 3, v_toBind_2199_);
lean_closure_set(v___f_2210_, 4, v___f_2209_);
lean_closure_set(v___f_2210_, 5, v_inst_2201_);
lean_closure_set(v___f_2210_, 6, v_inst_2202_);
v___x_2211_ = l_Lean_Meta_lambdaTelescope___redArg(v_inst_2201_, v_inst_2202_, v___x_2200_, v___f_2203_, v___x_2193_);
v___x_2212_ = lean_apply_4(v_toBind_2199_, lean_box(0), lean_box(0), v___x_2211_, v___f_2210_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed(lean_object* v_xs_2213_, lean_object* v___x_2214_, lean_object* v___x_2215_, lean_object* v_inst_2216_, lean_object* v_remaining_x27_2217_, lean_object* v_onAlt_2218_, lean_object* v_next_2219_, lean_object* v_toBind_2220_, lean_object* v___x_2221_, lean_object* v_inst_2222_, lean_object* v_inst_2223_, lean_object* v___f_2224_, lean_object* v_ys4_2225_, lean_object* v_altType_2226_){
_start:
{
uint8_t v___x_14997__boxed_2227_; uint8_t v___x_14998__boxed_2228_; lean_object* v_res_2229_; 
v___x_14997__boxed_2227_ = lean_unbox(v___x_2214_);
v___x_14998__boxed_2228_ = lean_unbox(v___x_2215_);
v_res_2229_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__26(v_xs_2213_, v___x_14997__boxed_2227_, v___x_14998__boxed_2228_, v_inst_2216_, v_remaining_x27_2217_, v_onAlt_2218_, v_next_2219_, v_toBind_2220_, v___x_2221_, v_inst_2222_, v_inst_2223_, v___f_2224_, v_ys4_2225_, v_altType_2226_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27(uint8_t v___x_2230_, uint8_t v___x_2231_, lean_object* v_inst_2232_, lean_object* v_remaining_x27_2233_, lean_object* v_onAlt_2234_, lean_object* v_next_2235_, lean_object* v_toBind_2236_, lean_object* v___x_2237_, lean_object* v_inst_2238_, lean_object* v_inst_2239_, lean_object* v___f_2240_, lean_object* v_fst_2241_, lean_object* v_xs_2242_, lean_object* v_altType_2243_){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___f_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2244_ = lean_box(v___x_2230_);
v___x_2245_ = lean_box(v___x_2231_);
lean_inc_ref(v_inst_2239_);
lean_inc_ref(v_inst_2238_);
v___f_2246_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed), 14, 12);
lean_closure_set(v___f_2246_, 0, v_xs_2242_);
lean_closure_set(v___f_2246_, 1, v___x_2244_);
lean_closure_set(v___f_2246_, 2, v___x_2245_);
lean_closure_set(v___f_2246_, 3, v_inst_2232_);
lean_closure_set(v___f_2246_, 4, v_remaining_x27_2233_);
lean_closure_set(v___f_2246_, 5, v_onAlt_2234_);
lean_closure_set(v___f_2246_, 6, v_next_2235_);
lean_closure_set(v___f_2246_, 7, v_toBind_2236_);
lean_closure_set(v___f_2246_, 8, v___x_2237_);
lean_closure_set(v___f_2246_, 9, v_inst_2238_);
lean_closure_set(v___f_2246_, 10, v_inst_2239_);
lean_closure_set(v___f_2246_, 11, v___f_2240_);
v___x_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2247_, 0, v_fst_2241_);
v___x_2248_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2238_, v_inst_2239_, v_altType_2243_, v___x_2247_, v___f_2246_, v___x_2230_, v___x_2230_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed(lean_object* v___x_2249_, lean_object* v___x_2250_, lean_object* v_inst_2251_, lean_object* v_remaining_x27_2252_, lean_object* v_onAlt_2253_, lean_object* v_next_2254_, lean_object* v_toBind_2255_, lean_object* v___x_2256_, lean_object* v_inst_2257_, lean_object* v_inst_2258_, lean_object* v___f_2259_, lean_object* v_fst_2260_, lean_object* v_xs_2261_, lean_object* v_altType_2262_){
_start:
{
uint8_t v___x_15032__boxed_2263_; uint8_t v___x_15033__boxed_2264_; lean_object* v_res_2265_; 
v___x_15032__boxed_2263_ = lean_unbox(v___x_2249_);
v___x_15033__boxed_2264_ = lean_unbox(v___x_2250_);
v_res_2265_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__27(v___x_15032__boxed_2263_, v___x_15033__boxed_2264_, v_inst_2251_, v_remaining_x27_2252_, v_onAlt_2253_, v_next_2254_, v_toBind_2255_, v___x_2256_, v_inst_2257_, v_inst_2258_, v___f_2259_, v_fst_2260_, v_xs_2261_, v_altType_2262_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__28(lean_object* v_fst_2266_, lean_object* v___x_2267_, lean_object* v___x_2268_, lean_object* v___x_2269_, lean_object* v_toPure_2270_, lean_object* v_alt_x27_2271_){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2272_ = lean_array_push(v_fst_2266_, v_alt_x27_2271_);
v___x_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2267_);
lean_ctor_set(v___x_2273_, 1, v___x_2268_);
v___x_2274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2269_);
lean_ctor_set(v___x_2274_, 1, v___x_2273_);
v___x_2275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2272_);
lean_ctor_set(v___x_2275_, 1, v___x_2274_);
v___x_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
v___x_2277_ = lean_apply_2(v_toPure_2270_, lean_box(0), v___x_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29(lean_object* v___x_2278_, lean_object* v_toPure_2279_, lean_object* v_toBind_2280_, lean_object* v___f_2281_, uint8_t v___x_2282_, uint8_t v___x_2283_, lean_object* v_inst_2284_, lean_object* v_remaining_x27_2285_, lean_object* v_onAlt_2286_, lean_object* v_inst_2287_, lean_object* v_inst_2288_, lean_object* v___f_2289_, lean_object* v_fst_2290_, lean_object* v_next_2291_, lean_object* v_acc_2292_, lean_object* v_h_2293_, lean_object* v_G_2294_){
_start:
{
uint8_t v___x_2295_; 
v___x_2295_ = lean_nat_dec_lt(v_next_2291_, v___x_2278_);
if (v___x_2295_ == 0)
{
lean_object* v___x_2296_; 
lean_dec(v_G_2294_);
lean_dec(v_next_2291_);
lean_dec(v_fst_2290_);
lean_dec(v___f_2289_);
lean_dec_ref(v_inst_2288_);
lean_dec_ref(v_inst_2287_);
lean_dec(v_onAlt_2286_);
lean_dec_ref(v_remaining_x27_2285_);
lean_dec(v_inst_2284_);
lean_dec(v___f_2281_);
lean_dec(v_toBind_2280_);
v___x_2296_ = lean_apply_2(v_toPure_2279_, lean_box(0), v_acc_2292_);
return v___x_2296_;
}
else
{
lean_object* v_snd_2297_; lean_object* v_snd_2298_; lean_object* v_snd_2299_; lean_object* v_fst_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2410_; 
v_snd_2297_ = lean_ctor_get(v_acc_2292_, 1);
lean_inc(v_snd_2297_);
v_snd_2298_ = lean_ctor_get(v_snd_2297_, 1);
lean_inc(v_snd_2298_);
v_snd_2299_ = lean_ctor_get(v_snd_2298_, 1);
lean_inc(v_snd_2299_);
v_fst_2300_ = lean_ctor_get(v_acc_2292_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v_acc_2292_);
if (v_isSharedCheck_2410_ == 0)
{
lean_object* v_unused_2411_; 
v_unused_2411_ = lean_ctor_get(v_acc_2292_, 1);
lean_dec(v_unused_2411_);
v___x_2302_ = v_acc_2292_;
v_isShared_2303_ = v_isSharedCheck_2410_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_fst_2300_);
lean_dec(v_acc_2292_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2410_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v_fst_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2408_; 
v_fst_2304_ = lean_ctor_get(v_snd_2297_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v_snd_2297_);
if (v_isSharedCheck_2408_ == 0)
{
lean_object* v_unused_2409_; 
v_unused_2409_ = lean_ctor_get(v_snd_2297_, 1);
lean_dec(v_unused_2409_);
v___x_2306_ = v_snd_2297_;
v_isShared_2307_ = v_isSharedCheck_2408_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_fst_2304_);
lean_dec(v_snd_2297_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2408_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v_fst_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2406_; 
v_fst_2308_ = lean_ctor_get(v_snd_2298_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v_snd_2298_);
if (v_isSharedCheck_2406_ == 0)
{
lean_object* v_unused_2407_; 
v_unused_2407_ = lean_ctor_get(v_snd_2298_, 1);
lean_dec(v_unused_2407_);
v___x_2310_ = v_snd_2298_;
v_isShared_2311_ = v_isSharedCheck_2406_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_fst_2308_);
lean_dec(v_snd_2298_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2406_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v_array_2312_; lean_object* v_start_2313_; lean_object* v_stop_2314_; lean_object* v___f_2315_; lean_object* v___y_2317_; uint8_t v___x_2320_; 
v_array_2312_ = lean_ctor_get(v_snd_2299_, 0);
v_start_2313_ = lean_ctor_get(v_snd_2299_, 1);
v_stop_2314_ = lean_ctor_get(v_snd_2299_, 2);
lean_inc(v_next_2291_);
lean_inc(v_toPure_2279_);
v___f_2315_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__22___boxed), 4, 3);
lean_closure_set(v___f_2315_, 0, v_toPure_2279_);
lean_closure_set(v___f_2315_, 1, v_next_2291_);
lean_closure_set(v___f_2315_, 2, v_G_2294_);
v___x_2320_ = lean_nat_dec_lt(v_start_2313_, v_stop_2314_);
if (v___x_2320_ == 0)
{
lean_object* v___x_2322_; 
lean_dec(v_next_2291_);
lean_dec(v_fst_2290_);
lean_dec(v___f_2289_);
lean_dec_ref(v_inst_2288_);
lean_dec_ref(v_inst_2287_);
lean_dec(v_onAlt_2286_);
lean_dec_ref(v_remaining_x27_2285_);
lean_dec(v_inst_2284_);
if (v_isShared_2311_ == 0)
{
v___x_2322_ = v___x_2310_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_fst_2308_);
lean_ctor_set(v_reuseFailAlloc_2331_, 1, v_snd_2299_);
v___x_2322_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
lean_object* v___x_2324_; 
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 1, v___x_2322_);
v___x_2324_ = v___x_2306_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_fst_2304_);
lean_ctor_set(v_reuseFailAlloc_2330_, 1, v___x_2322_);
v___x_2324_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
lean_object* v___x_2326_; 
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 1, v___x_2324_);
v___x_2326_ = v___x_2302_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_fst_2300_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v___x_2324_);
v___x_2326_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
v___x_2328_ = lean_apply_2(v_toPure_2279_, lean_box(0), v___x_2327_);
v___y_2317_ = v___x_2328_;
goto v___jp_2316_;
}
}
}
}
else
{
lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2402_; 
lean_inc(v_stop_2314_);
lean_inc(v_start_2313_);
lean_inc_ref(v_array_2312_);
v_isSharedCheck_2402_ = !lean_is_exclusive(v_snd_2299_);
if (v_isSharedCheck_2402_ == 0)
{
lean_object* v_unused_2403_; lean_object* v_unused_2404_; lean_object* v_unused_2405_; 
v_unused_2403_ = lean_ctor_get(v_snd_2299_, 2);
lean_dec(v_unused_2403_);
v_unused_2404_ = lean_ctor_get(v_snd_2299_, 1);
lean_dec(v_unused_2404_);
v_unused_2405_ = lean_ctor_get(v_snd_2299_, 0);
lean_dec(v_unused_2405_);
v___x_2333_ = v_snd_2299_;
v_isShared_2334_ = v_isSharedCheck_2402_;
goto v_resetjp_2332_;
}
else
{
lean_dec(v_snd_2299_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2402_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v_array_2335_; lean_object* v_start_2336_; lean_object* v_stop_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2342_; 
v_array_2335_ = lean_ctor_get(v_fst_2308_, 0);
v_start_2336_ = lean_ctor_get(v_fst_2308_, 1);
v_stop_2337_ = lean_ctor_get(v_fst_2308_, 2);
v___x_2338_ = lean_array_fget(v_array_2312_, v_start_2313_);
v___x_2339_ = lean_unsigned_to_nat(1u);
v___x_2340_ = lean_nat_add(v_start_2313_, v___x_2339_);
lean_dec(v_start_2313_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 1, v___x_2340_);
v___x_2342_ = v___x_2333_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_array_2312_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v___x_2340_);
lean_ctor_set(v_reuseFailAlloc_2401_, 2, v_stop_2314_);
v___x_2342_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
uint8_t v___x_2343_; 
v___x_2343_ = lean_nat_dec_lt(v_start_2336_, v_stop_2337_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2345_; 
lean_dec(v___x_2338_);
lean_dec(v_next_2291_);
lean_dec(v_fst_2290_);
lean_dec(v___f_2289_);
lean_dec_ref(v_inst_2288_);
lean_dec_ref(v_inst_2287_);
lean_dec(v_onAlt_2286_);
lean_dec_ref(v_remaining_x27_2285_);
lean_dec(v_inst_2284_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 1, v___x_2342_);
v___x_2345_ = v___x_2310_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_fst_2308_);
lean_ctor_set(v_reuseFailAlloc_2354_, 1, v___x_2342_);
v___x_2345_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
lean_object* v___x_2347_; 
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 1, v___x_2345_);
v___x_2347_ = v___x_2306_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_fst_2304_);
lean_ctor_set(v_reuseFailAlloc_2353_, 1, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
lean_object* v___x_2349_; 
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 1, v___x_2347_);
v___x_2349_ = v___x_2302_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_fst_2300_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
v___x_2351_ = lean_apply_2(v_toPure_2279_, lean_box(0), v___x_2350_);
v___y_2317_ = v___x_2351_;
goto v___jp_2316_;
}
}
}
}
else
{
lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2397_; 
lean_inc(v_stop_2337_);
lean_inc(v_start_2336_);
lean_inc_ref(v_array_2335_);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_fst_2308_);
if (v_isSharedCheck_2397_ == 0)
{
lean_object* v_unused_2398_; lean_object* v_unused_2399_; lean_object* v_unused_2400_; 
v_unused_2398_ = lean_ctor_get(v_fst_2308_, 2);
lean_dec(v_unused_2398_);
v_unused_2399_ = lean_ctor_get(v_fst_2308_, 1);
lean_dec(v_unused_2399_);
v_unused_2400_ = lean_ctor_get(v_fst_2308_, 0);
lean_dec(v_unused_2400_);
v___x_2356_ = v_fst_2308_;
v_isShared_2357_ = v_isSharedCheck_2397_;
goto v_resetjp_2355_;
}
else
{
lean_dec(v_fst_2308_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2397_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v_array_2358_; lean_object* v_start_2359_; lean_object* v_stop_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2364_; 
v_array_2358_ = lean_ctor_get(v_fst_2304_, 0);
v_start_2359_ = lean_ctor_get(v_fst_2304_, 1);
v_stop_2360_ = lean_ctor_get(v_fst_2304_, 2);
v___x_2361_ = lean_array_fget(v_array_2335_, v_start_2336_);
v___x_2362_ = lean_nat_add(v_start_2336_, v___x_2339_);
lean_dec(v_start_2336_);
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 1, v___x_2362_);
v___x_2364_ = v___x_2356_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_array_2335_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v___x_2362_);
lean_ctor_set(v_reuseFailAlloc_2396_, 2, v_stop_2337_);
v___x_2364_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
uint8_t v___x_2365_; 
v___x_2365_ = lean_nat_dec_lt(v_start_2359_, v_stop_2360_);
if (v___x_2365_ == 0)
{
lean_object* v___x_2367_; 
lean_dec(v___x_2361_);
lean_dec(v___x_2338_);
lean_dec(v_next_2291_);
lean_dec(v_fst_2290_);
lean_dec(v___f_2289_);
lean_dec_ref(v_inst_2288_);
lean_dec_ref(v_inst_2287_);
lean_dec(v_onAlt_2286_);
lean_dec_ref(v_remaining_x27_2285_);
lean_dec(v_inst_2284_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 1, v___x_2342_);
lean_ctor_set(v___x_2310_, 0, v___x_2364_);
v___x_2367_ = v___x_2310_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2364_);
lean_ctor_set(v_reuseFailAlloc_2376_, 1, v___x_2342_);
v___x_2367_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
lean_object* v___x_2369_; 
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 1, v___x_2367_);
v___x_2369_ = v___x_2306_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_fst_2304_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2371_; 
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 1, v___x_2369_);
v___x_2371_ = v___x_2302_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_fst_2300_);
lean_ctor_set(v_reuseFailAlloc_2374_, 1, v___x_2369_);
v___x_2371_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2371_);
v___x_2373_ = lean_apply_2(v_toPure_2279_, lean_box(0), v___x_2372_);
v___y_2317_ = v___x_2373_;
goto v___jp_2316_;
}
}
}
}
else
{
lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2392_; 
lean_inc(v_stop_2360_);
lean_inc(v_start_2359_);
lean_inc_ref(v_array_2358_);
lean_del_object(v___x_2310_);
lean_del_object(v___x_2306_);
lean_del_object(v___x_2302_);
v_isSharedCheck_2392_ = !lean_is_exclusive(v_fst_2304_);
if (v_isSharedCheck_2392_ == 0)
{
lean_object* v_unused_2393_; lean_object* v_unused_2394_; lean_object* v_unused_2395_; 
v_unused_2393_ = lean_ctor_get(v_fst_2304_, 2);
lean_dec(v_unused_2393_);
v_unused_2394_ = lean_ctor_get(v_fst_2304_, 1);
lean_dec(v_unused_2394_);
v_unused_2395_ = lean_ctor_get(v_fst_2304_, 0);
lean_dec(v_unused_2395_);
v___x_2378_ = v_fst_2304_;
v_isShared_2379_ = v_isSharedCheck_2392_;
goto v_resetjp_2377_;
}
else
{
lean_dec(v_fst_2304_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2392_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___f_2383_; lean_object* v___x_2384_; lean_object* v___x_2386_; 
v___x_2380_ = lean_array_fget_borrowed(v_array_2358_, v_start_2359_);
v___x_2381_ = lean_box(v___x_2282_);
v___x_2382_ = lean_box(v___x_2283_);
lean_inc_ref(v_inst_2288_);
lean_inc_ref(v_inst_2287_);
lean_inc(v___x_2380_);
lean_inc(v_toBind_2280_);
v___f_2383_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed), 14, 12);
lean_closure_set(v___f_2383_, 0, v___x_2381_);
lean_closure_set(v___f_2383_, 1, v___x_2382_);
lean_closure_set(v___f_2383_, 2, v_inst_2284_);
lean_closure_set(v___f_2383_, 3, v_remaining_x27_2285_);
lean_closure_set(v___f_2383_, 4, v_onAlt_2286_);
lean_closure_set(v___f_2383_, 5, v_next_2291_);
lean_closure_set(v___f_2383_, 6, v_toBind_2280_);
lean_closure_set(v___f_2383_, 7, v___x_2380_);
lean_closure_set(v___f_2383_, 8, v_inst_2287_);
lean_closure_set(v___f_2383_, 9, v_inst_2288_);
lean_closure_set(v___f_2383_, 10, v___f_2289_);
lean_closure_set(v___f_2383_, 11, v_fst_2290_);
v___x_2384_ = lean_nat_add(v_start_2359_, v___x_2339_);
lean_dec(v_start_2359_);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 1, v___x_2384_);
v___x_2386_ = v___x_2378_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_array_2358_);
lean_ctor_set(v_reuseFailAlloc_2391_, 1, v___x_2384_);
lean_ctor_set(v_reuseFailAlloc_2391_, 2, v_stop_2360_);
v___x_2386_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
lean_object* v___f_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___f_2387_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__28), 6, 5);
lean_closure_set(v___f_2387_, 0, v_fst_2300_);
lean_closure_set(v___f_2387_, 1, v___x_2364_);
lean_closure_set(v___f_2387_, 2, v___x_2342_);
lean_closure_set(v___f_2387_, 3, v___x_2386_);
lean_closure_set(v___f_2387_, 4, v_toPure_2279_);
v___x_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2361_);
v___x_2389_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2287_, v_inst_2288_, v___x_2338_, v___x_2388_, v___f_2383_, v___x_2282_, v___x_2282_);
lean_inc(v_toBind_2280_);
v___x_2390_ = lean_apply_4(v_toBind_2280_, lean_box(0), lean_box(0), v___x_2389_, v___f_2387_);
v___y_2317_ = v___x_2390_;
goto v___jp_2316_;
}
}
}
}
}
}
}
}
}
v___jp_2316_:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
lean_inc(v_toBind_2280_);
v___x_2318_ = lean_apply_4(v_toBind_2280_, lean_box(0), lean_box(0), v___y_2317_, v___f_2281_);
v___x_2319_ = lean_apply_4(v_toBind_2280_, lean_box(0), lean_box(0), v___x_2318_, v___f_2315_);
return v___x_2319_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29___boxed(lean_object** _args){
lean_object* v___x_2412_ = _args[0];
lean_object* v_toPure_2413_ = _args[1];
lean_object* v_toBind_2414_ = _args[2];
lean_object* v___f_2415_ = _args[3];
lean_object* v___x_2416_ = _args[4];
lean_object* v___x_2417_ = _args[5];
lean_object* v_inst_2418_ = _args[6];
lean_object* v_remaining_x27_2419_ = _args[7];
lean_object* v_onAlt_2420_ = _args[8];
lean_object* v_inst_2421_ = _args[9];
lean_object* v_inst_2422_ = _args[10];
lean_object* v___f_2423_ = _args[11];
lean_object* v_fst_2424_ = _args[12];
lean_object* v_next_2425_ = _args[13];
lean_object* v_acc_2426_ = _args[14];
lean_object* v_h_2427_ = _args[15];
lean_object* v_G_2428_ = _args[16];
_start:
{
uint8_t v___x_15083__boxed_2429_; uint8_t v___x_15084__boxed_2430_; lean_object* v_res_2431_; 
v___x_15083__boxed_2429_ = lean_unbox(v___x_2416_);
v___x_15084__boxed_2430_ = lean_unbox(v___x_2417_);
v_res_2431_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__29(v___x_2412_, v_toPure_2413_, v_toBind_2414_, v___f_2415_, v___x_15083__boxed_2429_, v___x_15084__boxed_2430_, v_inst_2418_, v_remaining_x27_2419_, v_onAlt_2420_, v_inst_2421_, v_inst_2422_, v___f_2423_, v_fst_2424_, v_next_2425_, v_acc_2426_, v_h_2427_, v_G_2428_);
lean_dec(v___x_2412_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__30(lean_object* v_matcherApp_2432_, lean_object* v_alts_2433_, lean_object* v___x_2434_, lean_object* v___x_2435_, lean_object* v_remaining_x27_2436_, lean_object* v___f_2437_, lean_object* v_toBind_2438_, lean_object* v___f_2439_, lean_object* v_altTypes_2440_){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2441_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_2432_);
v___x_2442_ = lean_array_get_size(v___x_2441_);
v___x_2443_ = lean_array_get_size(v_altTypes_2440_);
lean_inc_n(v___x_2434_, 3);
v___x_2444_ = l_Array_toSubarray___redArg(v_alts_2433_, v___x_2434_, v___x_2435_);
v___x_2445_ = l_Array_toSubarray___redArg(v___x_2441_, v___x_2434_, v___x_2442_);
v___x_2446_ = l_Array_toSubarray___redArg(v_altTypes_2440_, v___x_2434_, v___x_2443_);
v___x_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2445_);
lean_ctor_set(v___x_2447_, 1, v___x_2446_);
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2444_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2449_, 0, v_remaining_x27_2436_);
lean_ctor_set(v___x_2449_, 1, v___x_2448_);
v___x_2450_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2437_, v___x_2434_, v___x_2449_, lean_box(0));
v___x_2451_ = lean_apply_4(v_toBind_2438_, lean_box(0), lean_box(0), v___x_2450_, v___f_2439_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31(lean_object* v_alts_2452_, lean_object* v_toPure_2453_, lean_object* v_toBind_2454_, lean_object* v___f_2455_, uint8_t v___x_2456_, uint8_t v___x_2457_, lean_object* v_inst_2458_, lean_object* v_remaining_x27_2459_, lean_object* v_onAlt_2460_, lean_object* v_inst_2461_, lean_object* v_inst_2462_, lean_object* v___f_2463_, lean_object* v_fst_2464_, lean_object* v_matcherApp_2465_, lean_object* v___x_2466_, lean_object* v___f_2467_, lean_object* v_aux_2468_, lean_object* v_____r_2469_){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___f_2473_; lean_object* v___f_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2470_ = lean_array_get_size(v_alts_2452_);
v___x_2471_ = lean_box(v___x_2456_);
v___x_2472_ = lean_box(v___x_2457_);
lean_inc_ref(v_remaining_x27_2459_);
lean_inc(v_inst_2458_);
lean_inc_n(v_toBind_2454_, 2);
v___f_2473_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__29___boxed), 17, 13);
lean_closure_set(v___f_2473_, 0, v___x_2470_);
lean_closure_set(v___f_2473_, 1, v_toPure_2453_);
lean_closure_set(v___f_2473_, 2, v_toBind_2454_);
lean_closure_set(v___f_2473_, 3, v___f_2455_);
lean_closure_set(v___f_2473_, 4, v___x_2471_);
lean_closure_set(v___f_2473_, 5, v___x_2472_);
lean_closure_set(v___f_2473_, 6, v_inst_2458_);
lean_closure_set(v___f_2473_, 7, v_remaining_x27_2459_);
lean_closure_set(v___f_2473_, 8, v_onAlt_2460_);
lean_closure_set(v___f_2473_, 9, v_inst_2461_);
lean_closure_set(v___f_2473_, 10, v_inst_2462_);
lean_closure_set(v___f_2473_, 11, v___f_2463_);
lean_closure_set(v___f_2473_, 12, v_fst_2464_);
v___f_2474_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__30), 9, 8);
lean_closure_set(v___f_2474_, 0, v_matcherApp_2465_);
lean_closure_set(v___f_2474_, 1, v_alts_2452_);
lean_closure_set(v___f_2474_, 2, v___x_2466_);
lean_closure_set(v___f_2474_, 3, v___x_2470_);
lean_closure_set(v___f_2474_, 4, v_remaining_x27_2459_);
lean_closure_set(v___f_2474_, 5, v___f_2473_);
lean_closure_set(v___f_2474_, 6, v_toBind_2454_);
lean_closure_set(v___f_2474_, 7, v___f_2467_);
v___x_2475_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_2475_, 0, v___x_2470_);
lean_closure_set(v___x_2475_, 1, v_aux_2468_);
v___x_2476_ = lean_apply_2(v_inst_2458_, lean_box(0), v___x_2475_);
v___x_2477_ = lean_apply_4(v_toBind_2454_, lean_box(0), lean_box(0), v___x_2476_, v___f_2474_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed(lean_object** _args){
lean_object* v_alts_2478_ = _args[0];
lean_object* v_toPure_2479_ = _args[1];
lean_object* v_toBind_2480_ = _args[2];
lean_object* v___f_2481_ = _args[3];
lean_object* v___x_2482_ = _args[4];
lean_object* v___x_2483_ = _args[5];
lean_object* v_inst_2484_ = _args[6];
lean_object* v_remaining_x27_2485_ = _args[7];
lean_object* v_onAlt_2486_ = _args[8];
lean_object* v_inst_2487_ = _args[9];
lean_object* v_inst_2488_ = _args[10];
lean_object* v___f_2489_ = _args[11];
lean_object* v_fst_2490_ = _args[12];
lean_object* v_matcherApp_2491_ = _args[13];
lean_object* v___x_2492_ = _args[14];
lean_object* v___f_2493_ = _args[15];
lean_object* v_aux_2494_ = _args[16];
lean_object* v_____r_2495_ = _args[17];
_start:
{
uint8_t v___x_15340__boxed_2496_; uint8_t v___x_15341__boxed_2497_; lean_object* v_res_2498_; 
v___x_15340__boxed_2496_ = lean_unbox(v___x_2482_);
v___x_15341__boxed_2497_ = lean_unbox(v___x_2483_);
v_res_2498_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__31(v_alts_2478_, v_toPure_2479_, v_toBind_2480_, v___f_2481_, v___x_15340__boxed_2496_, v___x_15341__boxed_2497_, v_inst_2484_, v_remaining_x27_2485_, v_onAlt_2486_, v_inst_2487_, v_inst_2488_, v___f_2489_, v_fst_2490_, v_matcherApp_2491_, v___x_2492_, v___f_2493_, v_aux_2494_, v_____r_2495_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__32(lean_object* v___x_2499_, lean_object* v_e_2500_){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2501_ = l_Lean_indentD(v_e_2500_);
v___x_2502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2499_);
lean_ctor_set(v___x_2502_, 1, v___x_2501_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33(lean_object* v___x_2503_, lean_object* v___f_2504_, lean_object* v_runInBase_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2511_ = lean_apply_2(v_runInBase_2505_, lean_box(0), v___x_2503_);
v___x_2512_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2511_, v___f_2504_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed(lean_object* v___x_2513_, lean_object* v___f_2514_, lean_object* v_runInBase_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__33(v___x_2513_, v___f_2514_, v_runInBase_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34(lean_object* v_toPure_2522_, lean_object* v_next_2523_, lean_object* v_G_2524_, lean_object* v_____do__lift_2525_){
_start:
{
if (lean_obj_tag(v_____do__lift_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v___x_2527_; 
lean_dec(v_G_2524_);
v_a_2526_ = lean_ctor_get(v_____do__lift_2525_, 0);
lean_inc(v_a_2526_);
lean_dec_ref(v_____do__lift_2525_);
v___x_2527_ = lean_apply_2(v_toPure_2522_, lean_box(0), v_a_2526_);
return v___x_2527_;
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
lean_dec(v_toPure_2522_);
v_a_2528_ = lean_ctor_get(v_____do__lift_2525_, 0);
lean_inc(v_a_2528_);
lean_dec_ref(v_____do__lift_2525_);
v___x_2529_ = lean_unsigned_to_nat(1u);
v___x_2530_ = lean_nat_add(v_next_2523_, v___x_2529_);
v___x_2531_ = lean_apply_4(v_G_2524_, v___x_2530_, v_a_2528_, lean_box(0), lean_box(0));
return v___x_2531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed(lean_object* v_toPure_2532_, lean_object* v_next_2533_, lean_object* v_G_2534_, lean_object* v_____do__lift_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__34(v_toPure_2532_, v_next_2533_, v_G_2534_, v_____do__lift_2535_);
lean_dec(v_next_2533_);
return v_res_2536_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__5(void){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2545_ = lean_box(0);
v___x_2546_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__4));
v___x_2547_ = l_Lean_mkConst(v___x_2546_, v___x_2545_);
return v___x_2547_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__6(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2548_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__5);
v___x_2549_ = lean_unsigned_to_nat(2u);
v___x_2550_ = lean_mk_empty_array_with_capacity(v___x_2549_);
v___x_2551_ = lean_array_push(v___x_2550_, v___x_2548_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35(lean_object* v___x_2552_, lean_object* v_toPure_2553_, lean_object* v_inst_2554_, lean_object* v_alt_x27_2555_){
_start:
{
uint8_t v_hasUnitThunk_2556_; 
v_hasUnitThunk_2556_ = lean_ctor_get_uint8(v___x_2552_, sizeof(void*)*2);
if (v_hasUnitThunk_2556_ == 0)
{
lean_object* v___x_2557_; 
lean_dec(v_inst_2554_);
v___x_2557_ = lean_apply_2(v_toPure_2553_, lean_box(0), v_alt_x27_2555_);
return v___x_2557_;
}
else
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
lean_dec(v_toPure_2553_);
v___x_2558_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__2));
v___x_2559_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__6);
v___x_2560_ = lean_array_push(v___x_2559_, v_alt_x27_2555_);
v___x_2561_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___boxed), 7, 2);
lean_closure_set(v___x_2561_, 0, v___x_2558_);
lean_closure_set(v___x_2561_, 1, v___x_2560_);
v___x_2562_ = lean_apply_2(v_inst_2554_, lean_box(0), v___x_2561_);
return v___x_2562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed(lean_object* v___x_2563_, lean_object* v_toPure_2564_, lean_object* v_inst_2565_, lean_object* v_alt_x27_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__35(v___x_2563_, v_toPure_2564_, v_inst_2565_, v_alt_x27_2566_);
lean_dec_ref(v___x_2563_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36(lean_object* v_ys_2568_, lean_object* v_ys2_2569_, lean_object* v_ys3_2570_, lean_object* v_ys4_2571_, uint8_t v___x_2572_, uint8_t v_useSplitter_2573_, lean_object* v_inst_2574_, lean_object* v_alt_x27_2575_){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; uint8_t v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2576_ = l_Array_append___redArg(v_ys_2568_, v_ys2_2569_);
v___x_2577_ = l_Array_append___redArg(v___x_2576_, v_ys3_2570_);
v___x_2578_ = l_Array_append___redArg(v___x_2577_, v_ys4_2571_);
v___x_2579_ = 1;
v___x_2580_ = lean_box(v___x_2572_);
v___x_2581_ = lean_box(v_useSplitter_2573_);
v___x_2582_ = lean_box(v___x_2572_);
v___x_2583_ = lean_box(v_useSplitter_2573_);
v___x_2584_ = lean_box(v___x_2579_);
v___x_2585_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_2585_, 0, v___x_2578_);
lean_closure_set(v___x_2585_, 1, v_alt_x27_2575_);
lean_closure_set(v___x_2585_, 2, v___x_2580_);
lean_closure_set(v___x_2585_, 3, v___x_2581_);
lean_closure_set(v___x_2585_, 4, v___x_2582_);
lean_closure_set(v___x_2585_, 5, v___x_2583_);
lean_closure_set(v___x_2585_, 6, v___x_2584_);
v___x_2586_ = lean_apply_2(v_inst_2574_, lean_box(0), v___x_2585_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed(lean_object* v_ys_2587_, lean_object* v_ys2_2588_, lean_object* v_ys3_2589_, lean_object* v_ys4_2590_, lean_object* v___x_2591_, lean_object* v_useSplitter_2592_, lean_object* v_inst_2593_, lean_object* v_alt_x27_2594_){
_start:
{
uint8_t v___x_15494__boxed_2595_; uint8_t v_useSplitter_boxed_2596_; lean_object* v_res_2597_; 
v___x_15494__boxed_2595_ = lean_unbox(v___x_2591_);
v_useSplitter_boxed_2596_ = lean_unbox(v_useSplitter_2592_);
v_res_2597_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__36(v_ys_2587_, v_ys2_2588_, v_ys3_2589_, v_ys4_2590_, v___x_15494__boxed_2595_, v_useSplitter_boxed_2596_, v_inst_2593_, v_alt_x27_2594_);
lean_dec_ref(v_ys4_2590_);
lean_dec_ref(v_ys3_2589_);
lean_dec_ref(v_ys2_2588_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__37(lean_object* v_args_2598_, lean_object* v_ys_2599_, lean_object* v_ys2_2600_, lean_object* v_ys3_2601_, lean_object* v_ys4_2602_, lean_object* v_onAlt_2603_, lean_object* v_next_2604_, lean_object* v_altType_2605_, lean_object* v_toBind_2606_, lean_object* v___f_2607_, lean_object* v_alt_2608_){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2609_, 0, v_args_2598_);
lean_ctor_set(v___x_2609_, 1, v_ys_2599_);
lean_ctor_set(v___x_2609_, 2, v_ys2_2600_);
lean_ctor_set(v___x_2609_, 3, v_ys3_2601_);
lean_ctor_set(v___x_2609_, 4, v_ys4_2602_);
v___x_2610_ = lean_apply_4(v_onAlt_2603_, v_next_2604_, v_altType_2605_, v___x_2609_, v_alt_2608_);
v___x_2611_ = lean_apply_4(v_toBind_2606_, lean_box(0), lean_box(0), v___x_2610_, v___f_2607_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38(lean_object* v_inst_2612_, lean_object* v_ys_2613_, lean_object* v_ys2_2614_, lean_object* v_ys3_2615_, uint8_t v___x_2616_, uint8_t v_useSplitter_2617_, lean_object* v_inst_2618_, lean_object* v_args_2619_, lean_object* v_onAlt_2620_, lean_object* v_next_2621_, lean_object* v_toBind_2622_, lean_object* v___x_2623_, lean_object* v___f_2624_, lean_object* v_ys4_2625_, lean_object* v_altType_2626_){
_start:
{
lean_object* v_toMonadExceptOf_2627_; lean_object* v_tryCatch_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___f_2631_; lean_object* v___f_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v_toMonadExceptOf_2627_ = lean_ctor_get(v_inst_2612_, 0);
lean_inc_ref(v_toMonadExceptOf_2627_);
lean_dec_ref(v_inst_2612_);
v_tryCatch_2628_ = lean_ctor_get(v_toMonadExceptOf_2627_, 1);
lean_inc(v_tryCatch_2628_);
lean_dec_ref(v_toMonadExceptOf_2627_);
v___x_2629_ = lean_box(v___x_2616_);
v___x_2630_ = lean_box(v_useSplitter_2617_);
lean_inc(v_inst_2618_);
lean_inc_ref(v_ys4_2625_);
lean_inc_ref_n(v_ys3_2615_, 2);
lean_inc_ref(v_ys2_2614_);
lean_inc_ref(v_ys_2613_);
v___f_2631_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed), 8, 7);
lean_closure_set(v___f_2631_, 0, v_ys_2613_);
lean_closure_set(v___f_2631_, 1, v_ys2_2614_);
lean_closure_set(v___f_2631_, 2, v_ys3_2615_);
lean_closure_set(v___f_2631_, 3, v_ys4_2625_);
lean_closure_set(v___f_2631_, 4, v___x_2629_);
lean_closure_set(v___f_2631_, 5, v___x_2630_);
lean_closure_set(v___f_2631_, 6, v_inst_2618_);
lean_inc(v_toBind_2622_);
lean_inc_ref(v_args_2619_);
v___f_2632_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37), 11, 10);
lean_closure_set(v___f_2632_, 0, v_args_2619_);
lean_closure_set(v___f_2632_, 1, v_ys_2613_);
lean_closure_set(v___f_2632_, 2, v_ys2_2614_);
lean_closure_set(v___f_2632_, 3, v_ys3_2615_);
lean_closure_set(v___f_2632_, 4, v_ys4_2625_);
lean_closure_set(v___f_2632_, 5, v_onAlt_2620_);
lean_closure_set(v___f_2632_, 6, v_next_2621_);
lean_closure_set(v___f_2632_, 7, v_altType_2626_);
lean_closure_set(v___f_2632_, 8, v_toBind_2622_);
lean_closure_set(v___f_2632_, 9, v___f_2631_);
v___x_2633_ = l_Array_append___redArg(v_args_2619_, v_ys3_2615_);
lean_dec_ref(v_ys3_2615_);
v___x_2634_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLambda___boxed), 7, 2);
lean_closure_set(v___x_2634_, 0, v___x_2623_);
lean_closure_set(v___x_2634_, 1, v___x_2633_);
v___x_2635_ = lean_apply_2(v_inst_2618_, lean_box(0), v___x_2634_);
v___x_2636_ = lean_apply_3(v_tryCatch_2628_, lean_box(0), v___x_2635_, v___f_2624_);
v___x_2637_ = lean_apply_4(v_toBind_2622_, lean_box(0), lean_box(0), v___x_2636_, v___f_2632_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed(lean_object* v_inst_2638_, lean_object* v_ys_2639_, lean_object* v_ys2_2640_, lean_object* v_ys3_2641_, lean_object* v___x_2642_, lean_object* v_useSplitter_2643_, lean_object* v_inst_2644_, lean_object* v_args_2645_, lean_object* v_onAlt_2646_, lean_object* v_next_2647_, lean_object* v_toBind_2648_, lean_object* v___x_2649_, lean_object* v___f_2650_, lean_object* v_ys4_2651_, lean_object* v_altType_2652_){
_start:
{
uint8_t v___x_15531__boxed_2653_; uint8_t v_useSplitter_boxed_2654_; lean_object* v_res_2655_; 
v___x_15531__boxed_2653_ = lean_unbox(v___x_2642_);
v_useSplitter_boxed_2654_ = lean_unbox(v_useSplitter_2643_);
v_res_2655_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__38(v_inst_2638_, v_ys_2639_, v_ys2_2640_, v_ys3_2641_, v___x_15531__boxed_2653_, v_useSplitter_boxed_2654_, v_inst_2644_, v_args_2645_, v_onAlt_2646_, v_next_2647_, v_toBind_2648_, v___x_2649_, v___f_2650_, v_ys4_2651_, v_altType_2652_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39(lean_object* v_inst_2656_, lean_object* v_ys_2657_, lean_object* v_ys2_2658_, uint8_t v___x_2659_, uint8_t v_useSplitter_2660_, lean_object* v_inst_2661_, lean_object* v_args_2662_, lean_object* v_onAlt_2663_, lean_object* v_next_2664_, lean_object* v_toBind_2665_, lean_object* v___x_2666_, lean_object* v___f_2667_, lean_object* v_fst_2668_, lean_object* v_inst_2669_, lean_object* v_inst_2670_, lean_object* v_ys3_2671_, lean_object* v_altType_2672_){
_start:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___f_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2673_ = lean_box(v___x_2659_);
v___x_2674_ = lean_box(v_useSplitter_2660_);
v___f_2675_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed), 15, 13);
lean_closure_set(v___f_2675_, 0, v_inst_2656_);
lean_closure_set(v___f_2675_, 1, v_ys_2657_);
lean_closure_set(v___f_2675_, 2, v_ys2_2658_);
lean_closure_set(v___f_2675_, 3, v_ys3_2671_);
lean_closure_set(v___f_2675_, 4, v___x_2673_);
lean_closure_set(v___f_2675_, 5, v___x_2674_);
lean_closure_set(v___f_2675_, 6, v_inst_2661_);
lean_closure_set(v___f_2675_, 7, v_args_2662_);
lean_closure_set(v___f_2675_, 8, v_onAlt_2663_);
lean_closure_set(v___f_2675_, 9, v_next_2664_);
lean_closure_set(v___f_2675_, 10, v_toBind_2665_);
lean_closure_set(v___f_2675_, 11, v___x_2666_);
lean_closure_set(v___f_2675_, 12, v___f_2667_);
v___x_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2676_, 0, v_fst_2668_);
v___x_2677_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2669_, v_inst_2670_, v_altType_2672_, v___x_2676_, v___f_2675_, v___x_2659_, v___x_2659_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39___boxed(lean_object** _args){
lean_object* v_inst_2678_ = _args[0];
lean_object* v_ys_2679_ = _args[1];
lean_object* v_ys2_2680_ = _args[2];
lean_object* v___x_2681_ = _args[3];
lean_object* v_useSplitter_2682_ = _args[4];
lean_object* v_inst_2683_ = _args[5];
lean_object* v_args_2684_ = _args[6];
lean_object* v_onAlt_2685_ = _args[7];
lean_object* v_next_2686_ = _args[8];
lean_object* v_toBind_2687_ = _args[9];
lean_object* v___x_2688_ = _args[10];
lean_object* v___f_2689_ = _args[11];
lean_object* v_fst_2690_ = _args[12];
lean_object* v_inst_2691_ = _args[13];
lean_object* v_inst_2692_ = _args[14];
lean_object* v_ys3_2693_ = _args[15];
lean_object* v_altType_2694_ = _args[16];
_start:
{
uint8_t v___x_15564__boxed_2695_; uint8_t v_useSplitter_boxed_2696_; lean_object* v_res_2697_; 
v___x_15564__boxed_2695_ = lean_unbox(v___x_2681_);
v_useSplitter_boxed_2696_ = lean_unbox(v_useSplitter_2682_);
v_res_2697_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__39(v_inst_2678_, v_ys_2679_, v_ys2_2680_, v___x_15564__boxed_2695_, v_useSplitter_boxed_2696_, v_inst_2683_, v_args_2684_, v_onAlt_2685_, v_next_2686_, v_toBind_2687_, v___x_2688_, v___f_2689_, v_fst_2690_, v_inst_2691_, v_inst_2692_, v_ys3_2693_, v_altType_2694_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40(lean_object* v_inst_2698_, lean_object* v_ys_2699_, uint8_t v___x_2700_, uint8_t v_useSplitter_2701_, lean_object* v_inst_2702_, lean_object* v_args_2703_, lean_object* v_onAlt_2704_, lean_object* v_next_2705_, lean_object* v_toBind_2706_, lean_object* v___x_2707_, lean_object* v___f_2708_, lean_object* v_fst_2709_, lean_object* v_inst_2710_, lean_object* v_inst_2711_, lean_object* v_numDiscrEqs_2712_, lean_object* v_ys2_2713_, lean_object* v_altType_2714_){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___f_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2715_ = lean_box(v___x_2700_);
v___x_2716_ = lean_box(v_useSplitter_2701_);
lean_inc_ref(v_inst_2711_);
lean_inc_ref(v_inst_2710_);
v___f_2717_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__39___boxed), 17, 15);
lean_closure_set(v___f_2717_, 0, v_inst_2698_);
lean_closure_set(v___f_2717_, 1, v_ys_2699_);
lean_closure_set(v___f_2717_, 2, v_ys2_2713_);
lean_closure_set(v___f_2717_, 3, v___x_2715_);
lean_closure_set(v___f_2717_, 4, v___x_2716_);
lean_closure_set(v___f_2717_, 5, v_inst_2702_);
lean_closure_set(v___f_2717_, 6, v_args_2703_);
lean_closure_set(v___f_2717_, 7, v_onAlt_2704_);
lean_closure_set(v___f_2717_, 8, v_next_2705_);
lean_closure_set(v___f_2717_, 9, v_toBind_2706_);
lean_closure_set(v___f_2717_, 10, v___x_2707_);
lean_closure_set(v___f_2717_, 11, v___f_2708_);
lean_closure_set(v___f_2717_, 12, v_fst_2709_);
lean_closure_set(v___f_2717_, 13, v_inst_2710_);
lean_closure_set(v___f_2717_, 14, v_inst_2711_);
v___x_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2718_, 0, v_numDiscrEqs_2712_);
v___x_2719_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2710_, v_inst_2711_, v_altType_2714_, v___x_2718_, v___f_2717_, v___x_2700_, v___x_2700_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed(lean_object** _args){
lean_object* v_inst_2720_ = _args[0];
lean_object* v_ys_2721_ = _args[1];
lean_object* v___x_2722_ = _args[2];
lean_object* v_useSplitter_2723_ = _args[3];
lean_object* v_inst_2724_ = _args[4];
lean_object* v_args_2725_ = _args[5];
lean_object* v_onAlt_2726_ = _args[6];
lean_object* v_next_2727_ = _args[7];
lean_object* v_toBind_2728_ = _args[8];
lean_object* v___x_2729_ = _args[9];
lean_object* v___f_2730_ = _args[10];
lean_object* v_fst_2731_ = _args[11];
lean_object* v_inst_2732_ = _args[12];
lean_object* v_inst_2733_ = _args[13];
lean_object* v_numDiscrEqs_2734_ = _args[14];
lean_object* v_ys2_2735_ = _args[15];
lean_object* v_altType_2736_ = _args[16];
_start:
{
uint8_t v___x_15595__boxed_2737_; uint8_t v_useSplitter_boxed_2738_; lean_object* v_res_2739_; 
v___x_15595__boxed_2737_ = lean_unbox(v___x_2722_);
v_useSplitter_boxed_2738_ = lean_unbox(v_useSplitter_2723_);
v_res_2739_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__40(v_inst_2720_, v_ys_2721_, v___x_15595__boxed_2737_, v_useSplitter_boxed_2738_, v_inst_2724_, v_args_2725_, v_onAlt_2726_, v_next_2727_, v_toBind_2728_, v___x_2729_, v___f_2730_, v_fst_2731_, v_inst_2732_, v_inst_2733_, v_numDiscrEqs_2734_, v_ys2_2735_, v_altType_2736_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41(lean_object* v___x_2740_, lean_object* v_inst_2741_, lean_object* v_inst_2742_, lean_object* v___f_2743_, uint8_t v___x_2744_, lean_object* v_toBind_2745_, lean_object* v___f_2746_, lean_object* v_altType_2747_){
_start:
{
lean_object* v_numOverlaps_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v_numOverlaps_2748_ = lean_ctor_get(v___x_2740_, 1);
lean_inc(v_numOverlaps_2748_);
v___x_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2749_, 0, v_numOverlaps_2748_);
v___x_2750_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2741_, v_inst_2742_, v_altType_2747_, v___x_2749_, v___f_2743_, v___x_2744_, v___x_2744_);
v___x_2751_ = lean_apply_4(v_toBind_2745_, lean_box(0), lean_box(0), v___x_2750_, v___f_2746_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed(lean_object* v___x_2752_, lean_object* v_inst_2753_, lean_object* v_inst_2754_, lean_object* v___f_2755_, lean_object* v___x_2756_, lean_object* v_toBind_2757_, lean_object* v___f_2758_, lean_object* v_altType_2759_){
_start:
{
uint8_t v___x_15629__boxed_2760_; lean_object* v_res_2761_; 
v___x_15629__boxed_2760_ = lean_unbox(v___x_2756_);
v_res_2761_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__41(v___x_2752_, v_inst_2753_, v_inst_2754_, v___f_2755_, v___x_15629__boxed_2760_, v_toBind_2757_, v___f_2758_, v_altType_2759_);
lean_dec_ref(v___x_2752_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__42(lean_object* v___f_2762_, lean_object* v_altType_2763_){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = lean_apply_1(v___f_2762_, v_altType_2763_);
return v___x_2764_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2(void){
_start:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2769_ = lean_box(0);
v___x_2770_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__1));
v___x_2771_ = l_Lean_mkConst(v___x_2770_, v___x_2769_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44(uint8_t v_hasUnitThunk_2772_, lean_object* v_toPure_2773_, lean_object* v_toBind_2774_, lean_object* v___f_2775_, lean_object* v___x_2776_, lean_object* v_inst_2777_, lean_object* v___f_2778_, lean_object* v_altType_2779_){
_start:
{
if (v_hasUnitThunk_2772_ == 0)
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
lean_dec(v___f_2778_);
lean_dec(v_inst_2777_);
v___x_2780_ = lean_apply_2(v_toPure_2773_, lean_box(0), v_altType_2779_);
v___x_2781_ = lean_apply_4(v_toBind_2774_, lean_box(0), lean_box(0), v___x_2780_, v___f_2775_);
return v___x_2781_;
}
else
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
lean_dec(v___f_2775_);
lean_dec(v_toPure_2773_);
v___x_2782_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2);
v___x_2783_ = lean_mk_empty_array_with_capacity(v___x_2776_);
v___x_2784_ = lean_array_push(v___x_2783_, v___x_2782_);
v___x_2785_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateForall___boxed), 7, 2);
lean_closure_set(v___x_2785_, 0, v_altType_2779_);
lean_closure_set(v___x_2785_, 1, v___x_2784_);
v___x_2786_ = lean_apply_2(v_inst_2777_, lean_box(0), v___x_2785_);
v___x_2787_ = lean_apply_4(v_toBind_2774_, lean_box(0), lean_box(0), v___x_2786_, v___f_2778_);
return v___x_2787_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed(lean_object* v_hasUnitThunk_2788_, lean_object* v_toPure_2789_, lean_object* v_toBind_2790_, lean_object* v___f_2791_, lean_object* v___x_2792_, lean_object* v_inst_2793_, lean_object* v___f_2794_, lean_object* v_altType_2795_){
_start:
{
uint8_t v_hasUnitThunk_boxed_2796_; lean_object* v_res_2797_; 
v_hasUnitThunk_boxed_2796_ = lean_unbox(v_hasUnitThunk_2788_);
v_res_2797_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__44(v_hasUnitThunk_boxed_2796_, v_toPure_2789_, v_toBind_2790_, v___f_2791_, v___x_2792_, v_inst_2793_, v___f_2794_, v_altType_2795_);
lean_dec(v___x_2792_);
return v_res_2797_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3(void){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2801_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__2));
v___x_2802_ = lean_unsigned_to_nat(8u);
v___x_2803_ = lean_unsigned_to_nat(360u);
v___x_2804_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__1));
v___x_2805_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__0));
v___x_2806_ = l_mkPanicMessageWithDecl(v___x_2805_, v___x_2804_, v___x_2803_, v___x_2802_, v___x_2801_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43(lean_object* v___x_2807_, lean_object* v_inst_2808_, lean_object* v_inst_2809_, uint8_t v___x_2810_, uint8_t v_useSplitter_2811_, lean_object* v_inst_2812_, lean_object* v_onAlt_2813_, lean_object* v_next_2814_, lean_object* v_toBind_2815_, lean_object* v___x_2816_, lean_object* v___f_2817_, lean_object* v_fst_2818_, lean_object* v_inst_2819_, lean_object* v_numDiscrEqs_2820_, lean_object* v___f_2821_, uint8_t v_hasUnitThunk_2822_, lean_object* v_toPure_2823_, lean_object* v___x_2824_, lean_object* v___x_2825_, lean_object* v_ys_2826_, lean_object* v_args_2827_){
_start:
{
lean_object* v_numFields_2828_; lean_object* v___x_2829_; uint8_t v___x_2830_; 
v_numFields_2828_ = lean_ctor_get(v___x_2807_, 0);
v___x_2829_ = lean_array_get_size(v_ys_2826_);
v___x_2830_ = lean_nat_dec_eq(v___x_2829_, v_numFields_2828_);
if (v___x_2830_ == 0)
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
lean_dec_ref(v_args_2827_);
lean_dec_ref(v_ys_2826_);
lean_dec_ref(v___x_2825_);
lean_dec(v___x_2824_);
lean_dec(v_toPure_2823_);
lean_dec(v___f_2821_);
lean_dec(v_numDiscrEqs_2820_);
lean_dec_ref(v_inst_2819_);
lean_dec(v_fst_2818_);
lean_dec(v___f_2817_);
lean_dec_ref(v___x_2816_);
lean_dec(v_toBind_2815_);
lean_dec(v_next_2814_);
lean_dec(v_onAlt_2813_);
lean_dec(v_inst_2812_);
lean_dec_ref(v_inst_2809_);
lean_dec_ref(v___x_2807_);
v___x_2831_ = l_Lean_instInhabitedExpr;
v___x_2832_ = l_instInhabitedOfMonad___redArg(v_inst_2808_, v___x_2831_);
v___x_2833_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3);
v___x_2834_ = l_panic___redArg(v___x_2832_, v___x_2833_);
lean_dec(v___x_2832_);
return v___x_2834_;
}
else
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___f_2837_; lean_object* v___x_2838_; lean_object* v___f_2839_; lean_object* v___f_2840_; lean_object* v___x_2841_; lean_object* v___f_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2835_ = lean_box(v___x_2810_);
v___x_2836_ = lean_box(v_useSplitter_2811_);
lean_inc_ref(v_inst_2808_);
lean_inc_ref(v_inst_2819_);
lean_inc_n(v_toBind_2815_, 3);
lean_inc_n(v_inst_2812_, 2);
lean_inc_ref(v_ys_2826_);
v___f_2837_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed), 17, 15);
lean_closure_set(v___f_2837_, 0, v_inst_2809_);
lean_closure_set(v___f_2837_, 1, v_ys_2826_);
lean_closure_set(v___f_2837_, 2, v___x_2835_);
lean_closure_set(v___f_2837_, 3, v___x_2836_);
lean_closure_set(v___f_2837_, 4, v_inst_2812_);
lean_closure_set(v___f_2837_, 5, v_args_2827_);
lean_closure_set(v___f_2837_, 6, v_onAlt_2813_);
lean_closure_set(v___f_2837_, 7, v_next_2814_);
lean_closure_set(v___f_2837_, 8, v_toBind_2815_);
lean_closure_set(v___f_2837_, 9, v___x_2816_);
lean_closure_set(v___f_2837_, 10, v___f_2817_);
lean_closure_set(v___f_2837_, 11, v_fst_2818_);
lean_closure_set(v___f_2837_, 12, v_inst_2819_);
lean_closure_set(v___f_2837_, 13, v_inst_2808_);
lean_closure_set(v___f_2837_, 14, v_numDiscrEqs_2820_);
v___x_2838_ = lean_box(v___x_2810_);
v___f_2839_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed), 8, 7);
lean_closure_set(v___f_2839_, 0, v___x_2807_);
lean_closure_set(v___f_2839_, 1, v_inst_2819_);
lean_closure_set(v___f_2839_, 2, v_inst_2808_);
lean_closure_set(v___f_2839_, 3, v___f_2837_);
lean_closure_set(v___f_2839_, 4, v___x_2838_);
lean_closure_set(v___f_2839_, 5, v_toBind_2815_);
lean_closure_set(v___f_2839_, 6, v___f_2821_);
v___f_2840_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__42), 2, 1);
lean_closure_set(v___f_2840_, 0, v___f_2839_);
v___x_2841_ = lean_box(v_hasUnitThunk_2822_);
lean_inc_ref(v___f_2840_);
v___f_2842_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed), 8, 7);
lean_closure_set(v___f_2842_, 0, v___x_2841_);
lean_closure_set(v___f_2842_, 1, v_toPure_2823_);
lean_closure_set(v___f_2842_, 2, v_toBind_2815_);
lean_closure_set(v___f_2842_, 3, v___f_2840_);
lean_closure_set(v___f_2842_, 4, v___x_2824_);
lean_closure_set(v___f_2842_, 5, v_inst_2812_);
lean_closure_set(v___f_2842_, 6, v___f_2840_);
v___x_2843_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateForall___boxed), 7, 2);
lean_closure_set(v___x_2843_, 0, v___x_2825_);
lean_closure_set(v___x_2843_, 1, v_ys_2826_);
v___x_2844_ = lean_apply_2(v_inst_2812_, lean_box(0), v___x_2843_);
v___x_2845_ = lean_apply_4(v_toBind_2815_, lean_box(0), lean_box(0), v___x_2844_, v___f_2842_);
return v___x_2845_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed(lean_object** _args){
lean_object* v___x_2846_ = _args[0];
lean_object* v_inst_2847_ = _args[1];
lean_object* v_inst_2848_ = _args[2];
lean_object* v___x_2849_ = _args[3];
lean_object* v_useSplitter_2850_ = _args[4];
lean_object* v_inst_2851_ = _args[5];
lean_object* v_onAlt_2852_ = _args[6];
lean_object* v_next_2853_ = _args[7];
lean_object* v_toBind_2854_ = _args[8];
lean_object* v___x_2855_ = _args[9];
lean_object* v___f_2856_ = _args[10];
lean_object* v_fst_2857_ = _args[11];
lean_object* v_inst_2858_ = _args[12];
lean_object* v_numDiscrEqs_2859_ = _args[13];
lean_object* v___f_2860_ = _args[14];
lean_object* v_hasUnitThunk_2861_ = _args[15];
lean_object* v_toPure_2862_ = _args[16];
lean_object* v___x_2863_ = _args[17];
lean_object* v___x_2864_ = _args[18];
lean_object* v_ys_2865_ = _args[19];
lean_object* v_args_2866_ = _args[20];
_start:
{
uint8_t v___x_15724__boxed_2867_; uint8_t v_useSplitter_boxed_2868_; uint8_t v_hasUnitThunk_boxed_2869_; lean_object* v_res_2870_; 
v___x_15724__boxed_2867_ = lean_unbox(v___x_2849_);
v_useSplitter_boxed_2868_ = lean_unbox(v_useSplitter_2850_);
v_hasUnitThunk_boxed_2869_ = lean_unbox(v_hasUnitThunk_2861_);
v_res_2870_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__43(v___x_2846_, v_inst_2847_, v_inst_2848_, v___x_15724__boxed_2867_, v_useSplitter_boxed_2868_, v_inst_2851_, v_onAlt_2852_, v_next_2853_, v_toBind_2854_, v___x_2855_, v___f_2856_, v_fst_2857_, v_inst_2858_, v_numDiscrEqs_2859_, v___f_2860_, v_hasUnitThunk_boxed_2869_, v_toPure_2862_, v___x_2863_, v___x_2864_, v_ys_2865_, v_args_2866_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45(lean_object* v_fst_2871_, lean_object* v___x_2872_, lean_object* v___x_2873_, lean_object* v___x_2874_, lean_object* v___x_2875_, lean_object* v___x_2876_, lean_object* v_toPure_2877_, lean_object* v_alt_x27_2878_){
_start:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2879_ = lean_array_push(v_fst_2871_, v_alt_x27_2878_);
v___x_2880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2872_);
lean_ctor_set(v___x_2880_, 1, v___x_2873_);
v___x_2881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2874_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
v___x_2882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2875_);
lean_ctor_set(v___x_2882_, 1, v___x_2881_);
v___x_2883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2876_);
lean_ctor_set(v___x_2883_, 1, v___x_2882_);
v___x_2884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2879_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
v___x_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2884_);
v___x_2886_ = lean_apply_2(v_toPure_2877_, lean_box(0), v___x_2885_);
return v___x_2886_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0(void){
_start:
{
lean_object* v___x_2887_; 
v___x_2887_ = l_Array_instInhabited(lean_box(0));
return v___x_2887_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1(void){
_start:
{
lean_object* v___x_2888_; 
v___x_2888_ = l_Subarray_empty(lean_box(0));
return v___x_2888_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2(void){
_start:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_2890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
return v___x_2890_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__3(void){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2891_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2);
v___x_2892_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_2893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2892_);
lean_ctor_set(v___x_2893_, 1, v___x_2891_);
return v___x_2893_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__4(void){
_start:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2894_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__3);
v___x_2895_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_2896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2895_);
lean_ctor_set(v___x_2896_, 1, v___x_2894_);
return v___x_2896_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__5(void){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2897_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__4, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__4_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__4);
v___x_2898_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_2899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
lean_ctor_set(v___x_2899_, 1, v___x_2897_);
return v___x_2899_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__6(void){
_start:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2900_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__5);
v___x_2901_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0);
v___x_2902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
lean_ctor_set(v___x_2902_, 1, v___x_2900_);
return v___x_2902_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7(void){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2903_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__6);
v___x_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2903_);
return v___x_2904_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9(void){
_start:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2906_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__8));
v___x_2907_ = lean_unsigned_to_nat(6u);
v___x_2908_ = lean_unsigned_to_nat(358u);
v___x_2909_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__1));
v___x_2910_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__0));
v___x_2911_ = l_mkPanicMessageWithDecl(v___x_2910_, v___x_2909_, v___x_2908_, v___x_2907_, v___x_2906_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46(lean_object* v___x_2912_, lean_object* v_toPure_2913_, lean_object* v_toBind_2914_, lean_object* v___f_2915_, lean_object* v___x_2916_, lean_object* v_inst_2917_, lean_object* v_inst_2918_, lean_object* v_inst_2919_, uint8_t v___x_2920_, uint8_t v_useSplitter_2921_, lean_object* v_onAlt_2922_, lean_object* v___f_2923_, lean_object* v_fst_2924_, lean_object* v_inst_2925_, lean_object* v_numDiscrEqs_2926_, lean_object* v_next_2927_, lean_object* v_acc_2928_, lean_object* v_h_2929_, lean_object* v_G_2930_){
_start:
{
uint8_t v___x_2931_; 
v___x_2931_ = lean_nat_dec_lt(v_next_2927_, v___x_2912_);
if (v___x_2931_ == 0)
{
lean_object* v___x_2932_; 
lean_dec(v_G_2930_);
lean_dec(v_next_2927_);
lean_dec(v_numDiscrEqs_2926_);
lean_dec_ref(v_inst_2925_);
lean_dec(v_fst_2924_);
lean_dec(v___f_2923_);
lean_dec(v_onAlt_2922_);
lean_dec_ref(v_inst_2919_);
lean_dec(v_inst_2918_);
lean_dec_ref(v_inst_2917_);
lean_dec(v___f_2915_);
lean_dec(v_toBind_2914_);
v___x_2932_ = lean_apply_2(v_toPure_2913_, lean_box(0), v_acc_2928_);
return v___x_2932_;
}
else
{
lean_object* v_snd_2933_; lean_object* v_snd_2934_; lean_object* v_snd_2935_; lean_object* v_snd_2936_; lean_object* v_snd_2937_; lean_object* v_fst_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_3152_; 
v_snd_2933_ = lean_ctor_get(v_acc_2928_, 1);
lean_inc(v_snd_2933_);
v_snd_2934_ = lean_ctor_get(v_snd_2933_, 1);
lean_inc(v_snd_2934_);
v_snd_2935_ = lean_ctor_get(v_snd_2934_, 1);
lean_inc(v_snd_2935_);
v_snd_2936_ = lean_ctor_get(v_snd_2935_, 1);
lean_inc(v_snd_2936_);
v_snd_2937_ = lean_ctor_get(v_snd_2936_, 1);
lean_inc(v_snd_2937_);
v_fst_2938_ = lean_ctor_get(v_acc_2928_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v_acc_2928_);
if (v_isSharedCheck_3152_ == 0)
{
lean_object* v_unused_3153_; 
v_unused_3153_ = lean_ctor_get(v_acc_2928_, 1);
lean_dec(v_unused_3153_);
v___x_2940_ = v_acc_2928_;
v_isShared_2941_ = v_isSharedCheck_3152_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_fst_2938_);
lean_dec(v_acc_2928_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_3152_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v_fst_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_3150_; 
v_fst_2942_ = lean_ctor_get(v_snd_2933_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v_snd_2933_);
if (v_isSharedCheck_3150_ == 0)
{
lean_object* v_unused_3151_; 
v_unused_3151_ = lean_ctor_get(v_snd_2933_, 1);
lean_dec(v_unused_3151_);
v___x_2944_ = v_snd_2933_;
v_isShared_2945_ = v_isSharedCheck_3150_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_fst_2942_);
lean_dec(v_snd_2933_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_3150_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v_fst_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_3148_; 
v_fst_2946_ = lean_ctor_get(v_snd_2934_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v_snd_2934_);
if (v_isSharedCheck_3148_ == 0)
{
lean_object* v_unused_3149_; 
v_unused_3149_ = lean_ctor_get(v_snd_2934_, 1);
lean_dec(v_unused_3149_);
v___x_2948_ = v_snd_2934_;
v_isShared_2949_ = v_isSharedCheck_3148_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_fst_2946_);
lean_dec(v_snd_2934_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_3148_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v_fst_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_3146_; 
v_fst_2950_ = lean_ctor_get(v_snd_2935_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v_snd_2935_);
if (v_isSharedCheck_3146_ == 0)
{
lean_object* v_unused_3147_; 
v_unused_3147_ = lean_ctor_get(v_snd_2935_, 1);
lean_dec(v_unused_3147_);
v___x_2952_ = v_snd_2935_;
v_isShared_2953_ = v_isSharedCheck_3146_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_fst_2950_);
lean_dec(v_snd_2935_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_3146_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v_fst_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_3144_; 
v_fst_2954_ = lean_ctor_get(v_snd_2936_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v_snd_2936_);
if (v_isSharedCheck_3144_ == 0)
{
lean_object* v_unused_3145_; 
v_unused_3145_ = lean_ctor_get(v_snd_2936_, 1);
lean_dec(v_unused_3145_);
v___x_2956_ = v_snd_2936_;
v_isShared_2957_ = v_isSharedCheck_3144_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_fst_2954_);
lean_dec(v_snd_2936_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_3144_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v_array_2958_; lean_object* v_start_2959_; lean_object* v_stop_2960_; lean_object* v___f_2961_; lean_object* v___y_2963_; uint8_t v___x_2966_; 
v_array_2958_ = lean_ctor_get(v_snd_2937_, 0);
v_start_2959_ = lean_ctor_get(v_snd_2937_, 1);
v_stop_2960_ = lean_ctor_get(v_snd_2937_, 2);
lean_inc(v_next_2927_);
lean_inc(v_toPure_2913_);
v___f_2961_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed), 4, 3);
lean_closure_set(v___f_2961_, 0, v_toPure_2913_);
lean_closure_set(v___f_2961_, 1, v_next_2927_);
lean_closure_set(v___f_2961_, 2, v_G_2930_);
v___x_2966_ = lean_nat_dec_lt(v_start_2959_, v_stop_2960_);
if (v___x_2966_ == 0)
{
lean_object* v___x_2968_; 
lean_dec(v_next_2927_);
lean_dec(v_numDiscrEqs_2926_);
lean_dec_ref(v_inst_2925_);
lean_dec(v_fst_2924_);
lean_dec(v___f_2923_);
lean_dec(v_onAlt_2922_);
lean_dec_ref(v_inst_2919_);
lean_dec(v_inst_2918_);
lean_dec_ref(v_inst_2917_);
if (v_isShared_2957_ == 0)
{
v___x_2968_ = v___x_2956_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_fst_2954_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v_snd_2937_);
v___x_2968_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
lean_object* v___x_2970_; 
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 1, v___x_2968_);
v___x_2970_ = v___x_2952_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_fst_2950_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v___x_2968_);
v___x_2970_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2972_; 
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 1, v___x_2970_);
v___x_2972_ = v___x_2948_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_fst_2946_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v___x_2970_);
v___x_2972_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
lean_object* v___x_2974_; 
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 1, v___x_2972_);
v___x_2974_ = v___x_2944_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_fst_2942_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
lean_object* v___x_2976_; 
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 1, v___x_2974_);
v___x_2976_ = v___x_2940_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_fst_2938_);
lean_ctor_set(v_reuseFailAlloc_2979_, 1, v___x_2974_);
v___x_2976_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
v___x_2978_ = lean_apply_2(v_toPure_2913_, lean_box(0), v___x_2977_);
v___y_2963_ = v___x_2978_;
goto v___jp_2962_;
}
}
}
}
}
}
else
{
lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_3140_; 
lean_inc(v_stop_2960_);
lean_inc(v_start_2959_);
lean_inc_ref(v_array_2958_);
v_isSharedCheck_3140_ = !lean_is_exclusive(v_snd_2937_);
if (v_isSharedCheck_3140_ == 0)
{
lean_object* v_unused_3141_; lean_object* v_unused_3142_; lean_object* v_unused_3143_; 
v_unused_3141_ = lean_ctor_get(v_snd_2937_, 2);
lean_dec(v_unused_3141_);
v_unused_3142_ = lean_ctor_get(v_snd_2937_, 1);
lean_dec(v_unused_3142_);
v_unused_3143_ = lean_ctor_get(v_snd_2937_, 0);
lean_dec(v_unused_3143_);
v___x_2985_ = v_snd_2937_;
v_isShared_2986_ = v_isSharedCheck_3140_;
goto v_resetjp_2984_;
}
else
{
lean_dec(v_snd_2937_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_3140_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v_array_2987_; lean_object* v_start_2988_; lean_object* v_stop_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2994_; 
v_array_2987_ = lean_ctor_get(v_fst_2954_, 0);
v_start_2988_ = lean_ctor_get(v_fst_2954_, 1);
v_stop_2989_ = lean_ctor_get(v_fst_2954_, 2);
v___x_2990_ = lean_array_fget(v_array_2958_, v_start_2959_);
v___x_2991_ = lean_unsigned_to_nat(1u);
v___x_2992_ = lean_nat_add(v_start_2959_, v___x_2991_);
lean_dec(v_start_2959_);
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 1, v___x_2992_);
v___x_2994_ = v___x_2985_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_array_2958_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v___x_2992_);
lean_ctor_set(v_reuseFailAlloc_3139_, 2, v_stop_2960_);
v___x_2994_ = v_reuseFailAlloc_3139_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
uint8_t v___x_2995_; 
v___x_2995_ = lean_nat_dec_lt(v_start_2988_, v_stop_2989_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2997_; 
lean_dec(v___x_2990_);
lean_dec(v_next_2927_);
lean_dec(v_numDiscrEqs_2926_);
lean_dec_ref(v_inst_2925_);
lean_dec(v_fst_2924_);
lean_dec(v___f_2923_);
lean_dec(v_onAlt_2922_);
lean_dec_ref(v_inst_2919_);
lean_dec(v_inst_2918_);
lean_dec_ref(v_inst_2917_);
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 1, v___x_2994_);
v___x_2997_ = v___x_2956_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_fst_2954_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v___x_2994_);
v___x_2997_ = v_reuseFailAlloc_3012_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
lean_object* v___x_2999_; 
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 1, v___x_2997_);
v___x_2999_ = v___x_2952_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_fst_2950_);
lean_ctor_set(v_reuseFailAlloc_3011_, 1, v___x_2997_);
v___x_2999_ = v_reuseFailAlloc_3011_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
lean_object* v___x_3001_; 
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 1, v___x_2999_);
v___x_3001_ = v___x_2948_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_fst_2946_);
lean_ctor_set(v_reuseFailAlloc_3010_, 1, v___x_2999_);
v___x_3001_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
lean_object* v___x_3003_; 
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 1, v___x_3001_);
v___x_3003_ = v___x_2944_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_fst_2942_);
lean_ctor_set(v_reuseFailAlloc_3009_, 1, v___x_3001_);
v___x_3003_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
lean_object* v___x_3005_; 
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 1, v___x_3003_);
v___x_3005_ = v___x_2940_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_fst_2938_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v___x_3003_);
v___x_3005_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3006_, 0, v___x_3005_);
v___x_3007_ = lean_apply_2(v_toPure_2913_, lean_box(0), v___x_3006_);
v___y_2963_ = v___x_3007_;
goto v___jp_2962_;
}
}
}
}
}
}
else
{
lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3135_; 
lean_inc(v_stop_2989_);
lean_inc(v_start_2988_);
lean_inc_ref(v_array_2987_);
v_isSharedCheck_3135_ = !lean_is_exclusive(v_fst_2954_);
if (v_isSharedCheck_3135_ == 0)
{
lean_object* v_unused_3136_; lean_object* v_unused_3137_; lean_object* v_unused_3138_; 
v_unused_3136_ = lean_ctor_get(v_fst_2954_, 2);
lean_dec(v_unused_3136_);
v_unused_3137_ = lean_ctor_get(v_fst_2954_, 1);
lean_dec(v_unused_3137_);
v_unused_3138_ = lean_ctor_get(v_fst_2954_, 0);
lean_dec(v_unused_3138_);
v___x_3014_ = v_fst_2954_;
v_isShared_3015_ = v_isSharedCheck_3135_;
goto v_resetjp_3013_;
}
else
{
lean_dec(v_fst_2954_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3135_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v_array_3016_; lean_object* v_start_3017_; lean_object* v_stop_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3022_; 
v_array_3016_ = lean_ctor_get(v_fst_2950_, 0);
v_start_3017_ = lean_ctor_get(v_fst_2950_, 1);
v_stop_3018_ = lean_ctor_get(v_fst_2950_, 2);
v___x_3019_ = lean_array_fget(v_array_2987_, v_start_2988_);
v___x_3020_ = lean_nat_add(v_start_2988_, v___x_2991_);
lean_dec(v_start_2988_);
if (v_isShared_3015_ == 0)
{
lean_ctor_set(v___x_3014_, 1, v___x_3020_);
v___x_3022_ = v___x_3014_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_array_2987_);
lean_ctor_set(v_reuseFailAlloc_3134_, 1, v___x_3020_);
lean_ctor_set(v_reuseFailAlloc_3134_, 2, v_stop_2989_);
v___x_3022_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
uint8_t v___x_3023_; 
v___x_3023_ = lean_nat_dec_lt(v_start_3017_, v_stop_3018_);
if (v___x_3023_ == 0)
{
lean_object* v___x_3025_; 
lean_dec(v___x_3019_);
lean_dec(v___x_2990_);
lean_dec(v_next_2927_);
lean_dec(v_numDiscrEqs_2926_);
lean_dec_ref(v_inst_2925_);
lean_dec(v_fst_2924_);
lean_dec(v___f_2923_);
lean_dec(v_onAlt_2922_);
lean_dec_ref(v_inst_2919_);
lean_dec(v_inst_2918_);
lean_dec_ref(v_inst_2917_);
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 1, v___x_2994_);
lean_ctor_set(v___x_2956_, 0, v___x_3022_);
v___x_3025_ = v___x_2956_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3022_);
lean_ctor_set(v_reuseFailAlloc_3040_, 1, v___x_2994_);
v___x_3025_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
lean_object* v___x_3027_; 
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 1, v___x_3025_);
v___x_3027_ = v___x_2952_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_fst_2950_);
lean_ctor_set(v_reuseFailAlloc_3039_, 1, v___x_3025_);
v___x_3027_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
lean_object* v___x_3029_; 
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 1, v___x_3027_);
v___x_3029_ = v___x_2948_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_fst_2946_);
lean_ctor_set(v_reuseFailAlloc_3038_, 1, v___x_3027_);
v___x_3029_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
lean_object* v___x_3031_; 
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 1, v___x_3029_);
v___x_3031_ = v___x_2944_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_fst_2942_);
lean_ctor_set(v_reuseFailAlloc_3037_, 1, v___x_3029_);
v___x_3031_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
lean_object* v___x_3033_; 
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 1, v___x_3031_);
v___x_3033_ = v___x_2940_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_fst_2938_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v___x_3031_);
v___x_3033_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
v___x_3035_ = lean_apply_2(v_toPure_2913_, lean_box(0), v___x_3034_);
v___y_2963_ = v___x_3035_;
goto v___jp_2962_;
}
}
}
}
}
}
else
{
lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3130_; 
lean_inc(v_stop_3018_);
lean_inc(v_start_3017_);
lean_inc_ref(v_array_3016_);
v_isSharedCheck_3130_ = !lean_is_exclusive(v_fst_2950_);
if (v_isSharedCheck_3130_ == 0)
{
lean_object* v_unused_3131_; lean_object* v_unused_3132_; lean_object* v_unused_3133_; 
v_unused_3131_ = lean_ctor_get(v_fst_2950_, 2);
lean_dec(v_unused_3131_);
v_unused_3132_ = lean_ctor_get(v_fst_2950_, 1);
lean_dec(v_unused_3132_);
v_unused_3133_ = lean_ctor_get(v_fst_2950_, 0);
lean_dec(v_unused_3133_);
v___x_3042_ = v_fst_2950_;
v_isShared_3043_ = v_isSharedCheck_3130_;
goto v_resetjp_3041_;
}
else
{
lean_dec(v_fst_2950_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3130_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v_array_3044_; lean_object* v_start_3045_; lean_object* v_stop_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3050_; 
v_array_3044_ = lean_ctor_get(v_fst_2946_, 0);
v_start_3045_ = lean_ctor_get(v_fst_2946_, 1);
v_stop_3046_ = lean_ctor_get(v_fst_2946_, 2);
v___x_3047_ = lean_array_fget(v_array_3016_, v_start_3017_);
v___x_3048_ = lean_nat_add(v_start_3017_, v___x_2991_);
lean_dec(v_start_3017_);
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 1, v___x_3048_);
v___x_3050_ = v___x_3042_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_array_3016_);
lean_ctor_set(v_reuseFailAlloc_3129_, 1, v___x_3048_);
lean_ctor_set(v_reuseFailAlloc_3129_, 2, v_stop_3018_);
v___x_3050_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
uint8_t v___x_3051_; 
v___x_3051_ = lean_nat_dec_lt(v_start_3045_, v_stop_3046_);
if (v___x_3051_ == 0)
{
lean_object* v___x_3053_; 
lean_dec(v___x_3047_);
lean_dec(v___x_3019_);
lean_dec(v___x_2990_);
lean_dec(v_next_2927_);
lean_dec(v_numDiscrEqs_2926_);
lean_dec_ref(v_inst_2925_);
lean_dec(v_fst_2924_);
lean_dec(v___f_2923_);
lean_dec(v_onAlt_2922_);
lean_dec_ref(v_inst_2919_);
lean_dec(v_inst_2918_);
lean_dec_ref(v_inst_2917_);
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 1, v___x_2994_);
lean_ctor_set(v___x_2956_, 0, v___x_3022_);
v___x_3053_ = v___x_2956_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3022_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v___x_2994_);
v___x_3053_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
lean_object* v___x_3055_; 
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 1, v___x_3053_);
lean_ctor_set(v___x_2952_, 0, v___x_3050_);
v___x_3055_ = v___x_2952_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v___x_3050_);
lean_ctor_set(v_reuseFailAlloc_3067_, 1, v___x_3053_);
v___x_3055_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
lean_object* v___x_3057_; 
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 1, v___x_3055_);
v___x_3057_ = v___x_2948_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_fst_2946_);
lean_ctor_set(v_reuseFailAlloc_3066_, 1, v___x_3055_);
v___x_3057_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
lean_object* v___x_3059_; 
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 1, v___x_3057_);
v___x_3059_ = v___x_2944_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_fst_2942_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v___x_3057_);
v___x_3059_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
lean_object* v___x_3061_; 
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 1, v___x_3059_);
v___x_3061_ = v___x_2940_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_fst_2938_);
lean_ctor_set(v_reuseFailAlloc_3064_, 1, v___x_3059_);
v___x_3061_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3061_);
v___x_3063_ = lean_apply_2(v_toPure_2913_, lean_box(0), v___x_3062_);
v___y_2963_ = v___x_3063_;
goto v___jp_2962_;
}
}
}
}
}
}
else
{
lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3125_; 
lean_inc(v_stop_3046_);
lean_inc(v_start_3045_);
lean_inc_ref(v_array_3044_);
v_isSharedCheck_3125_ = !lean_is_exclusive(v_fst_2946_);
if (v_isSharedCheck_3125_ == 0)
{
lean_object* v_unused_3126_; lean_object* v_unused_3127_; lean_object* v_unused_3128_; 
v_unused_3126_ = lean_ctor_get(v_fst_2946_, 2);
lean_dec(v_unused_3126_);
v_unused_3127_ = lean_ctor_get(v_fst_2946_, 1);
lean_dec(v_unused_3127_);
v_unused_3128_ = lean_ctor_get(v_fst_2946_, 0);
lean_dec(v_unused_3128_);
v___x_3070_ = v_fst_2946_;
v_isShared_3071_ = v_isSharedCheck_3125_;
goto v_resetjp_3069_;
}
else
{
lean_dec(v_fst_2946_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3125_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v_array_3072_; lean_object* v_start_3073_; lean_object* v_stop_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3078_; 
v_array_3072_ = lean_ctor_get(v_fst_2942_, 0);
v_start_3073_ = lean_ctor_get(v_fst_2942_, 1);
v_stop_3074_ = lean_ctor_get(v_fst_2942_, 2);
v___x_3075_ = lean_array_fget(v_array_3044_, v_start_3045_);
v___x_3076_ = lean_nat_add(v_start_3045_, v___x_2991_);
lean_dec(v_start_3045_);
if (v_isShared_3071_ == 0)
{
lean_ctor_set(v___x_3070_, 1, v___x_3076_);
v___x_3078_ = v___x_3070_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_array_3044_);
lean_ctor_set(v_reuseFailAlloc_3124_, 1, v___x_3076_);
lean_ctor_set(v_reuseFailAlloc_3124_, 2, v_stop_3046_);
v___x_3078_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
uint8_t v___x_3079_; 
v___x_3079_ = lean_nat_dec_lt(v_start_3073_, v_stop_3074_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3081_; 
lean_dec(v___x_3075_);
lean_dec(v___x_3047_);
lean_dec(v___x_3019_);
lean_dec(v___x_2990_);
lean_dec(v_next_2927_);
lean_dec(v_numDiscrEqs_2926_);
lean_dec_ref(v_inst_2925_);
lean_dec(v_fst_2924_);
lean_dec(v___f_2923_);
lean_dec(v_onAlt_2922_);
lean_dec_ref(v_inst_2919_);
lean_dec(v_inst_2918_);
lean_dec_ref(v_inst_2917_);
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 1, v___x_2994_);
lean_ctor_set(v___x_2956_, 0, v___x_3022_);
v___x_3081_ = v___x_2956_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3022_);
lean_ctor_set(v_reuseFailAlloc_3096_, 1, v___x_2994_);
v___x_3081_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
lean_object* v___x_3083_; 
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 1, v___x_3081_);
lean_ctor_set(v___x_2952_, 0, v___x_3050_);
v___x_3083_ = v___x_2952_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3050_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v___x_3081_);
v___x_3083_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
lean_object* v___x_3085_; 
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 1, v___x_3083_);
lean_ctor_set(v___x_2948_, 0, v___x_3078_);
v___x_3085_ = v___x_2948_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3078_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v___x_3083_);
v___x_3085_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
lean_object* v___x_3087_; 
if (v_isShared_2945_ == 0)
{
lean_ctor_set(v___x_2944_, 1, v___x_3085_);
v___x_3087_ = v___x_2944_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_fst_2942_);
lean_ctor_set(v_reuseFailAlloc_3093_, 1, v___x_3085_);
v___x_3087_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
lean_object* v___x_3089_; 
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 1, v___x_3087_);
v___x_3089_ = v___x_2940_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_fst_2938_);
lean_ctor_set(v_reuseFailAlloc_3092_, 1, v___x_3087_);
v___x_3089_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3089_);
v___x_3091_ = lean_apply_2(v_toPure_2913_, lean_box(0), v___x_3090_);
v___y_2963_ = v___x_3091_;
goto v___jp_2962_;
}
}
}
}
}
}
else
{
lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3120_; 
lean_inc(v_stop_3074_);
lean_inc(v_start_3073_);
lean_inc_ref(v_array_3072_);
lean_del_object(v___x_2956_);
lean_del_object(v___x_2952_);
lean_del_object(v___x_2948_);
lean_del_object(v___x_2944_);
lean_del_object(v___x_2940_);
v_isSharedCheck_3120_ = !lean_is_exclusive(v_fst_2942_);
if (v_isSharedCheck_3120_ == 0)
{
lean_object* v_unused_3121_; lean_object* v_unused_3122_; lean_object* v_unused_3123_; 
v_unused_3121_ = lean_ctor_get(v_fst_2942_, 2);
lean_dec(v_unused_3121_);
v_unused_3122_ = lean_ctor_get(v_fst_2942_, 1);
lean_dec(v_unused_3122_);
v_unused_3123_ = lean_ctor_get(v_fst_2942_, 0);
lean_dec(v_unused_3123_);
v___x_3098_ = v_fst_2942_;
v_isShared_3099_ = v_isSharedCheck_3120_;
goto v_resetjp_3097_;
}
else
{
lean_dec(v_fst_2942_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3120_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v_numOverlaps_3100_; uint8_t v_hasUnitThunk_3101_; uint8_t v___x_3102_; 
v_numOverlaps_3100_ = lean_ctor_get(v___x_3075_, 1);
v_hasUnitThunk_3101_ = lean_ctor_get_uint8(v___x_3075_, sizeof(void*)*2);
v___x_3102_ = lean_nat_dec_eq(v_numOverlaps_3100_, v___x_2916_);
if (v___x_3102_ == 0)
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
lean_del_object(v___x_3098_);
lean_dec_ref(v___x_3078_);
lean_dec(v___x_3075_);
lean_dec(v_stop_3074_);
lean_dec(v_start_3073_);
lean_dec_ref(v_array_3072_);
lean_dec_ref(v___x_3050_);
lean_dec(v___x_3047_);
lean_dec_ref(v___x_3022_);
lean_dec(v___x_3019_);
lean_dec_ref(v___x_2994_);
lean_dec(v___x_2990_);
lean_dec(v_fst_2938_);
lean_dec(v_next_2927_);
lean_dec(v_numDiscrEqs_2926_);
lean_dec_ref(v_inst_2925_);
lean_dec(v_fst_2924_);
lean_dec(v___f_2923_);
lean_dec(v_onAlt_2922_);
lean_dec_ref(v_inst_2919_);
lean_dec(v_inst_2918_);
lean_dec(v_toPure_2913_);
v___x_3103_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7);
v___x_3104_ = l_instInhabitedOfMonad___redArg(v_inst_2917_, v___x_3103_);
v___x_3105_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9);
v___x_3106_ = l_panic___redArg(v___x_3104_, v___x_3105_);
lean_dec(v___x_3104_);
v___y_2963_ = v___x_3106_;
goto v___jp_2962_;
}
else
{
lean_object* v___f_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___f_3112_; lean_object* v___x_3113_; lean_object* v___x_3115_; 
lean_inc(v_inst_2918_);
lean_inc_n(v_toPure_2913_, 2);
lean_inc(v___x_3047_);
v___f_3107_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed), 4, 3);
lean_closure_set(v___f_3107_, 0, v___x_3047_);
lean_closure_set(v___f_3107_, 1, v_toPure_2913_);
lean_closure_set(v___f_3107_, 2, v_inst_2918_);
v___x_3108_ = lean_array_fget_borrowed(v_array_3072_, v_start_3073_);
v___x_3109_ = lean_box(v___x_2920_);
v___x_3110_ = lean_box(v_useSplitter_2921_);
v___x_3111_ = lean_box(v_hasUnitThunk_3101_);
lean_inc_ref(v_inst_2925_);
lean_inc(v___x_3108_);
lean_inc(v_toBind_2914_);
lean_inc_ref(v_inst_2917_);
v___f_3112_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed), 21, 19);
lean_closure_set(v___f_3112_, 0, v___x_3047_);
lean_closure_set(v___f_3112_, 1, v_inst_2917_);
lean_closure_set(v___f_3112_, 2, v_inst_2919_);
lean_closure_set(v___f_3112_, 3, v___x_3109_);
lean_closure_set(v___f_3112_, 4, v___x_3110_);
lean_closure_set(v___f_3112_, 5, v_inst_2918_);
lean_closure_set(v___f_3112_, 6, v_onAlt_2922_);
lean_closure_set(v___f_3112_, 7, v_next_2927_);
lean_closure_set(v___f_3112_, 8, v_toBind_2914_);
lean_closure_set(v___f_3112_, 9, v___x_3108_);
lean_closure_set(v___f_3112_, 10, v___f_2923_);
lean_closure_set(v___f_3112_, 11, v_fst_2924_);
lean_closure_set(v___f_3112_, 12, v_inst_2925_);
lean_closure_set(v___f_3112_, 13, v_numDiscrEqs_2926_);
lean_closure_set(v___f_3112_, 14, v___f_3107_);
lean_closure_set(v___f_3112_, 15, v___x_3111_);
lean_closure_set(v___f_3112_, 16, v_toPure_2913_);
lean_closure_set(v___f_3112_, 17, v___x_2991_);
lean_closure_set(v___f_3112_, 18, v___x_2990_);
v___x_3113_ = lean_nat_add(v_start_3073_, v___x_2991_);
lean_dec(v_start_3073_);
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 1, v___x_3113_);
v___x_3115_ = v___x_3098_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_array_3072_);
lean_ctor_set(v_reuseFailAlloc_3119_, 1, v___x_3113_);
lean_ctor_set(v_reuseFailAlloc_3119_, 2, v_stop_3074_);
v___x_3115_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
lean_object* v___f_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___f_3116_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__45), 8, 7);
lean_closure_set(v___f_3116_, 0, v_fst_2938_);
lean_closure_set(v___f_3116_, 1, v___x_3022_);
lean_closure_set(v___f_3116_, 2, v___x_2994_);
lean_closure_set(v___f_3116_, 3, v___x_3050_);
lean_closure_set(v___f_3116_, 4, v___x_3078_);
lean_closure_set(v___f_3116_, 5, v___x_3115_);
lean_closure_set(v___f_3116_, 6, v_toPure_2913_);
v___x_3117_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(v_inst_2917_, v_inst_2925_, v___x_3019_, v___x_3075_, v___f_3112_);
lean_inc(v_toBind_2914_);
v___x_3118_ = lean_apply_4(v_toBind_2914_, lean_box(0), lean_box(0), v___x_3117_, v___f_3116_);
v___y_2963_ = v___x_3118_;
goto v___jp_2962_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_2962_:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_inc(v_toBind_2914_);
v___x_2964_ = lean_apply_4(v_toBind_2914_, lean_box(0), lean_box(0), v___y_2963_, v___f_2915_);
v___x_2965_ = lean_apply_4(v_toBind_2914_, lean_box(0), lean_box(0), v___x_2964_, v___f_2961_);
return v___x_2965_;
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
lean_object* v___x_3154_ = _args[0];
lean_object* v_toPure_3155_ = _args[1];
lean_object* v_toBind_3156_ = _args[2];
lean_object* v___f_3157_ = _args[3];
lean_object* v___x_3158_ = _args[4];
lean_object* v_inst_3159_ = _args[5];
lean_object* v_inst_3160_ = _args[6];
lean_object* v_inst_3161_ = _args[7];
lean_object* v___x_3162_ = _args[8];
lean_object* v_useSplitter_3163_ = _args[9];
lean_object* v_onAlt_3164_ = _args[10];
lean_object* v___f_3165_ = _args[11];
lean_object* v_fst_3166_ = _args[12];
lean_object* v_inst_3167_ = _args[13];
lean_object* v_numDiscrEqs_3168_ = _args[14];
lean_object* v_next_3169_ = _args[15];
lean_object* v_acc_3170_ = _args[16];
lean_object* v_h_3171_ = _args[17];
lean_object* v_G_3172_ = _args[18];
_start:
{
uint8_t v___x_15883__boxed_3173_; uint8_t v_useSplitter_boxed_3174_; lean_object* v_res_3175_; 
v___x_15883__boxed_3173_ = lean_unbox(v___x_3162_);
v_useSplitter_boxed_3174_ = lean_unbox(v_useSplitter_3163_);
v_res_3175_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__46(v___x_3154_, v_toPure_3155_, v_toBind_3156_, v___f_3157_, v___x_3158_, v_inst_3159_, v_inst_3160_, v_inst_3161_, v___x_15883__boxed_3173_, v_useSplitter_boxed_3174_, v_onAlt_3164_, v___f_3165_, v_fst_3166_, v_inst_3167_, v_numDiscrEqs_3168_, v_next_3169_, v_acc_3170_, v_h_3171_, v_G_3172_);
lean_dec(v___x_3158_);
lean_dec(v___x_3154_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47(lean_object* v_fst_3176_, lean_object* v_numParams_3177_, lean_object* v_numDiscrs_3178_, lean_object* v_altInfos_3179_, lean_object* v_uElimPos_x3f_3180_, lean_object* v_snd_3181_, lean_object* v_overlaps_3182_, lean_object* v_splitterName_3183_, lean_object* v_matcherLevels_3184_, lean_object* v_params_x27_3185_, lean_object* v_fst_3186_, lean_object* v_discrs_x27_3187_, lean_object* v_fst_3188_, lean_object* v_toPure_3189_, lean_object* v_____do__lift_3190_){
_start:
{
lean_object* v_remaining_x27_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v_remaining_x27_3191_ = l_Array_append___redArg(v_fst_3176_, v_____do__lift_3190_);
v___x_3192_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3192_, 0, v_numParams_3177_);
lean_ctor_set(v___x_3192_, 1, v_numDiscrs_3178_);
lean_ctor_set(v___x_3192_, 2, v_altInfos_3179_);
lean_ctor_set(v___x_3192_, 3, v_uElimPos_x3f_3180_);
lean_ctor_set(v___x_3192_, 4, v_snd_3181_);
lean_ctor_set(v___x_3192_, 5, v_overlaps_3182_);
v___x_3193_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3192_);
lean_ctor_set(v___x_3193_, 1, v_splitterName_3183_);
lean_ctor_set(v___x_3193_, 2, v_matcherLevels_3184_);
lean_ctor_set(v___x_3193_, 3, v_params_x27_3185_);
lean_ctor_set(v___x_3193_, 4, v_fst_3186_);
lean_ctor_set(v___x_3193_, 5, v_discrs_x27_3187_);
lean_ctor_set(v___x_3193_, 6, v_fst_3188_);
lean_ctor_set(v___x_3193_, 7, v_remaining_x27_3191_);
v___x_3194_ = lean_apply_2(v_toPure_3189_, lean_box(0), v___x_3193_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47___boxed(lean_object* v_fst_3195_, lean_object* v_numParams_3196_, lean_object* v_numDiscrs_3197_, lean_object* v_altInfos_3198_, lean_object* v_uElimPos_x3f_3199_, lean_object* v_snd_3200_, lean_object* v_overlaps_3201_, lean_object* v_splitterName_3202_, lean_object* v_matcherLevels_3203_, lean_object* v_params_x27_3204_, lean_object* v_fst_3205_, lean_object* v_discrs_x27_3206_, lean_object* v_fst_3207_, lean_object* v_toPure_3208_, lean_object* v_____do__lift_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__47(v_fst_3195_, v_numParams_3196_, v_numDiscrs_3197_, v_altInfos_3198_, v_uElimPos_x3f_3199_, v_snd_3200_, v_overlaps_3201_, v_splitterName_3202_, v_matcherLevels_3203_, v_params_x27_3204_, v_fst_3205_, v_discrs_x27_3206_, v_fst_3207_, v_toPure_3208_, v_____do__lift_3209_);
lean_dec_ref(v_____do__lift_3209_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48(lean_object* v_fst_3211_, lean_object* v_numParams_3212_, lean_object* v_numDiscrs_3213_, lean_object* v_altInfos_3214_, lean_object* v_uElimPos_x3f_3215_, lean_object* v_snd_3216_, lean_object* v_overlaps_3217_, lean_object* v_splitterName_3218_, lean_object* v_matcherLevels_3219_, lean_object* v_params_x27_3220_, lean_object* v_fst_3221_, lean_object* v_discrs_x27_3222_, lean_object* v_toPure_3223_, lean_object* v_onRemaining_3224_, lean_object* v_remaining_3225_, lean_object* v_toBind_3226_, lean_object* v_____s_3227_){
_start:
{
lean_object* v_fst_3228_; lean_object* v___f_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v_fst_3228_ = lean_ctor_get(v_____s_3227_, 0);
lean_inc(v_fst_3228_);
lean_dec_ref(v_____s_3227_);
v___f_3229_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__47___boxed), 15, 14);
lean_closure_set(v___f_3229_, 0, v_fst_3211_);
lean_closure_set(v___f_3229_, 1, v_numParams_3212_);
lean_closure_set(v___f_3229_, 2, v_numDiscrs_3213_);
lean_closure_set(v___f_3229_, 3, v_altInfos_3214_);
lean_closure_set(v___f_3229_, 4, v_uElimPos_x3f_3215_);
lean_closure_set(v___f_3229_, 5, v_snd_3216_);
lean_closure_set(v___f_3229_, 6, v_overlaps_3217_);
lean_closure_set(v___f_3229_, 7, v_splitterName_3218_);
lean_closure_set(v___f_3229_, 8, v_matcherLevels_3219_);
lean_closure_set(v___f_3229_, 9, v_params_x27_3220_);
lean_closure_set(v___f_3229_, 10, v_fst_3221_);
lean_closure_set(v___f_3229_, 11, v_discrs_x27_3222_);
lean_closure_set(v___f_3229_, 12, v_fst_3228_);
lean_closure_set(v___f_3229_, 13, v_toPure_3223_);
v___x_3230_ = lean_apply_1(v_onRemaining_3224_, v_remaining_3225_);
v___x_3231_ = lean_apply_4(v_toBind_3226_, lean_box(0), lean_box(0), v___x_3230_, v___f_3229_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed(lean_object** _args){
lean_object* v_fst_3232_ = _args[0];
lean_object* v_numParams_3233_ = _args[1];
lean_object* v_numDiscrs_3234_ = _args[2];
lean_object* v_altInfos_3235_ = _args[3];
lean_object* v_uElimPos_x3f_3236_ = _args[4];
lean_object* v_snd_3237_ = _args[5];
lean_object* v_overlaps_3238_ = _args[6];
lean_object* v_splitterName_3239_ = _args[7];
lean_object* v_matcherLevels_3240_ = _args[8];
lean_object* v_params_x27_3241_ = _args[9];
lean_object* v_fst_3242_ = _args[10];
lean_object* v_discrs_x27_3243_ = _args[11];
lean_object* v_toPure_3244_ = _args[12];
lean_object* v_onRemaining_3245_ = _args[13];
lean_object* v_remaining_3246_ = _args[14];
lean_object* v_toBind_3247_ = _args[15];
lean_object* v_____s_3248_ = _args[16];
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__48(v_fst_3232_, v_numParams_3233_, v_numDiscrs_3234_, v_altInfos_3235_, v_uElimPos_x3f_3236_, v_snd_3237_, v_overlaps_3238_, v_splitterName_3239_, v_matcherLevels_3240_, v_params_x27_3241_, v_fst_3242_, v_discrs_x27_3243_, v_toPure_3244_, v_onRemaining_3245_, v_remaining_3246_, v_toBind_3247_, v_____s_3248_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49(lean_object* v_splitterMatchInfo_3250_, lean_object* v_fst_3251_, lean_object* v_numParams_3252_, lean_object* v_numDiscrs_3253_, lean_object* v_altInfos_3254_, lean_object* v_uElimPos_x3f_3255_, lean_object* v_snd_3256_, lean_object* v_overlaps_3257_, lean_object* v_splitterName_3258_, lean_object* v_matcherLevels_3259_, lean_object* v_params_x27_3260_, lean_object* v_fst_3261_, lean_object* v_discrs_x27_3262_, lean_object* v_toPure_3263_, lean_object* v_onRemaining_3264_, lean_object* v_remaining_3265_, lean_object* v_toBind_3266_, lean_object* v_origAltTypes_3267_, lean_object* v_alts_3268_, lean_object* v___x_3269_, lean_object* v___x_3270_, lean_object* v_remaining_x27_3271_, lean_object* v___f_3272_, lean_object* v_altTypes_3273_){
_start:
{
lean_object* v_altInfos_3274_; lean_object* v___f_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v_altInfos_3274_ = lean_ctor_get(v_splitterMatchInfo_3250_, 2);
lean_inc_ref(v_altInfos_3274_);
lean_dec_ref(v_splitterMatchInfo_3250_);
lean_inc(v_toBind_3266_);
lean_inc_ref(v_altInfos_3254_);
v___f_3275_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 17, 16);
lean_closure_set(v___f_3275_, 0, v_fst_3251_);
lean_closure_set(v___f_3275_, 1, v_numParams_3252_);
lean_closure_set(v___f_3275_, 2, v_numDiscrs_3253_);
lean_closure_set(v___f_3275_, 3, v_altInfos_3254_);
lean_closure_set(v___f_3275_, 4, v_uElimPos_x3f_3255_);
lean_closure_set(v___f_3275_, 5, v_snd_3256_);
lean_closure_set(v___f_3275_, 6, v_overlaps_3257_);
lean_closure_set(v___f_3275_, 7, v_splitterName_3258_);
lean_closure_set(v___f_3275_, 8, v_matcherLevels_3259_);
lean_closure_set(v___f_3275_, 9, v_params_x27_3260_);
lean_closure_set(v___f_3275_, 10, v_fst_3261_);
lean_closure_set(v___f_3275_, 11, v_discrs_x27_3262_);
lean_closure_set(v___f_3275_, 12, v_toPure_3263_);
lean_closure_set(v___f_3275_, 13, v_onRemaining_3264_);
lean_closure_set(v___f_3275_, 14, v_remaining_3265_);
lean_closure_set(v___f_3275_, 15, v_toBind_3266_);
v___x_3276_ = lean_array_get_size(v_altInfos_3254_);
v___x_3277_ = lean_array_get_size(v_altInfos_3274_);
v___x_3278_ = lean_array_get_size(v_origAltTypes_3267_);
v___x_3279_ = lean_array_get_size(v_altTypes_3273_);
lean_inc_n(v___x_3269_, 5);
v___x_3280_ = l_Array_toSubarray___redArg(v_alts_3268_, v___x_3269_, v___x_3270_);
v___x_3281_ = l_Array_toSubarray___redArg(v_altInfos_3254_, v___x_3269_, v___x_3276_);
v___x_3282_ = l_Array_toSubarray___redArg(v_altInfos_3274_, v___x_3269_, v___x_3277_);
v___x_3283_ = l_Array_toSubarray___redArg(v_origAltTypes_3267_, v___x_3269_, v___x_3278_);
v___x_3284_ = l_Array_toSubarray___redArg(v_altTypes_3273_, v___x_3269_, v___x_3279_);
v___x_3285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3283_);
lean_ctor_set(v___x_3285_, 1, v___x_3284_);
v___x_3286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3282_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
v___x_3287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3281_);
lean_ctor_set(v___x_3287_, 1, v___x_3286_);
v___x_3288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3280_);
lean_ctor_set(v___x_3288_, 1, v___x_3287_);
v___x_3289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3289_, 0, v_remaining_x27_3271_);
lean_ctor_set(v___x_3289_, 1, v___x_3288_);
v___x_3290_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3272_, v___x_3269_, v___x_3289_, lean_box(0));
v___x_3291_ = lean_apply_4(v_toBind_3266_, lean_box(0), lean_box(0), v___x_3290_, v___f_3275_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed(lean_object** _args){
lean_object* v_splitterMatchInfo_3292_ = _args[0];
lean_object* v_fst_3293_ = _args[1];
lean_object* v_numParams_3294_ = _args[2];
lean_object* v_numDiscrs_3295_ = _args[3];
lean_object* v_altInfos_3296_ = _args[4];
lean_object* v_uElimPos_x3f_3297_ = _args[5];
lean_object* v_snd_3298_ = _args[6];
lean_object* v_overlaps_3299_ = _args[7];
lean_object* v_splitterName_3300_ = _args[8];
lean_object* v_matcherLevels_3301_ = _args[9];
lean_object* v_params_x27_3302_ = _args[10];
lean_object* v_fst_3303_ = _args[11];
lean_object* v_discrs_x27_3304_ = _args[12];
lean_object* v_toPure_3305_ = _args[13];
lean_object* v_onRemaining_3306_ = _args[14];
lean_object* v_remaining_3307_ = _args[15];
lean_object* v_toBind_3308_ = _args[16];
lean_object* v_origAltTypes_3309_ = _args[17];
lean_object* v_alts_3310_ = _args[18];
lean_object* v___x_3311_ = _args[19];
lean_object* v___x_3312_ = _args[20];
lean_object* v_remaining_x27_3313_ = _args[21];
lean_object* v___f_3314_ = _args[22];
lean_object* v_altTypes_3315_ = _args[23];
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__49(v_splitterMatchInfo_3292_, v_fst_3293_, v_numParams_3294_, v_numDiscrs_3295_, v_altInfos_3296_, v_uElimPos_x3f_3297_, v_snd_3298_, v_overlaps_3299_, v_splitterName_3300_, v_matcherLevels_3301_, v_params_x27_3302_, v_fst_3303_, v_discrs_x27_3304_, v_toPure_3305_, v_onRemaining_3306_, v_remaining_3307_, v_toBind_3308_, v_origAltTypes_3309_, v_alts_3310_, v___x_3311_, v___x_3312_, v_remaining_x27_3313_, v___f_3314_, v_altTypes_3315_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__50(lean_object* v___x_3317_, lean_object* v_aux2_3318_, lean_object* v_inst_3319_, lean_object* v_toBind_3320_, lean_object* v___f_3321_, lean_object* v_____r_3322_){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3323_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_3323_, 0, v___x_3317_);
lean_closure_set(v___x_3323_, 1, v_aux2_3318_);
v___x_3324_ = lean_apply_2(v_inst_3319_, lean_box(0), v___x_3323_);
v___x_3325_ = lean_apply_4(v_toBind_3320_, lean_box(0), lean_box(0), v___x_3324_, v___f_3321_);
return v___x_3325_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1(void){
_start:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3327_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__0));
v___x_3328_ = l_Lean_stringToMessageData(v___x_3327_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53(lean_object* v___x_3329_, lean_object* v_params_x27_3330_, lean_object* v_fst_3331_, lean_object* v_discrs_x27_3332_, lean_object* v_fst_3333_, lean_object* v_numParams_3334_, lean_object* v_numDiscrs_3335_, lean_object* v_altInfos_3336_, lean_object* v_uElimPos_x3f_3337_, lean_object* v_snd_3338_, lean_object* v_overlaps_3339_, lean_object* v_matcherLevels_3340_, lean_object* v_toPure_3341_, lean_object* v_onRemaining_3342_, lean_object* v_remaining_3343_, lean_object* v_toBind_3344_, lean_object* v_origAltTypes_3345_, lean_object* v_alts_3346_, lean_object* v___x_3347_, lean_object* v___x_3348_, lean_object* v_remaining_x27_3349_, lean_object* v___f_3350_, lean_object* v_inst_3351_, lean_object* v___x_3352_, lean_object* v_liftWith_3353_, lean_object* v_restoreM_3354_, lean_object* v_matchEqns_3355_){
_start:
{
lean_object* v_splitterName_3356_; lean_object* v_splitterMatchInfo_3357_; lean_object* v___x_3358_; lean_object* v_aux2_3359_; lean_object* v_aux2_3360_; lean_object* v_aux2_3361_; lean_object* v___x_3362_; lean_object* v___f_3363_; lean_object* v___f_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___f_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___f_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v_splitterName_3356_ = lean_ctor_get(v_matchEqns_3355_, 1);
lean_inc_n(v_splitterName_3356_, 2);
v_splitterMatchInfo_3357_ = lean_ctor_get(v_matchEqns_3355_, 2);
lean_inc_ref(v_splitterMatchInfo_3357_);
lean_dec_ref(v_matchEqns_3355_);
v___x_3358_ = l_Lean_mkConst(v_splitterName_3356_, v___x_3329_);
v_aux2_3359_ = l_Lean_mkAppN(v___x_3358_, v_params_x27_3330_);
lean_inc_ref(v_fst_3331_);
v_aux2_3360_ = l_Lean_Expr_app___override(v_aux2_3359_, v_fst_3331_);
v_aux2_3361_ = l_Lean_mkAppN(v_aux2_3360_, v_discrs_x27_3332_);
lean_inc_ref_n(v_aux2_3361_, 2);
v___x_3362_ = l_Lean_indentExpr(v_aux2_3361_);
lean_inc(v___x_3348_);
lean_inc_n(v_toBind_3344_, 3);
v___f_3363_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed), 24, 23);
lean_closure_set(v___f_3363_, 0, v_splitterMatchInfo_3357_);
lean_closure_set(v___f_3363_, 1, v_fst_3333_);
lean_closure_set(v___f_3363_, 2, v_numParams_3334_);
lean_closure_set(v___f_3363_, 3, v_numDiscrs_3335_);
lean_closure_set(v___f_3363_, 4, v_altInfos_3336_);
lean_closure_set(v___f_3363_, 5, v_uElimPos_x3f_3337_);
lean_closure_set(v___f_3363_, 6, v_snd_3338_);
lean_closure_set(v___f_3363_, 7, v_overlaps_3339_);
lean_closure_set(v___f_3363_, 8, v_splitterName_3356_);
lean_closure_set(v___f_3363_, 9, v_matcherLevels_3340_);
lean_closure_set(v___f_3363_, 10, v_params_x27_3330_);
lean_closure_set(v___f_3363_, 11, v_fst_3331_);
lean_closure_set(v___f_3363_, 12, v_discrs_x27_3332_);
lean_closure_set(v___f_3363_, 13, v_toPure_3341_);
lean_closure_set(v___f_3363_, 14, v_onRemaining_3342_);
lean_closure_set(v___f_3363_, 15, v_remaining_3343_);
lean_closure_set(v___f_3363_, 16, v_toBind_3344_);
lean_closure_set(v___f_3363_, 17, v_origAltTypes_3345_);
lean_closure_set(v___f_3363_, 18, v_alts_3346_);
lean_closure_set(v___f_3363_, 19, v___x_3347_);
lean_closure_set(v___f_3363_, 20, v___x_3348_);
lean_closure_set(v___f_3363_, 21, v_remaining_x27_3349_);
lean_closure_set(v___f_3363_, 22, v___f_3350_);
lean_inc(v_inst_3351_);
v___f_3364_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__50), 6, 5);
lean_closure_set(v___f_3364_, 0, v___x_3348_);
lean_closure_set(v___f_3364_, 1, v_aux2_3361_);
lean_closure_set(v___f_3364_, 2, v_inst_3351_);
lean_closure_set(v___f_3364_, 3, v_toBind_3344_);
lean_closure_set(v___f_3364_, 4, v___f_3363_);
v___x_3365_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1);
v___x_3366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
lean_ctor_set(v___x_3366_, 1, v___x_3362_);
v___x_3367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3366_);
lean_ctor_set(v___x_3367_, 1, v___x_3352_);
v___f_3368_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3368_, 0, v___x_3367_);
v___x_3369_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(v___x_3369_, 0, v_aux2_3361_);
v___x_3370_ = lean_apply_2(v_inst_3351_, lean_box(0), v___x_3369_);
v___f_3371_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3371_, 0, v___x_3370_);
lean_closure_set(v___f_3371_, 1, v___f_3368_);
v___x_3372_ = lean_apply_2(v_liftWith_3353_, lean_box(0), v___f_3371_);
v___x_3373_ = lean_apply_1(v_restoreM_3354_, lean_box(0));
v___x_3374_ = lean_apply_4(v_toBind_3344_, lean_box(0), lean_box(0), v___x_3372_, v___x_3373_);
v___x_3375_ = lean_apply_4(v_toBind_3344_, lean_box(0), lean_box(0), v___x_3374_, v___f_3364_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed(lean_object** _args){
lean_object* v___x_3376_ = _args[0];
lean_object* v_params_x27_3377_ = _args[1];
lean_object* v_fst_3378_ = _args[2];
lean_object* v_discrs_x27_3379_ = _args[3];
lean_object* v_fst_3380_ = _args[4];
lean_object* v_numParams_3381_ = _args[5];
lean_object* v_numDiscrs_3382_ = _args[6];
lean_object* v_altInfos_3383_ = _args[7];
lean_object* v_uElimPos_x3f_3384_ = _args[8];
lean_object* v_snd_3385_ = _args[9];
lean_object* v_overlaps_3386_ = _args[10];
lean_object* v_matcherLevels_3387_ = _args[11];
lean_object* v_toPure_3388_ = _args[12];
lean_object* v_onRemaining_3389_ = _args[13];
lean_object* v_remaining_3390_ = _args[14];
lean_object* v_toBind_3391_ = _args[15];
lean_object* v_origAltTypes_3392_ = _args[16];
lean_object* v_alts_3393_ = _args[17];
lean_object* v___x_3394_ = _args[18];
lean_object* v___x_3395_ = _args[19];
lean_object* v_remaining_x27_3396_ = _args[20];
lean_object* v___f_3397_ = _args[21];
lean_object* v_inst_3398_ = _args[22];
lean_object* v___x_3399_ = _args[23];
lean_object* v_liftWith_3400_ = _args[24];
lean_object* v_restoreM_3401_ = _args[25];
lean_object* v_matchEqns_3402_ = _args[26];
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__53(v___x_3376_, v_params_x27_3377_, v_fst_3378_, v_discrs_x27_3379_, v_fst_3380_, v_numParams_3381_, v_numDiscrs_3382_, v_altInfos_3383_, v_uElimPos_x3f_3384_, v_snd_3385_, v_overlaps_3386_, v_matcherLevels_3387_, v_toPure_3388_, v_onRemaining_3389_, v_remaining_3390_, v_toBind_3391_, v_origAltTypes_3392_, v_alts_3393_, v___x_3394_, v___x_3395_, v_remaining_x27_3396_, v___f_3397_, v_inst_3398_, v___x_3399_, v_liftWith_3400_, v_restoreM_3401_, v_matchEqns_3402_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51(lean_object* v___x_3404_, lean_object* v_params_x27_3405_, lean_object* v_fst_3406_, lean_object* v_discrs_x27_3407_, lean_object* v_fst_3408_, lean_object* v_numParams_3409_, lean_object* v_numDiscrs_3410_, lean_object* v_altInfos_3411_, lean_object* v_uElimPos_x3f_3412_, lean_object* v_snd_3413_, lean_object* v_overlaps_3414_, lean_object* v_matcherLevels_3415_, lean_object* v_toPure_3416_, lean_object* v_onRemaining_3417_, lean_object* v_remaining_3418_, lean_object* v_toBind_3419_, lean_object* v_alts_3420_, lean_object* v___x_3421_, lean_object* v___x_3422_, lean_object* v_remaining_x27_3423_, lean_object* v___f_3424_, lean_object* v_inst_3425_, lean_object* v___x_3426_, lean_object* v_liftWith_3427_, lean_object* v_restoreM_3428_, lean_object* v_matcherName_3429_, lean_object* v_origAltTypes_3430_){
_start:
{
lean_object* v___f_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
lean_inc(v_inst_3425_);
lean_inc(v_toBind_3419_);
v___f_3431_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed), 27, 26);
lean_closure_set(v___f_3431_, 0, v___x_3404_);
lean_closure_set(v___f_3431_, 1, v_params_x27_3405_);
lean_closure_set(v___f_3431_, 2, v_fst_3406_);
lean_closure_set(v___f_3431_, 3, v_discrs_x27_3407_);
lean_closure_set(v___f_3431_, 4, v_fst_3408_);
lean_closure_set(v___f_3431_, 5, v_numParams_3409_);
lean_closure_set(v___f_3431_, 6, v_numDiscrs_3410_);
lean_closure_set(v___f_3431_, 7, v_altInfos_3411_);
lean_closure_set(v___f_3431_, 8, v_uElimPos_x3f_3412_);
lean_closure_set(v___f_3431_, 9, v_snd_3413_);
lean_closure_set(v___f_3431_, 10, v_overlaps_3414_);
lean_closure_set(v___f_3431_, 11, v_matcherLevels_3415_);
lean_closure_set(v___f_3431_, 12, v_toPure_3416_);
lean_closure_set(v___f_3431_, 13, v_onRemaining_3417_);
lean_closure_set(v___f_3431_, 14, v_remaining_3418_);
lean_closure_set(v___f_3431_, 15, v_toBind_3419_);
lean_closure_set(v___f_3431_, 16, v_origAltTypes_3430_);
lean_closure_set(v___f_3431_, 17, v_alts_3420_);
lean_closure_set(v___f_3431_, 18, v___x_3421_);
lean_closure_set(v___f_3431_, 19, v___x_3422_);
lean_closure_set(v___f_3431_, 20, v_remaining_x27_3423_);
lean_closure_set(v___f_3431_, 21, v___f_3424_);
lean_closure_set(v___f_3431_, 22, v_inst_3425_);
lean_closure_set(v___f_3431_, 23, v___x_3426_);
lean_closure_set(v___f_3431_, 24, v_liftWith_3427_);
lean_closure_set(v___f_3431_, 25, v_restoreM_3428_);
v___x_3432_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_getEquationsFor___boxed), 6, 1);
lean_closure_set(v___x_3432_, 0, v_matcherName_3429_);
v___x_3433_ = lean_apply_2(v_inst_3425_, lean_box(0), v___x_3432_);
v___x_3434_ = lean_apply_4(v_toBind_3419_, lean_box(0), lean_box(0), v___x_3433_, v___f_3431_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed(lean_object** _args){
lean_object* v___x_3435_ = _args[0];
lean_object* v_params_x27_3436_ = _args[1];
lean_object* v_fst_3437_ = _args[2];
lean_object* v_discrs_x27_3438_ = _args[3];
lean_object* v_fst_3439_ = _args[4];
lean_object* v_numParams_3440_ = _args[5];
lean_object* v_numDiscrs_3441_ = _args[6];
lean_object* v_altInfos_3442_ = _args[7];
lean_object* v_uElimPos_x3f_3443_ = _args[8];
lean_object* v_snd_3444_ = _args[9];
lean_object* v_overlaps_3445_ = _args[10];
lean_object* v_matcherLevels_3446_ = _args[11];
lean_object* v_toPure_3447_ = _args[12];
lean_object* v_onRemaining_3448_ = _args[13];
lean_object* v_remaining_3449_ = _args[14];
lean_object* v_toBind_3450_ = _args[15];
lean_object* v_alts_3451_ = _args[16];
lean_object* v___x_3452_ = _args[17];
lean_object* v___x_3453_ = _args[18];
lean_object* v_remaining_x27_3454_ = _args[19];
lean_object* v___f_3455_ = _args[20];
lean_object* v_inst_3456_ = _args[21];
lean_object* v___x_3457_ = _args[22];
lean_object* v_liftWith_3458_ = _args[23];
lean_object* v_restoreM_3459_ = _args[24];
lean_object* v_matcherName_3460_ = _args[25];
lean_object* v_origAltTypes_3461_ = _args[26];
_start:
{
lean_object* v_res_3462_; 
v_res_3462_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__51(v___x_3435_, v_params_x27_3436_, v_fst_3437_, v_discrs_x27_3438_, v_fst_3439_, v_numParams_3440_, v_numDiscrs_3441_, v_altInfos_3442_, v_uElimPos_x3f_3443_, v_snd_3444_, v_overlaps_3445_, v_matcherLevels_3446_, v_toPure_3447_, v_onRemaining_3448_, v_remaining_3449_, v_toBind_3450_, v_alts_3451_, v___x_3452_, v___x_3453_, v_remaining_x27_3454_, v___f_3455_, v_inst_3456_, v___x_3457_, v_liftWith_3458_, v_restoreM_3459_, v_matcherName_3460_, v_origAltTypes_3461_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52(lean_object* v_alts_3463_, lean_object* v_toPure_3464_, lean_object* v_toBind_3465_, lean_object* v___f_3466_, lean_object* v___x_3467_, lean_object* v_inst_3468_, lean_object* v_inst_3469_, lean_object* v_inst_3470_, uint8_t v___x_3471_, uint8_t v_useSplitter_3472_, lean_object* v_onAlt_3473_, lean_object* v___f_3474_, lean_object* v_fst_3475_, lean_object* v_inst_3476_, lean_object* v_numDiscrEqs_3477_, lean_object* v___x_3478_, lean_object* v_params_x27_3479_, lean_object* v_fst_3480_, lean_object* v_discrs_x27_3481_, lean_object* v_fst_3482_, lean_object* v_numParams_3483_, lean_object* v_numDiscrs_3484_, lean_object* v_altInfos_3485_, lean_object* v_uElimPos_x3f_3486_, lean_object* v_snd_3487_, lean_object* v_overlaps_3488_, lean_object* v_matcherLevels_3489_, lean_object* v_onRemaining_3490_, lean_object* v_remaining_3491_, lean_object* v_remaining_x27_3492_, lean_object* v___x_3493_, lean_object* v_liftWith_3494_, lean_object* v_restoreM_3495_, lean_object* v_matcherName_3496_, lean_object* v_aux1_3497_, lean_object* v_____r_3498_){
_start:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___f_3502_; lean_object* v___f_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3499_ = lean_array_get_size(v_alts_3463_);
v___x_3500_ = lean_box(v___x_3471_);
v___x_3501_ = lean_box(v_useSplitter_3472_);
lean_inc_n(v_inst_3469_, 2);
lean_inc(v___x_3467_);
lean_inc_n(v_toBind_3465_, 2);
lean_inc(v_toPure_3464_);
v___f_3502_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46___boxed), 19, 15);
lean_closure_set(v___f_3502_, 0, v___x_3499_);
lean_closure_set(v___f_3502_, 1, v_toPure_3464_);
lean_closure_set(v___f_3502_, 2, v_toBind_3465_);
lean_closure_set(v___f_3502_, 3, v___f_3466_);
lean_closure_set(v___f_3502_, 4, v___x_3467_);
lean_closure_set(v___f_3502_, 5, v_inst_3468_);
lean_closure_set(v___f_3502_, 6, v_inst_3469_);
lean_closure_set(v___f_3502_, 7, v_inst_3470_);
lean_closure_set(v___f_3502_, 8, v___x_3500_);
lean_closure_set(v___f_3502_, 9, v___x_3501_);
lean_closure_set(v___f_3502_, 10, v_onAlt_3473_);
lean_closure_set(v___f_3502_, 11, v___f_3474_);
lean_closure_set(v___f_3502_, 12, v_fst_3475_);
lean_closure_set(v___f_3502_, 13, v_inst_3476_);
lean_closure_set(v___f_3502_, 14, v_numDiscrEqs_3477_);
v___f_3503_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed), 27, 26);
lean_closure_set(v___f_3503_, 0, v___x_3478_);
lean_closure_set(v___f_3503_, 1, v_params_x27_3479_);
lean_closure_set(v___f_3503_, 2, v_fst_3480_);
lean_closure_set(v___f_3503_, 3, v_discrs_x27_3481_);
lean_closure_set(v___f_3503_, 4, v_fst_3482_);
lean_closure_set(v___f_3503_, 5, v_numParams_3483_);
lean_closure_set(v___f_3503_, 6, v_numDiscrs_3484_);
lean_closure_set(v___f_3503_, 7, v_altInfos_3485_);
lean_closure_set(v___f_3503_, 8, v_uElimPos_x3f_3486_);
lean_closure_set(v___f_3503_, 9, v_snd_3487_);
lean_closure_set(v___f_3503_, 10, v_overlaps_3488_);
lean_closure_set(v___f_3503_, 11, v_matcherLevels_3489_);
lean_closure_set(v___f_3503_, 12, v_toPure_3464_);
lean_closure_set(v___f_3503_, 13, v_onRemaining_3490_);
lean_closure_set(v___f_3503_, 14, v_remaining_3491_);
lean_closure_set(v___f_3503_, 15, v_toBind_3465_);
lean_closure_set(v___f_3503_, 16, v_alts_3463_);
lean_closure_set(v___f_3503_, 17, v___x_3467_);
lean_closure_set(v___f_3503_, 18, v___x_3499_);
lean_closure_set(v___f_3503_, 19, v_remaining_x27_3492_);
lean_closure_set(v___f_3503_, 20, v___f_3502_);
lean_closure_set(v___f_3503_, 21, v_inst_3469_);
lean_closure_set(v___f_3503_, 22, v___x_3493_);
lean_closure_set(v___f_3503_, 23, v_liftWith_3494_);
lean_closure_set(v___f_3503_, 24, v_restoreM_3495_);
lean_closure_set(v___f_3503_, 25, v_matcherName_3496_);
v___x_3504_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_3504_, 0, v___x_3499_);
lean_closure_set(v___x_3504_, 1, v_aux1_3497_);
v___x_3505_ = lean_apply_2(v_inst_3469_, lean_box(0), v___x_3504_);
v___x_3506_ = lean_apply_4(v_toBind_3465_, lean_box(0), lean_box(0), v___x_3505_, v___f_3503_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed(lean_object** _args){
lean_object* v_alts_3507_ = _args[0];
lean_object* v_toPure_3508_ = _args[1];
lean_object* v_toBind_3509_ = _args[2];
lean_object* v___f_3510_ = _args[3];
lean_object* v___x_3511_ = _args[4];
lean_object* v_inst_3512_ = _args[5];
lean_object* v_inst_3513_ = _args[6];
lean_object* v_inst_3514_ = _args[7];
lean_object* v___x_3515_ = _args[8];
lean_object* v_useSplitter_3516_ = _args[9];
lean_object* v_onAlt_3517_ = _args[10];
lean_object* v___f_3518_ = _args[11];
lean_object* v_fst_3519_ = _args[12];
lean_object* v_inst_3520_ = _args[13];
lean_object* v_numDiscrEqs_3521_ = _args[14];
lean_object* v___x_3522_ = _args[15];
lean_object* v_params_x27_3523_ = _args[16];
lean_object* v_fst_3524_ = _args[17];
lean_object* v_discrs_x27_3525_ = _args[18];
lean_object* v_fst_3526_ = _args[19];
lean_object* v_numParams_3527_ = _args[20];
lean_object* v_numDiscrs_3528_ = _args[21];
lean_object* v_altInfos_3529_ = _args[22];
lean_object* v_uElimPos_x3f_3530_ = _args[23];
lean_object* v_snd_3531_ = _args[24];
lean_object* v_overlaps_3532_ = _args[25];
lean_object* v_matcherLevels_3533_ = _args[26];
lean_object* v_onRemaining_3534_ = _args[27];
lean_object* v_remaining_3535_ = _args[28];
lean_object* v_remaining_x27_3536_ = _args[29];
lean_object* v___x_3537_ = _args[30];
lean_object* v_liftWith_3538_ = _args[31];
lean_object* v_restoreM_3539_ = _args[32];
lean_object* v_matcherName_3540_ = _args[33];
lean_object* v_aux1_3541_ = _args[34];
lean_object* v_____r_3542_ = _args[35];
_start:
{
uint8_t v___x_16514__boxed_3543_; uint8_t v_useSplitter_boxed_3544_; lean_object* v_res_3545_; 
v___x_16514__boxed_3543_ = lean_unbox(v___x_3515_);
v_useSplitter_boxed_3544_ = lean_unbox(v_useSplitter_3516_);
v_res_3545_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__52(v_alts_3507_, v_toPure_3508_, v_toBind_3509_, v___f_3510_, v___x_3511_, v_inst_3512_, v_inst_3513_, v_inst_3514_, v___x_16514__boxed_3543_, v_useSplitter_boxed_3544_, v_onAlt_3517_, v___f_3518_, v_fst_3519_, v_inst_3520_, v_numDiscrEqs_3521_, v___x_3522_, v_params_x27_3523_, v_fst_3524_, v_discrs_x27_3525_, v_fst_3526_, v_numParams_3527_, v_numDiscrs_3528_, v_altInfos_3529_, v_uElimPos_x3f_3530_, v_snd_3531_, v_overlaps_3532_, v_matcherLevels_3533_, v_onRemaining_3534_, v_remaining_3535_, v_remaining_x27_3536_, v___x_3537_, v_liftWith_3538_, v_restoreM_3539_, v_matcherName_3540_, v_aux1_3541_, v_____r_3542_);
return v_res_3545_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__1(void){
_start:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3547_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__0));
v___x_3548_ = l_Lean_stringToMessageData(v___x_3547_);
return v___x_3548_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__3(void){
_start:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3550_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__2));
v___x_3551_ = l_Lean_stringToMessageData(v___x_3550_);
return v___x_3551_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__5(void){
_start:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3553_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__4));
v___x_3554_ = l_Lean_stringToMessageData(v___x_3553_);
return v___x_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56(lean_object* v_numParams_3555_, lean_object* v_numDiscrs_3556_, lean_object* v_altInfos_3557_, lean_object* v_uElimPos_x3f_3558_, lean_object* v_snd_3559_, lean_object* v_overlaps_3560_, lean_object* v_matcherName_3561_, lean_object* v_matcherLevels_3562_, lean_object* v_params_x27_3563_, lean_object* v_fst_3564_, lean_object* v_discrs_x27_3565_, lean_object* v_toPure_3566_, lean_object* v_onRemaining_3567_, lean_object* v_remaining_3568_, lean_object* v_toBind_3569_, lean_object* v_inst_3570_, lean_object* v_alts_3571_, lean_object* v___f_3572_, uint8_t v___x_3573_, lean_object* v_inst_3574_, lean_object* v_remaining_x27_3575_, lean_object* v_onAlt_3576_, lean_object* v_inst_3577_, lean_object* v___f_3578_, lean_object* v_matcherApp_3579_, lean_object* v___x_3580_, uint8_t v_useSplitter_3581_, uint8_t v_isCasesOn_3582_, lean_object* v___f_3583_, lean_object* v_inst_3584_, lean_object* v___f_3585_, lean_object* v_numDiscrEqs_3586_, lean_object* v_____s_3587_){
_start:
{
lean_object* v_snd_3588_; lean_object* v_fst_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3650_; 
v_snd_3588_ = lean_ctor_get(v_____s_3587_, 1);
v_fst_3589_ = lean_ctor_get(v_____s_3587_, 0);
v_isSharedCheck_3650_ = !lean_is_exclusive(v_____s_3587_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3591_ = v_____s_3587_;
v_isShared_3592_ = v_isSharedCheck_3650_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_snd_3588_);
lean_inc(v_fst_3589_);
lean_dec(v_____s_3587_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3650_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v_fst_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3648_; 
v_fst_3593_ = lean_ctor_get(v_snd_3588_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v_snd_3588_);
if (v_isSharedCheck_3648_ == 0)
{
lean_object* v_unused_3649_; 
v_unused_3649_ = lean_ctor_get(v_snd_3588_, 1);
lean_dec(v_unused_3649_);
v___x_3595_ = v_snd_3588_;
v_isShared_3596_ = v_isSharedCheck_3648_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_fst_3593_);
lean_dec(v_snd_3588_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3648_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___f_3597_; 
lean_inc(v_toBind_3569_);
lean_inc_ref(v_remaining_3568_);
lean_inc(v_onRemaining_3567_);
lean_inc(v_toPure_3566_);
lean_inc_ref(v_discrs_x27_3565_);
lean_inc_ref(v_fst_3564_);
lean_inc_ref(v_params_x27_3563_);
lean_inc_ref(v_matcherLevels_3562_);
lean_inc(v_matcherName_3561_);
lean_inc_ref(v_overlaps_3560_);
lean_inc_ref(v_snd_3559_);
lean_inc(v_uElimPos_x3f_3558_);
lean_inc_ref(v_altInfos_3557_);
lean_inc(v_numDiscrs_3556_);
lean_inc(v_numParams_3555_);
lean_inc(v_fst_3589_);
v___f_3597_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed), 17, 16);
lean_closure_set(v___f_3597_, 0, v_fst_3589_);
lean_closure_set(v___f_3597_, 1, v_numParams_3555_);
lean_closure_set(v___f_3597_, 2, v_numDiscrs_3556_);
lean_closure_set(v___f_3597_, 3, v_altInfos_3557_);
lean_closure_set(v___f_3597_, 4, v_uElimPos_x3f_3558_);
lean_closure_set(v___f_3597_, 5, v_snd_3559_);
lean_closure_set(v___f_3597_, 6, v_overlaps_3560_);
lean_closure_set(v___f_3597_, 7, v_matcherName_3561_);
lean_closure_set(v___f_3597_, 8, v_matcherLevels_3562_);
lean_closure_set(v___f_3597_, 9, v_params_x27_3563_);
lean_closure_set(v___f_3597_, 10, v_fst_3564_);
lean_closure_set(v___f_3597_, 11, v_discrs_x27_3565_);
lean_closure_set(v___f_3597_, 12, v_toPure_3566_);
lean_closure_set(v___f_3597_, 13, v_onRemaining_3567_);
lean_closure_set(v___f_3597_, 14, v_remaining_3568_);
lean_closure_set(v___f_3597_, 15, v_toBind_3569_);
if (v_useSplitter_3581_ == 0)
{
lean_del_object(v___x_3591_);
lean_dec(v_fst_3589_);
lean_dec(v_numDiscrEqs_3586_);
lean_dec(v___f_3585_);
lean_dec_ref(v_inst_3584_);
lean_dec(v___f_3583_);
lean_dec_ref(v_remaining_3568_);
lean_dec(v_onRemaining_3567_);
lean_dec_ref(v_overlaps_3560_);
lean_dec_ref(v_snd_3559_);
lean_dec(v_uElimPos_x3f_3558_);
lean_dec_ref(v_altInfos_3557_);
lean_dec(v_numDiscrs_3556_);
lean_dec(v_numParams_3555_);
goto v___jp_3598_;
}
else
{
if (v_isCasesOn_3582_ == 0)
{
lean_object* v_liftWith_3623_; lean_object* v_restoreM_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v_aux1_3627_; lean_object* v_aux1_3628_; lean_object* v_aux1_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3633_; 
lean_dec_ref(v___f_3597_);
lean_del_object(v___x_3595_);
lean_dec_ref(v_matcherApp_3579_);
lean_dec(v___f_3578_);
lean_dec(v___f_3572_);
v_liftWith_3623_ = lean_ctor_get(v_inst_3570_, 0);
lean_inc(v_liftWith_3623_);
v_restoreM_3624_ = lean_ctor_get(v_inst_3570_, 1);
lean_inc(v_restoreM_3624_);
lean_inc_ref(v_matcherLevels_3562_);
v___x_3625_ = lean_array_to_list(v_matcherLevels_3562_);
lean_inc(v___x_3625_);
lean_inc(v_matcherName_3561_);
v___x_3626_ = l_Lean_mkConst(v_matcherName_3561_, v___x_3625_);
v_aux1_3627_ = l_Lean_mkAppN(v___x_3626_, v_params_x27_3563_);
lean_inc_ref(v_fst_3564_);
v_aux1_3628_ = l_Lean_Expr_app___override(v_aux1_3627_, v_fst_3564_);
v_aux1_3629_ = l_Lean_mkAppN(v_aux1_3628_, v_discrs_x27_3565_);
lean_inc_ref(v_aux1_3629_);
v___x_3630_ = l_Lean_indentExpr(v_aux1_3629_);
v___x_3631_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__3);
if (v_isShared_3592_ == 0)
{
lean_ctor_set_tag(v___x_3591_, 7);
lean_ctor_set(v___x_3591_, 1, v___x_3630_);
lean_ctor_set(v___x_3591_, 0, v___x_3631_);
v___x_3633_ = v___x_3591_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v___x_3631_);
lean_ctor_set(v_reuseFailAlloc_3647_, 1, v___x_3630_);
v___x_3633_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___f_3637_; lean_object* v___x_3638_; lean_object* v___f_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___f_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3634_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__5);
v___x_3635_ = lean_box(v___x_3573_);
v___x_3636_ = lean_box(v_useSplitter_3581_);
lean_inc_ref(v_aux1_3629_);
lean_inc(v_restoreM_3624_);
lean_inc(v_liftWith_3623_);
lean_inc(v_inst_3574_);
lean_inc_n(v_toBind_3569_, 2);
v___f_3637_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed), 36, 35);
lean_closure_set(v___f_3637_, 0, v_alts_3571_);
lean_closure_set(v___f_3637_, 1, v_toPure_3566_);
lean_closure_set(v___f_3637_, 2, v_toBind_3569_);
lean_closure_set(v___f_3637_, 3, v___f_3583_);
lean_closure_set(v___f_3637_, 4, v___x_3580_);
lean_closure_set(v___f_3637_, 5, v_inst_3577_);
lean_closure_set(v___f_3637_, 6, v_inst_3574_);
lean_closure_set(v___f_3637_, 7, v_inst_3584_);
lean_closure_set(v___f_3637_, 8, v___x_3635_);
lean_closure_set(v___f_3637_, 9, v___x_3636_);
lean_closure_set(v___f_3637_, 10, v_onAlt_3576_);
lean_closure_set(v___f_3637_, 11, v___f_3585_);
lean_closure_set(v___f_3637_, 12, v_fst_3593_);
lean_closure_set(v___f_3637_, 13, v_inst_3570_);
lean_closure_set(v___f_3637_, 14, v_numDiscrEqs_3586_);
lean_closure_set(v___f_3637_, 15, v___x_3625_);
lean_closure_set(v___f_3637_, 16, v_params_x27_3563_);
lean_closure_set(v___f_3637_, 17, v_fst_3564_);
lean_closure_set(v___f_3637_, 18, v_discrs_x27_3565_);
lean_closure_set(v___f_3637_, 19, v_fst_3589_);
lean_closure_set(v___f_3637_, 20, v_numParams_3555_);
lean_closure_set(v___f_3637_, 21, v_numDiscrs_3556_);
lean_closure_set(v___f_3637_, 22, v_altInfos_3557_);
lean_closure_set(v___f_3637_, 23, v_uElimPos_x3f_3558_);
lean_closure_set(v___f_3637_, 24, v_snd_3559_);
lean_closure_set(v___f_3637_, 25, v_overlaps_3560_);
lean_closure_set(v___f_3637_, 26, v_matcherLevels_3562_);
lean_closure_set(v___f_3637_, 27, v_onRemaining_3567_);
lean_closure_set(v___f_3637_, 28, v_remaining_3568_);
lean_closure_set(v___f_3637_, 29, v_remaining_x27_3575_);
lean_closure_set(v___f_3637_, 30, v___x_3634_);
lean_closure_set(v___f_3637_, 31, v_liftWith_3623_);
lean_closure_set(v___f_3637_, 32, v_restoreM_3624_);
lean_closure_set(v___f_3637_, 33, v_matcherName_3561_);
lean_closure_set(v___f_3637_, 34, v_aux1_3629_);
v___x_3638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3638_, 0, v___x_3633_);
lean_ctor_set(v___x_3638_, 1, v___x_3634_);
v___f_3639_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3639_, 0, v___x_3638_);
v___x_3640_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(v___x_3640_, 0, v_aux1_3629_);
v___x_3641_ = lean_apply_2(v_inst_3574_, lean_box(0), v___x_3640_);
v___f_3642_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3642_, 0, v___x_3641_);
lean_closure_set(v___f_3642_, 1, v___f_3639_);
v___x_3643_ = lean_apply_2(v_liftWith_3623_, lean_box(0), v___f_3642_);
v___x_3644_ = lean_apply_1(v_restoreM_3624_, lean_box(0));
v___x_3645_ = lean_apply_4(v_toBind_3569_, lean_box(0), lean_box(0), v___x_3643_, v___x_3644_);
v___x_3646_ = lean_apply_4(v_toBind_3569_, lean_box(0), lean_box(0), v___x_3645_, v___f_3637_);
return v___x_3646_;
}
}
else
{
lean_del_object(v___x_3591_);
lean_dec(v_fst_3589_);
lean_dec(v_numDiscrEqs_3586_);
lean_dec(v___f_3585_);
lean_dec_ref(v_inst_3584_);
lean_dec(v___f_3583_);
lean_dec_ref(v_remaining_3568_);
lean_dec(v_onRemaining_3567_);
lean_dec_ref(v_overlaps_3560_);
lean_dec_ref(v_snd_3559_);
lean_dec(v_uElimPos_x3f_3558_);
lean_dec_ref(v_altInfos_3557_);
lean_dec(v_numDiscrs_3556_);
lean_dec(v_numParams_3555_);
goto v___jp_3598_;
}
}
v___jp_3598_:
{
lean_object* v_liftWith_3599_; lean_object* v_restoreM_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v_aux_3603_; lean_object* v_aux_3604_; lean_object* v_aux_3605_; lean_object* v___x_3606_; uint8_t v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___f_3610_; lean_object* v___x_3611_; lean_object* v___x_3613_; 
v_liftWith_3599_ = lean_ctor_get(v_inst_3570_, 0);
lean_inc(v_liftWith_3599_);
v_restoreM_3600_ = lean_ctor_get(v_inst_3570_, 1);
lean_inc(v_restoreM_3600_);
v___x_3601_ = lean_array_to_list(v_matcherLevels_3562_);
v___x_3602_ = l_Lean_mkConst(v_matcherName_3561_, v___x_3601_);
v_aux_3603_ = l_Lean_mkAppN(v___x_3602_, v_params_x27_3563_);
lean_dec_ref(v_params_x27_3563_);
v_aux_3604_ = l_Lean_Expr_app___override(v_aux_3603_, v_fst_3564_);
v_aux_3605_ = l_Lean_mkAppN(v_aux_3604_, v_discrs_x27_3565_);
lean_dec_ref(v_discrs_x27_3565_);
lean_inc_ref_n(v_aux_3605_, 2);
v___x_3606_ = l_Lean_indentExpr(v_aux_3605_);
v___x_3607_ = 1;
v___x_3608_ = lean_box(v___x_3573_);
v___x_3609_ = lean_box(v___x_3607_);
lean_inc(v_inst_3574_);
lean_inc(v_toBind_3569_);
v___f_3610_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 18, 17);
lean_closure_set(v___f_3610_, 0, v_alts_3571_);
lean_closure_set(v___f_3610_, 1, v_toPure_3566_);
lean_closure_set(v___f_3610_, 2, v_toBind_3569_);
lean_closure_set(v___f_3610_, 3, v___f_3572_);
lean_closure_set(v___f_3610_, 4, v___x_3608_);
lean_closure_set(v___f_3610_, 5, v___x_3609_);
lean_closure_set(v___f_3610_, 6, v_inst_3574_);
lean_closure_set(v___f_3610_, 7, v_remaining_x27_3575_);
lean_closure_set(v___f_3610_, 8, v_onAlt_3576_);
lean_closure_set(v___f_3610_, 9, v_inst_3570_);
lean_closure_set(v___f_3610_, 10, v_inst_3577_);
lean_closure_set(v___f_3610_, 11, v___f_3578_);
lean_closure_set(v___f_3610_, 12, v_fst_3593_);
lean_closure_set(v___f_3610_, 13, v_matcherApp_3579_);
lean_closure_set(v___f_3610_, 14, v___x_3580_);
lean_closure_set(v___f_3610_, 15, v___f_3597_);
lean_closure_set(v___f_3610_, 16, v_aux_3605_);
v___x_3611_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__1);
if (v_isShared_3596_ == 0)
{
lean_ctor_set_tag(v___x_3595_, 7);
lean_ctor_set(v___x_3595_, 1, v___x_3606_);
lean_ctor_set(v___x_3595_, 0, v___x_3611_);
v___x_3613_ = v___x_3595_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3611_);
lean_ctor_set(v_reuseFailAlloc_3622_, 1, v___x_3606_);
v___x_3613_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3612_;
}
v_reusejp_3612_:
{
lean_object* v___f_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___f_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___f_3614_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3614_, 0, v___x_3613_);
v___x_3615_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(v___x_3615_, 0, v_aux_3605_);
v___x_3616_ = lean_apply_2(v_inst_3574_, lean_box(0), v___x_3615_);
v___f_3617_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3617_, 0, v___x_3616_);
lean_closure_set(v___f_3617_, 1, v___f_3614_);
v___x_3618_ = lean_apply_2(v_liftWith_3599_, lean_box(0), v___f_3617_);
v___x_3619_ = lean_apply_1(v_restoreM_3600_, lean_box(0));
lean_inc(v_toBind_3569_);
v___x_3620_ = lean_apply_4(v_toBind_3569_, lean_box(0), lean_box(0), v___x_3618_, v___x_3619_);
v___x_3621_ = lean_apply_4(v_toBind_3569_, lean_box(0), lean_box(0), v___x_3620_, v___f_3610_);
return v___x_3621_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56___boxed(lean_object** _args){
lean_object* v_numParams_3651_ = _args[0];
lean_object* v_numDiscrs_3652_ = _args[1];
lean_object* v_altInfos_3653_ = _args[2];
lean_object* v_uElimPos_x3f_3654_ = _args[3];
lean_object* v_snd_3655_ = _args[4];
lean_object* v_overlaps_3656_ = _args[5];
lean_object* v_matcherName_3657_ = _args[6];
lean_object* v_matcherLevels_3658_ = _args[7];
lean_object* v_params_x27_3659_ = _args[8];
lean_object* v_fst_3660_ = _args[9];
lean_object* v_discrs_x27_3661_ = _args[10];
lean_object* v_toPure_3662_ = _args[11];
lean_object* v_onRemaining_3663_ = _args[12];
lean_object* v_remaining_3664_ = _args[13];
lean_object* v_toBind_3665_ = _args[14];
lean_object* v_inst_3666_ = _args[15];
lean_object* v_alts_3667_ = _args[16];
lean_object* v___f_3668_ = _args[17];
lean_object* v___x_3669_ = _args[18];
lean_object* v_inst_3670_ = _args[19];
lean_object* v_remaining_x27_3671_ = _args[20];
lean_object* v_onAlt_3672_ = _args[21];
lean_object* v_inst_3673_ = _args[22];
lean_object* v___f_3674_ = _args[23];
lean_object* v_matcherApp_3675_ = _args[24];
lean_object* v___x_3676_ = _args[25];
lean_object* v_useSplitter_3677_ = _args[26];
lean_object* v_isCasesOn_3678_ = _args[27];
lean_object* v___f_3679_ = _args[28];
lean_object* v_inst_3680_ = _args[29];
lean_object* v___f_3681_ = _args[30];
lean_object* v_numDiscrEqs_3682_ = _args[31];
lean_object* v_____s_3683_ = _args[32];
_start:
{
uint8_t v___x_16586__boxed_3684_; uint8_t v_useSplitter_boxed_3685_; uint8_t v_isCasesOn_boxed_3686_; lean_object* v_res_3687_; 
v___x_16586__boxed_3684_ = lean_unbox(v___x_3669_);
v_useSplitter_boxed_3685_ = lean_unbox(v_useSplitter_3677_);
v_isCasesOn_boxed_3686_ = lean_unbox(v_isCasesOn_3678_);
v_res_3687_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__56(v_numParams_3651_, v_numDiscrs_3652_, v_altInfos_3653_, v_uElimPos_x3f_3654_, v_snd_3655_, v_overlaps_3656_, v_matcherName_3657_, v_matcherLevels_3658_, v_params_x27_3659_, v_fst_3660_, v_discrs_x27_3661_, v_toPure_3662_, v_onRemaining_3663_, v_remaining_3664_, v_toBind_3665_, v_inst_3666_, v_alts_3667_, v___f_3668_, v___x_16586__boxed_3684_, v_inst_3670_, v_remaining_x27_3671_, v_onAlt_3672_, v_inst_3673_, v___f_3674_, v_matcherApp_3675_, v___x_3676_, v_useSplitter_boxed_3685_, v_isCasesOn_boxed_3686_, v___f_3679_, v_inst_3680_, v___f_3681_, v_numDiscrEqs_3682_, v_____s_3683_);
return v_res_3687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54(lean_object* v_numParams_3688_, lean_object* v_numDiscrs_3689_, lean_object* v_altInfos_3690_, lean_object* v_uElimPos_x3f_3691_, lean_object* v_snd_3692_, lean_object* v_overlaps_3693_, lean_object* v_matcherName_3694_, lean_object* v_params_x27_3695_, lean_object* v_fst_3696_, lean_object* v_discrs_x27_3697_, lean_object* v_toPure_3698_, lean_object* v_onRemaining_3699_, lean_object* v_remaining_3700_, lean_object* v_toBind_3701_, lean_object* v_inst_3702_, lean_object* v_alts_3703_, lean_object* v___f_3704_, uint8_t v___x_3705_, lean_object* v_inst_3706_, lean_object* v_onAlt_3707_, lean_object* v_inst_3708_, lean_object* v___f_3709_, lean_object* v_matcherApp_3710_, uint8_t v_useSplitter_3711_, uint8_t v_isCasesOn_3712_, lean_object* v___f_3713_, lean_object* v_inst_3714_, lean_object* v___f_3715_, lean_object* v_numDiscrEqs_3716_, lean_object* v_fst_3717_, lean_object* v___f_3718_, lean_object* v_matcherLevels_3719_){
_start:
{
lean_object* v___x_3720_; lean_object* v_remaining_x27_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___f_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; size_t v_sz_3732_; size_t v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3720_ = lean_unsigned_to_nat(0u);
v_remaining_x27_3721_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_3722_ = lean_box(v___x_3705_);
v___x_3723_ = lean_box(v_useSplitter_3711_);
v___x_3724_ = lean_box(v_isCasesOn_3712_);
lean_inc_ref(v_inst_3708_);
lean_inc(v_toBind_3701_);
lean_inc_ref(v_discrs_x27_3697_);
v___f_3725_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56___boxed), 33, 32);
lean_closure_set(v___f_3725_, 0, v_numParams_3688_);
lean_closure_set(v___f_3725_, 1, v_numDiscrs_3689_);
lean_closure_set(v___f_3725_, 2, v_altInfos_3690_);
lean_closure_set(v___f_3725_, 3, v_uElimPos_x3f_3691_);
lean_closure_set(v___f_3725_, 4, v_snd_3692_);
lean_closure_set(v___f_3725_, 5, v_overlaps_3693_);
lean_closure_set(v___f_3725_, 6, v_matcherName_3694_);
lean_closure_set(v___f_3725_, 7, v_matcherLevels_3719_);
lean_closure_set(v___f_3725_, 8, v_params_x27_3695_);
lean_closure_set(v___f_3725_, 9, v_fst_3696_);
lean_closure_set(v___f_3725_, 10, v_discrs_x27_3697_);
lean_closure_set(v___f_3725_, 11, v_toPure_3698_);
lean_closure_set(v___f_3725_, 12, v_onRemaining_3699_);
lean_closure_set(v___f_3725_, 13, v_remaining_3700_);
lean_closure_set(v___f_3725_, 14, v_toBind_3701_);
lean_closure_set(v___f_3725_, 15, v_inst_3702_);
lean_closure_set(v___f_3725_, 16, v_alts_3703_);
lean_closure_set(v___f_3725_, 17, v___f_3704_);
lean_closure_set(v___f_3725_, 18, v___x_3722_);
lean_closure_set(v___f_3725_, 19, v_inst_3706_);
lean_closure_set(v___f_3725_, 20, v_remaining_x27_3721_);
lean_closure_set(v___f_3725_, 21, v_onAlt_3707_);
lean_closure_set(v___f_3725_, 22, v_inst_3708_);
lean_closure_set(v___f_3725_, 23, v___f_3709_);
lean_closure_set(v___f_3725_, 24, v_matcherApp_3710_);
lean_closure_set(v___f_3725_, 25, v___x_3720_);
lean_closure_set(v___f_3725_, 26, v___x_3723_);
lean_closure_set(v___f_3725_, 27, v___x_3724_);
lean_closure_set(v___f_3725_, 28, v___f_3713_);
lean_closure_set(v___f_3725_, 29, v_inst_3714_);
lean_closure_set(v___f_3725_, 30, v___f_3715_);
lean_closure_set(v___f_3725_, 31, v_numDiscrEqs_3716_);
v___x_3726_ = l_Array_reverse___redArg(v_fst_3717_);
v___x_3727_ = lean_array_get_size(v___x_3726_);
v___x_3728_ = l_Array_toSubarray___redArg(v___x_3726_, v___x_3720_, v___x_3727_);
v___x_3729_ = l_Array_reverse___redArg(v_discrs_x27_3697_);
v___x_3730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3720_);
lean_ctor_set(v___x_3730_, 1, v___x_3728_);
v___x_3731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3731_, 0, v_remaining_x27_3721_);
lean_ctor_set(v___x_3731_, 1, v___x_3730_);
v_sz_3732_ = lean_array_size(v___x_3729_);
v___x_3733_ = ((size_t)0ULL);
v___x_3734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3708_, v___x_3729_, v___f_3718_, v_sz_3732_, v___x_3733_, v___x_3731_);
v___x_3735_ = lean_apply_4(v_toBind_3701_, lean_box(0), lean_box(0), v___x_3734_, v___f_3725_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed(lean_object** _args){
lean_object* v_numParams_3736_ = _args[0];
lean_object* v_numDiscrs_3737_ = _args[1];
lean_object* v_altInfos_3738_ = _args[2];
lean_object* v_uElimPos_x3f_3739_ = _args[3];
lean_object* v_snd_3740_ = _args[4];
lean_object* v_overlaps_3741_ = _args[5];
lean_object* v_matcherName_3742_ = _args[6];
lean_object* v_params_x27_3743_ = _args[7];
lean_object* v_fst_3744_ = _args[8];
lean_object* v_discrs_x27_3745_ = _args[9];
lean_object* v_toPure_3746_ = _args[10];
lean_object* v_onRemaining_3747_ = _args[11];
lean_object* v_remaining_3748_ = _args[12];
lean_object* v_toBind_3749_ = _args[13];
lean_object* v_inst_3750_ = _args[14];
lean_object* v_alts_3751_ = _args[15];
lean_object* v___f_3752_ = _args[16];
lean_object* v___x_3753_ = _args[17];
lean_object* v_inst_3754_ = _args[18];
lean_object* v_onAlt_3755_ = _args[19];
lean_object* v_inst_3756_ = _args[20];
lean_object* v___f_3757_ = _args[21];
lean_object* v_matcherApp_3758_ = _args[22];
lean_object* v_useSplitter_3759_ = _args[23];
lean_object* v_isCasesOn_3760_ = _args[24];
lean_object* v___f_3761_ = _args[25];
lean_object* v_inst_3762_ = _args[26];
lean_object* v___f_3763_ = _args[27];
lean_object* v_numDiscrEqs_3764_ = _args[28];
lean_object* v_fst_3765_ = _args[29];
lean_object* v___f_3766_ = _args[30];
lean_object* v_matcherLevels_3767_ = _args[31];
_start:
{
uint8_t v___x_16735__boxed_3768_; uint8_t v_useSplitter_boxed_3769_; uint8_t v_isCasesOn_boxed_3770_; lean_object* v_res_3771_; 
v___x_16735__boxed_3768_ = lean_unbox(v___x_3753_);
v_useSplitter_boxed_3769_ = lean_unbox(v_useSplitter_3759_);
v_isCasesOn_boxed_3770_ = lean_unbox(v_isCasesOn_3760_);
v_res_3771_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__54(v_numParams_3736_, v_numDiscrs_3737_, v_altInfos_3738_, v_uElimPos_x3f_3739_, v_snd_3740_, v_overlaps_3741_, v_matcherName_3742_, v_params_x27_3743_, v_fst_3744_, v_discrs_x27_3745_, v_toPure_3746_, v_onRemaining_3747_, v_remaining_3748_, v_toBind_3749_, v_inst_3750_, v_alts_3751_, v___f_3752_, v___x_16735__boxed_3768_, v_inst_3754_, v_onAlt_3755_, v_inst_3756_, v___f_3757_, v_matcherApp_3758_, v_useSplitter_boxed_3769_, v_isCasesOn_boxed_3770_, v___f_3761_, v_inst_3762_, v___f_3763_, v_numDiscrEqs_3764_, v_fst_3765_, v___f_3766_, v_matcherLevels_3767_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55(lean_object* v___f_3772_, lean_object* v_matcherLevels_3773_){
_start:
{
lean_object* v___x_3774_; 
v___x_3774_ = lean_apply_1(v___f_3772_, v_matcherLevels_3773_);
return v___x_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58(lean_object* v_toMatcherInfo_3775_, lean_object* v_matcherName_3776_, lean_object* v_params_x27_3777_, lean_object* v_discrs_x27_3778_, lean_object* v_toPure_3779_, lean_object* v_onRemaining_3780_, lean_object* v_remaining_3781_, lean_object* v_toBind_3782_, lean_object* v_inst_3783_, lean_object* v_alts_3784_, lean_object* v___f_3785_, uint8_t v___x_3786_, lean_object* v_inst_3787_, lean_object* v_onAlt_3788_, lean_object* v_inst_3789_, lean_object* v___f_3790_, lean_object* v_matcherApp_3791_, uint8_t v_useSplitter_3792_, uint8_t v_isCasesOn_3793_, lean_object* v___f_3794_, lean_object* v_inst_3795_, lean_object* v___f_3796_, lean_object* v_numDiscrEqs_3797_, lean_object* v___f_3798_, lean_object* v_matcherLevels_3799_, lean_object* v_____x_3800_){
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
v_numParams_3807_ = lean_ctor_get(v_toMatcherInfo_3775_, 0);
lean_inc(v_numParams_3807_);
v_numDiscrs_3808_ = lean_ctor_get(v_toMatcherInfo_3775_, 1);
lean_inc(v_numDiscrs_3808_);
v_altInfos_3809_ = lean_ctor_get(v_toMatcherInfo_3775_, 2);
lean_inc_ref(v_altInfos_3809_);
v_uElimPos_x3f_3810_ = lean_ctor_get(v_toMatcherInfo_3775_, 3);
lean_inc_n(v_uElimPos_x3f_3810_, 2);
v_overlaps_3811_ = lean_ctor_get(v_toMatcherInfo_3775_, 5);
lean_inc_ref(v_overlaps_3811_);
lean_dec_ref(v_toMatcherInfo_3775_);
v___x_3812_ = lean_box(v___x_3786_);
v___x_3813_ = lean_box(v_useSplitter_3792_);
v___x_3814_ = lean_box(v_isCasesOn_3793_);
lean_inc(v_toBind_3782_);
lean_inc(v_toPure_3779_);
v___f_3815_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed), 32, 31);
lean_closure_set(v___f_3815_, 0, v_numParams_3807_);
lean_closure_set(v___f_3815_, 1, v_numDiscrs_3808_);
lean_closure_set(v___f_3815_, 2, v_altInfos_3809_);
lean_closure_set(v___f_3815_, 3, v_uElimPos_x3f_3810_);
lean_closure_set(v___f_3815_, 4, v_snd_3806_);
lean_closure_set(v___f_3815_, 5, v_overlaps_3811_);
lean_closure_set(v___f_3815_, 6, v_matcherName_3776_);
lean_closure_set(v___f_3815_, 7, v_params_x27_3777_);
lean_closure_set(v___f_3815_, 8, v_fst_3803_);
lean_closure_set(v___f_3815_, 9, v_discrs_x27_3778_);
lean_closure_set(v___f_3815_, 10, v_toPure_3779_);
lean_closure_set(v___f_3815_, 11, v_onRemaining_3780_);
lean_closure_set(v___f_3815_, 12, v_remaining_3781_);
lean_closure_set(v___f_3815_, 13, v_toBind_3782_);
lean_closure_set(v___f_3815_, 14, v_inst_3783_);
lean_closure_set(v___f_3815_, 15, v_alts_3784_);
lean_closure_set(v___f_3815_, 16, v___f_3785_);
lean_closure_set(v___f_3815_, 17, v___x_3812_);
lean_closure_set(v___f_3815_, 18, v_inst_3787_);
lean_closure_set(v___f_3815_, 19, v_onAlt_3788_);
lean_closure_set(v___f_3815_, 20, v_inst_3789_);
lean_closure_set(v___f_3815_, 21, v___f_3790_);
lean_closure_set(v___f_3815_, 22, v_matcherApp_3791_);
lean_closure_set(v___f_3815_, 23, v___x_3813_);
lean_closure_set(v___f_3815_, 24, v___x_3814_);
lean_closure_set(v___f_3815_, 25, v___f_3794_);
lean_closure_set(v___f_3815_, 26, v_inst_3795_);
lean_closure_set(v___f_3815_, 27, v___f_3796_);
lean_closure_set(v___f_3815_, 28, v_numDiscrEqs_3797_);
lean_closure_set(v___f_3815_, 29, v_fst_3805_);
lean_closure_set(v___f_3815_, 30, v___f_3798_);
if (lean_obj_tag(v_uElimPos_x3f_3810_) == 0)
{
lean_object* v___f_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; 
lean_dec(v_fst_3804_);
v___f_3816_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55), 2, 1);
lean_closure_set(v___f_3816_, 0, v___f_3815_);
v___x_3817_ = lean_apply_2(v_toPure_3779_, lean_box(0), v_matcherLevels_3799_);
v___x_3818_ = lean_apply_4(v_toBind_3782_, lean_box(0), lean_box(0), v___x_3817_, v___f_3816_);
return v___x_3818_;
}
else
{
lean_object* v_val_3819_; lean_object* v___f_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; 
v_val_3819_ = lean_ctor_get(v_uElimPos_x3f_3810_, 0);
lean_inc(v_val_3819_);
lean_dec_ref(v_uElimPos_x3f_3810_);
v___f_3820_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55), 2, 1);
lean_closure_set(v___f_3820_, 0, v___f_3815_);
v___x_3821_ = lean_array_set(v_matcherLevels_3799_, v_val_3819_, v_fst_3804_);
lean_dec(v_val_3819_);
v___x_3822_ = lean_apply_2(v_toPure_3779_, lean_box(0), v___x_3821_);
v___x_3823_ = lean_apply_4(v_toBind_3782_, lean_box(0), lean_box(0), v___x_3822_, v___f_3820_);
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
lean_object* v_inst_3844_ = _args[20];
lean_object* v___f_3845_ = _args[21];
lean_object* v_numDiscrEqs_3846_ = _args[22];
lean_object* v___f_3847_ = _args[23];
lean_object* v_matcherLevels_3848_ = _args[24];
lean_object* v_____x_3849_ = _args[25];
_start:
{
uint8_t v___x_16804__boxed_3850_; uint8_t v_useSplitter_boxed_3851_; uint8_t v_isCasesOn_boxed_3852_; lean_object* v_res_3853_; 
v___x_16804__boxed_3850_ = lean_unbox(v___x_3835_);
v_useSplitter_boxed_3851_ = lean_unbox(v_useSplitter_3841_);
v_isCasesOn_boxed_3852_ = lean_unbox(v_isCasesOn_3842_);
v_res_3853_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__58(v_toMatcherInfo_3824_, v_matcherName_3825_, v_params_x27_3826_, v_discrs_x27_3827_, v_toPure_3828_, v_onRemaining_3829_, v_remaining_3830_, v_toBind_3831_, v_inst_3832_, v_alts_3833_, v___f_3834_, v___x_16804__boxed_3850_, v_inst_3836_, v_onAlt_3837_, v_inst_3838_, v___f_3839_, v_matcherApp_3840_, v_useSplitter_boxed_3851_, v_isCasesOn_boxed_3852_, v___f_3843_, v_inst_3844_, v___f_3845_, v_numDiscrEqs_3846_, v___f_3847_, v_matcherLevels_3848_, v_____x_3849_);
return v_res_3853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57(lean_object* v_toPure_3854_, lean_object* v_inst_3855_, lean_object* v_toBind_3856_, lean_object* v_toMatcherInfo_3857_, lean_object* v_inst_3858_, lean_object* v___f_3859_, lean_object* v_onMotive_3860_, lean_object* v_discrs_3861_, lean_object* v_inst_3862_, lean_object* v_matcherName_3863_, lean_object* v_params_x27_3864_, lean_object* v_onRemaining_3865_, lean_object* v_remaining_3866_, lean_object* v_inst_3867_, lean_object* v_alts_3868_, lean_object* v___f_3869_, lean_object* v_onAlt_3870_, lean_object* v___f_3871_, lean_object* v_matcherApp_3872_, uint8_t v_useSplitter_3873_, uint8_t v_isCasesOn_3874_, lean_object* v___f_3875_, lean_object* v___f_3876_, lean_object* v_numDiscrEqs_3877_, lean_object* v___f_3878_, lean_object* v_matcherLevels_3879_, lean_object* v_motive_3880_, lean_object* v_discrs_x27_3881_){
_start:
{
lean_object* v___f_3882_; uint8_t v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___f_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; 
lean_inc_ref(v_inst_3862_);
lean_inc_ref_n(v_inst_3858_, 2);
lean_inc_ref(v_discrs_x27_3881_);
lean_inc_ref(v_toMatcherInfo_3857_);
lean_inc_n(v_toBind_3856_, 2);
lean_inc(v_inst_3855_);
lean_inc(v_toPure_3854_);
v___f_3882_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__19___boxed), 12, 10);
lean_closure_set(v___f_3882_, 0, v_toPure_3854_);
lean_closure_set(v___f_3882_, 1, v_inst_3855_);
lean_closure_set(v___f_3882_, 2, v_toBind_3856_);
lean_closure_set(v___f_3882_, 3, v_toMatcherInfo_3857_);
lean_closure_set(v___f_3882_, 4, v_discrs_x27_3881_);
lean_closure_set(v___f_3882_, 5, v_inst_3858_);
lean_closure_set(v___f_3882_, 6, v___f_3859_);
lean_closure_set(v___f_3882_, 7, v_onMotive_3860_);
lean_closure_set(v___f_3882_, 8, v_discrs_3861_);
lean_closure_set(v___f_3882_, 9, v_inst_3862_);
v___x_3883_ = 0;
v___x_3884_ = lean_box(v___x_3883_);
v___x_3885_ = lean_box(v_useSplitter_3873_);
v___x_3886_ = lean_box(v_isCasesOn_3874_);
lean_inc_ref(v_inst_3867_);
v___f_3887_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed), 26, 25);
lean_closure_set(v___f_3887_, 0, v_toMatcherInfo_3857_);
lean_closure_set(v___f_3887_, 1, v_matcherName_3863_);
lean_closure_set(v___f_3887_, 2, v_params_x27_3864_);
lean_closure_set(v___f_3887_, 3, v_discrs_x27_3881_);
lean_closure_set(v___f_3887_, 4, v_toPure_3854_);
lean_closure_set(v___f_3887_, 5, v_onRemaining_3865_);
lean_closure_set(v___f_3887_, 6, v_remaining_3866_);
lean_closure_set(v___f_3887_, 7, v_toBind_3856_);
lean_closure_set(v___f_3887_, 8, v_inst_3867_);
lean_closure_set(v___f_3887_, 9, v_alts_3868_);
lean_closure_set(v___f_3887_, 10, v___f_3869_);
lean_closure_set(v___f_3887_, 11, v___x_3884_);
lean_closure_set(v___f_3887_, 12, v_inst_3855_);
lean_closure_set(v___f_3887_, 13, v_onAlt_3870_);
lean_closure_set(v___f_3887_, 14, v_inst_3858_);
lean_closure_set(v___f_3887_, 15, v___f_3871_);
lean_closure_set(v___f_3887_, 16, v_matcherApp_3872_);
lean_closure_set(v___f_3887_, 17, v___x_3885_);
lean_closure_set(v___f_3887_, 18, v___x_3886_);
lean_closure_set(v___f_3887_, 19, v___f_3875_);
lean_closure_set(v___f_3887_, 20, v_inst_3862_);
lean_closure_set(v___f_3887_, 21, v___f_3876_);
lean_closure_set(v___f_3887_, 22, v_numDiscrEqs_3877_);
lean_closure_set(v___f_3887_, 23, v___f_3878_);
lean_closure_set(v___f_3887_, 24, v_matcherLevels_3879_);
v___x_3888_ = l_Lean_Meta_lambdaTelescope___redArg(v_inst_3867_, v_inst_3858_, v_motive_3880_, v___f_3882_, v___x_3883_);
v___x_3889_ = lean_apply_4(v_toBind_3856_, lean_box(0), lean_box(0), v___x_3888_, v___f_3887_);
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed(lean_object** _args){
lean_object* v_toPure_3890_ = _args[0];
lean_object* v_inst_3891_ = _args[1];
lean_object* v_toBind_3892_ = _args[2];
lean_object* v_toMatcherInfo_3893_ = _args[3];
lean_object* v_inst_3894_ = _args[4];
lean_object* v___f_3895_ = _args[5];
lean_object* v_onMotive_3896_ = _args[6];
lean_object* v_discrs_3897_ = _args[7];
lean_object* v_inst_3898_ = _args[8];
lean_object* v_matcherName_3899_ = _args[9];
lean_object* v_params_x27_3900_ = _args[10];
lean_object* v_onRemaining_3901_ = _args[11];
lean_object* v_remaining_3902_ = _args[12];
lean_object* v_inst_3903_ = _args[13];
lean_object* v_alts_3904_ = _args[14];
lean_object* v___f_3905_ = _args[15];
lean_object* v_onAlt_3906_ = _args[16];
lean_object* v___f_3907_ = _args[17];
lean_object* v_matcherApp_3908_ = _args[18];
lean_object* v_useSplitter_3909_ = _args[19];
lean_object* v_isCasesOn_3910_ = _args[20];
lean_object* v___f_3911_ = _args[21];
lean_object* v___f_3912_ = _args[22];
lean_object* v_numDiscrEqs_3913_ = _args[23];
lean_object* v___f_3914_ = _args[24];
lean_object* v_matcherLevels_3915_ = _args[25];
lean_object* v_motive_3916_ = _args[26];
lean_object* v_discrs_x27_3917_ = _args[27];
_start:
{
uint8_t v_useSplitter_boxed_3918_; uint8_t v_isCasesOn_boxed_3919_; lean_object* v_res_3920_; 
v_useSplitter_boxed_3918_ = lean_unbox(v_useSplitter_3909_);
v_isCasesOn_boxed_3919_ = lean_unbox(v_isCasesOn_3910_);
v_res_3920_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__57(v_toPure_3890_, v_inst_3891_, v_toBind_3892_, v_toMatcherInfo_3893_, v_inst_3894_, v___f_3895_, v_onMotive_3896_, v_discrs_3897_, v_inst_3898_, v_matcherName_3899_, v_params_x27_3900_, v_onRemaining_3901_, v_remaining_3902_, v_inst_3903_, v_alts_3904_, v___f_3905_, v_onAlt_3906_, v___f_3907_, v_matcherApp_3908_, v_useSplitter_boxed_3918_, v_isCasesOn_boxed_3919_, v___f_3911_, v___f_3912_, v_numDiscrEqs_3913_, v___f_3914_, v_matcherLevels_3915_, v_motive_3916_, v_discrs_x27_3917_);
return v_res_3920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59(lean_object* v_toPure_3921_, lean_object* v_inst_3922_, lean_object* v_toBind_3923_, lean_object* v_toMatcherInfo_3924_, lean_object* v_inst_3925_, lean_object* v___f_3926_, lean_object* v_onMotive_3927_, lean_object* v_discrs_3928_, lean_object* v_inst_3929_, lean_object* v_matcherName_3930_, lean_object* v_onRemaining_3931_, lean_object* v_remaining_3932_, lean_object* v_inst_3933_, lean_object* v_alts_3934_, lean_object* v___f_3935_, lean_object* v_onAlt_3936_, lean_object* v___f_3937_, lean_object* v_matcherApp_3938_, uint8_t v_useSplitter_3939_, uint8_t v_isCasesOn_3940_, lean_object* v___f_3941_, lean_object* v___f_3942_, lean_object* v_numDiscrEqs_3943_, lean_object* v___f_3944_, lean_object* v_matcherLevels_3945_, lean_object* v_motive_3946_, lean_object* v_onParams_3947_, lean_object* v_params_x27_3948_){
_start:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___f_3951_; size_t v_sz_3952_; size_t v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v___x_3949_ = lean_box(v_useSplitter_3939_);
v___x_3950_ = lean_box(v_isCasesOn_3940_);
lean_inc_ref(v_discrs_3928_);
lean_inc_ref(v_inst_3925_);
lean_inc(v_toBind_3923_);
v___f_3951_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed), 28, 27);
lean_closure_set(v___f_3951_, 0, v_toPure_3921_);
lean_closure_set(v___f_3951_, 1, v_inst_3922_);
lean_closure_set(v___f_3951_, 2, v_toBind_3923_);
lean_closure_set(v___f_3951_, 3, v_toMatcherInfo_3924_);
lean_closure_set(v___f_3951_, 4, v_inst_3925_);
lean_closure_set(v___f_3951_, 5, v___f_3926_);
lean_closure_set(v___f_3951_, 6, v_onMotive_3927_);
lean_closure_set(v___f_3951_, 7, v_discrs_3928_);
lean_closure_set(v___f_3951_, 8, v_inst_3929_);
lean_closure_set(v___f_3951_, 9, v_matcherName_3930_);
lean_closure_set(v___f_3951_, 10, v_params_x27_3948_);
lean_closure_set(v___f_3951_, 11, v_onRemaining_3931_);
lean_closure_set(v___f_3951_, 12, v_remaining_3932_);
lean_closure_set(v___f_3951_, 13, v_inst_3933_);
lean_closure_set(v___f_3951_, 14, v_alts_3934_);
lean_closure_set(v___f_3951_, 15, v___f_3935_);
lean_closure_set(v___f_3951_, 16, v_onAlt_3936_);
lean_closure_set(v___f_3951_, 17, v___f_3937_);
lean_closure_set(v___f_3951_, 18, v_matcherApp_3938_);
lean_closure_set(v___f_3951_, 19, v___x_3949_);
lean_closure_set(v___f_3951_, 20, v___x_3950_);
lean_closure_set(v___f_3951_, 21, v___f_3941_);
lean_closure_set(v___f_3951_, 22, v___f_3942_);
lean_closure_set(v___f_3951_, 23, v_numDiscrEqs_3943_);
lean_closure_set(v___f_3951_, 24, v___f_3944_);
lean_closure_set(v___f_3951_, 25, v_matcherLevels_3945_);
lean_closure_set(v___f_3951_, 26, v_motive_3946_);
v_sz_3952_ = lean_array_size(v_discrs_3928_);
v___x_3953_ = ((size_t)0ULL);
v___x_3954_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_3925_, v_onParams_3947_, v_sz_3952_, v___x_3953_, v_discrs_3928_);
v___x_3955_ = lean_apply_4(v_toBind_3923_, lean_box(0), lean_box(0), v___x_3954_, v___f_3951_);
return v___x_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed(lean_object** _args){
lean_object* v_toPure_3956_ = _args[0];
lean_object* v_inst_3957_ = _args[1];
lean_object* v_toBind_3958_ = _args[2];
lean_object* v_toMatcherInfo_3959_ = _args[3];
lean_object* v_inst_3960_ = _args[4];
lean_object* v___f_3961_ = _args[5];
lean_object* v_onMotive_3962_ = _args[6];
lean_object* v_discrs_3963_ = _args[7];
lean_object* v_inst_3964_ = _args[8];
lean_object* v_matcherName_3965_ = _args[9];
lean_object* v_onRemaining_3966_ = _args[10];
lean_object* v_remaining_3967_ = _args[11];
lean_object* v_inst_3968_ = _args[12];
lean_object* v_alts_3969_ = _args[13];
lean_object* v___f_3970_ = _args[14];
lean_object* v_onAlt_3971_ = _args[15];
lean_object* v___f_3972_ = _args[16];
lean_object* v_matcherApp_3973_ = _args[17];
lean_object* v_useSplitter_3974_ = _args[18];
lean_object* v_isCasesOn_3975_ = _args[19];
lean_object* v___f_3976_ = _args[20];
lean_object* v___f_3977_ = _args[21];
lean_object* v_numDiscrEqs_3978_ = _args[22];
lean_object* v___f_3979_ = _args[23];
lean_object* v_matcherLevels_3980_ = _args[24];
lean_object* v_motive_3981_ = _args[25];
lean_object* v_onParams_3982_ = _args[26];
lean_object* v_params_x27_3983_ = _args[27];
_start:
{
uint8_t v_useSplitter_boxed_3984_; uint8_t v_isCasesOn_boxed_3985_; lean_object* v_res_3986_; 
v_useSplitter_boxed_3984_ = lean_unbox(v_useSplitter_3974_);
v_isCasesOn_boxed_3985_ = lean_unbox(v_isCasesOn_3975_);
v_res_3986_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__59(v_toPure_3956_, v_inst_3957_, v_toBind_3958_, v_toMatcherInfo_3959_, v_inst_3960_, v___f_3961_, v_onMotive_3962_, v_discrs_3963_, v_inst_3964_, v_matcherName_3965_, v_onRemaining_3966_, v_remaining_3967_, v_inst_3968_, v_alts_3969_, v___f_3970_, v_onAlt_3971_, v___f_3972_, v_matcherApp_3973_, v_useSplitter_boxed_3984_, v_isCasesOn_boxed_3985_, v___f_3976_, v___f_3977_, v_numDiscrEqs_3978_, v___f_3979_, v_matcherLevels_3980_, v_motive_3981_, v_onParams_3982_, v_params_x27_3983_);
return v_res_3986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60(lean_object* v_toPure_3987_, lean_object* v_inst_3988_, lean_object* v_toBind_3989_, lean_object* v_toMatcherInfo_3990_, lean_object* v_inst_3991_, lean_object* v___f_3992_, lean_object* v_onMotive_3993_, lean_object* v_discrs_3994_, lean_object* v_inst_3995_, lean_object* v_matcherName_3996_, lean_object* v_onRemaining_3997_, lean_object* v_remaining_3998_, lean_object* v_inst_3999_, lean_object* v_alts_4000_, lean_object* v___f_4001_, lean_object* v_onAlt_4002_, lean_object* v___f_4003_, lean_object* v_matcherApp_4004_, uint8_t v_useSplitter_4005_, uint8_t v_isCasesOn_4006_, lean_object* v___f_4007_, lean_object* v___f_4008_, lean_object* v___f_4009_, lean_object* v_matcherLevels_4010_, lean_object* v_motive_4011_, lean_object* v_onParams_4012_, lean_object* v_params_4013_, lean_object* v_numDiscrEqs_4014_){
_start:
{
lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___f_4017_; size_t v_sz_4018_; size_t v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___x_4015_ = lean_box(v_useSplitter_4005_);
v___x_4016_ = lean_box(v_isCasesOn_4006_);
lean_inc(v_onParams_4012_);
lean_inc_ref(v_inst_3991_);
lean_inc(v_toBind_3989_);
v___f_4017_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed), 28, 27);
lean_closure_set(v___f_4017_, 0, v_toPure_3987_);
lean_closure_set(v___f_4017_, 1, v_inst_3988_);
lean_closure_set(v___f_4017_, 2, v_toBind_3989_);
lean_closure_set(v___f_4017_, 3, v_toMatcherInfo_3990_);
lean_closure_set(v___f_4017_, 4, v_inst_3991_);
lean_closure_set(v___f_4017_, 5, v___f_3992_);
lean_closure_set(v___f_4017_, 6, v_onMotive_3993_);
lean_closure_set(v___f_4017_, 7, v_discrs_3994_);
lean_closure_set(v___f_4017_, 8, v_inst_3995_);
lean_closure_set(v___f_4017_, 9, v_matcherName_3996_);
lean_closure_set(v___f_4017_, 10, v_onRemaining_3997_);
lean_closure_set(v___f_4017_, 11, v_remaining_3998_);
lean_closure_set(v___f_4017_, 12, v_inst_3999_);
lean_closure_set(v___f_4017_, 13, v_alts_4000_);
lean_closure_set(v___f_4017_, 14, v___f_4001_);
lean_closure_set(v___f_4017_, 15, v_onAlt_4002_);
lean_closure_set(v___f_4017_, 16, v___f_4003_);
lean_closure_set(v___f_4017_, 17, v_matcherApp_4004_);
lean_closure_set(v___f_4017_, 18, v___x_4015_);
lean_closure_set(v___f_4017_, 19, v___x_4016_);
lean_closure_set(v___f_4017_, 20, v___f_4007_);
lean_closure_set(v___f_4017_, 21, v___f_4008_);
lean_closure_set(v___f_4017_, 22, v_numDiscrEqs_4014_);
lean_closure_set(v___f_4017_, 23, v___f_4009_);
lean_closure_set(v___f_4017_, 24, v_matcherLevels_4010_);
lean_closure_set(v___f_4017_, 25, v_motive_4011_);
lean_closure_set(v___f_4017_, 26, v_onParams_4012_);
v_sz_4018_ = lean_array_size(v_params_4013_);
v___x_4019_ = ((size_t)0ULL);
v___x_4020_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_3991_, v_onParams_4012_, v_sz_4018_, v___x_4019_, v_params_4013_);
v___x_4021_ = lean_apply_4(v_toBind_3989_, lean_box(0), lean_box(0), v___x_4020_, v___f_4017_);
return v___x_4021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed(lean_object** _args){
lean_object* v_toPure_4022_ = _args[0];
lean_object* v_inst_4023_ = _args[1];
lean_object* v_toBind_4024_ = _args[2];
lean_object* v_toMatcherInfo_4025_ = _args[3];
lean_object* v_inst_4026_ = _args[4];
lean_object* v___f_4027_ = _args[5];
lean_object* v_onMotive_4028_ = _args[6];
lean_object* v_discrs_4029_ = _args[7];
lean_object* v_inst_4030_ = _args[8];
lean_object* v_matcherName_4031_ = _args[9];
lean_object* v_onRemaining_4032_ = _args[10];
lean_object* v_remaining_4033_ = _args[11];
lean_object* v_inst_4034_ = _args[12];
lean_object* v_alts_4035_ = _args[13];
lean_object* v___f_4036_ = _args[14];
lean_object* v_onAlt_4037_ = _args[15];
lean_object* v___f_4038_ = _args[16];
lean_object* v_matcherApp_4039_ = _args[17];
lean_object* v_useSplitter_4040_ = _args[18];
lean_object* v_isCasesOn_4041_ = _args[19];
lean_object* v___f_4042_ = _args[20];
lean_object* v___f_4043_ = _args[21];
lean_object* v___f_4044_ = _args[22];
lean_object* v_matcherLevels_4045_ = _args[23];
lean_object* v_motive_4046_ = _args[24];
lean_object* v_onParams_4047_ = _args[25];
lean_object* v_params_4048_ = _args[26];
lean_object* v_numDiscrEqs_4049_ = _args[27];
_start:
{
uint8_t v_useSplitter_boxed_4050_; uint8_t v_isCasesOn_boxed_4051_; lean_object* v_res_4052_; 
v_useSplitter_boxed_4050_ = lean_unbox(v_useSplitter_4040_);
v_isCasesOn_boxed_4051_ = lean_unbox(v_isCasesOn_4041_);
v_res_4052_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__60(v_toPure_4022_, v_inst_4023_, v_toBind_4024_, v_toMatcherInfo_4025_, v_inst_4026_, v___f_4027_, v_onMotive_4028_, v_discrs_4029_, v_inst_4030_, v_matcherName_4031_, v_onRemaining_4032_, v_remaining_4033_, v_inst_4034_, v_alts_4035_, v___f_4036_, v_onAlt_4037_, v___f_4038_, v_matcherApp_4039_, v_useSplitter_boxed_4050_, v_isCasesOn_boxed_4051_, v___f_4042_, v___f_4043_, v___f_4044_, v_matcherLevels_4045_, v_motive_4046_, v_onParams_4047_, v_params_4048_, v_numDiscrEqs_4049_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__61(lean_object* v___f_4053_, lean_object* v_numDiscrEqs_4054_){
_start:
{
lean_object* v___x_4055_; 
v___x_4055_ = lean_apply_1(v___f_4053_, v_numDiscrEqs_4054_);
return v___x_4055_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1(void){
_start:
{
lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4057_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__0));
v___x_4058_ = l_Lean_stringToMessageData(v___x_4057_);
return v___x_4058_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3(void){
_start:
{
lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4060_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__2));
v___x_4061_ = l_Lean_stringToMessageData(v___x_4060_);
return v___x_4061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63(lean_object* v_matcherName_4062_, lean_object* v_inst_4063_, lean_object* v_inst_4064_, lean_object* v_toBind_4065_, lean_object* v___f_4066_, lean_object* v_toPure_4067_, lean_object* v___f_4068_, lean_object* v_____do__lift_4069_){
_start:
{
if (lean_obj_tag(v_____do__lift_4069_) == 0)
{
lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
lean_dec(v___f_4068_);
lean_dec(v_toPure_4067_);
v___x_4070_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1);
v___x_4071_ = l_Lean_MessageData_ofName(v_matcherName_4062_);
v___x_4072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4070_);
lean_ctor_set(v___x_4072_, 1, v___x_4071_);
v___x_4073_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3);
v___x_4074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4072_);
lean_ctor_set(v___x_4074_, 1, v___x_4073_);
v___x_4075_ = l_Lean_throwError___redArg(v_inst_4063_, v_inst_4064_, v___x_4074_);
v___x_4076_ = lean_apply_4(v_toBind_4065_, lean_box(0), lean_box(0), v___x_4075_, v___f_4066_);
return v___x_4076_;
}
else
{
lean_object* v_val_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
lean_dec(v___f_4066_);
lean_dec_ref(v_inst_4064_);
lean_dec_ref(v_inst_4063_);
lean_dec(v_matcherName_4062_);
v_val_4077_ = lean_ctor_get(v_____do__lift_4069_, 0);
v___x_4078_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_4077_);
v___x_4079_ = lean_apply_2(v_toPure_4067_, lean_box(0), v___x_4078_);
v___x_4080_ = lean_apply_4(v_toBind_4065_, lean_box(0), lean_box(0), v___x_4079_, v___f_4068_);
return v___x_4080_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed(lean_object* v_matcherName_4081_, lean_object* v_inst_4082_, lean_object* v_inst_4083_, lean_object* v_toBind_4084_, lean_object* v___f_4085_, lean_object* v_toPure_4086_, lean_object* v___f_4087_, lean_object* v_____do__lift_4088_){
_start:
{
lean_object* v_res_4089_; 
v_res_4089_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__63(v_matcherName_4081_, v_inst_4082_, v_inst_4083_, v_toBind_4084_, v___f_4085_, v_toPure_4086_, v___f_4087_, v_____do__lift_4088_);
lean_dec(v_____do__lift_4088_);
return v_res_4089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64(lean_object* v_matcherApp_4090_, lean_object* v_toPure_4091_, lean_object* v_inst_4092_, lean_object* v_toBind_4093_, lean_object* v_inst_4094_, lean_object* v___f_4095_, lean_object* v_onMotive_4096_, lean_object* v_inst_4097_, lean_object* v_onRemaining_4098_, lean_object* v_inst_4099_, lean_object* v___f_4100_, lean_object* v_onAlt_4101_, lean_object* v___f_4102_, uint8_t v_useSplitter_4103_, lean_object* v___f_4104_, lean_object* v___f_4105_, lean_object* v___f_4106_, lean_object* v_onParams_4107_, lean_object* v_inst_4108_, lean_object* v_____do__lift_4109_){
_start:
{
lean_object* v_toMatcherInfo_4110_; lean_object* v_matcherName_4111_; lean_object* v_matcherLevels_4112_; lean_object* v_params_4113_; lean_object* v_motive_4114_; lean_object* v_discrs_4115_; lean_object* v_alts_4116_; lean_object* v_remaining_4117_; uint8_t v_isCasesOn_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___f_4121_; 
v_toMatcherInfo_4110_ = lean_ctor_get(v_matcherApp_4090_, 0);
lean_inc_ref(v_toMatcherInfo_4110_);
v_matcherName_4111_ = lean_ctor_get(v_matcherApp_4090_, 1);
lean_inc_n(v_matcherName_4111_, 3);
v_matcherLevels_4112_ = lean_ctor_get(v_matcherApp_4090_, 2);
lean_inc_ref(v_matcherLevels_4112_);
v_params_4113_ = lean_ctor_get(v_matcherApp_4090_, 3);
lean_inc_ref(v_params_4113_);
v_motive_4114_ = lean_ctor_get(v_matcherApp_4090_, 4);
lean_inc_ref(v_motive_4114_);
v_discrs_4115_ = lean_ctor_get(v_matcherApp_4090_, 5);
lean_inc_ref(v_discrs_4115_);
v_alts_4116_ = lean_ctor_get(v_matcherApp_4090_, 6);
lean_inc_ref(v_alts_4116_);
v_remaining_4117_ = lean_ctor_get(v_matcherApp_4090_, 7);
lean_inc_ref(v_remaining_4117_);
v_isCasesOn_4118_ = l_Lean_isCasesOnRecursor(v_____do__lift_4109_, v_matcherName_4111_);
v___x_4119_ = lean_box(v_useSplitter_4103_);
v___x_4120_ = lean_box(v_isCasesOn_4118_);
lean_inc_ref(v_inst_4097_);
lean_inc_ref(v_inst_4094_);
lean_inc(v_toBind_4093_);
lean_inc(v_toPure_4091_);
v___f_4121_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed), 28, 27);
lean_closure_set(v___f_4121_, 0, v_toPure_4091_);
lean_closure_set(v___f_4121_, 1, v_inst_4092_);
lean_closure_set(v___f_4121_, 2, v_toBind_4093_);
lean_closure_set(v___f_4121_, 3, v_toMatcherInfo_4110_);
lean_closure_set(v___f_4121_, 4, v_inst_4094_);
lean_closure_set(v___f_4121_, 5, v___f_4095_);
lean_closure_set(v___f_4121_, 6, v_onMotive_4096_);
lean_closure_set(v___f_4121_, 7, v_discrs_4115_);
lean_closure_set(v___f_4121_, 8, v_inst_4097_);
lean_closure_set(v___f_4121_, 9, v_matcherName_4111_);
lean_closure_set(v___f_4121_, 10, v_onRemaining_4098_);
lean_closure_set(v___f_4121_, 11, v_remaining_4117_);
lean_closure_set(v___f_4121_, 12, v_inst_4099_);
lean_closure_set(v___f_4121_, 13, v_alts_4116_);
lean_closure_set(v___f_4121_, 14, v___f_4100_);
lean_closure_set(v___f_4121_, 15, v_onAlt_4101_);
lean_closure_set(v___f_4121_, 16, v___f_4102_);
lean_closure_set(v___f_4121_, 17, v_matcherApp_4090_);
lean_closure_set(v___f_4121_, 18, v___x_4119_);
lean_closure_set(v___f_4121_, 19, v___x_4120_);
lean_closure_set(v___f_4121_, 20, v___f_4104_);
lean_closure_set(v___f_4121_, 21, v___f_4105_);
lean_closure_set(v___f_4121_, 22, v___f_4106_);
lean_closure_set(v___f_4121_, 23, v_matcherLevels_4112_);
lean_closure_set(v___f_4121_, 24, v_motive_4114_);
lean_closure_set(v___f_4121_, 25, v_onParams_4107_);
lean_closure_set(v___f_4121_, 26, v_params_4113_);
if (v_isCasesOn_4118_ == 0)
{
lean_object* v___f_4122_; lean_object* v___f_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; 
v___f_4122_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61), 2, 1);
lean_closure_set(v___f_4122_, 0, v___f_4121_);
lean_inc_ref(v___f_4122_);
lean_inc(v_toBind_4093_);
lean_inc_ref(v_inst_4094_);
lean_inc(v_matcherName_4111_);
v___f_4123_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed), 8, 7);
lean_closure_set(v___f_4123_, 0, v_matcherName_4111_);
lean_closure_set(v___f_4123_, 1, v_inst_4094_);
lean_closure_set(v___f_4123_, 2, v_inst_4097_);
lean_closure_set(v___f_4123_, 3, v_toBind_4093_);
lean_closure_set(v___f_4123_, 4, v___f_4122_);
lean_closure_set(v___f_4123_, 5, v_toPure_4091_);
lean_closure_set(v___f_4123_, 6, v___f_4122_);
v___x_4124_ = l_Lean_Meta_getMatcherInfo_x3f___redArg(v_inst_4094_, v_inst_4108_, v_matcherName_4111_);
v___x_4125_ = lean_apply_4(v_toBind_4093_, lean_box(0), lean_box(0), v___x_4124_, v___f_4123_);
return v___x_4125_;
}
else
{
lean_object* v___f_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
lean_dec(v_matcherName_4111_);
lean_dec_ref(v_inst_4108_);
lean_dec_ref(v_inst_4097_);
lean_dec_ref(v_inst_4094_);
v___f_4126_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61), 2, 1);
lean_closure_set(v___f_4126_, 0, v___f_4121_);
v___x_4127_ = lean_unsigned_to_nat(0u);
v___x_4128_ = lean_apply_2(v_toPure_4091_, lean_box(0), v___x_4127_);
v___x_4129_ = lean_apply_4(v_toBind_4093_, lean_box(0), lean_box(0), v___x_4128_, v___f_4126_);
return v___x_4129_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed(lean_object** _args){
lean_object* v_matcherApp_4130_ = _args[0];
lean_object* v_toPure_4131_ = _args[1];
lean_object* v_inst_4132_ = _args[2];
lean_object* v_toBind_4133_ = _args[3];
lean_object* v_inst_4134_ = _args[4];
lean_object* v___f_4135_ = _args[5];
lean_object* v_onMotive_4136_ = _args[6];
lean_object* v_inst_4137_ = _args[7];
lean_object* v_onRemaining_4138_ = _args[8];
lean_object* v_inst_4139_ = _args[9];
lean_object* v___f_4140_ = _args[10];
lean_object* v_onAlt_4141_ = _args[11];
lean_object* v___f_4142_ = _args[12];
lean_object* v_useSplitter_4143_ = _args[13];
lean_object* v___f_4144_ = _args[14];
lean_object* v___f_4145_ = _args[15];
lean_object* v___f_4146_ = _args[16];
lean_object* v_onParams_4147_ = _args[17];
lean_object* v_inst_4148_ = _args[18];
lean_object* v_____do__lift_4149_ = _args[19];
_start:
{
uint8_t v_useSplitter_boxed_4150_; lean_object* v_res_4151_; 
v_useSplitter_boxed_4150_ = lean_unbox(v_useSplitter_4143_);
v_res_4151_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__64(v_matcherApp_4130_, v_toPure_4131_, v_inst_4132_, v_toBind_4133_, v_inst_4134_, v___f_4135_, v_onMotive_4136_, v_inst_4137_, v_onRemaining_4138_, v_inst_4139_, v___f_4140_, v_onAlt_4141_, v___f_4142_, v_useSplitter_boxed_4150_, v___f_4144_, v___f_4145_, v___f_4146_, v_onParams_4147_, v_inst_4148_, v_____do__lift_4149_);
return v_res_4151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg(lean_object* v_inst_4152_, lean_object* v_inst_4153_, lean_object* v_inst_4154_, lean_object* v_inst_4155_, lean_object* v_inst_4156_, lean_object* v_matcherApp_4157_, uint8_t v_useSplitter_4158_, uint8_t v_addEqualities_4159_, lean_object* v_onParams_4160_, lean_object* v_onMotive_4161_, lean_object* v_onAlt_4162_, lean_object* v_onRemaining_4163_){
_start:
{
lean_object* v_toApplicative_4164_; lean_object* v_toBind_4165_; lean_object* v_getEnv_4166_; lean_object* v_toPure_4167_; lean_object* v___f_4168_; lean_object* v___f_4169_; lean_object* v___f_4170_; lean_object* v___f_4171_; lean_object* v___f_4172_; lean_object* v___f_4173_; lean_object* v___x_4174_; lean_object* v___f_4175_; lean_object* v___x_4176_; lean_object* v___f_4177_; lean_object* v___x_4178_; 
v_toApplicative_4164_ = lean_ctor_get(v_inst_4154_, 0);
v_toBind_4165_ = lean_ctor_get(v_inst_4154_, 1);
lean_inc_n(v_toBind_4165_, 4);
v_getEnv_4166_ = lean_ctor_get(v_inst_4156_, 0);
lean_inc(v_getEnv_4166_);
v_toPure_4167_ = lean_ctor_get(v_toApplicative_4164_, 1);
lean_inc_n(v_toPure_4167_, 5);
lean_inc_ref(v_inst_4155_);
lean_inc_ref_n(v_inst_4154_, 2);
v___f_4168_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4168_, 0, v_inst_4154_);
lean_closure_set(v___f_4168_, 1, v_inst_4155_);
lean_inc_n(v_inst_4152_, 3);
v___f_4169_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4169_, 0, v_inst_4152_);
v___f_4170_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4170_, 0, v_inst_4154_);
lean_closure_set(v___f_4170_, 1, v___f_4169_);
v___f_4171_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__3), 2, 1);
lean_closure_set(v___f_4171_, 0, v_toPure_4167_);
v___f_4172_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__4), 2, 1);
lean_closure_set(v___f_4172_, 0, v_toPure_4167_);
v___f_4173_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7), 6, 3);
lean_closure_set(v___f_4173_, 0, v_toPure_4167_);
lean_closure_set(v___f_4173_, 1, v_inst_4152_);
lean_closure_set(v___f_4173_, 2, v_toBind_4165_);
v___x_4174_ = lean_box(v_addEqualities_4159_);
v___f_4175_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__12___boxed), 7, 4);
lean_closure_set(v___f_4175_, 0, v_toPure_4167_);
lean_closure_set(v___f_4175_, 1, v___x_4174_);
lean_closure_set(v___f_4175_, 2, v_inst_4152_);
lean_closure_set(v___f_4175_, 3, v_toBind_4165_);
v___x_4176_ = lean_box(v_useSplitter_4158_);
v___f_4177_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed), 20, 19);
lean_closure_set(v___f_4177_, 0, v_matcherApp_4157_);
lean_closure_set(v___f_4177_, 1, v_toPure_4167_);
lean_closure_set(v___f_4177_, 2, v_inst_4152_);
lean_closure_set(v___f_4177_, 3, v_toBind_4165_);
lean_closure_set(v___f_4177_, 4, v_inst_4154_);
lean_closure_set(v___f_4177_, 5, v___f_4175_);
lean_closure_set(v___f_4177_, 6, v_onMotive_4161_);
lean_closure_set(v___f_4177_, 7, v_inst_4155_);
lean_closure_set(v___f_4177_, 8, v_onRemaining_4163_);
lean_closure_set(v___f_4177_, 9, v_inst_4153_);
lean_closure_set(v___f_4177_, 10, v___f_4171_);
lean_closure_set(v___f_4177_, 11, v_onAlt_4162_);
lean_closure_set(v___f_4177_, 12, v___f_4170_);
lean_closure_set(v___f_4177_, 13, v___x_4176_);
lean_closure_set(v___f_4177_, 14, v___f_4172_);
lean_closure_set(v___f_4177_, 15, v___f_4168_);
lean_closure_set(v___f_4177_, 16, v___f_4173_);
lean_closure_set(v___f_4177_, 17, v_onParams_4160_);
lean_closure_set(v___f_4177_, 18, v_inst_4156_);
v___x_4178_ = lean_apply_4(v_toBind_4165_, lean_box(0), lean_box(0), v_getEnv_4166_, v___f_4177_);
return v___x_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___boxed(lean_object* v_inst_4179_, lean_object* v_inst_4180_, lean_object* v_inst_4181_, lean_object* v_inst_4182_, lean_object* v_inst_4183_, lean_object* v_matcherApp_4184_, lean_object* v_useSplitter_4185_, lean_object* v_addEqualities_4186_, lean_object* v_onParams_4187_, lean_object* v_onMotive_4188_, lean_object* v_onAlt_4189_, lean_object* v_onRemaining_4190_){
_start:
{
uint8_t v_useSplitter_boxed_4191_; uint8_t v_addEqualities_boxed_4192_; lean_object* v_res_4193_; 
v_useSplitter_boxed_4191_ = lean_unbox(v_useSplitter_4185_);
v_addEqualities_boxed_4192_ = lean_unbox(v_addEqualities_4186_);
v_res_4193_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_4179_, v_inst_4180_, v_inst_4181_, v_inst_4182_, v_inst_4183_, v_matcherApp_4184_, v_useSplitter_boxed_4191_, v_addEqualities_boxed_4192_, v_onParams_4187_, v_onMotive_4188_, v_onAlt_4189_, v_onRemaining_4190_);
return v_res_4193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform(lean_object* v_n_4194_, lean_object* v_inst_4195_, lean_object* v_inst_4196_, lean_object* v_inst_4197_, lean_object* v_inst_4198_, lean_object* v_inst_4199_, lean_object* v_inst_4200_, lean_object* v_inst_4201_, lean_object* v_inst_4202_, lean_object* v_matcherApp_4203_, uint8_t v_useSplitter_4204_, uint8_t v_addEqualities_4205_, lean_object* v_onParams_4206_, lean_object* v_onMotive_4207_, lean_object* v_onAlt_4208_, lean_object* v_onRemaining_4209_){
_start:
{
lean_object* v___x_4210_; 
v___x_4210_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_4195_, v_inst_4196_, v_inst_4197_, v_inst_4198_, v_inst_4199_, v_matcherApp_4203_, v_useSplitter_4204_, v_addEqualities_4205_, v_onParams_4206_, v_onMotive_4207_, v_onAlt_4208_, v_onRemaining_4209_);
return v___x_4210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___boxed(lean_object* v_n_4211_, lean_object* v_inst_4212_, lean_object* v_inst_4213_, lean_object* v_inst_4214_, lean_object* v_inst_4215_, lean_object* v_inst_4216_, lean_object* v_inst_4217_, lean_object* v_inst_4218_, lean_object* v_inst_4219_, lean_object* v_matcherApp_4220_, lean_object* v_useSplitter_4221_, lean_object* v_addEqualities_4222_, lean_object* v_onParams_4223_, lean_object* v_onMotive_4224_, lean_object* v_onAlt_4225_, lean_object* v_onRemaining_4226_){
_start:
{
uint8_t v_useSplitter_boxed_4227_; uint8_t v_addEqualities_boxed_4228_; lean_object* v_res_4229_; 
v_useSplitter_boxed_4227_ = lean_unbox(v_useSplitter_4221_);
v_addEqualities_boxed_4228_ = lean_unbox(v_addEqualities_4222_);
v_res_4229_ = l_Lean_Meta_MatcherApp_transform(v_n_4211_, v_inst_4212_, v_inst_4213_, v_inst_4214_, v_inst_4215_, v_inst_4216_, v_inst_4217_, v_inst_4218_, v_inst_4219_, v_matcherApp_4220_, v_useSplitter_boxed_4227_, v_addEqualities_boxed_4228_, v_onParams_4223_, v_onMotive_4224_, v_onAlt_4225_, v_onRemaining_4226_);
lean_dec(v_inst_4219_);
lean_dec(v_inst_4218_);
lean_dec_ref(v_inst_4217_);
return v_res_4229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0(lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_){
_start:
{
lean_object* v___x_4236_; 
v___x_4236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4236_, 0, v___y_4230_);
return v___x_4236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0___boxed(lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_){
_start:
{
lean_object* v_res_4243_; 
v_res_4243_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__0(v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
lean_dec(v___y_4239_);
lean_dec_ref(v___y_4238_);
return v_res_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1(lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
lean_object* v___x_4250_; 
v___x_4250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4250_, 0, v___y_4244_);
return v___x_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1___boxed(lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_){
_start:
{
lean_object* v_res_4257_; 
v_res_4257_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__1(v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_);
lean_dec(v___y_4255_);
lean_dec_ref(v___y_4254_);
lean_dec(v___y_4253_);
lean_dec_ref(v___y_4252_);
return v_res_4257_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(lean_object* v_opts_4258_, lean_object* v_opt_4259_){
_start:
{
lean_object* v_name_4260_; lean_object* v_defValue_4261_; lean_object* v_map_4262_; lean_object* v___x_4263_; 
v_name_4260_ = lean_ctor_get(v_opt_4259_, 0);
v_defValue_4261_ = lean_ctor_get(v_opt_4259_, 1);
v_map_4262_ = lean_ctor_get(v_opts_4258_, 0);
v___x_4263_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4262_, v_name_4260_);
if (lean_obj_tag(v___x_4263_) == 0)
{
uint8_t v___x_4264_; 
v___x_4264_ = lean_unbox(v_defValue_4261_);
return v___x_4264_;
}
else
{
lean_object* v_val_4265_; 
v_val_4265_ = lean_ctor_get(v___x_4263_, 0);
lean_inc(v_val_4265_);
lean_dec_ref(v___x_4263_);
if (lean_obj_tag(v_val_4265_) == 1)
{
uint8_t v_v_4266_; 
v_v_4266_ = lean_ctor_get_uint8(v_val_4265_, 0);
lean_dec_ref(v_val_4265_);
return v_v_4266_;
}
else
{
uint8_t v___x_4267_; 
lean_dec(v_val_4265_);
v___x_4267_ = lean_unbox(v_defValue_4261_);
return v___x_4267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11___boxed(lean_object* v_opts_4268_, lean_object* v_opt_4269_){
_start:
{
uint8_t v_res_4270_; lean_object* v_r_4271_; 
v_res_4270_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(v_opts_4268_, v_opt_4269_);
lean_dec_ref(v_opt_4269_);
lean_dec_ref(v_opts_4268_);
v_r_4271_ = lean_box(v_res_4270_);
return v_r_4271_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(uint8_t v___y_4280_, uint8_t v_suppressElabErrors_4281_, lean_object* v_x_4282_){
_start:
{
if (lean_obj_tag(v_x_4282_) == 1)
{
lean_object* v_pre_4283_; 
v_pre_4283_ = lean_ctor_get(v_x_4282_, 0);
switch(lean_obj_tag(v_pre_4283_))
{
case 1:
{
lean_object* v_pre_4284_; 
v_pre_4284_ = lean_ctor_get(v_pre_4283_, 0);
switch(lean_obj_tag(v_pre_4284_))
{
case 0:
{
lean_object* v_str_4285_; lean_object* v_str_4286_; lean_object* v___x_4287_; uint8_t v___x_4288_; 
v_str_4285_ = lean_ctor_get(v_x_4282_, 1);
v_str_4286_ = lean_ctor_get(v_pre_4283_, 1);
v___x_4287_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_4288_ = lean_string_dec_eq(v_str_4286_, v___x_4287_);
if (v___x_4288_ == 0)
{
lean_object* v___x_4289_; uint8_t v___x_4290_; 
v___x_4289_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_4290_ = lean_string_dec_eq(v_str_4286_, v___x_4289_);
if (v___x_4290_ == 0)
{
return v___y_4280_;
}
else
{
lean_object* v___x_4291_; uint8_t v___x_4292_; 
v___x_4291_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_4292_ = lean_string_dec_eq(v_str_4285_, v___x_4291_);
if (v___x_4292_ == 0)
{
return v___y_4280_;
}
else
{
return v_suppressElabErrors_4281_;
}
}
}
else
{
lean_object* v___x_4293_; uint8_t v___x_4294_; 
v___x_4293_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_4294_ = lean_string_dec_eq(v_str_4285_, v___x_4293_);
if (v___x_4294_ == 0)
{
return v___y_4280_;
}
else
{
return v_suppressElabErrors_4281_;
}
}
}
case 1:
{
lean_object* v_pre_4295_; 
v_pre_4295_ = lean_ctor_get(v_pre_4284_, 0);
if (lean_obj_tag(v_pre_4295_) == 0)
{
lean_object* v_str_4296_; lean_object* v_str_4297_; lean_object* v_str_4298_; lean_object* v___x_4299_; uint8_t v___x_4300_; 
v_str_4296_ = lean_ctor_get(v_x_4282_, 1);
v_str_4297_ = lean_ctor_get(v_pre_4283_, 1);
v_str_4298_ = lean_ctor_get(v_pre_4284_, 1);
v___x_4299_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_4300_ = lean_string_dec_eq(v_str_4298_, v___x_4299_);
if (v___x_4300_ == 0)
{
return v___y_4280_;
}
else
{
lean_object* v___x_4301_; uint8_t v___x_4302_; 
v___x_4301_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_4302_ = lean_string_dec_eq(v_str_4297_, v___x_4301_);
if (v___x_4302_ == 0)
{
return v___y_4280_;
}
else
{
lean_object* v___x_4303_; uint8_t v___x_4304_; 
v___x_4303_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_4304_ = lean_string_dec_eq(v_str_4296_, v___x_4303_);
if (v___x_4304_ == 0)
{
return v___y_4280_;
}
else
{
return v_suppressElabErrors_4281_;
}
}
}
}
else
{
return v___y_4280_;
}
}
default: 
{
return v___y_4280_;
}
}
}
case 0:
{
lean_object* v_str_4305_; lean_object* v___x_4306_; uint8_t v___x_4307_; 
v_str_4305_ = lean_ctor_get(v_x_4282_, 1);
v___x_4306_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_4307_ = lean_string_dec_eq(v_str_4305_, v___x_4306_);
if (v___x_4307_ == 0)
{
return v___y_4280_;
}
else
{
return v_suppressElabErrors_4281_;
}
}
default: 
{
return v___y_4280_;
}
}
}
else
{
return v___y_4280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___y_4308_, lean_object* v_suppressElabErrors_4309_, lean_object* v_x_4310_){
_start:
{
uint8_t v___y_31993__boxed_4311_; uint8_t v_suppressElabErrors_boxed_4312_; uint8_t v_res_4313_; lean_object* v_r_4314_; 
v___y_31993__boxed_4311_ = lean_unbox(v___y_4308_);
v_suppressElabErrors_boxed_4312_ = lean_unbox(v_suppressElabErrors_4309_);
v_res_4313_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(v___y_31993__boxed_4311_, v_suppressElabErrors_boxed_4312_, v_x_4310_);
lean_dec(v_x_4310_);
v_r_4314_ = lean_box(v_res_4313_);
return v_r_4314_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(lean_object* v_ref_4316_, lean_object* v_msgData_4317_, uint8_t v_severity_4318_, uint8_t v_isSilent_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_){
_start:
{
uint8_t v___y_4326_; uint8_t v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4329_; lean_object* v___y_4330_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___y_4334_; lean_object* v___y_4362_; uint8_t v___y_4363_; uint8_t v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4366_; uint8_t v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4387_; uint8_t v___y_4388_; uint8_t v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; uint8_t v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4398_; uint8_t v___y_4399_; lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v___y_4402_; uint8_t v___y_4403_; uint8_t v___y_4404_; uint8_t v___x_4409_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v___y_4413_; uint8_t v___y_4414_; lean_object* v___y_4415_; uint8_t v___y_4416_; uint8_t v___y_4417_; uint8_t v___y_4419_; uint8_t v___x_4434_; 
v___x_4409_ = 2;
v___x_4434_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4318_, v___x_4409_);
if (v___x_4434_ == 0)
{
v___y_4419_ = v___x_4434_;
goto v___jp_4418_;
}
else
{
uint8_t v___x_4435_; 
lean_inc_ref(v_msgData_4317_);
v___x_4435_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4317_);
v___y_4419_ = v___x_4435_;
goto v___jp_4418_;
}
v___jp_4325_:
{
lean_object* v___x_4335_; lean_object* v_currNamespace_4336_; lean_object* v_openDecls_4337_; lean_object* v_env_4338_; lean_object* v_nextMacroScope_4339_; lean_object* v_ngen_4340_; lean_object* v_auxDeclNGen_4341_; lean_object* v_traceState_4342_; lean_object* v_cache_4343_; lean_object* v_messages_4344_; lean_object* v_infoState_4345_; lean_object* v_snapshotTasks_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4360_; 
v___x_4335_ = lean_st_ref_take(v___y_4334_);
v_currNamespace_4336_ = lean_ctor_get(v___y_4333_, 6);
v_openDecls_4337_ = lean_ctor_get(v___y_4333_, 7);
v_env_4338_ = lean_ctor_get(v___x_4335_, 0);
v_nextMacroScope_4339_ = lean_ctor_get(v___x_4335_, 1);
v_ngen_4340_ = lean_ctor_get(v___x_4335_, 2);
v_auxDeclNGen_4341_ = lean_ctor_get(v___x_4335_, 3);
v_traceState_4342_ = lean_ctor_get(v___x_4335_, 4);
v_cache_4343_ = lean_ctor_get(v___x_4335_, 5);
v_messages_4344_ = lean_ctor_get(v___x_4335_, 6);
v_infoState_4345_ = lean_ctor_get(v___x_4335_, 7);
v_snapshotTasks_4346_ = lean_ctor_get(v___x_4335_, 8);
v_isSharedCheck_4360_ = !lean_is_exclusive(v___x_4335_);
if (v_isSharedCheck_4360_ == 0)
{
v___x_4348_ = v___x_4335_;
v_isShared_4349_ = v_isSharedCheck_4360_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_snapshotTasks_4346_);
lean_inc(v_infoState_4345_);
lean_inc(v_messages_4344_);
lean_inc(v_cache_4343_);
lean_inc(v_traceState_4342_);
lean_inc(v_auxDeclNGen_4341_);
lean_inc(v_ngen_4340_);
lean_inc(v_nextMacroScope_4339_);
lean_inc(v_env_4338_);
lean_dec(v___x_4335_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4360_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4355_; 
lean_inc(v_openDecls_4337_);
lean_inc(v_currNamespace_4336_);
v___x_4350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4350_, 0, v_currNamespace_4336_);
lean_ctor_set(v___x_4350_, 1, v_openDecls_4337_);
v___x_4351_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4351_, 0, v___x_4350_);
lean_ctor_set(v___x_4351_, 1, v___y_4328_);
lean_inc_ref(v___y_4329_);
lean_inc_ref(v___y_4330_);
v___x_4352_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4352_, 0, v___y_4330_);
lean_ctor_set(v___x_4352_, 1, v___y_4331_);
lean_ctor_set(v___x_4352_, 2, v___y_4332_);
lean_ctor_set(v___x_4352_, 3, v___y_4329_);
lean_ctor_set(v___x_4352_, 4, v___x_4351_);
lean_ctor_set_uint8(v___x_4352_, sizeof(void*)*5, v___y_4327_);
lean_ctor_set_uint8(v___x_4352_, sizeof(void*)*5 + 1, v___y_4326_);
lean_ctor_set_uint8(v___x_4352_, sizeof(void*)*5 + 2, v_isSilent_4319_);
v___x_4353_ = l_Lean_MessageLog_add(v___x_4352_, v_messages_4344_);
if (v_isShared_4349_ == 0)
{
lean_ctor_set(v___x_4348_, 6, v___x_4353_);
v___x_4355_ = v___x_4348_;
goto v_reusejp_4354_;
}
else
{
lean_object* v_reuseFailAlloc_4359_; 
v_reuseFailAlloc_4359_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4359_, 0, v_env_4338_);
lean_ctor_set(v_reuseFailAlloc_4359_, 1, v_nextMacroScope_4339_);
lean_ctor_set(v_reuseFailAlloc_4359_, 2, v_ngen_4340_);
lean_ctor_set(v_reuseFailAlloc_4359_, 3, v_auxDeclNGen_4341_);
lean_ctor_set(v_reuseFailAlloc_4359_, 4, v_traceState_4342_);
lean_ctor_set(v_reuseFailAlloc_4359_, 5, v_cache_4343_);
lean_ctor_set(v_reuseFailAlloc_4359_, 6, v___x_4353_);
lean_ctor_set(v_reuseFailAlloc_4359_, 7, v_infoState_4345_);
lean_ctor_set(v_reuseFailAlloc_4359_, 8, v_snapshotTasks_4346_);
v___x_4355_ = v_reuseFailAlloc_4359_;
goto v_reusejp_4354_;
}
v_reusejp_4354_:
{
lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; 
v___x_4356_ = lean_st_ref_set(v___y_4334_, v___x_4355_);
v___x_4357_ = lean_box(0);
v___x_4358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4358_, 0, v___x_4357_);
return v___x_4358_;
}
}
}
v___jp_4361_:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v_a_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4385_; 
v___x_4370_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4317_);
v___x_4371_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(v___x_4370_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_);
v_a_4372_ = lean_ctor_get(v___x_4371_, 0);
v_isSharedCheck_4385_ = !lean_is_exclusive(v___x_4371_);
if (v_isSharedCheck_4385_ == 0)
{
v___x_4374_ = v___x_4371_;
v_isShared_4375_ = v_isSharedCheck_4385_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_a_4372_);
lean_dec(v___x_4371_);
v___x_4374_ = lean_box(0);
v_isShared_4375_ = v_isSharedCheck_4385_;
goto v_resetjp_4373_;
}
v_resetjp_4373_:
{
lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; 
lean_inc_ref_n(v___y_4365_, 2);
v___x_4376_ = l_Lean_FileMap_toPosition(v___y_4365_, v___y_4368_);
lean_dec(v___y_4368_);
v___x_4377_ = l_Lean_FileMap_toPosition(v___y_4365_, v___y_4369_);
lean_dec(v___y_4369_);
v___x_4378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4378_, 0, v___x_4377_);
v___x_4379_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___closed__0));
if (v___y_4367_ == 0)
{
lean_del_object(v___x_4374_);
lean_dec_ref(v___y_4362_);
v___y_4326_ = v___y_4364_;
v___y_4327_ = v___y_4363_;
v___y_4328_ = v_a_4372_;
v___y_4329_ = v___x_4379_;
v___y_4330_ = v___y_4366_;
v___y_4331_ = v___x_4376_;
v___y_4332_ = v___x_4378_;
v___y_4333_ = v___y_4322_;
v___y_4334_ = v___y_4323_;
goto v___jp_4325_;
}
else
{
uint8_t v___x_4380_; 
lean_inc(v_a_4372_);
v___x_4380_ = l_Lean_MessageData_hasTag(v___y_4362_, v_a_4372_);
if (v___x_4380_ == 0)
{
lean_object* v___x_4381_; lean_object* v___x_4383_; 
lean_dec_ref(v___x_4378_);
lean_dec_ref(v___x_4376_);
lean_dec(v_a_4372_);
v___x_4381_ = lean_box(0);
if (v_isShared_4375_ == 0)
{
lean_ctor_set(v___x_4374_, 0, v___x_4381_);
v___x_4383_ = v___x_4374_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v___x_4381_);
v___x_4383_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
return v___x_4383_;
}
}
else
{
lean_del_object(v___x_4374_);
v___y_4326_ = v___y_4364_;
v___y_4327_ = v___y_4363_;
v___y_4328_ = v_a_4372_;
v___y_4329_ = v___x_4379_;
v___y_4330_ = v___y_4366_;
v___y_4331_ = v___x_4376_;
v___y_4332_ = v___x_4378_;
v___y_4333_ = v___y_4322_;
v___y_4334_ = v___y_4323_;
goto v___jp_4325_;
}
}
}
}
v___jp_4386_:
{
lean_object* v___x_4395_; 
v___x_4395_ = l_Lean_Syntax_getTailPos_x3f(v___y_4393_, v___y_4389_);
lean_dec(v___y_4393_);
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_inc(v___y_4394_);
v___y_4362_ = v___y_4387_;
v___y_4363_ = v___y_4389_;
v___y_4364_ = v___y_4388_;
v___y_4365_ = v___y_4390_;
v___y_4366_ = v___y_4391_;
v___y_4367_ = v___y_4392_;
v___y_4368_ = v___y_4394_;
v___y_4369_ = v___y_4394_;
goto v___jp_4361_;
}
else
{
lean_object* v_val_4396_; 
v_val_4396_ = lean_ctor_get(v___x_4395_, 0);
lean_inc(v_val_4396_);
lean_dec_ref(v___x_4395_);
v___y_4362_ = v___y_4387_;
v___y_4363_ = v___y_4389_;
v___y_4364_ = v___y_4388_;
v___y_4365_ = v___y_4390_;
v___y_4366_ = v___y_4391_;
v___y_4367_ = v___y_4392_;
v___y_4368_ = v___y_4394_;
v___y_4369_ = v_val_4396_;
goto v___jp_4361_;
}
}
v___jp_4397_:
{
lean_object* v_ref_4405_; lean_object* v___x_4406_; 
v_ref_4405_ = l_Lean_replaceRef(v_ref_4316_, v___y_4400_);
v___x_4406_ = l_Lean_Syntax_getPos_x3f(v_ref_4405_, v___y_4399_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_object* v___x_4407_; 
v___x_4407_ = lean_unsigned_to_nat(0u);
v___y_4387_ = v___y_4398_;
v___y_4388_ = v___y_4404_;
v___y_4389_ = v___y_4399_;
v___y_4390_ = v___y_4401_;
v___y_4391_ = v___y_4402_;
v___y_4392_ = v___y_4403_;
v___y_4393_ = v_ref_4405_;
v___y_4394_ = v___x_4407_;
goto v___jp_4386_;
}
else
{
lean_object* v_val_4408_; 
v_val_4408_ = lean_ctor_get(v___x_4406_, 0);
lean_inc(v_val_4408_);
lean_dec_ref(v___x_4406_);
v___y_4387_ = v___y_4398_;
v___y_4388_ = v___y_4404_;
v___y_4389_ = v___y_4399_;
v___y_4390_ = v___y_4401_;
v___y_4391_ = v___y_4402_;
v___y_4392_ = v___y_4403_;
v___y_4393_ = v_ref_4405_;
v___y_4394_ = v_val_4408_;
goto v___jp_4386_;
}
}
v___jp_4410_:
{
if (v___y_4417_ == 0)
{
v___y_4398_ = v___y_4415_;
v___y_4399_ = v___y_4416_;
v___y_4400_ = v___y_4411_;
v___y_4401_ = v___y_4412_;
v___y_4402_ = v___y_4413_;
v___y_4403_ = v___y_4414_;
v___y_4404_ = v_severity_4318_;
goto v___jp_4397_;
}
else
{
v___y_4398_ = v___y_4415_;
v___y_4399_ = v___y_4416_;
v___y_4400_ = v___y_4411_;
v___y_4401_ = v___y_4412_;
v___y_4402_ = v___y_4413_;
v___y_4403_ = v___y_4414_;
v___y_4404_ = v___x_4409_;
goto v___jp_4397_;
}
}
v___jp_4418_:
{
if (v___y_4419_ == 0)
{
lean_object* v_fileName_4420_; lean_object* v_fileMap_4421_; lean_object* v_options_4422_; lean_object* v_ref_4423_; uint8_t v_suppressElabErrors_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___f_4427_; uint8_t v___x_4428_; uint8_t v___x_4429_; 
v_fileName_4420_ = lean_ctor_get(v___y_4322_, 0);
v_fileMap_4421_ = lean_ctor_get(v___y_4322_, 1);
v_options_4422_ = lean_ctor_get(v___y_4322_, 2);
v_ref_4423_ = lean_ctor_get(v___y_4322_, 5);
v_suppressElabErrors_4424_ = lean_ctor_get_uint8(v___y_4322_, sizeof(void*)*14 + 1);
v___x_4425_ = lean_box(v___y_4419_);
v___x_4426_ = lean_box(v_suppressElabErrors_4424_);
v___f_4427_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4427_, 0, v___x_4425_);
lean_closure_set(v___f_4427_, 1, v___x_4426_);
v___x_4428_ = 1;
v___x_4429_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4318_, v___x_4428_);
if (v___x_4429_ == 0)
{
v___y_4411_ = v_ref_4423_;
v___y_4412_ = v_fileMap_4421_;
v___y_4413_ = v_fileName_4420_;
v___y_4414_ = v_suppressElabErrors_4424_;
v___y_4415_ = v___f_4427_;
v___y_4416_ = v___y_4419_;
v___y_4417_ = v___x_4429_;
goto v___jp_4410_;
}
else
{
lean_object* v___x_4430_; uint8_t v___x_4431_; 
v___x_4430_ = l_Lean_warningAsError;
v___x_4431_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(v_options_4422_, v___x_4430_);
v___y_4411_ = v_ref_4423_;
v___y_4412_ = v_fileMap_4421_;
v___y_4413_ = v_fileName_4420_;
v___y_4414_ = v_suppressElabErrors_4424_;
v___y_4415_ = v___f_4427_;
v___y_4416_ = v___y_4419_;
v___y_4417_ = v___x_4431_;
goto v___jp_4410_;
}
}
else
{
lean_object* v___x_4432_; lean_object* v___x_4433_; 
lean_dec_ref(v_msgData_4317_);
v___x_4432_ = lean_box(0);
v___x_4433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4433_, 0, v___x_4432_);
return v___x_4433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_4436_, lean_object* v_msgData_4437_, lean_object* v_severity_4438_, lean_object* v_isSilent_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_){
_start:
{
uint8_t v_severity_boxed_4445_; uint8_t v_isSilent_boxed_4446_; lean_object* v_res_4447_; 
v_severity_boxed_4445_ = lean_unbox(v_severity_4438_);
v_isSilent_boxed_4446_ = lean_unbox(v_isSilent_4439_);
v_res_4447_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(v_ref_4436_, v_msgData_4437_, v_severity_boxed_4445_, v_isSilent_boxed_4446_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_);
lean_dec(v___y_4443_);
lean_dec_ref(v___y_4442_);
lean_dec(v___y_4441_);
lean_dec_ref(v___y_4440_);
lean_dec(v_ref_4436_);
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(lean_object* v_msgData_4448_, uint8_t v_severity_4449_, uint8_t v_isSilent_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_){
_start:
{
lean_object* v_ref_4456_; lean_object* v___x_4457_; 
v_ref_4456_ = lean_ctor_get(v___y_4453_, 5);
v___x_4457_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(v_ref_4456_, v_msgData_4448_, v_severity_4449_, v_isSilent_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
return v___x_4457_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0___boxed(lean_object* v_msgData_4458_, lean_object* v_severity_4459_, lean_object* v_isSilent_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_){
_start:
{
uint8_t v_severity_boxed_4466_; uint8_t v_isSilent_boxed_4467_; lean_object* v_res_4468_; 
v_severity_boxed_4466_ = lean_unbox(v_severity_4459_);
v_isSilent_boxed_4467_ = lean_unbox(v_isSilent_4460_);
v_res_4468_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(v_msgData_4458_, v_severity_boxed_4466_, v_isSilent_boxed_4467_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_);
lean_dec(v___y_4464_);
lean_dec_ref(v___y_4463_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
return v_res_4468_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(lean_object* v_msgData_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_){
_start:
{
uint8_t v___x_4475_; uint8_t v___x_4476_; lean_object* v___x_4477_; 
v___x_4475_ = 0;
v___x_4476_ = 0;
v___x_4477_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(v_msgData_4469_, v___x_4475_, v___x_4476_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_);
return v___x_4477_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0___boxed(lean_object* v_msgData_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_){
_start:
{
lean_object* v_res_4484_; 
v_res_4484_ = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(v_msgData_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
return v_res_4484_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1(void){
_start:
{
lean_object* v___x_4486_; lean_object* v___x_4487_; 
v___x_4486_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0));
v___x_4487_ = l_Lean_stringToMessageData(v___x_4486_);
return v___x_4487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2(uint8_t v___x_4488_, lean_object* v___altIdx_4489_, lean_object* v_expAltType_4490_, lean_object* v___altFVars_4491_, lean_object* v_alt_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_){
_start:
{
lean_object* v___x_4498_; 
lean_inc(v___y_4496_);
lean_inc_ref(v___y_4495_);
lean_inc(v___y_4494_);
lean_inc_ref(v___y_4493_);
lean_inc_ref(v_alt_4492_);
v___x_4498_ = lean_infer_type(v_alt_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
if (lean_obj_tag(v___x_4498_) == 0)
{
lean_object* v_a_4499_; lean_object* v___x_4500_; 
v_a_4499_ = lean_ctor_get(v___x_4498_, 0);
lean_inc(v_a_4499_);
lean_dec_ref(v___x_4498_);
v___x_4500_ = l_Lean_Meta_mkEq(v_expAltType_4490_, v_a_4499_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
if (lean_obj_tag(v___x_4500_) == 0)
{
lean_object* v_a_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; 
v_a_4501_ = lean_ctor_get(v___x_4500_, 0);
lean_inc(v_a_4501_);
lean_dec_ref(v___x_4500_);
v___x_4502_ = lean_box(0);
v___x_4503_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4501_, v___x_4502_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
if (lean_obj_tag(v___x_4503_) == 0)
{
lean_object* v_a_4504_; lean_object* v___y_4506_; lean_object* v___x_4516_; lean_object* v___x_4517_; 
v_a_4504_ = lean_ctor_get(v___x_4503_, 0);
lean_inc(v_a_4504_);
lean_dec_ref(v___x_4503_);
v___x_4516_ = l_Lean_Expr_mvarId_x21(v_a_4504_);
v___x_4517_ = l_Lean_Meta_Split_simpMatchTarget(v___x_4516_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
if (lean_obj_tag(v___x_4517_) == 0)
{
lean_object* v_a_4518_; lean_object* v___x_4519_; 
v_a_4518_ = lean_ctor_get(v___x_4517_, 0);
lean_inc_n(v_a_4518_, 2);
lean_dec_ref(v___x_4517_);
v___x_4519_ = l_Lean_MVarId_refl(v_a_4518_, v___x_4488_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
if (lean_obj_tag(v___x_4519_) == 0)
{
lean_dec(v_a_4518_);
v___y_4506_ = v___x_4519_;
goto v___jp_4505_;
}
else
{
lean_object* v_a_4520_; uint8_t v___y_4522_; uint8_t v___x_4535_; 
v_a_4520_ = lean_ctor_get(v___x_4519_, 0);
lean_inc(v_a_4520_);
v___x_4535_ = l_Lean_Exception_isInterrupt(v_a_4520_);
if (v___x_4535_ == 0)
{
uint8_t v___x_4536_; 
v___x_4536_ = l_Lean_Exception_isRuntime(v_a_4520_);
v___y_4522_ = v___x_4536_;
goto v___jp_4521_;
}
else
{
lean_dec(v_a_4520_);
v___y_4522_ = v___x_4535_;
goto v___jp_4521_;
}
v___jp_4521_:
{
if (v___y_4522_ == 0)
{
lean_object* v___x_4524_; uint8_t v_isShared_4525_; uint8_t v_isSharedCheck_4533_; 
v_isSharedCheck_4533_ = !lean_is_exclusive(v___x_4519_);
if (v_isSharedCheck_4533_ == 0)
{
lean_object* v_unused_4534_; 
v_unused_4534_ = lean_ctor_get(v___x_4519_, 0);
lean_dec(v_unused_4534_);
v___x_4524_ = v___x_4519_;
v_isShared_4525_ = v_isSharedCheck_4533_;
goto v_resetjp_4523_;
}
else
{
lean_dec(v___x_4519_);
v___x_4524_ = lean_box(0);
v_isShared_4525_ = v_isSharedCheck_4533_;
goto v_resetjp_4523_;
}
v_resetjp_4523_:
{
lean_object* v___x_4526_; lean_object* v___x_4528_; 
v___x_4526_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1, &l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1);
lean_inc(v_a_4518_);
if (v_isShared_4525_ == 0)
{
lean_ctor_set(v___x_4524_, 0, v_a_4518_);
v___x_4528_ = v___x_4524_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_a_4518_);
v___x_4528_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
lean_object* v___x_4529_; lean_object* v___x_4530_; 
v___x_4529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4529_, 0, v___x_4526_);
lean_ctor_set(v___x_4529_, 1, v___x_4528_);
v___x_4530_ = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(v___x_4529_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
if (lean_obj_tag(v___x_4530_) == 0)
{
lean_object* v___x_4531_; 
lean_dec_ref(v___x_4530_);
v___x_4531_ = l_Lean_MVarId_admit(v_a_4518_, v___x_4488_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
v___y_4506_ = v___x_4531_;
goto v___jp_4505_;
}
else
{
lean_dec(v_a_4518_);
v___y_4506_ = v___x_4530_;
goto v___jp_4505_;
}
}
}
}
else
{
lean_dec(v_a_4518_);
v___y_4506_ = v___x_4519_;
goto v___jp_4505_;
}
}
}
}
else
{
lean_object* v_a_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4544_; 
lean_dec(v_a_4504_);
lean_dec_ref(v_alt_4492_);
v_a_4537_ = lean_ctor_get(v___x_4517_, 0);
v_isSharedCheck_4544_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4539_ = v___x_4517_;
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_a_4537_);
lean_dec(v___x_4517_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v___x_4542_; 
if (v_isShared_4540_ == 0)
{
v___x_4542_ = v___x_4539_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v_a_4537_);
v___x_4542_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
return v___x_4542_;
}
}
}
v___jp_4505_:
{
if (lean_obj_tag(v___y_4506_) == 0)
{
lean_object* v___x_4507_; 
lean_dec_ref(v___y_4506_);
v___x_4507_ = l_Lean_Meta_mkEqMPR(v_a_4504_, v_alt_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
return v___x_4507_;
}
else
{
lean_object* v_a_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4515_; 
lean_dec(v_a_4504_);
lean_dec_ref(v_alt_4492_);
v_a_4508_ = lean_ctor_get(v___y_4506_, 0);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___y_4506_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4510_ = v___y_4506_;
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_a_4508_);
lean_dec(v___y_4506_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v___x_4513_; 
if (v_isShared_4511_ == 0)
{
v___x_4513_ = v___x_4510_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_a_4508_);
v___x_4513_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
return v___x_4513_;
}
}
}
}
}
else
{
lean_dec_ref(v_alt_4492_);
return v___x_4503_;
}
}
else
{
lean_dec_ref(v_alt_4492_);
return v___x_4500_;
}
}
else
{
lean_dec_ref(v_alt_4492_);
lean_dec_ref(v_expAltType_4490_);
return v___x_4498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___boxed(lean_object* v___x_4545_, lean_object* v___altIdx_4546_, lean_object* v_expAltType_4547_, lean_object* v___altFVars_4548_, lean_object* v_alt_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_){
_start:
{
uint8_t v___x_32316__boxed_4555_; lean_object* v_res_4556_; 
v___x_32316__boxed_4555_ = lean_unbox(v___x_4545_);
v_res_4556_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__2(v___x_32316__boxed_4555_, v___altIdx_4546_, v_expAltType_4547_, v___altFVars_4548_, v_alt_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_);
lean_dec(v___y_4553_);
lean_dec_ref(v___y_4552_);
lean_dec(v___y_4551_);
lean_dec_ref(v___y_4550_);
lean_dec_ref(v___altFVars_4548_);
lean_dec(v___altIdx_4546_);
return v_res_4556_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(lean_object* v___x_4557_, lean_object* v_e_4558_){
_start:
{
uint8_t v___x_4559_; lean_object* v_d_4561_; lean_object* v_b_4562_; 
v___x_4559_ = l_Lean_Expr_hasFVar(v_e_4558_);
if (v___x_4559_ == 0)
{
return v___x_4559_;
}
else
{
switch(lean_obj_tag(v_e_4558_))
{
case 7:
{
lean_object* v_binderType_4565_; lean_object* v_body_4566_; 
v_binderType_4565_ = lean_ctor_get(v_e_4558_, 1);
v_body_4566_ = lean_ctor_get(v_e_4558_, 2);
v_d_4561_ = v_binderType_4565_;
v_b_4562_ = v_body_4566_;
goto v___jp_4560_;
}
case 6:
{
lean_object* v_binderType_4567_; lean_object* v_body_4568_; 
v_binderType_4567_ = lean_ctor_get(v_e_4558_, 1);
v_body_4568_ = lean_ctor_get(v_e_4558_, 2);
v_d_4561_ = v_binderType_4567_;
v_b_4562_ = v_body_4568_;
goto v___jp_4560_;
}
case 10:
{
lean_object* v_expr_4569_; 
v_expr_4569_ = lean_ctor_get(v_e_4558_, 1);
v_e_4558_ = v_expr_4569_;
goto _start;
}
case 8:
{
lean_object* v_type_4571_; lean_object* v_value_4572_; lean_object* v_body_4573_; uint8_t v___x_4574_; 
v_type_4571_ = lean_ctor_get(v_e_4558_, 1);
v_value_4572_ = lean_ctor_get(v_e_4558_, 2);
v_body_4573_ = lean_ctor_get(v_e_4558_, 3);
v___x_4574_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4557_, v_type_4571_);
if (v___x_4574_ == 0)
{
uint8_t v___x_4575_; 
v___x_4575_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4557_, v_value_4572_);
if (v___x_4575_ == 0)
{
v_e_4558_ = v_body_4573_;
goto _start;
}
else
{
return v___x_4559_;
}
}
else
{
return v___x_4559_;
}
}
case 5:
{
lean_object* v_fn_4577_; lean_object* v_arg_4578_; uint8_t v___x_4579_; 
v_fn_4577_ = lean_ctor_get(v_e_4558_, 0);
v_arg_4578_ = lean_ctor_get(v_e_4558_, 1);
v___x_4579_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4557_, v_fn_4577_);
if (v___x_4579_ == 0)
{
v_e_4558_ = v_arg_4578_;
goto _start;
}
else
{
return v___x_4559_;
}
}
case 11:
{
lean_object* v_struct_4581_; 
v_struct_4581_ = lean_ctor_get(v_e_4558_, 2);
v_e_4558_ = v_struct_4581_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4583_; lean_object* v___x_4584_; uint8_t v___x_4585_; 
v_fvarId_4583_ = lean_ctor_get(v_e_4558_, 0);
v___x_4584_ = l_Lean_Expr_fvarId_x21(v___x_4557_);
v___x_4585_ = l_Lean_instBEqFVarId_beq(v_fvarId_4583_, v___x_4584_);
lean_dec(v___x_4584_);
return v___x_4585_;
}
default: 
{
uint8_t v___x_4586_; 
v___x_4586_ = 0;
return v___x_4586_;
}
}
}
v___jp_4560_:
{
uint8_t v___x_4563_; 
v___x_4563_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4557_, v_d_4561_);
if (v___x_4563_ == 0)
{
v_e_4558_ = v_b_4562_;
goto _start;
}
else
{
return v___x_4559_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1___boxed(lean_object* v___x_4587_, lean_object* v_e_4588_){
_start:
{
uint8_t v_res_4589_; lean_object* v_r_4590_; 
v_res_4589_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4587_, v_e_4588_);
lean_dec_ref(v_e_4588_);
lean_dec_ref(v___x_4587_);
v_r_4590_ = lean_box(v_res_4589_);
return v_r_4590_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4592_; lean_object* v___x_4593_; 
v___x_4592_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__0));
v___x_4593_ = l_Lean_stringToMessageData(v___x_4592_);
return v___x_4593_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4595_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__2));
v___x_4596_ = l_Lean_stringToMessageData(v___x_4595_);
return v___x_4596_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_4598_; lean_object* v___x_4599_; 
v___x_4598_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__4));
v___x_4599_ = l_Lean_stringToMessageData(v___x_4598_);
return v___x_4599_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(lean_object* v_a_4600_, lean_object* v_termAlt_4601_, lean_object* v_a_4602_, lean_object* v_b_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_){
_start:
{
lean_object* v_array_4609_; lean_object* v_start_4610_; lean_object* v_stop_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4639_; 
v_array_4609_ = lean_ctor_get(v_a_4602_, 0);
v_start_4610_ = lean_ctor_get(v_a_4602_, 1);
v_stop_4611_ = lean_ctor_get(v_a_4602_, 2);
v_isSharedCheck_4639_ = !lean_is_exclusive(v_a_4602_);
if (v_isSharedCheck_4639_ == 0)
{
v___x_4613_ = v_a_4602_;
v_isShared_4614_ = v_isSharedCheck_4639_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_stop_4611_);
lean_inc(v_start_4610_);
lean_inc(v_array_4609_);
lean_dec(v_a_4602_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4639_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
uint8_t v___x_4615_; 
v___x_4615_ = lean_nat_dec_lt(v_start_4610_, v_stop_4611_);
if (v___x_4615_ == 0)
{
lean_object* v___x_4616_; 
lean_del_object(v___x_4613_);
lean_dec(v_stop_4611_);
lean_dec(v_start_4610_);
lean_dec_ref(v_array_4609_);
lean_dec_ref(v_termAlt_4601_);
lean_dec_ref(v_a_4600_);
v___x_4616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4616_, 0, v_b_4603_);
return v___x_4616_;
}
else
{
lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4621_; 
v___x_4617_ = lean_box(0);
v___x_4618_ = lean_unsigned_to_nat(1u);
v___x_4619_ = lean_nat_add(v_start_4610_, v___x_4618_);
lean_inc_ref(v_array_4609_);
if (v_isShared_4614_ == 0)
{
lean_ctor_set(v___x_4613_, 1, v___x_4619_);
v___x_4621_ = v___x_4613_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v_array_4609_);
lean_ctor_set(v_reuseFailAlloc_4638_, 1, v___x_4619_);
lean_ctor_set(v_reuseFailAlloc_4638_, 2, v_stop_4611_);
v___x_4621_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
lean_object* v___x_4622_; uint8_t v___x_4623_; 
v___x_4622_ = lean_array_fget(v_array_4609_, v_start_4610_);
lean_dec(v_start_4610_);
lean_dec_ref(v_array_4609_);
v___x_4623_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4622_, v_a_4600_);
if (v___x_4623_ == 0)
{
lean_dec(v___x_4622_);
v_a_4602_ = v___x_4621_;
v_b_4603_ = v___x_4617_;
goto _start;
}
else
{
lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; 
v___x_4625_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1);
lean_inc_ref(v_a_4600_);
v___x_4626_ = l_Lean_MessageData_ofExpr(v_a_4600_);
v___x_4627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4627_, 0, v___x_4625_);
lean_ctor_set(v___x_4627_, 1, v___x_4626_);
v___x_4628_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3);
v___x_4629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4629_, 0, v___x_4627_);
lean_ctor_set(v___x_4629_, 1, v___x_4628_);
lean_inc_ref(v_termAlt_4601_);
v___x_4630_ = l_Lean_MessageData_ofExpr(v_termAlt_4601_);
v___x_4631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4631_, 0, v___x_4629_);
lean_ctor_set(v___x_4631_, 1, v___x_4630_);
v___x_4632_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5);
v___x_4633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4633_, 0, v___x_4631_);
lean_ctor_set(v___x_4633_, 1, v___x_4632_);
v___x_4634_ = l_Lean_MessageData_ofExpr(v___x_4622_);
v___x_4635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4635_, 0, v___x_4633_);
lean_ctor_set(v___x_4635_, 1, v___x_4634_);
v___x_4636_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_4635_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_);
if (lean_obj_tag(v___x_4636_) == 0)
{
lean_dec_ref(v___x_4636_);
v_a_4602_ = v___x_4621_;
v_b_4603_ = v___x_4617_;
goto _start;
}
else
{
lean_dec_ref(v___x_4621_);
lean_dec_ref(v_termAlt_4601_);
lean_dec_ref(v_a_4600_);
return v___x_4636_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___boxed(lean_object* v_a_4640_, lean_object* v_termAlt_4641_, lean_object* v_a_4642_, lean_object* v_b_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_){
_start:
{
lean_object* v_res_4649_; 
v_res_4649_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_4640_, v_termAlt_4641_, v_a_4642_, v_b_4643_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_);
lean_dec(v___y_4647_);
lean_dec_ref(v___y_4646_);
lean_dec(v___y_4645_);
lean_dec_ref(v___y_4644_);
return v_res_4649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(lean_object* v_nExtra_4650_, lean_object* v_v_4651_, uint8_t v___x_4652_, uint8_t v___x_4653_, uint8_t v___x_4654_, lean_object* v_xs_4655_, lean_object* v_termAltBody_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_){
_start:
{
lean_object* v___x_4662_; 
lean_inc(v___y_4660_);
lean_inc_ref(v___y_4659_);
lean_inc(v___y_4658_);
lean_inc_ref(v___y_4657_);
v___x_4662_ = lean_infer_type(v_termAltBody_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
if (lean_obj_tag(v___x_4662_) == 0)
{
lean_object* v_a_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; 
v_a_4663_ = lean_ctor_get(v___x_4662_, 0);
lean_inc_n(v_a_4663_, 2);
lean_dec_ref(v___x_4662_);
v___x_4664_ = lean_array_get_size(v_xs_4655_);
v___x_4665_ = lean_nat_sub(v___x_4664_, v_nExtra_4650_);
v___x_4666_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_4665_);
lean_inc_ref(v_xs_4655_);
v___x_4667_ = l_Array_toSubarray___redArg(v_xs_4655_, v___x_4666_, v___x_4665_);
v___x_4668_ = l_Array_toSubarray___redArg(v_xs_4655_, v___x_4665_, v___x_4664_);
v___x_4669_ = lean_box(0);
v___x_4670_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_4663_, v_v_4651_, v___x_4668_, v___x_4669_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
if (lean_obj_tag(v___x_4670_) == 0)
{
lean_object* v___x_4671_; lean_object* v___x_4672_; 
lean_dec_ref(v___x_4670_);
v___x_4671_ = l_Subarray_copy___redArg(v___x_4667_);
v___x_4672_ = l_Lean_Meta_mkLambdaFVars(v___x_4671_, v_a_4663_, v___x_4652_, v___x_4653_, v___x_4652_, v___x_4653_, v___x_4654_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
lean_dec_ref(v___x_4671_);
return v___x_4672_;
}
else
{
lean_object* v_a_4673_; lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4680_; 
lean_dec_ref(v___x_4667_);
lean_dec(v_a_4663_);
v_a_4673_ = lean_ctor_get(v___x_4670_, 0);
v_isSharedCheck_4680_ = !lean_is_exclusive(v___x_4670_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4675_ = v___x_4670_;
v_isShared_4676_ = v_isSharedCheck_4680_;
goto v_resetjp_4674_;
}
else
{
lean_inc(v_a_4673_);
lean_dec(v___x_4670_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4680_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4678_; 
if (v_isShared_4676_ == 0)
{
v___x_4678_ = v___x_4675_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v_a_4673_);
v___x_4678_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
return v___x_4678_;
}
}
}
}
else
{
lean_dec_ref(v_xs_4655_);
lean_dec(v_v_4651_);
return v___x_4662_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed(lean_object* v_nExtra_4681_, lean_object* v_v_4682_, lean_object* v___x_4683_, lean_object* v___x_4684_, lean_object* v___x_4685_, lean_object* v_xs_4686_, lean_object* v_termAltBody_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_){
_start:
{
uint8_t v___x_32605__boxed_4693_; uint8_t v___x_32606__boxed_4694_; uint8_t v___x_32607__boxed_4695_; lean_object* v_res_4696_; 
v___x_32605__boxed_4693_ = lean_unbox(v___x_4683_);
v___x_32606__boxed_4694_ = lean_unbox(v___x_4684_);
v___x_32607__boxed_4695_ = lean_unbox(v___x_4685_);
v_res_4696_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(v_nExtra_4681_, v_v_4682_, v___x_32605__boxed_4693_, v___x_32606__boxed_4694_, v___x_32607__boxed_4695_, v_xs_4686_, v_termAltBody_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_);
lean_dec(v___y_4691_);
lean_dec_ref(v___y_4690_);
lean_dec(v___y_4689_);
lean_dec_ref(v___y_4688_);
lean_dec(v_nExtra_4681_);
return v_res_4696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(lean_object* v_nExtra_4697_, size_t v_sz_4698_, size_t v_i_4699_, lean_object* v_bs_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_){
_start:
{
uint8_t v___x_4706_; 
v___x_4706_ = lean_usize_dec_lt(v_i_4699_, v_sz_4698_);
if (v___x_4706_ == 0)
{
lean_object* v___x_4707_; 
lean_dec(v_nExtra_4697_);
v___x_4707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4707_, 0, v_bs_4700_);
return v___x_4707_;
}
else
{
uint8_t v___x_4708_; uint8_t v___x_4709_; lean_object* v_v_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___f_4714_; lean_object* v___x_4715_; 
v___x_4708_ = 0;
v___x_4709_ = 1;
v_v_4710_ = lean_array_uget_borrowed(v_bs_4700_, v_i_4699_);
v___x_4711_ = lean_box(v___x_4708_);
v___x_4712_ = lean_box(v___x_4706_);
v___x_4713_ = lean_box(v___x_4709_);
lean_inc_n(v_v_4710_, 2);
lean_inc(v_nExtra_4697_);
v___f_4714_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4714_, 0, v_nExtra_4697_);
lean_closure_set(v___f_4714_, 1, v_v_4710_);
lean_closure_set(v___f_4714_, 2, v___x_4711_);
lean_closure_set(v___f_4714_, 3, v___x_4712_);
lean_closure_set(v___f_4714_, 4, v___x_4713_);
v___x_4715_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_v_4710_, v___f_4714_, v___x_4708_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_);
if (lean_obj_tag(v___x_4715_) == 0)
{
lean_object* v_a_4716_; lean_object* v___x_4717_; lean_object* v_bs_x27_4718_; size_t v___x_4719_; size_t v___x_4720_; lean_object* v___x_4721_; 
v_a_4716_ = lean_ctor_get(v___x_4715_, 0);
lean_inc(v_a_4716_);
lean_dec_ref(v___x_4715_);
v___x_4717_ = lean_unsigned_to_nat(0u);
v_bs_x27_4718_ = lean_array_uset(v_bs_4700_, v_i_4699_, v___x_4717_);
v___x_4719_ = ((size_t)1ULL);
v___x_4720_ = lean_usize_add(v_i_4699_, v___x_4719_);
v___x_4721_ = lean_array_uset(v_bs_x27_4718_, v_i_4699_, v_a_4716_);
v_i_4699_ = v___x_4720_;
v_bs_4700_ = v___x_4721_;
goto _start;
}
else
{
lean_object* v_a_4723_; lean_object* v___x_4725_; uint8_t v_isShared_4726_; uint8_t v_isSharedCheck_4730_; 
lean_dec_ref(v_bs_4700_);
lean_dec(v_nExtra_4697_);
v_a_4723_ = lean_ctor_get(v___x_4715_, 0);
v_isSharedCheck_4730_ = !lean_is_exclusive(v___x_4715_);
if (v_isSharedCheck_4730_ == 0)
{
v___x_4725_ = v___x_4715_;
v_isShared_4726_ = v_isSharedCheck_4730_;
goto v_resetjp_4724_;
}
else
{
lean_inc(v_a_4723_);
lean_dec(v___x_4715_);
v___x_4725_ = lean_box(0);
v_isShared_4726_ = v_isSharedCheck_4730_;
goto v_resetjp_4724_;
}
v_resetjp_4724_:
{
lean_object* v___x_4728_; 
if (v_isShared_4726_ == 0)
{
v___x_4728_ = v___x_4725_;
goto v_reusejp_4727_;
}
else
{
lean_object* v_reuseFailAlloc_4729_; 
v_reuseFailAlloc_4729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4729_, 0, v_a_4723_);
v___x_4728_ = v_reuseFailAlloc_4729_;
goto v_reusejp_4727_;
}
v_reusejp_4727_:
{
return v___x_4728_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___boxed(lean_object* v_nExtra_4731_, lean_object* v_sz_4732_, lean_object* v_i_4733_, lean_object* v_bs_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_){
_start:
{
size_t v_sz_boxed_4740_; size_t v_i_boxed_4741_; lean_object* v_res_4742_; 
v_sz_boxed_4740_ = lean_unbox_usize(v_sz_4732_);
lean_dec(v_sz_4732_);
v_i_boxed_4741_ = lean_unbox_usize(v_i_4733_);
lean_dec(v_i_4733_);
v_res_4742_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(v_nExtra_4731_, v_sz_boxed_4740_, v_i_boxed_4741_, v_bs_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
return v_res_4742_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0(void){
_start:
{
lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4743_ = lean_box(0);
v___x_4744_ = l_Lean_Expr_sort___override(v___x_4743_);
return v___x_4744_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1(void){
_start:
{
lean_object* v___x_4745_; lean_object* v___x_4746_; 
v___x_4745_ = lean_box(0);
v___x_4746_ = l_Lean_Level_succ___override(v___x_4745_);
return v___x_4746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3(lean_object* v_nExtra_4747_, uint8_t v___x_4748_, uint8_t v___x_4749_, lean_object* v_alts_4750_, lean_object* v_toMatcherInfo_4751_, lean_object* v_matcherName_4752_, lean_object* v_params_4753_, lean_object* v_matcherLevels_4754_, lean_object* v_motiveArgs_4755_, lean_object* v_body_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_){
_start:
{
lean_object* v___x_4762_; 
lean_inc(v_nExtra_4747_);
v___x_4762_ = l_Lean_Meta_arrowDomainsN(v_nExtra_4747_, v_body_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_);
if (lean_obj_tag(v___x_4762_) == 0)
{
lean_object* v_a_4763_; lean_object* v___x_4764_; uint8_t v___x_4765_; lean_object* v___x_4766_; 
v_a_4763_ = lean_ctor_get(v___x_4762_, 0);
lean_inc(v_a_4763_);
lean_dec_ref(v___x_4762_);
v___x_4764_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0, &l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0);
v___x_4765_ = 1;
v___x_4766_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_4755_, v___x_4764_, v___x_4748_, v___x_4749_, v___x_4748_, v___x_4749_, v___x_4765_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_);
if (lean_obj_tag(v___x_4766_) == 0)
{
lean_object* v_a_4767_; size_t v_sz_4768_; size_t v___x_4769_; lean_object* v___x_4770_; 
v_a_4767_ = lean_ctor_get(v___x_4766_, 0);
lean_inc(v_a_4767_);
lean_dec_ref(v___x_4766_);
v_sz_4768_ = lean_array_size(v_alts_4750_);
v___x_4769_ = ((size_t)0ULL);
v___x_4770_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(v_nExtra_4747_, v_sz_4768_, v___x_4769_, v_alts_4750_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_);
if (lean_obj_tag(v___x_4770_) == 0)
{
lean_object* v_a_4771_; lean_object* v_matcherLevels_4773_; lean_object* v___y_4774_; lean_object* v___y_4775_; lean_object* v_uElimPos_x3f_4780_; 
v_a_4771_ = lean_ctor_get(v___x_4770_, 0);
lean_inc(v_a_4771_);
lean_dec_ref(v___x_4770_);
v_uElimPos_x3f_4780_ = lean_ctor_get(v_toMatcherInfo_4751_, 3);
if (lean_obj_tag(v_uElimPos_x3f_4780_) == 0)
{
v_matcherLevels_4773_ = v_matcherLevels_4754_;
v___y_4774_ = v___y_4759_;
v___y_4775_ = v___y_4760_;
goto v___jp_4772_;
}
else
{
lean_object* v_val_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; 
v_val_4781_ = lean_ctor_get(v_uElimPos_x3f_4780_, 0);
v___x_4782_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1, &l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1);
v___x_4783_ = lean_array_set(v_matcherLevels_4754_, v_val_4781_, v___x_4782_);
v_matcherLevels_4773_ = v___x_4783_;
v___y_4774_ = v___y_4759_;
v___y_4775_ = v___y_4760_;
goto v___jp_4772_;
}
v___jp_4772_:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; 
v___x_4776_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_4777_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4777_, 0, v_toMatcherInfo_4751_);
lean_ctor_set(v___x_4777_, 1, v_matcherName_4752_);
lean_ctor_set(v___x_4777_, 2, v_matcherLevels_4773_);
lean_ctor_set(v___x_4777_, 3, v_params_4753_);
lean_ctor_set(v___x_4777_, 4, v_a_4767_);
lean_ctor_set(v___x_4777_, 5, v_motiveArgs_4755_);
lean_ctor_set(v___x_4777_, 6, v_a_4771_);
lean_ctor_set(v___x_4777_, 7, v___x_4776_);
v___x_4778_ = l_Lean_Meta_MatcherApp_toExpr(v___x_4777_);
v___x_4779_ = l_Lean_mkArrowN(v_a_4763_, v___x_4778_, v___y_4774_, v___y_4775_);
lean_dec(v_a_4763_);
return v___x_4779_;
}
}
else
{
lean_object* v_a_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4791_; 
lean_dec(v_a_4767_);
lean_dec(v_a_4763_);
lean_dec_ref(v_motiveArgs_4755_);
lean_dec_ref(v_matcherLevels_4754_);
lean_dec_ref(v_params_4753_);
lean_dec(v_matcherName_4752_);
lean_dec_ref(v_toMatcherInfo_4751_);
v_a_4784_ = lean_ctor_get(v___x_4770_, 0);
v_isSharedCheck_4791_ = !lean_is_exclusive(v___x_4770_);
if (v_isSharedCheck_4791_ == 0)
{
v___x_4786_ = v___x_4770_;
v_isShared_4787_ = v_isSharedCheck_4791_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_a_4784_);
lean_dec(v___x_4770_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4791_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
lean_object* v___x_4789_; 
if (v_isShared_4787_ == 0)
{
v___x_4789_ = v___x_4786_;
goto v_reusejp_4788_;
}
else
{
lean_object* v_reuseFailAlloc_4790_; 
v_reuseFailAlloc_4790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4790_, 0, v_a_4784_);
v___x_4789_ = v_reuseFailAlloc_4790_;
goto v_reusejp_4788_;
}
v_reusejp_4788_:
{
return v___x_4789_;
}
}
}
}
else
{
lean_dec(v_a_4763_);
lean_dec_ref(v_motiveArgs_4755_);
lean_dec_ref(v_matcherLevels_4754_);
lean_dec_ref(v_params_4753_);
lean_dec(v_matcherName_4752_);
lean_dec_ref(v_toMatcherInfo_4751_);
lean_dec_ref(v_alts_4750_);
lean_dec(v_nExtra_4747_);
return v___x_4766_;
}
}
else
{
lean_object* v_a_4792_; lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4799_; 
lean_dec_ref(v_motiveArgs_4755_);
lean_dec_ref(v_matcherLevels_4754_);
lean_dec_ref(v_params_4753_);
lean_dec(v_matcherName_4752_);
lean_dec_ref(v_toMatcherInfo_4751_);
lean_dec_ref(v_alts_4750_);
lean_dec(v_nExtra_4747_);
v_a_4792_ = lean_ctor_get(v___x_4762_, 0);
v_isSharedCheck_4799_ = !lean_is_exclusive(v___x_4762_);
if (v_isSharedCheck_4799_ == 0)
{
v___x_4794_ = v___x_4762_;
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
else
{
lean_inc(v_a_4792_);
lean_dec(v___x_4762_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
lean_object* v___x_4797_; 
if (v_isShared_4795_ == 0)
{
v___x_4797_ = v___x_4794_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_a_4792_);
v___x_4797_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
return v___x_4797_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed(lean_object* v_nExtra_4800_, lean_object* v___x_4801_, lean_object* v___x_4802_, lean_object* v_alts_4803_, lean_object* v_toMatcherInfo_4804_, lean_object* v_matcherName_4805_, lean_object* v_params_4806_, lean_object* v_matcherLevels_4807_, lean_object* v_motiveArgs_4808_, lean_object* v_body_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_){
_start:
{
uint8_t v___x_32740__boxed_4815_; uint8_t v___x_32741__boxed_4816_; lean_object* v_res_4817_; 
v___x_32740__boxed_4815_ = lean_unbox(v___x_4801_);
v___x_32741__boxed_4816_ = lean_unbox(v___x_4802_);
v_res_4817_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__3(v_nExtra_4800_, v___x_32740__boxed_4815_, v___x_32741__boxed_4816_, v_alts_4803_, v_toMatcherInfo_4804_, v_matcherName_4805_, v_params_4806_, v_matcherLevels_4807_, v_motiveArgs_4808_, v_body_4809_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_);
lean_dec(v___y_4813_);
lean_dec_ref(v___y_4812_);
lean_dec(v___y_4811_);
lean_dec_ref(v___y_4810_);
return v_res_4817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(lean_object* v_k_4818_, lean_object* v_ys_4819_, lean_object* v_args_4820_, lean_object* v___mask_4821_, lean_object* v___bodyType_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_){
_start:
{
lean_object* v___x_4828_; 
lean_inc(v___y_4826_);
lean_inc_ref(v___y_4825_);
lean_inc(v___y_4824_);
lean_inc_ref(v___y_4823_);
v___x_4828_ = lean_apply_7(v_k_4818_, v_ys_4819_, v_args_4820_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_, lean_box(0));
return v___x_4828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed(lean_object* v_k_4829_, lean_object* v_ys_4830_, lean_object* v_args_4831_, lean_object* v___mask_4832_, lean_object* v___bodyType_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_){
_start:
{
lean_object* v_res_4839_; 
v_res_4839_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(v_k_4829_, v_ys_4830_, v_args_4831_, v___mask_4832_, v___bodyType_4833_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_);
lean_dec(v___y_4837_);
lean_dec_ref(v___y_4836_);
lean_dec(v___y_4835_);
lean_dec_ref(v___y_4834_);
lean_dec_ref(v___bodyType_4833_);
lean_dec_ref(v___mask_4832_);
return v_res_4839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(lean_object* v_origAltType_4840_, lean_object* v_altInfo_4841_, lean_object* v_k_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_){
_start:
{
lean_object* v___f_4848_; lean_object* v___x_4849_; 
v___f_4848_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_4848_, 0, v_k_4842_);
v___x_4849_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_origAltType_4840_, v_altInfo_4841_, v___f_4848_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_);
if (lean_obj_tag(v___x_4849_) == 0)
{
lean_object* v_a_4850_; lean_object* v___x_4852_; uint8_t v_isShared_4853_; uint8_t v_isSharedCheck_4857_; 
v_a_4850_ = lean_ctor_get(v___x_4849_, 0);
v_isSharedCheck_4857_ = !lean_is_exclusive(v___x_4849_);
if (v_isSharedCheck_4857_ == 0)
{
v___x_4852_ = v___x_4849_;
v_isShared_4853_ = v_isSharedCheck_4857_;
goto v_resetjp_4851_;
}
else
{
lean_inc(v_a_4850_);
lean_dec(v___x_4849_);
v___x_4852_ = lean_box(0);
v_isShared_4853_ = v_isSharedCheck_4857_;
goto v_resetjp_4851_;
}
v_resetjp_4851_:
{
lean_object* v___x_4855_; 
if (v_isShared_4853_ == 0)
{
v___x_4855_ = v___x_4852_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4856_; 
v_reuseFailAlloc_4856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4856_, 0, v_a_4850_);
v___x_4855_ = v_reuseFailAlloc_4856_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
return v___x_4855_;
}
}
}
else
{
lean_object* v_a_4858_; lean_object* v___x_4860_; uint8_t v_isShared_4861_; uint8_t v_isSharedCheck_4865_; 
v_a_4858_ = lean_ctor_get(v___x_4849_, 0);
v_isSharedCheck_4865_ = !lean_is_exclusive(v___x_4849_);
if (v_isSharedCheck_4865_ == 0)
{
v___x_4860_ = v___x_4849_;
v_isShared_4861_ = v_isSharedCheck_4865_;
goto v_resetjp_4859_;
}
else
{
lean_inc(v_a_4858_);
lean_dec(v___x_4849_);
v___x_4860_ = lean_box(0);
v_isShared_4861_ = v_isSharedCheck_4865_;
goto v_resetjp_4859_;
}
v_resetjp_4859_:
{
lean_object* v___x_4863_; 
if (v_isShared_4861_ == 0)
{
v___x_4863_ = v___x_4860_;
goto v_reusejp_4862_;
}
else
{
lean_object* v_reuseFailAlloc_4864_; 
v_reuseFailAlloc_4864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4864_, 0, v_a_4858_);
v___x_4863_ = v_reuseFailAlloc_4864_;
goto v_reusejp_4862_;
}
v_reusejp_4862_:
{
return v___x_4863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___boxed(lean_object* v_origAltType_4866_, lean_object* v_altInfo_4867_, lean_object* v_k_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_){
_start:
{
lean_object* v_res_4874_; 
v_res_4874_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v_origAltType_4866_, v_altInfo_4867_, v_k_4868_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_);
lean_dec(v___y_4872_);
lean_dec_ref(v___y_4871_);
lean_dec(v___y_4870_);
lean_dec_ref(v___y_4869_);
return v_res_4874_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(lean_object* v___x_4875_, lean_object* v___x_4876_, lean_object* v___f_4877_, lean_object* v_fst_4878_, lean_object* v___x_4879_, lean_object* v___x_4880_, lean_object* v___x_4881_, lean_object* v___x_4882_, lean_object* v___x_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_){
_start:
{
lean_object* v___x_4889_; 
v___x_4889_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v___x_4875_, v___x_4876_, v___f_4877_, v___y_4884_, v___y_4885_, v___y_4886_, v___y_4887_);
if (lean_obj_tag(v___x_4889_) == 0)
{
lean_object* v_a_4890_; lean_object* v___x_4892_; uint8_t v_isShared_4893_; uint8_t v_isSharedCheck_4904_; 
v_a_4890_ = lean_ctor_get(v___x_4889_, 0);
v_isSharedCheck_4904_ = !lean_is_exclusive(v___x_4889_);
if (v_isSharedCheck_4904_ == 0)
{
v___x_4892_ = v___x_4889_;
v_isShared_4893_ = v_isSharedCheck_4904_;
goto v_resetjp_4891_;
}
else
{
lean_inc(v_a_4890_);
lean_dec(v___x_4889_);
v___x_4892_ = lean_box(0);
v_isShared_4893_ = v_isSharedCheck_4904_;
goto v_resetjp_4891_;
}
v_resetjp_4891_:
{
lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4902_; 
v___x_4894_ = lean_array_push(v_fst_4878_, v_a_4890_);
v___x_4895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4895_, 0, v___x_4879_);
lean_ctor_set(v___x_4895_, 1, v___x_4880_);
v___x_4896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4896_, 0, v___x_4881_);
lean_ctor_set(v___x_4896_, 1, v___x_4895_);
v___x_4897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4897_, 0, v___x_4882_);
lean_ctor_set(v___x_4897_, 1, v___x_4896_);
v___x_4898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4898_, 0, v___x_4883_);
lean_ctor_set(v___x_4898_, 1, v___x_4897_);
v___x_4899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4899_, 0, v___x_4894_);
lean_ctor_set(v___x_4899_, 1, v___x_4898_);
v___x_4900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4900_, 0, v___x_4899_);
if (v_isShared_4893_ == 0)
{
lean_ctor_set(v___x_4892_, 0, v___x_4900_);
v___x_4902_ = v___x_4892_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v___x_4900_);
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
lean_dec_ref(v___x_4883_);
lean_dec_ref(v___x_4882_);
lean_dec_ref(v___x_4881_);
lean_dec_ref(v___x_4880_);
lean_dec_ref(v___x_4879_);
lean_dec(v_fst_4878_);
v_a_4905_ = lean_ctor_get(v___x_4889_, 0);
v_isSharedCheck_4912_ = !lean_is_exclusive(v___x_4889_);
if (v_isSharedCheck_4912_ == 0)
{
v___x_4907_ = v___x_4889_;
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_a_4905_);
lean_dec(v___x_4889_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed(lean_object* v___x_4913_, lean_object* v___x_4914_, lean_object* v___f_4915_, lean_object* v_fst_4916_, lean_object* v___x_4917_, lean_object* v___x_4918_, lean_object* v___x_4919_, lean_object* v___x_4920_, lean_object* v___x_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_){
_start:
{
lean_object* v_res_4927_; 
v_res_4927_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(v___x_4913_, v___x_4914_, v___f_4915_, v_fst_4916_, v___x_4917_, v___x_4918_, v___x_4919_, v___x_4920_, v___x_4921_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_);
lean_dec(v___y_4925_);
lean_dec_ref(v___y_4924_);
lean_dec(v___y_4923_);
lean_dec_ref(v___y_4922_);
return v_res_4927_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0(void){
_start:
{
lean_object* v___x_4928_; 
v___x_4928_ = l_instMonadEIO(lean_box(0));
return v___x_4928_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(lean_object* v_msg_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_){
_start:
{
lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v_toApplicative_4941_; lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_5002_; 
v___x_4939_ = lean_obj_once(&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0, &l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0_once, _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0);
v___x_4940_ = l_StateRefT_x27_instMonad___redArg(v___x_4939_);
v_toApplicative_4941_ = lean_ctor_get(v___x_4940_, 0);
v_isSharedCheck_5002_ = !lean_is_exclusive(v___x_4940_);
if (v_isSharedCheck_5002_ == 0)
{
lean_object* v_unused_5003_; 
v_unused_5003_ = lean_ctor_get(v___x_4940_, 1);
lean_dec(v_unused_5003_);
v___x_4943_ = v___x_4940_;
v_isShared_4944_ = v_isSharedCheck_5002_;
goto v_resetjp_4942_;
}
else
{
lean_inc(v_toApplicative_4941_);
lean_dec(v___x_4940_);
v___x_4943_ = lean_box(0);
v_isShared_4944_ = v_isSharedCheck_5002_;
goto v_resetjp_4942_;
}
v_resetjp_4942_:
{
lean_object* v_toFunctor_4945_; lean_object* v_toSeq_4946_; lean_object* v_toSeqLeft_4947_; lean_object* v_toSeqRight_4948_; lean_object* v___x_4950_; uint8_t v_isShared_4951_; uint8_t v_isSharedCheck_5000_; 
v_toFunctor_4945_ = lean_ctor_get(v_toApplicative_4941_, 0);
v_toSeq_4946_ = lean_ctor_get(v_toApplicative_4941_, 2);
v_toSeqLeft_4947_ = lean_ctor_get(v_toApplicative_4941_, 3);
v_toSeqRight_4948_ = lean_ctor_get(v_toApplicative_4941_, 4);
v_isSharedCheck_5000_ = !lean_is_exclusive(v_toApplicative_4941_);
if (v_isSharedCheck_5000_ == 0)
{
lean_object* v_unused_5001_; 
v_unused_5001_ = lean_ctor_get(v_toApplicative_4941_, 1);
lean_dec(v_unused_5001_);
v___x_4950_ = v_toApplicative_4941_;
v_isShared_4951_ = v_isSharedCheck_5000_;
goto v_resetjp_4949_;
}
else
{
lean_inc(v_toSeqRight_4948_);
lean_inc(v_toSeqLeft_4947_);
lean_inc(v_toSeq_4946_);
lean_inc(v_toFunctor_4945_);
lean_dec(v_toApplicative_4941_);
v___x_4950_ = lean_box(0);
v_isShared_4951_ = v_isSharedCheck_5000_;
goto v_resetjp_4949_;
}
v_resetjp_4949_:
{
lean_object* v___f_4952_; lean_object* v___f_4953_; lean_object* v___f_4954_; lean_object* v___f_4955_; lean_object* v___x_4956_; lean_object* v___f_4957_; lean_object* v___f_4958_; lean_object* v___f_4959_; lean_object* v___x_4961_; 
v___f_4952_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__1));
v___f_4953_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__2));
lean_inc_ref(v_toFunctor_4945_);
v___f_4954_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4954_, 0, v_toFunctor_4945_);
v___f_4955_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4955_, 0, v_toFunctor_4945_);
v___x_4956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4956_, 0, v___f_4954_);
lean_ctor_set(v___x_4956_, 1, v___f_4955_);
v___f_4957_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4957_, 0, v_toSeqRight_4948_);
v___f_4958_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4958_, 0, v_toSeqLeft_4947_);
v___f_4959_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4959_, 0, v_toSeq_4946_);
if (v_isShared_4951_ == 0)
{
lean_ctor_set(v___x_4950_, 4, v___f_4957_);
lean_ctor_set(v___x_4950_, 3, v___f_4958_);
lean_ctor_set(v___x_4950_, 2, v___f_4959_);
lean_ctor_set(v___x_4950_, 1, v___f_4952_);
lean_ctor_set(v___x_4950_, 0, v___x_4956_);
v___x_4961_ = v___x_4950_;
goto v_reusejp_4960_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v___x_4956_);
lean_ctor_set(v_reuseFailAlloc_4999_, 1, v___f_4952_);
lean_ctor_set(v_reuseFailAlloc_4999_, 2, v___f_4959_);
lean_ctor_set(v_reuseFailAlloc_4999_, 3, v___f_4958_);
lean_ctor_set(v_reuseFailAlloc_4999_, 4, v___f_4957_);
v___x_4961_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4960_;
}
v_reusejp_4960_:
{
lean_object* v___x_4963_; 
if (v_isShared_4944_ == 0)
{
lean_ctor_set(v___x_4943_, 1, v___f_4953_);
lean_ctor_set(v___x_4943_, 0, v___x_4961_);
v___x_4963_ = v___x_4943_;
goto v_reusejp_4962_;
}
else
{
lean_object* v_reuseFailAlloc_4998_; 
v_reuseFailAlloc_4998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4998_, 0, v___x_4961_);
lean_ctor_set(v_reuseFailAlloc_4998_, 1, v___f_4953_);
v___x_4963_ = v_reuseFailAlloc_4998_;
goto v_reusejp_4962_;
}
v_reusejp_4962_:
{
lean_object* v___x_4964_; lean_object* v_toApplicative_4965_; lean_object* v___x_4967_; uint8_t v_isShared_4968_; uint8_t v_isSharedCheck_4996_; 
v___x_4964_ = l_StateRefT_x27_instMonad___redArg(v___x_4963_);
v_toApplicative_4965_ = lean_ctor_get(v___x_4964_, 0);
v_isSharedCheck_4996_ = !lean_is_exclusive(v___x_4964_);
if (v_isSharedCheck_4996_ == 0)
{
lean_object* v_unused_4997_; 
v_unused_4997_ = lean_ctor_get(v___x_4964_, 1);
lean_dec(v_unused_4997_);
v___x_4967_ = v___x_4964_;
v_isShared_4968_ = v_isSharedCheck_4996_;
goto v_resetjp_4966_;
}
else
{
lean_inc(v_toApplicative_4965_);
lean_dec(v___x_4964_);
v___x_4967_ = lean_box(0);
v_isShared_4968_ = v_isSharedCheck_4996_;
goto v_resetjp_4966_;
}
v_resetjp_4966_:
{
lean_object* v_toFunctor_4969_; lean_object* v_toSeq_4970_; lean_object* v_toSeqLeft_4971_; lean_object* v_toSeqRight_4972_; lean_object* v___x_4974_; uint8_t v_isShared_4975_; uint8_t v_isSharedCheck_4994_; 
v_toFunctor_4969_ = lean_ctor_get(v_toApplicative_4965_, 0);
v_toSeq_4970_ = lean_ctor_get(v_toApplicative_4965_, 2);
v_toSeqLeft_4971_ = lean_ctor_get(v_toApplicative_4965_, 3);
v_toSeqRight_4972_ = lean_ctor_get(v_toApplicative_4965_, 4);
v_isSharedCheck_4994_ = !lean_is_exclusive(v_toApplicative_4965_);
if (v_isSharedCheck_4994_ == 0)
{
lean_object* v_unused_4995_; 
v_unused_4995_ = lean_ctor_get(v_toApplicative_4965_, 1);
lean_dec(v_unused_4995_);
v___x_4974_ = v_toApplicative_4965_;
v_isShared_4975_ = v_isSharedCheck_4994_;
goto v_resetjp_4973_;
}
else
{
lean_inc(v_toSeqRight_4972_);
lean_inc(v_toSeqLeft_4971_);
lean_inc(v_toSeq_4970_);
lean_inc(v_toFunctor_4969_);
lean_dec(v_toApplicative_4965_);
v___x_4974_ = lean_box(0);
v_isShared_4975_ = v_isSharedCheck_4994_;
goto v_resetjp_4973_;
}
v_resetjp_4973_:
{
lean_object* v___f_4976_; lean_object* v___f_4977_; lean_object* v___f_4978_; lean_object* v___f_4979_; lean_object* v___x_4980_; lean_object* v___f_4981_; lean_object* v___f_4982_; lean_object* v___f_4983_; lean_object* v___x_4985_; 
v___f_4976_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3));
v___f_4977_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4));
lean_inc_ref(v_toFunctor_4969_);
v___f_4978_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4978_, 0, v_toFunctor_4969_);
v___f_4979_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4979_, 0, v_toFunctor_4969_);
v___x_4980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4980_, 0, v___f_4978_);
lean_ctor_set(v___x_4980_, 1, v___f_4979_);
v___f_4981_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4981_, 0, v_toSeqRight_4972_);
v___f_4982_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4982_, 0, v_toSeqLeft_4971_);
v___f_4983_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4983_, 0, v_toSeq_4970_);
if (v_isShared_4975_ == 0)
{
lean_ctor_set(v___x_4974_, 4, v___f_4981_);
lean_ctor_set(v___x_4974_, 3, v___f_4982_);
lean_ctor_set(v___x_4974_, 2, v___f_4983_);
lean_ctor_set(v___x_4974_, 1, v___f_4976_);
lean_ctor_set(v___x_4974_, 0, v___x_4980_);
v___x_4985_ = v___x_4974_;
goto v_reusejp_4984_;
}
else
{
lean_object* v_reuseFailAlloc_4993_; 
v_reuseFailAlloc_4993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4993_, 0, v___x_4980_);
lean_ctor_set(v_reuseFailAlloc_4993_, 1, v___f_4976_);
lean_ctor_set(v_reuseFailAlloc_4993_, 2, v___f_4983_);
lean_ctor_set(v_reuseFailAlloc_4993_, 3, v___f_4982_);
lean_ctor_set(v_reuseFailAlloc_4993_, 4, v___f_4981_);
v___x_4985_ = v_reuseFailAlloc_4993_;
goto v_reusejp_4984_;
}
v_reusejp_4984_:
{
lean_object* v___x_4987_; 
if (v_isShared_4968_ == 0)
{
lean_ctor_set(v___x_4967_, 1, v___f_4977_);
lean_ctor_set(v___x_4967_, 0, v___x_4985_);
v___x_4987_ = v___x_4967_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4992_; 
v_reuseFailAlloc_4992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4992_, 0, v___x_4985_);
lean_ctor_set(v_reuseFailAlloc_4992_, 1, v___f_4977_);
v___x_4987_ = v_reuseFailAlloc_4992_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_27491__overap_4990_; lean_object* v___x_4991_; 
v___x_4988_ = l_Lean_instInhabitedExpr;
v___x_4989_ = l_instInhabitedOfMonad___redArg(v___x_4987_, v___x_4988_);
v___x_27491__overap_4990_ = lean_panic_fn_borrowed(v___x_4989_, v_msg_4933_);
lean_dec(v___x_4989_);
lean_inc(v___y_4937_);
lean_inc_ref(v___y_4936_);
lean_inc(v___y_4935_);
lean_inc_ref(v___y_4934_);
v___x_4991_ = lean_apply_5(v___x_27491__overap_4990_, v___y_4934_, v___y_4935_, v___y_4936_, v___y_4937_, lean_box(0));
return v___x_4991_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___boxed(lean_object* v_msg_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_){
_start:
{
lean_object* v_res_5010_; 
v_res_5010_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(v_msg_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_);
lean_dec(v___y_5008_);
lean_dec_ref(v___y_5007_);
lean_dec(v___y_5006_);
lean_dec_ref(v___y_5005_);
return v_res_5010_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(lean_object* v_args_5011_, lean_object* v_ys_5012_, lean_object* v_ys2_5013_, lean_object* v_ys3_5014_, lean_object* v_onAlt_5015_, lean_object* v_a_5016_, uint8_t v___x_5017_, uint8_t v_useSplitter_5018_, lean_object* v___x_5019_, lean_object* v_ys4_5020_, lean_object* v_altType_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_){
_start:
{
lean_object* v___y_5028_; lean_object* v___x_5038_; lean_object* v___x_5039_; 
lean_inc_ref(v_args_5011_);
v___x_5038_ = l_Array_append___redArg(v_args_5011_, v_ys3_5014_);
v___x_5039_ = l_Lean_Meta_instantiateLambda(v___x_5019_, v___x_5038_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_);
lean_dec_ref(v___x_5038_);
if (lean_obj_tag(v___x_5039_) == 0)
{
v___y_5028_ = v___x_5039_;
goto v___jp_5027_;
}
else
{
lean_object* v_a_5040_; uint8_t v___y_5042_; uint8_t v___x_5045_; 
v_a_5040_ = lean_ctor_get(v___x_5039_, 0);
lean_inc(v_a_5040_);
v___x_5045_ = l_Lean_Exception_isInterrupt(v_a_5040_);
if (v___x_5045_ == 0)
{
uint8_t v___x_5046_; 
v___x_5046_ = l_Lean_Exception_isRuntime(v_a_5040_);
v___y_5042_ = v___x_5046_;
goto v___jp_5041_;
}
else
{
lean_dec(v_a_5040_);
v___y_5042_ = v___x_5045_;
goto v___jp_5041_;
}
v___jp_5041_:
{
if (v___y_5042_ == 0)
{
lean_object* v___x_5043_; lean_object* v___x_5044_; 
lean_dec_ref(v___x_5039_);
v___x_5043_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2);
v___x_5044_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_5043_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_);
v___y_5028_ = v___x_5044_;
goto v___jp_5027_;
}
else
{
v___y_5028_ = v___x_5039_;
goto v___jp_5027_;
}
}
}
v___jp_5027_:
{
if (lean_obj_tag(v___y_5028_) == 0)
{
lean_object* v_a_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; 
v_a_5029_ = lean_ctor_get(v___y_5028_, 0);
lean_inc(v_a_5029_);
lean_dec_ref(v___y_5028_);
lean_inc_ref(v_ys4_5020_);
lean_inc_ref(v_ys3_5014_);
lean_inc_ref(v_ys2_5013_);
lean_inc_ref(v_ys_5012_);
v___x_5030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5030_, 0, v_args_5011_);
lean_ctor_set(v___x_5030_, 1, v_ys_5012_);
lean_ctor_set(v___x_5030_, 2, v_ys2_5013_);
lean_ctor_set(v___x_5030_, 3, v_ys3_5014_);
lean_ctor_set(v___x_5030_, 4, v_ys4_5020_);
lean_inc(v___y_5025_);
lean_inc_ref(v___y_5024_);
lean_inc(v___y_5023_);
lean_inc_ref(v___y_5022_);
v___x_5031_ = lean_apply_9(v_onAlt_5015_, v_a_5016_, v_altType_5021_, v___x_5030_, v_a_5029_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_, lean_box(0));
if (lean_obj_tag(v___x_5031_) == 0)
{
lean_object* v_a_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; uint8_t v___x_5036_; lean_object* v___x_5037_; 
v_a_5032_ = lean_ctor_get(v___x_5031_, 0);
lean_inc(v_a_5032_);
lean_dec_ref(v___x_5031_);
v___x_5033_ = l_Array_append___redArg(v_ys_5012_, v_ys2_5013_);
lean_dec_ref(v_ys2_5013_);
v___x_5034_ = l_Array_append___redArg(v___x_5033_, v_ys3_5014_);
lean_dec_ref(v_ys3_5014_);
v___x_5035_ = l_Array_append___redArg(v___x_5034_, v_ys4_5020_);
lean_dec_ref(v_ys4_5020_);
v___x_5036_ = 1;
v___x_5037_ = l_Lean_Meta_mkLambdaFVars(v___x_5035_, v_a_5032_, v___x_5017_, v_useSplitter_5018_, v___x_5017_, v_useSplitter_5018_, v___x_5036_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_);
lean_dec_ref(v___x_5035_);
return v___x_5037_;
}
else
{
lean_dec_ref(v_ys4_5020_);
lean_dec_ref(v_ys3_5014_);
lean_dec_ref(v_ys2_5013_);
lean_dec_ref(v_ys_5012_);
return v___x_5031_;
}
}
else
{
lean_dec_ref(v_altType_5021_);
lean_dec_ref(v_ys4_5020_);
lean_dec(v_a_5016_);
lean_dec_ref(v_onAlt_5015_);
lean_dec_ref(v_ys3_5014_);
lean_dec_ref(v_ys2_5013_);
lean_dec_ref(v_ys_5012_);
lean_dec_ref(v_args_5011_);
return v___y_5028_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed(lean_object* v_args_5047_, lean_object* v_ys_5048_, lean_object* v_ys2_5049_, lean_object* v_ys3_5050_, lean_object* v_onAlt_5051_, lean_object* v_a_5052_, lean_object* v___x_5053_, lean_object* v_useSplitter_5054_, lean_object* v___x_5055_, lean_object* v_ys4_5056_, lean_object* v_altType_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_){
_start:
{
uint8_t v___x_33132__boxed_5063_; uint8_t v_useSplitter_boxed_5064_; lean_object* v_res_5065_; 
v___x_33132__boxed_5063_ = lean_unbox(v___x_5053_);
v_useSplitter_boxed_5064_ = lean_unbox(v_useSplitter_5054_);
v_res_5065_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(v_args_5047_, v_ys_5048_, v_ys2_5049_, v_ys3_5050_, v_onAlt_5051_, v_a_5052_, v___x_33132__boxed_5063_, v_useSplitter_boxed_5064_, v___x_5055_, v_ys4_5056_, v_altType_5057_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_);
lean_dec(v___y_5061_);
lean_dec_ref(v___y_5060_);
lean_dec(v___y_5059_);
lean_dec_ref(v___y_5058_);
return v_res_5065_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(lean_object* v_args_5066_, lean_object* v_ys_5067_, lean_object* v_ys2_5068_, lean_object* v_onAlt_5069_, lean_object* v_a_5070_, uint8_t v___x_5071_, uint8_t v_useSplitter_5072_, lean_object* v___x_5073_, lean_object* v_extraEqualities_5074_, lean_object* v_ys3_5075_, lean_object* v_altType_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_){
_start:
{
lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___f_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; 
v___x_5082_ = lean_box(v___x_5071_);
v___x_5083_ = lean_box(v_useSplitter_5072_);
v___f_5084_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed), 16, 9);
lean_closure_set(v___f_5084_, 0, v_args_5066_);
lean_closure_set(v___f_5084_, 1, v_ys_5067_);
lean_closure_set(v___f_5084_, 2, v_ys2_5068_);
lean_closure_set(v___f_5084_, 3, v_ys3_5075_);
lean_closure_set(v___f_5084_, 4, v_onAlt_5069_);
lean_closure_set(v___f_5084_, 5, v_a_5070_);
lean_closure_set(v___f_5084_, 6, v___x_5082_);
lean_closure_set(v___f_5084_, 7, v___x_5083_);
lean_closure_set(v___f_5084_, 8, v___x_5073_);
v___x_5085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5085_, 0, v_extraEqualities_5074_);
v___x_5086_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_5076_, v___x_5085_, v___f_5084_, v___x_5071_, v___x_5071_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_);
return v___x_5086_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed(lean_object* v_args_5087_, lean_object* v_ys_5088_, lean_object* v_ys2_5089_, lean_object* v_onAlt_5090_, lean_object* v_a_5091_, lean_object* v___x_5092_, lean_object* v_useSplitter_5093_, lean_object* v___x_5094_, lean_object* v_extraEqualities_5095_, lean_object* v_ys3_5096_, lean_object* v_altType_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_){
_start:
{
uint8_t v___x_33197__boxed_5103_; uint8_t v_useSplitter_boxed_5104_; lean_object* v_res_5105_; 
v___x_33197__boxed_5103_ = lean_unbox(v___x_5092_);
v_useSplitter_boxed_5104_ = lean_unbox(v_useSplitter_5093_);
v_res_5105_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(v_args_5087_, v_ys_5088_, v_ys2_5089_, v_onAlt_5090_, v_a_5091_, v___x_33197__boxed_5103_, v_useSplitter_boxed_5104_, v___x_5094_, v_extraEqualities_5095_, v_ys3_5096_, v_altType_5097_, v___y_5098_, v___y_5099_, v___y_5100_, v___y_5101_);
lean_dec(v___y_5101_);
lean_dec_ref(v___y_5100_);
lean_dec(v___y_5099_);
lean_dec_ref(v___y_5098_);
return v_res_5105_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(lean_object* v_args_5106_, lean_object* v_ys_5107_, lean_object* v_onAlt_5108_, lean_object* v_a_5109_, uint8_t v___x_5110_, uint8_t v_useSplitter_5111_, lean_object* v___x_5112_, lean_object* v_extraEqualities_5113_, lean_object* v_numDiscrEqs_5114_, lean_object* v_ys2_5115_, lean_object* v_altType_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_){
_start:
{
lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___f_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; 
v___x_5122_ = lean_box(v___x_5110_);
v___x_5123_ = lean_box(v_useSplitter_5111_);
v___f_5124_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_5124_, 0, v_args_5106_);
lean_closure_set(v___f_5124_, 1, v_ys_5107_);
lean_closure_set(v___f_5124_, 2, v_ys2_5115_);
lean_closure_set(v___f_5124_, 3, v_onAlt_5108_);
lean_closure_set(v___f_5124_, 4, v_a_5109_);
lean_closure_set(v___f_5124_, 5, v___x_5122_);
lean_closure_set(v___f_5124_, 6, v___x_5123_);
lean_closure_set(v___f_5124_, 7, v___x_5112_);
lean_closure_set(v___f_5124_, 8, v_extraEqualities_5113_);
v___x_5125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5125_, 0, v_numDiscrEqs_5114_);
v___x_5126_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_5116_, v___x_5125_, v___f_5124_, v___x_5110_, v___x_5110_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_);
return v___x_5126_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed(lean_object* v_args_5127_, lean_object* v_ys_5128_, lean_object* v_onAlt_5129_, lean_object* v_a_5130_, lean_object* v___x_5131_, lean_object* v_useSplitter_5132_, lean_object* v___x_5133_, lean_object* v_extraEqualities_5134_, lean_object* v_numDiscrEqs_5135_, lean_object* v_ys2_5136_, lean_object* v_altType_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_){
_start:
{
uint8_t v___x_33228__boxed_5143_; uint8_t v_useSplitter_boxed_5144_; lean_object* v_res_5145_; 
v___x_33228__boxed_5143_ = lean_unbox(v___x_5131_);
v_useSplitter_boxed_5144_ = lean_unbox(v_useSplitter_5132_);
v_res_5145_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(v_args_5127_, v_ys_5128_, v_onAlt_5129_, v_a_5130_, v___x_33228__boxed_5143_, v_useSplitter_boxed_5144_, v___x_5133_, v_extraEqualities_5134_, v_numDiscrEqs_5135_, v_ys2_5136_, v_altType_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_);
lean_dec(v___y_5141_);
lean_dec_ref(v___y_5140_);
lean_dec(v___y_5139_);
lean_dec_ref(v___y_5138_);
return v_res_5145_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(lean_object* v___x_5146_, lean_object* v___x_5147_, lean_object* v_onAlt_5148_, lean_object* v_a_5149_, uint8_t v___x_5150_, uint8_t v_useSplitter_5151_, lean_object* v___x_5152_, lean_object* v_extraEqualities_5153_, lean_object* v_numDiscrEqs_5154_, uint8_t v_hasUnitThunk_5155_, lean_object* v___x_5156_, lean_object* v_ys_5157_, lean_object* v_args_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_){
_start:
{
lean_object* v_numFields_5164_; lean_object* v_numOverlaps_5165_; uint8_t v_hasUnitThunk_5166_; lean_object* v___x_5167_; uint8_t v___x_5168_; 
v_numFields_5164_ = lean_ctor_get(v___x_5146_, 0);
v_numOverlaps_5165_ = lean_ctor_get(v___x_5146_, 1);
v_hasUnitThunk_5166_ = lean_ctor_get_uint8(v___x_5146_, sizeof(void*)*2);
v___x_5167_ = lean_array_get_size(v_ys_5157_);
v___x_5168_ = lean_nat_dec_eq(v___x_5167_, v_numFields_5164_);
if (v___x_5168_ == 0)
{
lean_object* v___x_5169_; lean_object* v___x_5170_; 
lean_dec_ref(v_args_5158_);
lean_dec_ref(v_ys_5157_);
lean_dec(v_numDiscrEqs_5154_);
lean_dec(v_extraEqualities_5153_);
lean_dec_ref(v___x_5152_);
lean_dec(v_a_5149_);
lean_dec_ref(v_onAlt_5148_);
lean_dec_ref(v___x_5147_);
v___x_5169_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3);
v___x_5170_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(v___x_5169_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_);
return v___x_5170_;
}
else
{
lean_object* v___x_5171_; 
v___x_5171_ = l_Lean_Meta_instantiateForall(v___x_5147_, v_ys_5157_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_);
if (lean_obj_tag(v___x_5171_) == 0)
{
lean_object* v_a_5172_; lean_object* v___x_5174_; uint8_t v_isShared_5175_; uint8_t v_isSharedCheck_5201_; 
v_a_5172_ = lean_ctor_get(v___x_5171_, 0);
v_isSharedCheck_5201_ = !lean_is_exclusive(v___x_5171_);
if (v_isSharedCheck_5201_ == 0)
{
v___x_5174_ = v___x_5171_;
v_isShared_5175_ = v_isSharedCheck_5201_;
goto v_resetjp_5173_;
}
else
{
lean_inc(v_a_5172_);
lean_dec(v___x_5171_);
v___x_5174_ = lean_box(0);
v_isShared_5175_ = v_isSharedCheck_5201_;
goto v_resetjp_5173_;
}
v_resetjp_5173_:
{
lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___f_5178_; lean_object* v_altType_5180_; lean_object* v___y_5181_; lean_object* v___y_5182_; lean_object* v___y_5183_; lean_object* v___y_5184_; 
v___x_5176_ = lean_box(v___x_5150_);
v___x_5177_ = lean_box(v_useSplitter_5151_);
v___f_5178_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed), 16, 9);
lean_closure_set(v___f_5178_, 0, v_args_5158_);
lean_closure_set(v___f_5178_, 1, v_ys_5157_);
lean_closure_set(v___f_5178_, 2, v_onAlt_5148_);
lean_closure_set(v___f_5178_, 3, v_a_5149_);
lean_closure_set(v___f_5178_, 4, v___x_5176_);
lean_closure_set(v___f_5178_, 5, v___x_5177_);
lean_closure_set(v___f_5178_, 6, v___x_5152_);
lean_closure_set(v___f_5178_, 7, v_extraEqualities_5153_);
lean_closure_set(v___f_5178_, 8, v_numDiscrEqs_5154_);
if (v_hasUnitThunk_5155_ == 0)
{
v_altType_5180_ = v_a_5172_;
v___y_5181_ = v___y_5159_;
v___y_5182_ = v___y_5160_;
v___y_5183_ = v___y_5161_;
v___y_5184_ = v___y_5162_;
goto v___jp_5179_;
}
else
{
lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; 
v___x_5196_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2);
v___x_5197_ = lean_mk_empty_array_with_capacity(v___x_5156_);
v___x_5198_ = lean_array_push(v___x_5197_, v___x_5196_);
v___x_5199_ = l_Lean_Meta_instantiateForall(v_a_5172_, v___x_5198_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_);
lean_dec_ref(v___x_5198_);
if (lean_obj_tag(v___x_5199_) == 0)
{
lean_object* v_a_5200_; 
v_a_5200_ = lean_ctor_get(v___x_5199_, 0);
lean_inc(v_a_5200_);
lean_dec_ref(v___x_5199_);
v_altType_5180_ = v_a_5200_;
v___y_5181_ = v___y_5159_;
v___y_5182_ = v___y_5160_;
v___y_5183_ = v___y_5161_;
v___y_5184_ = v___y_5162_;
goto v___jp_5179_;
}
else
{
lean_dec_ref(v___f_5178_);
lean_del_object(v___x_5174_);
return v___x_5199_;
}
}
v___jp_5179_:
{
lean_object* v___x_5186_; 
lean_inc(v_numOverlaps_5165_);
if (v_isShared_5175_ == 0)
{
lean_ctor_set_tag(v___x_5174_, 1);
lean_ctor_set(v___x_5174_, 0, v_numOverlaps_5165_);
v___x_5186_ = v___x_5174_;
goto v_reusejp_5185_;
}
else
{
lean_object* v_reuseFailAlloc_5195_; 
v_reuseFailAlloc_5195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5195_, 0, v_numOverlaps_5165_);
v___x_5186_ = v_reuseFailAlloc_5195_;
goto v_reusejp_5185_;
}
v_reusejp_5185_:
{
lean_object* v___x_5187_; 
v___x_5187_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_5180_, v___x_5186_, v___f_5178_, v___x_5150_, v___x_5150_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_);
if (lean_obj_tag(v___x_5187_) == 0)
{
if (v_hasUnitThunk_5166_ == 0)
{
return v___x_5187_;
}
else
{
lean_object* v_a_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; 
v_a_5188_ = lean_ctor_get(v___x_5187_, 0);
lean_inc(v_a_5188_);
lean_dec_ref(v___x_5187_);
v___x_5189_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__2));
v___x_5190_ = lean_unsigned_to_nat(2u);
v___x_5191_ = lean_mk_empty_array_with_capacity(v___x_5190_);
lean_dec_ref(v___x_5191_);
v___x_5192_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__35___closed__6);
v___x_5193_ = lean_array_push(v___x_5192_, v_a_5188_);
v___x_5194_ = l_Lean_Meta_mkAppM(v___x_5189_, v___x_5193_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_);
return v___x_5194_;
}
}
else
{
return v___x_5187_;
}
}
}
}
}
else
{
lean_dec_ref(v_args_5158_);
lean_dec_ref(v_ys_5157_);
lean_dec(v_numDiscrEqs_5154_);
lean_dec(v_extraEqualities_5153_);
lean_dec_ref(v___x_5152_);
lean_dec(v_a_5149_);
lean_dec_ref(v_onAlt_5148_);
return v___x_5171_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_5202_ = _args[0];
lean_object* v___x_5203_ = _args[1];
lean_object* v_onAlt_5204_ = _args[2];
lean_object* v_a_5205_ = _args[3];
lean_object* v___x_5206_ = _args[4];
lean_object* v_useSplitter_5207_ = _args[5];
lean_object* v___x_5208_ = _args[6];
lean_object* v_extraEqualities_5209_ = _args[7];
lean_object* v_numDiscrEqs_5210_ = _args[8];
lean_object* v_hasUnitThunk_5211_ = _args[9];
lean_object* v___x_5212_ = _args[10];
lean_object* v_ys_5213_ = _args[11];
lean_object* v_args_5214_ = _args[12];
lean_object* v___y_5215_ = _args[13];
lean_object* v___y_5216_ = _args[14];
lean_object* v___y_5217_ = _args[15];
lean_object* v___y_5218_ = _args[16];
lean_object* v___y_5219_ = _args[17];
_start:
{
uint8_t v___x_33293__boxed_5220_; uint8_t v_useSplitter_boxed_5221_; uint8_t v_hasUnitThunk_boxed_5222_; lean_object* v_res_5223_; 
v___x_33293__boxed_5220_ = lean_unbox(v___x_5206_);
v_useSplitter_boxed_5221_ = lean_unbox(v_useSplitter_5207_);
v_hasUnitThunk_boxed_5222_ = lean_unbox(v_hasUnitThunk_5211_);
v_res_5223_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(v___x_5202_, v___x_5203_, v_onAlt_5204_, v_a_5205_, v___x_33293__boxed_5220_, v_useSplitter_boxed_5221_, v___x_5208_, v_extraEqualities_5209_, v_numDiscrEqs_5210_, v_hasUnitThunk_boxed_5222_, v___x_5212_, v_ys_5213_, v_args_5214_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_);
lean_dec(v___y_5218_);
lean_dec_ref(v___y_5217_);
lean_dec(v___y_5216_);
lean_dec_ref(v___y_5215_);
lean_dec(v___x_5212_);
lean_dec_ref(v___x_5202_);
return v_res_5223_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(lean_object* v___x_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_){
_start:
{
lean_object* v___x_5230_; 
v___x_5230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5230_, 0, v___x_5224_);
return v___x_5230_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed(lean_object* v___x_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_, lean_object* v___y_5236_){
_start:
{
lean_object* v_res_5237_; 
v_res_5237_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(v___x_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_);
lean_dec(v___y_5235_);
lean_dec_ref(v___y_5234_);
lean_dec(v___y_5233_);
lean_dec_ref(v___y_5232_);
return v_res_5237_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(lean_object* v_msg_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_){
_start:
{
lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v_toApplicative_5246_; lean_object* v___x_5248_; uint8_t v_isShared_5249_; uint8_t v_isSharedCheck_5307_; 
v___x_5244_ = lean_obj_once(&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0, &l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0_once, _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0);
v___x_5245_ = l_StateRefT_x27_instMonad___redArg(v___x_5244_);
v_toApplicative_5246_ = lean_ctor_get(v___x_5245_, 0);
v_isSharedCheck_5307_ = !lean_is_exclusive(v___x_5245_);
if (v_isSharedCheck_5307_ == 0)
{
lean_object* v_unused_5308_; 
v_unused_5308_ = lean_ctor_get(v___x_5245_, 1);
lean_dec(v_unused_5308_);
v___x_5248_ = v___x_5245_;
v_isShared_5249_ = v_isSharedCheck_5307_;
goto v_resetjp_5247_;
}
else
{
lean_inc(v_toApplicative_5246_);
lean_dec(v___x_5245_);
v___x_5248_ = lean_box(0);
v_isShared_5249_ = v_isSharedCheck_5307_;
goto v_resetjp_5247_;
}
v_resetjp_5247_:
{
lean_object* v_toFunctor_5250_; lean_object* v_toSeq_5251_; lean_object* v_toSeqLeft_5252_; lean_object* v_toSeqRight_5253_; lean_object* v___x_5255_; uint8_t v_isShared_5256_; uint8_t v_isSharedCheck_5305_; 
v_toFunctor_5250_ = lean_ctor_get(v_toApplicative_5246_, 0);
v_toSeq_5251_ = lean_ctor_get(v_toApplicative_5246_, 2);
v_toSeqLeft_5252_ = lean_ctor_get(v_toApplicative_5246_, 3);
v_toSeqRight_5253_ = lean_ctor_get(v_toApplicative_5246_, 4);
v_isSharedCheck_5305_ = !lean_is_exclusive(v_toApplicative_5246_);
if (v_isSharedCheck_5305_ == 0)
{
lean_object* v_unused_5306_; 
v_unused_5306_ = lean_ctor_get(v_toApplicative_5246_, 1);
lean_dec(v_unused_5306_);
v___x_5255_ = v_toApplicative_5246_;
v_isShared_5256_ = v_isSharedCheck_5305_;
goto v_resetjp_5254_;
}
else
{
lean_inc(v_toSeqRight_5253_);
lean_inc(v_toSeqLeft_5252_);
lean_inc(v_toSeq_5251_);
lean_inc(v_toFunctor_5250_);
lean_dec(v_toApplicative_5246_);
v___x_5255_ = lean_box(0);
v_isShared_5256_ = v_isSharedCheck_5305_;
goto v_resetjp_5254_;
}
v_resetjp_5254_:
{
lean_object* v___f_5257_; lean_object* v___f_5258_; lean_object* v___f_5259_; lean_object* v___f_5260_; lean_object* v___x_5261_; lean_object* v___f_5262_; lean_object* v___f_5263_; lean_object* v___f_5264_; lean_object* v___x_5266_; 
v___f_5257_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__1));
v___f_5258_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__2));
lean_inc_ref(v_toFunctor_5250_);
v___f_5259_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5259_, 0, v_toFunctor_5250_);
v___f_5260_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5260_, 0, v_toFunctor_5250_);
v___x_5261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5261_, 0, v___f_5259_);
lean_ctor_set(v___x_5261_, 1, v___f_5260_);
v___f_5262_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5262_, 0, v_toSeqRight_5253_);
v___f_5263_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5263_, 0, v_toSeqLeft_5252_);
v___f_5264_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5264_, 0, v_toSeq_5251_);
if (v_isShared_5256_ == 0)
{
lean_ctor_set(v___x_5255_, 4, v___f_5262_);
lean_ctor_set(v___x_5255_, 3, v___f_5263_);
lean_ctor_set(v___x_5255_, 2, v___f_5264_);
lean_ctor_set(v___x_5255_, 1, v___f_5257_);
lean_ctor_set(v___x_5255_, 0, v___x_5261_);
v___x_5266_ = v___x_5255_;
goto v_reusejp_5265_;
}
else
{
lean_object* v_reuseFailAlloc_5304_; 
v_reuseFailAlloc_5304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5304_, 0, v___x_5261_);
lean_ctor_set(v_reuseFailAlloc_5304_, 1, v___f_5257_);
lean_ctor_set(v_reuseFailAlloc_5304_, 2, v___f_5264_);
lean_ctor_set(v_reuseFailAlloc_5304_, 3, v___f_5263_);
lean_ctor_set(v_reuseFailAlloc_5304_, 4, v___f_5262_);
v___x_5266_ = v_reuseFailAlloc_5304_;
goto v_reusejp_5265_;
}
v_reusejp_5265_:
{
lean_object* v___x_5268_; 
if (v_isShared_5249_ == 0)
{
lean_ctor_set(v___x_5248_, 1, v___f_5258_);
lean_ctor_set(v___x_5248_, 0, v___x_5266_);
v___x_5268_ = v___x_5248_;
goto v_reusejp_5267_;
}
else
{
lean_object* v_reuseFailAlloc_5303_; 
v_reuseFailAlloc_5303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5303_, 0, v___x_5266_);
lean_ctor_set(v_reuseFailAlloc_5303_, 1, v___f_5258_);
v___x_5268_ = v_reuseFailAlloc_5303_;
goto v_reusejp_5267_;
}
v_reusejp_5267_:
{
lean_object* v___x_5269_; lean_object* v_toApplicative_5270_; lean_object* v___x_5272_; uint8_t v_isShared_5273_; uint8_t v_isSharedCheck_5301_; 
v___x_5269_ = l_StateRefT_x27_instMonad___redArg(v___x_5268_);
v_toApplicative_5270_ = lean_ctor_get(v___x_5269_, 0);
v_isSharedCheck_5301_ = !lean_is_exclusive(v___x_5269_);
if (v_isSharedCheck_5301_ == 0)
{
lean_object* v_unused_5302_; 
v_unused_5302_ = lean_ctor_get(v___x_5269_, 1);
lean_dec(v_unused_5302_);
v___x_5272_ = v___x_5269_;
v_isShared_5273_ = v_isSharedCheck_5301_;
goto v_resetjp_5271_;
}
else
{
lean_inc(v_toApplicative_5270_);
lean_dec(v___x_5269_);
v___x_5272_ = lean_box(0);
v_isShared_5273_ = v_isSharedCheck_5301_;
goto v_resetjp_5271_;
}
v_resetjp_5271_:
{
lean_object* v_toFunctor_5274_; lean_object* v_toSeq_5275_; lean_object* v_toSeqLeft_5276_; lean_object* v_toSeqRight_5277_; lean_object* v___x_5279_; uint8_t v_isShared_5280_; uint8_t v_isSharedCheck_5299_; 
v_toFunctor_5274_ = lean_ctor_get(v_toApplicative_5270_, 0);
v_toSeq_5275_ = lean_ctor_get(v_toApplicative_5270_, 2);
v_toSeqLeft_5276_ = lean_ctor_get(v_toApplicative_5270_, 3);
v_toSeqRight_5277_ = lean_ctor_get(v_toApplicative_5270_, 4);
v_isSharedCheck_5299_ = !lean_is_exclusive(v_toApplicative_5270_);
if (v_isSharedCheck_5299_ == 0)
{
lean_object* v_unused_5300_; 
v_unused_5300_ = lean_ctor_get(v_toApplicative_5270_, 1);
lean_dec(v_unused_5300_);
v___x_5279_ = v_toApplicative_5270_;
v_isShared_5280_ = v_isSharedCheck_5299_;
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
v_isShared_5280_ = v_isSharedCheck_5299_;
goto v_resetjp_5278_;
}
v_resetjp_5278_:
{
lean_object* v___f_5281_; lean_object* v___f_5282_; lean_object* v___f_5283_; lean_object* v___f_5284_; lean_object* v___x_5285_; lean_object* v___f_5286_; lean_object* v___f_5287_; lean_object* v___f_5288_; lean_object* v___x_5290_; 
v___f_5281_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3));
v___f_5282_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4));
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
lean_object* v_reuseFailAlloc_5298_; 
v_reuseFailAlloc_5298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5298_, 0, v___x_5285_);
lean_ctor_set(v_reuseFailAlloc_5298_, 1, v___f_5281_);
lean_ctor_set(v_reuseFailAlloc_5298_, 2, v___f_5288_);
lean_ctor_set(v_reuseFailAlloc_5298_, 3, v___f_5287_);
lean_ctor_set(v_reuseFailAlloc_5298_, 4, v___f_5286_);
v___x_5290_ = v_reuseFailAlloc_5298_;
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
lean_object* v_reuseFailAlloc_5297_; 
v_reuseFailAlloc_5297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5297_, 0, v___x_5290_);
lean_ctor_set(v_reuseFailAlloc_5297_, 1, v___f_5282_);
v___x_5292_ = v_reuseFailAlloc_5297_;
goto v_reusejp_5291_;
}
v_reusejp_5291_:
{
lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_27479__overap_5295_; lean_object* v___x_5296_; 
v___x_5293_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7);
v___x_5294_ = l_instInhabitedOfMonad___redArg(v___x_5292_, v___x_5293_);
v___x_27479__overap_5295_ = lean_panic_fn_borrowed(v___x_5294_, v_msg_5238_);
lean_dec(v___x_5294_);
lean_inc(v___y_5242_);
lean_inc_ref(v___y_5241_);
lean_inc(v___y_5240_);
lean_inc_ref(v___y_5239_);
v___x_5296_ = lean_apply_5(v___x_27479__overap_5295_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, lean_box(0));
return v___x_5296_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed(lean_object* v_msg_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_){
_start:
{
lean_object* v_res_5315_; 
v_res_5315_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(v_msg_5309_, v___y_5310_, v___y_5311_, v___y_5312_, v___y_5313_);
lean_dec(v___y_5313_);
lean_dec_ref(v___y_5312_);
lean_dec(v___y_5311_);
lean_dec_ref(v___y_5310_);
return v_res_5315_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(lean_object* v_upperBound_5316_, lean_object* v_onAlt_5317_, uint8_t v_useSplitter_5318_, lean_object* v_extraEqualities_5319_, lean_object* v_numDiscrEqs_5320_, lean_object* v_a_5321_, lean_object* v_b_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_){
_start:
{
lean_object* v___y_5329_; uint8_t v___x_5352_; 
v___x_5352_ = lean_nat_dec_lt(v_a_5321_, v_upperBound_5316_);
if (v___x_5352_ == 0)
{
lean_object* v___x_5353_; 
lean_dec(v_a_5321_);
lean_dec(v_numDiscrEqs_5320_);
lean_dec(v_extraEqualities_5319_);
lean_dec_ref(v_onAlt_5317_);
v___x_5353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5353_, 0, v_b_5322_);
return v___x_5353_;
}
else
{
lean_object* v_snd_5354_; lean_object* v_snd_5355_; lean_object* v_snd_5356_; lean_object* v_snd_5357_; lean_object* v_snd_5358_; lean_object* v_fst_5359_; lean_object* v___x_5361_; uint8_t v_isShared_5362_; uint8_t v_isSharedCheck_5565_; 
v_snd_5354_ = lean_ctor_get(v_b_5322_, 1);
lean_inc(v_snd_5354_);
v_snd_5355_ = lean_ctor_get(v_snd_5354_, 1);
lean_inc(v_snd_5355_);
v_snd_5356_ = lean_ctor_get(v_snd_5355_, 1);
lean_inc(v_snd_5356_);
v_snd_5357_ = lean_ctor_get(v_snd_5356_, 1);
lean_inc(v_snd_5357_);
v_snd_5358_ = lean_ctor_get(v_snd_5357_, 1);
lean_inc(v_snd_5358_);
v_fst_5359_ = lean_ctor_get(v_b_5322_, 0);
v_isSharedCheck_5565_ = !lean_is_exclusive(v_b_5322_);
if (v_isSharedCheck_5565_ == 0)
{
lean_object* v_unused_5566_; 
v_unused_5566_ = lean_ctor_get(v_b_5322_, 1);
lean_dec(v_unused_5566_);
v___x_5361_ = v_b_5322_;
v_isShared_5362_ = v_isSharedCheck_5565_;
goto v_resetjp_5360_;
}
else
{
lean_inc(v_fst_5359_);
lean_dec(v_b_5322_);
v___x_5361_ = lean_box(0);
v_isShared_5362_ = v_isSharedCheck_5565_;
goto v_resetjp_5360_;
}
v_resetjp_5360_:
{
lean_object* v_fst_5363_; lean_object* v___x_5365_; uint8_t v_isShared_5366_; uint8_t v_isSharedCheck_5563_; 
v_fst_5363_ = lean_ctor_get(v_snd_5354_, 0);
v_isSharedCheck_5563_ = !lean_is_exclusive(v_snd_5354_);
if (v_isSharedCheck_5563_ == 0)
{
lean_object* v_unused_5564_; 
v_unused_5564_ = lean_ctor_get(v_snd_5354_, 1);
lean_dec(v_unused_5564_);
v___x_5365_ = v_snd_5354_;
v_isShared_5366_ = v_isSharedCheck_5563_;
goto v_resetjp_5364_;
}
else
{
lean_inc(v_fst_5363_);
lean_dec(v_snd_5354_);
v___x_5365_ = lean_box(0);
v_isShared_5366_ = v_isSharedCheck_5563_;
goto v_resetjp_5364_;
}
v_resetjp_5364_:
{
lean_object* v_fst_5367_; lean_object* v___x_5369_; uint8_t v_isShared_5370_; uint8_t v_isSharedCheck_5561_; 
v_fst_5367_ = lean_ctor_get(v_snd_5355_, 0);
v_isSharedCheck_5561_ = !lean_is_exclusive(v_snd_5355_);
if (v_isSharedCheck_5561_ == 0)
{
lean_object* v_unused_5562_; 
v_unused_5562_ = lean_ctor_get(v_snd_5355_, 1);
lean_dec(v_unused_5562_);
v___x_5369_ = v_snd_5355_;
v_isShared_5370_ = v_isSharedCheck_5561_;
goto v_resetjp_5368_;
}
else
{
lean_inc(v_fst_5367_);
lean_dec(v_snd_5355_);
v___x_5369_ = lean_box(0);
v_isShared_5370_ = v_isSharedCheck_5561_;
goto v_resetjp_5368_;
}
v_resetjp_5368_:
{
lean_object* v_fst_5371_; lean_object* v___x_5373_; uint8_t v_isShared_5374_; uint8_t v_isSharedCheck_5559_; 
v_fst_5371_ = lean_ctor_get(v_snd_5356_, 0);
v_isSharedCheck_5559_ = !lean_is_exclusive(v_snd_5356_);
if (v_isSharedCheck_5559_ == 0)
{
lean_object* v_unused_5560_; 
v_unused_5560_ = lean_ctor_get(v_snd_5356_, 1);
lean_dec(v_unused_5560_);
v___x_5373_ = v_snd_5356_;
v_isShared_5374_ = v_isSharedCheck_5559_;
goto v_resetjp_5372_;
}
else
{
lean_inc(v_fst_5371_);
lean_dec(v_snd_5356_);
v___x_5373_ = lean_box(0);
v_isShared_5374_ = v_isSharedCheck_5559_;
goto v_resetjp_5372_;
}
v_resetjp_5372_:
{
lean_object* v_fst_5375_; lean_object* v___x_5377_; uint8_t v_isShared_5378_; uint8_t v_isSharedCheck_5557_; 
v_fst_5375_ = lean_ctor_get(v_snd_5357_, 0);
v_isSharedCheck_5557_ = !lean_is_exclusive(v_snd_5357_);
if (v_isSharedCheck_5557_ == 0)
{
lean_object* v_unused_5558_; 
v_unused_5558_ = lean_ctor_get(v_snd_5357_, 1);
lean_dec(v_unused_5558_);
v___x_5377_ = v_snd_5357_;
v_isShared_5378_ = v_isSharedCheck_5557_;
goto v_resetjp_5376_;
}
else
{
lean_inc(v_fst_5375_);
lean_dec(v_snd_5357_);
v___x_5377_ = lean_box(0);
v_isShared_5378_ = v_isSharedCheck_5557_;
goto v_resetjp_5376_;
}
v_resetjp_5376_:
{
lean_object* v_array_5379_; lean_object* v_start_5380_; lean_object* v_stop_5381_; uint8_t v___x_5382_; 
v_array_5379_ = lean_ctor_get(v_snd_5358_, 0);
v_start_5380_ = lean_ctor_get(v_snd_5358_, 1);
v_stop_5381_ = lean_ctor_get(v_snd_5358_, 2);
v___x_5382_ = lean_nat_dec_lt(v_start_5380_, v_stop_5381_);
if (v___x_5382_ == 0)
{
lean_object* v___x_5384_; 
if (v_isShared_5378_ == 0)
{
v___x_5384_ = v___x_5377_;
goto v_reusejp_5383_;
}
else
{
lean_object* v_reuseFailAlloc_5399_; 
v_reuseFailAlloc_5399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5399_, 0, v_fst_5375_);
lean_ctor_set(v_reuseFailAlloc_5399_, 1, v_snd_5358_);
v___x_5384_ = v_reuseFailAlloc_5399_;
goto v_reusejp_5383_;
}
v_reusejp_5383_:
{
lean_object* v___x_5386_; 
if (v_isShared_5374_ == 0)
{
lean_ctor_set(v___x_5373_, 1, v___x_5384_);
v___x_5386_ = v___x_5373_;
goto v_reusejp_5385_;
}
else
{
lean_object* v_reuseFailAlloc_5398_; 
v_reuseFailAlloc_5398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5398_, 0, v_fst_5371_);
lean_ctor_set(v_reuseFailAlloc_5398_, 1, v___x_5384_);
v___x_5386_ = v_reuseFailAlloc_5398_;
goto v_reusejp_5385_;
}
v_reusejp_5385_:
{
lean_object* v___x_5388_; 
if (v_isShared_5370_ == 0)
{
lean_ctor_set(v___x_5369_, 1, v___x_5386_);
v___x_5388_ = v___x_5369_;
goto v_reusejp_5387_;
}
else
{
lean_object* v_reuseFailAlloc_5397_; 
v_reuseFailAlloc_5397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5397_, 0, v_fst_5367_);
lean_ctor_set(v_reuseFailAlloc_5397_, 1, v___x_5386_);
v___x_5388_ = v_reuseFailAlloc_5397_;
goto v_reusejp_5387_;
}
v_reusejp_5387_:
{
lean_object* v___x_5390_; 
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 1, v___x_5388_);
v___x_5390_ = v___x_5365_;
goto v_reusejp_5389_;
}
else
{
lean_object* v_reuseFailAlloc_5396_; 
v_reuseFailAlloc_5396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5396_, 0, v_fst_5363_);
lean_ctor_set(v_reuseFailAlloc_5396_, 1, v___x_5388_);
v___x_5390_ = v_reuseFailAlloc_5396_;
goto v_reusejp_5389_;
}
v_reusejp_5389_:
{
lean_object* v___x_5392_; 
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 1, v___x_5390_);
v___x_5392_ = v___x_5361_;
goto v_reusejp_5391_;
}
else
{
lean_object* v_reuseFailAlloc_5395_; 
v_reuseFailAlloc_5395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5395_, 0, v_fst_5359_);
lean_ctor_set(v_reuseFailAlloc_5395_, 1, v___x_5390_);
v___x_5392_ = v_reuseFailAlloc_5395_;
goto v_reusejp_5391_;
}
v_reusejp_5391_:
{
lean_object* v___x_5393_; lean_object* v___f_5394_; 
v___x_5393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5393_, 0, v___x_5392_);
v___f_5394_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5394_, 0, v___x_5393_);
v___y_5329_ = v___f_5394_;
goto v___jp_5328_;
}
}
}
}
}
}
else
{
lean_object* v___x_5401_; uint8_t v_isShared_5402_; uint8_t v_isSharedCheck_5553_; 
lean_inc(v_stop_5381_);
lean_inc(v_start_5380_);
lean_inc_ref(v_array_5379_);
v_isSharedCheck_5553_ = !lean_is_exclusive(v_snd_5358_);
if (v_isSharedCheck_5553_ == 0)
{
lean_object* v_unused_5554_; lean_object* v_unused_5555_; lean_object* v_unused_5556_; 
v_unused_5554_ = lean_ctor_get(v_snd_5358_, 2);
lean_dec(v_unused_5554_);
v_unused_5555_ = lean_ctor_get(v_snd_5358_, 1);
lean_dec(v_unused_5555_);
v_unused_5556_ = lean_ctor_get(v_snd_5358_, 0);
lean_dec(v_unused_5556_);
v___x_5401_ = v_snd_5358_;
v_isShared_5402_ = v_isSharedCheck_5553_;
goto v_resetjp_5400_;
}
else
{
lean_dec(v_snd_5358_);
v___x_5401_ = lean_box(0);
v_isShared_5402_ = v_isSharedCheck_5553_;
goto v_resetjp_5400_;
}
v_resetjp_5400_:
{
lean_object* v_array_5403_; lean_object* v_start_5404_; lean_object* v_stop_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5410_; 
v_array_5403_ = lean_ctor_get(v_fst_5375_, 0);
v_start_5404_ = lean_ctor_get(v_fst_5375_, 1);
v_stop_5405_ = lean_ctor_get(v_fst_5375_, 2);
v___x_5406_ = lean_array_fget(v_array_5379_, v_start_5380_);
v___x_5407_ = lean_unsigned_to_nat(1u);
v___x_5408_ = lean_nat_add(v_start_5380_, v___x_5407_);
lean_dec(v_start_5380_);
if (v_isShared_5402_ == 0)
{
lean_ctor_set(v___x_5401_, 1, v___x_5408_);
v___x_5410_ = v___x_5401_;
goto v_reusejp_5409_;
}
else
{
lean_object* v_reuseFailAlloc_5552_; 
v_reuseFailAlloc_5552_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5552_, 0, v_array_5379_);
lean_ctor_set(v_reuseFailAlloc_5552_, 1, v___x_5408_);
lean_ctor_set(v_reuseFailAlloc_5552_, 2, v_stop_5381_);
v___x_5410_ = v_reuseFailAlloc_5552_;
goto v_reusejp_5409_;
}
v_reusejp_5409_:
{
uint8_t v___x_5411_; 
v___x_5411_ = lean_nat_dec_lt(v_start_5404_, v_stop_5405_);
if (v___x_5411_ == 0)
{
lean_object* v___x_5413_; 
lean_dec(v___x_5406_);
if (v_isShared_5378_ == 0)
{
lean_ctor_set(v___x_5377_, 1, v___x_5410_);
v___x_5413_ = v___x_5377_;
goto v_reusejp_5412_;
}
else
{
lean_object* v_reuseFailAlloc_5428_; 
v_reuseFailAlloc_5428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5428_, 0, v_fst_5375_);
lean_ctor_set(v_reuseFailAlloc_5428_, 1, v___x_5410_);
v___x_5413_ = v_reuseFailAlloc_5428_;
goto v_reusejp_5412_;
}
v_reusejp_5412_:
{
lean_object* v___x_5415_; 
if (v_isShared_5374_ == 0)
{
lean_ctor_set(v___x_5373_, 1, v___x_5413_);
v___x_5415_ = v___x_5373_;
goto v_reusejp_5414_;
}
else
{
lean_object* v_reuseFailAlloc_5427_; 
v_reuseFailAlloc_5427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5427_, 0, v_fst_5371_);
lean_ctor_set(v_reuseFailAlloc_5427_, 1, v___x_5413_);
v___x_5415_ = v_reuseFailAlloc_5427_;
goto v_reusejp_5414_;
}
v_reusejp_5414_:
{
lean_object* v___x_5417_; 
if (v_isShared_5370_ == 0)
{
lean_ctor_set(v___x_5369_, 1, v___x_5415_);
v___x_5417_ = v___x_5369_;
goto v_reusejp_5416_;
}
else
{
lean_object* v_reuseFailAlloc_5426_; 
v_reuseFailAlloc_5426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5426_, 0, v_fst_5367_);
lean_ctor_set(v_reuseFailAlloc_5426_, 1, v___x_5415_);
v___x_5417_ = v_reuseFailAlloc_5426_;
goto v_reusejp_5416_;
}
v_reusejp_5416_:
{
lean_object* v___x_5419_; 
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 1, v___x_5417_);
v___x_5419_ = v___x_5365_;
goto v_reusejp_5418_;
}
else
{
lean_object* v_reuseFailAlloc_5425_; 
v_reuseFailAlloc_5425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5425_, 0, v_fst_5363_);
lean_ctor_set(v_reuseFailAlloc_5425_, 1, v___x_5417_);
v___x_5419_ = v_reuseFailAlloc_5425_;
goto v_reusejp_5418_;
}
v_reusejp_5418_:
{
lean_object* v___x_5421_; 
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 1, v___x_5419_);
v___x_5421_ = v___x_5361_;
goto v_reusejp_5420_;
}
else
{
lean_object* v_reuseFailAlloc_5424_; 
v_reuseFailAlloc_5424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5424_, 0, v_fst_5359_);
lean_ctor_set(v_reuseFailAlloc_5424_, 1, v___x_5419_);
v___x_5421_ = v_reuseFailAlloc_5424_;
goto v_reusejp_5420_;
}
v_reusejp_5420_:
{
lean_object* v___x_5422_; lean_object* v___f_5423_; 
v___x_5422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5422_, 0, v___x_5421_);
v___f_5423_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5423_, 0, v___x_5422_);
v___y_5329_ = v___f_5423_;
goto v___jp_5328_;
}
}
}
}
}
}
else
{
lean_object* v___x_5430_; uint8_t v_isShared_5431_; uint8_t v_isSharedCheck_5548_; 
lean_inc(v_stop_5405_);
lean_inc(v_start_5404_);
lean_inc_ref(v_array_5403_);
v_isSharedCheck_5548_ = !lean_is_exclusive(v_fst_5375_);
if (v_isSharedCheck_5548_ == 0)
{
lean_object* v_unused_5549_; lean_object* v_unused_5550_; lean_object* v_unused_5551_; 
v_unused_5549_ = lean_ctor_get(v_fst_5375_, 2);
lean_dec(v_unused_5549_);
v_unused_5550_ = lean_ctor_get(v_fst_5375_, 1);
lean_dec(v_unused_5550_);
v_unused_5551_ = lean_ctor_get(v_fst_5375_, 0);
lean_dec(v_unused_5551_);
v___x_5430_ = v_fst_5375_;
v_isShared_5431_ = v_isSharedCheck_5548_;
goto v_resetjp_5429_;
}
else
{
lean_dec(v_fst_5375_);
v___x_5430_ = lean_box(0);
v_isShared_5431_ = v_isSharedCheck_5548_;
goto v_resetjp_5429_;
}
v_resetjp_5429_:
{
lean_object* v_array_5432_; lean_object* v_start_5433_; lean_object* v_stop_5434_; lean_object* v___x_5435_; lean_object* v___x_5436_; lean_object* v___x_5438_; 
v_array_5432_ = lean_ctor_get(v_fst_5371_, 0);
v_start_5433_ = lean_ctor_get(v_fst_5371_, 1);
v_stop_5434_ = lean_ctor_get(v_fst_5371_, 2);
v___x_5435_ = lean_array_fget(v_array_5403_, v_start_5404_);
v___x_5436_ = lean_nat_add(v_start_5404_, v___x_5407_);
lean_dec(v_start_5404_);
if (v_isShared_5431_ == 0)
{
lean_ctor_set(v___x_5430_, 1, v___x_5436_);
v___x_5438_ = v___x_5430_;
goto v_reusejp_5437_;
}
else
{
lean_object* v_reuseFailAlloc_5547_; 
v_reuseFailAlloc_5547_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5547_, 0, v_array_5403_);
lean_ctor_set(v_reuseFailAlloc_5547_, 1, v___x_5436_);
lean_ctor_set(v_reuseFailAlloc_5547_, 2, v_stop_5405_);
v___x_5438_ = v_reuseFailAlloc_5547_;
goto v_reusejp_5437_;
}
v_reusejp_5437_:
{
uint8_t v___x_5439_; 
v___x_5439_ = lean_nat_dec_lt(v_start_5433_, v_stop_5434_);
if (v___x_5439_ == 0)
{
lean_object* v___x_5441_; 
lean_dec(v___x_5435_);
lean_dec(v___x_5406_);
if (v_isShared_5378_ == 0)
{
lean_ctor_set(v___x_5377_, 1, v___x_5410_);
lean_ctor_set(v___x_5377_, 0, v___x_5438_);
v___x_5441_ = v___x_5377_;
goto v_reusejp_5440_;
}
else
{
lean_object* v_reuseFailAlloc_5456_; 
v_reuseFailAlloc_5456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5456_, 0, v___x_5438_);
lean_ctor_set(v_reuseFailAlloc_5456_, 1, v___x_5410_);
v___x_5441_ = v_reuseFailAlloc_5456_;
goto v_reusejp_5440_;
}
v_reusejp_5440_:
{
lean_object* v___x_5443_; 
if (v_isShared_5374_ == 0)
{
lean_ctor_set(v___x_5373_, 1, v___x_5441_);
v___x_5443_ = v___x_5373_;
goto v_reusejp_5442_;
}
else
{
lean_object* v_reuseFailAlloc_5455_; 
v_reuseFailAlloc_5455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5455_, 0, v_fst_5371_);
lean_ctor_set(v_reuseFailAlloc_5455_, 1, v___x_5441_);
v___x_5443_ = v_reuseFailAlloc_5455_;
goto v_reusejp_5442_;
}
v_reusejp_5442_:
{
lean_object* v___x_5445_; 
if (v_isShared_5370_ == 0)
{
lean_ctor_set(v___x_5369_, 1, v___x_5443_);
v___x_5445_ = v___x_5369_;
goto v_reusejp_5444_;
}
else
{
lean_object* v_reuseFailAlloc_5454_; 
v_reuseFailAlloc_5454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5454_, 0, v_fst_5367_);
lean_ctor_set(v_reuseFailAlloc_5454_, 1, v___x_5443_);
v___x_5445_ = v_reuseFailAlloc_5454_;
goto v_reusejp_5444_;
}
v_reusejp_5444_:
{
lean_object* v___x_5447_; 
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 1, v___x_5445_);
v___x_5447_ = v___x_5365_;
goto v_reusejp_5446_;
}
else
{
lean_object* v_reuseFailAlloc_5453_; 
v_reuseFailAlloc_5453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5453_, 0, v_fst_5363_);
lean_ctor_set(v_reuseFailAlloc_5453_, 1, v___x_5445_);
v___x_5447_ = v_reuseFailAlloc_5453_;
goto v_reusejp_5446_;
}
v_reusejp_5446_:
{
lean_object* v___x_5449_; 
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 1, v___x_5447_);
v___x_5449_ = v___x_5361_;
goto v_reusejp_5448_;
}
else
{
lean_object* v_reuseFailAlloc_5452_; 
v_reuseFailAlloc_5452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5452_, 0, v_fst_5359_);
lean_ctor_set(v_reuseFailAlloc_5452_, 1, v___x_5447_);
v___x_5449_ = v_reuseFailAlloc_5452_;
goto v_reusejp_5448_;
}
v_reusejp_5448_:
{
lean_object* v___x_5450_; lean_object* v___f_5451_; 
v___x_5450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5450_, 0, v___x_5449_);
v___f_5451_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5451_, 0, v___x_5450_);
v___y_5329_ = v___f_5451_;
goto v___jp_5328_;
}
}
}
}
}
}
else
{
lean_object* v___x_5458_; uint8_t v_isShared_5459_; uint8_t v_isSharedCheck_5543_; 
lean_inc(v_stop_5434_);
lean_inc(v_start_5433_);
lean_inc_ref(v_array_5432_);
v_isSharedCheck_5543_ = !lean_is_exclusive(v_fst_5371_);
if (v_isSharedCheck_5543_ == 0)
{
lean_object* v_unused_5544_; lean_object* v_unused_5545_; lean_object* v_unused_5546_; 
v_unused_5544_ = lean_ctor_get(v_fst_5371_, 2);
lean_dec(v_unused_5544_);
v_unused_5545_ = lean_ctor_get(v_fst_5371_, 1);
lean_dec(v_unused_5545_);
v_unused_5546_ = lean_ctor_get(v_fst_5371_, 0);
lean_dec(v_unused_5546_);
v___x_5458_ = v_fst_5371_;
v_isShared_5459_ = v_isSharedCheck_5543_;
goto v_resetjp_5457_;
}
else
{
lean_dec(v_fst_5371_);
v___x_5458_ = lean_box(0);
v_isShared_5459_ = v_isSharedCheck_5543_;
goto v_resetjp_5457_;
}
v_resetjp_5457_:
{
lean_object* v_array_5460_; lean_object* v_start_5461_; lean_object* v_stop_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5466_; 
v_array_5460_ = lean_ctor_get(v_fst_5367_, 0);
v_start_5461_ = lean_ctor_get(v_fst_5367_, 1);
v_stop_5462_ = lean_ctor_get(v_fst_5367_, 2);
v___x_5463_ = lean_array_fget(v_array_5432_, v_start_5433_);
v___x_5464_ = lean_nat_add(v_start_5433_, v___x_5407_);
lean_dec(v_start_5433_);
if (v_isShared_5459_ == 0)
{
lean_ctor_set(v___x_5458_, 1, v___x_5464_);
v___x_5466_ = v___x_5458_;
goto v_reusejp_5465_;
}
else
{
lean_object* v_reuseFailAlloc_5542_; 
v_reuseFailAlloc_5542_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5542_, 0, v_array_5432_);
lean_ctor_set(v_reuseFailAlloc_5542_, 1, v___x_5464_);
lean_ctor_set(v_reuseFailAlloc_5542_, 2, v_stop_5434_);
v___x_5466_ = v_reuseFailAlloc_5542_;
goto v_reusejp_5465_;
}
v_reusejp_5465_:
{
uint8_t v___x_5467_; 
v___x_5467_ = lean_nat_dec_lt(v_start_5461_, v_stop_5462_);
if (v___x_5467_ == 0)
{
lean_object* v___x_5469_; 
lean_dec(v___x_5463_);
lean_dec(v___x_5435_);
lean_dec(v___x_5406_);
if (v_isShared_5378_ == 0)
{
lean_ctor_set(v___x_5377_, 1, v___x_5410_);
lean_ctor_set(v___x_5377_, 0, v___x_5438_);
v___x_5469_ = v___x_5377_;
goto v_reusejp_5468_;
}
else
{
lean_object* v_reuseFailAlloc_5484_; 
v_reuseFailAlloc_5484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5484_, 0, v___x_5438_);
lean_ctor_set(v_reuseFailAlloc_5484_, 1, v___x_5410_);
v___x_5469_ = v_reuseFailAlloc_5484_;
goto v_reusejp_5468_;
}
v_reusejp_5468_:
{
lean_object* v___x_5471_; 
if (v_isShared_5374_ == 0)
{
lean_ctor_set(v___x_5373_, 1, v___x_5469_);
lean_ctor_set(v___x_5373_, 0, v___x_5466_);
v___x_5471_ = v___x_5373_;
goto v_reusejp_5470_;
}
else
{
lean_object* v_reuseFailAlloc_5483_; 
v_reuseFailAlloc_5483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5483_, 0, v___x_5466_);
lean_ctor_set(v_reuseFailAlloc_5483_, 1, v___x_5469_);
v___x_5471_ = v_reuseFailAlloc_5483_;
goto v_reusejp_5470_;
}
v_reusejp_5470_:
{
lean_object* v___x_5473_; 
if (v_isShared_5370_ == 0)
{
lean_ctor_set(v___x_5369_, 1, v___x_5471_);
v___x_5473_ = v___x_5369_;
goto v_reusejp_5472_;
}
else
{
lean_object* v_reuseFailAlloc_5482_; 
v_reuseFailAlloc_5482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5482_, 0, v_fst_5367_);
lean_ctor_set(v_reuseFailAlloc_5482_, 1, v___x_5471_);
v___x_5473_ = v_reuseFailAlloc_5482_;
goto v_reusejp_5472_;
}
v_reusejp_5472_:
{
lean_object* v___x_5475_; 
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 1, v___x_5473_);
v___x_5475_ = v___x_5365_;
goto v_reusejp_5474_;
}
else
{
lean_object* v_reuseFailAlloc_5481_; 
v_reuseFailAlloc_5481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5481_, 0, v_fst_5363_);
lean_ctor_set(v_reuseFailAlloc_5481_, 1, v___x_5473_);
v___x_5475_ = v_reuseFailAlloc_5481_;
goto v_reusejp_5474_;
}
v_reusejp_5474_:
{
lean_object* v___x_5477_; 
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 1, v___x_5475_);
v___x_5477_ = v___x_5361_;
goto v_reusejp_5476_;
}
else
{
lean_object* v_reuseFailAlloc_5480_; 
v_reuseFailAlloc_5480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5480_, 0, v_fst_5359_);
lean_ctor_set(v_reuseFailAlloc_5480_, 1, v___x_5475_);
v___x_5477_ = v_reuseFailAlloc_5480_;
goto v_reusejp_5476_;
}
v_reusejp_5476_:
{
lean_object* v___x_5478_; lean_object* v___f_5479_; 
v___x_5478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5478_, 0, v___x_5477_);
v___f_5479_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5479_, 0, v___x_5478_);
v___y_5329_ = v___f_5479_;
goto v___jp_5328_;
}
}
}
}
}
}
else
{
lean_object* v___x_5486_; uint8_t v_isShared_5487_; uint8_t v_isSharedCheck_5538_; 
lean_inc(v_stop_5462_);
lean_inc(v_start_5461_);
lean_inc_ref(v_array_5460_);
v_isSharedCheck_5538_ = !lean_is_exclusive(v_fst_5367_);
if (v_isSharedCheck_5538_ == 0)
{
lean_object* v_unused_5539_; lean_object* v_unused_5540_; lean_object* v_unused_5541_; 
v_unused_5539_ = lean_ctor_get(v_fst_5367_, 2);
lean_dec(v_unused_5539_);
v_unused_5540_ = lean_ctor_get(v_fst_5367_, 1);
lean_dec(v_unused_5540_);
v_unused_5541_ = lean_ctor_get(v_fst_5367_, 0);
lean_dec(v_unused_5541_);
v___x_5486_ = v_fst_5367_;
v_isShared_5487_ = v_isSharedCheck_5538_;
goto v_resetjp_5485_;
}
else
{
lean_dec(v_fst_5367_);
v___x_5486_ = lean_box(0);
v_isShared_5487_ = v_isSharedCheck_5538_;
goto v_resetjp_5485_;
}
v_resetjp_5485_:
{
lean_object* v_array_5488_; lean_object* v_start_5489_; lean_object* v_stop_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; lean_object* v___x_5494_; 
v_array_5488_ = lean_ctor_get(v_fst_5363_, 0);
v_start_5489_ = lean_ctor_get(v_fst_5363_, 1);
v_stop_5490_ = lean_ctor_get(v_fst_5363_, 2);
v___x_5491_ = lean_array_fget(v_array_5460_, v_start_5461_);
v___x_5492_ = lean_nat_add(v_start_5461_, v___x_5407_);
lean_dec(v_start_5461_);
if (v_isShared_5487_ == 0)
{
lean_ctor_set(v___x_5486_, 1, v___x_5492_);
v___x_5494_ = v___x_5486_;
goto v_reusejp_5493_;
}
else
{
lean_object* v_reuseFailAlloc_5537_; 
v_reuseFailAlloc_5537_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5537_, 0, v_array_5460_);
lean_ctor_set(v_reuseFailAlloc_5537_, 1, v___x_5492_);
lean_ctor_set(v_reuseFailAlloc_5537_, 2, v_stop_5462_);
v___x_5494_ = v_reuseFailAlloc_5537_;
goto v_reusejp_5493_;
}
v_reusejp_5493_:
{
uint8_t v___x_5495_; 
v___x_5495_ = lean_nat_dec_lt(v_start_5489_, v_stop_5490_);
if (v___x_5495_ == 0)
{
lean_object* v___x_5497_; 
lean_dec(v___x_5491_);
lean_dec(v___x_5463_);
lean_dec(v___x_5435_);
lean_dec(v___x_5406_);
if (v_isShared_5378_ == 0)
{
lean_ctor_set(v___x_5377_, 1, v___x_5410_);
lean_ctor_set(v___x_5377_, 0, v___x_5438_);
v___x_5497_ = v___x_5377_;
goto v_reusejp_5496_;
}
else
{
lean_object* v_reuseFailAlloc_5512_; 
v_reuseFailAlloc_5512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5512_, 0, v___x_5438_);
lean_ctor_set(v_reuseFailAlloc_5512_, 1, v___x_5410_);
v___x_5497_ = v_reuseFailAlloc_5512_;
goto v_reusejp_5496_;
}
v_reusejp_5496_:
{
lean_object* v___x_5499_; 
if (v_isShared_5374_ == 0)
{
lean_ctor_set(v___x_5373_, 1, v___x_5497_);
lean_ctor_set(v___x_5373_, 0, v___x_5466_);
v___x_5499_ = v___x_5373_;
goto v_reusejp_5498_;
}
else
{
lean_object* v_reuseFailAlloc_5511_; 
v_reuseFailAlloc_5511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5511_, 0, v___x_5466_);
lean_ctor_set(v_reuseFailAlloc_5511_, 1, v___x_5497_);
v___x_5499_ = v_reuseFailAlloc_5511_;
goto v_reusejp_5498_;
}
v_reusejp_5498_:
{
lean_object* v___x_5501_; 
if (v_isShared_5370_ == 0)
{
lean_ctor_set(v___x_5369_, 1, v___x_5499_);
lean_ctor_set(v___x_5369_, 0, v___x_5494_);
v___x_5501_ = v___x_5369_;
goto v_reusejp_5500_;
}
else
{
lean_object* v_reuseFailAlloc_5510_; 
v_reuseFailAlloc_5510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5510_, 0, v___x_5494_);
lean_ctor_set(v_reuseFailAlloc_5510_, 1, v___x_5499_);
v___x_5501_ = v_reuseFailAlloc_5510_;
goto v_reusejp_5500_;
}
v_reusejp_5500_:
{
lean_object* v___x_5503_; 
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 1, v___x_5501_);
v___x_5503_ = v___x_5365_;
goto v_reusejp_5502_;
}
else
{
lean_object* v_reuseFailAlloc_5509_; 
v_reuseFailAlloc_5509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5509_, 0, v_fst_5363_);
lean_ctor_set(v_reuseFailAlloc_5509_, 1, v___x_5501_);
v___x_5503_ = v_reuseFailAlloc_5509_;
goto v_reusejp_5502_;
}
v_reusejp_5502_:
{
lean_object* v___x_5505_; 
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 1, v___x_5503_);
v___x_5505_ = v___x_5361_;
goto v_reusejp_5504_;
}
else
{
lean_object* v_reuseFailAlloc_5508_; 
v_reuseFailAlloc_5508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5508_, 0, v_fst_5359_);
lean_ctor_set(v_reuseFailAlloc_5508_, 1, v___x_5503_);
v___x_5505_ = v_reuseFailAlloc_5508_;
goto v_reusejp_5504_;
}
v_reusejp_5504_:
{
lean_object* v___x_5506_; lean_object* v___f_5507_; 
v___x_5506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5506_, 0, v___x_5505_);
v___f_5507_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5507_, 0, v___x_5506_);
v___y_5329_ = v___f_5507_;
goto v___jp_5328_;
}
}
}
}
}
}
else
{
lean_object* v___x_5514_; uint8_t v_isShared_5515_; uint8_t v_isSharedCheck_5533_; 
lean_inc(v_stop_5490_);
lean_inc(v_start_5489_);
lean_inc_ref(v_array_5488_);
lean_del_object(v___x_5377_);
lean_del_object(v___x_5373_);
lean_del_object(v___x_5369_);
lean_del_object(v___x_5365_);
lean_del_object(v___x_5361_);
v_isSharedCheck_5533_ = !lean_is_exclusive(v_fst_5363_);
if (v_isSharedCheck_5533_ == 0)
{
lean_object* v_unused_5534_; lean_object* v_unused_5535_; lean_object* v_unused_5536_; 
v_unused_5534_ = lean_ctor_get(v_fst_5363_, 2);
lean_dec(v_unused_5534_);
v_unused_5535_ = lean_ctor_get(v_fst_5363_, 1);
lean_dec(v_unused_5535_);
v_unused_5536_ = lean_ctor_get(v_fst_5363_, 0);
lean_dec(v_unused_5536_);
v___x_5514_ = v_fst_5363_;
v_isShared_5515_ = v_isSharedCheck_5533_;
goto v_resetjp_5513_;
}
else
{
lean_dec(v_fst_5363_);
v___x_5514_ = lean_box(0);
v_isShared_5515_ = v_isSharedCheck_5533_;
goto v_resetjp_5513_;
}
v_resetjp_5513_:
{
lean_object* v_numOverlaps_5516_; uint8_t v_hasUnitThunk_5517_; lean_object* v___x_5518_; uint8_t v___x_5519_; 
v_numOverlaps_5516_ = lean_ctor_get(v___x_5491_, 1);
v_hasUnitThunk_5517_ = lean_ctor_get_uint8(v___x_5491_, sizeof(void*)*2);
v___x_5518_ = lean_unsigned_to_nat(0u);
v___x_5519_ = lean_nat_dec_eq(v_numOverlaps_5516_, v___x_5518_);
if (v___x_5519_ == 0)
{
lean_object* v___x_5520_; lean_object* v___x_5521_; 
lean_del_object(v___x_5514_);
lean_dec_ref(v___x_5494_);
lean_dec(v___x_5491_);
lean_dec(v_stop_5490_);
lean_dec(v_start_5489_);
lean_dec_ref(v_array_5488_);
lean_dec_ref(v___x_5466_);
lean_dec(v___x_5463_);
lean_dec_ref(v___x_5438_);
lean_dec(v___x_5435_);
lean_dec_ref(v___x_5410_);
lean_dec(v___x_5406_);
lean_dec(v_fst_5359_);
v___x_5520_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9);
v___x_5521_ = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed), 6, 1);
lean_closure_set(v___x_5521_, 0, v___x_5520_);
v___y_5329_ = v___x_5521_;
goto v___jp_5328_;
}
else
{
uint8_t v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___f_5527_; lean_object* v___x_5528_; lean_object* v___x_5530_; 
v___x_5522_ = 0;
v___x_5523_ = lean_array_fget_borrowed(v_array_5488_, v_start_5489_);
v___x_5524_ = lean_box(v___x_5522_);
v___x_5525_ = lean_box(v_useSplitter_5318_);
v___x_5526_ = lean_box(v_hasUnitThunk_5517_);
lean_inc(v_numDiscrEqs_5320_);
lean_inc(v_extraEqualities_5319_);
lean_inc(v___x_5523_);
lean_inc(v_a_5321_);
lean_inc_ref(v_onAlt_5317_);
v___f_5527_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed), 18, 11);
lean_closure_set(v___f_5527_, 0, v___x_5463_);
lean_closure_set(v___f_5527_, 1, v___x_5406_);
lean_closure_set(v___f_5527_, 2, v_onAlt_5317_);
lean_closure_set(v___f_5527_, 3, v_a_5321_);
lean_closure_set(v___f_5527_, 4, v___x_5524_);
lean_closure_set(v___f_5527_, 5, v___x_5525_);
lean_closure_set(v___f_5527_, 6, v___x_5523_);
lean_closure_set(v___f_5527_, 7, v_extraEqualities_5319_);
lean_closure_set(v___f_5527_, 8, v_numDiscrEqs_5320_);
lean_closure_set(v___f_5527_, 9, v___x_5526_);
lean_closure_set(v___f_5527_, 10, v___x_5407_);
v___x_5528_ = lean_nat_add(v_start_5489_, v___x_5407_);
lean_dec(v_start_5489_);
if (v_isShared_5515_ == 0)
{
lean_ctor_set(v___x_5514_, 1, v___x_5528_);
v___x_5530_ = v___x_5514_;
goto v_reusejp_5529_;
}
else
{
lean_object* v_reuseFailAlloc_5532_; 
v_reuseFailAlloc_5532_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5532_, 0, v_array_5488_);
lean_ctor_set(v_reuseFailAlloc_5532_, 1, v___x_5528_);
lean_ctor_set(v_reuseFailAlloc_5532_, 2, v_stop_5490_);
v___x_5530_ = v_reuseFailAlloc_5532_;
goto v_reusejp_5529_;
}
v_reusejp_5529_:
{
lean_object* v___f_5531_; 
v___f_5531_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed), 14, 9);
lean_closure_set(v___f_5531_, 0, v___x_5435_);
lean_closure_set(v___f_5531_, 1, v___x_5491_);
lean_closure_set(v___f_5531_, 2, v___f_5527_);
lean_closure_set(v___f_5531_, 3, v_fst_5359_);
lean_closure_set(v___f_5531_, 4, v___x_5438_);
lean_closure_set(v___f_5531_, 5, v___x_5410_);
lean_closure_set(v___f_5531_, 6, v___x_5466_);
lean_closure_set(v___f_5531_, 7, v___x_5494_);
lean_closure_set(v___f_5531_, 8, v___x_5530_);
v___y_5329_ = v___f_5531_;
goto v___jp_5328_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_5328_:
{
lean_object* v___x_5330_; 
lean_inc(v___y_5326_);
lean_inc_ref(v___y_5325_);
lean_inc(v___y_5324_);
lean_inc_ref(v___y_5323_);
v___x_5330_ = lean_apply_5(v___y_5329_, v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_, lean_box(0));
if (lean_obj_tag(v___x_5330_) == 0)
{
lean_object* v_a_5331_; lean_object* v___x_5333_; uint8_t v_isShared_5334_; uint8_t v_isSharedCheck_5343_; 
v_a_5331_ = lean_ctor_get(v___x_5330_, 0);
v_isSharedCheck_5343_ = !lean_is_exclusive(v___x_5330_);
if (v_isSharedCheck_5343_ == 0)
{
v___x_5333_ = v___x_5330_;
v_isShared_5334_ = v_isSharedCheck_5343_;
goto v_resetjp_5332_;
}
else
{
lean_inc(v_a_5331_);
lean_dec(v___x_5330_);
v___x_5333_ = lean_box(0);
v_isShared_5334_ = v_isSharedCheck_5343_;
goto v_resetjp_5332_;
}
v_resetjp_5332_:
{
if (lean_obj_tag(v_a_5331_) == 0)
{
lean_object* v_a_5335_; lean_object* v___x_5337_; 
lean_dec(v_a_5321_);
lean_dec(v_numDiscrEqs_5320_);
lean_dec(v_extraEqualities_5319_);
lean_dec_ref(v_onAlt_5317_);
v_a_5335_ = lean_ctor_get(v_a_5331_, 0);
lean_inc(v_a_5335_);
lean_dec_ref(v_a_5331_);
if (v_isShared_5334_ == 0)
{
lean_ctor_set(v___x_5333_, 0, v_a_5335_);
v___x_5337_ = v___x_5333_;
goto v_reusejp_5336_;
}
else
{
lean_object* v_reuseFailAlloc_5338_; 
v_reuseFailAlloc_5338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5338_, 0, v_a_5335_);
v___x_5337_ = v_reuseFailAlloc_5338_;
goto v_reusejp_5336_;
}
v_reusejp_5336_:
{
return v___x_5337_;
}
}
else
{
lean_object* v_a_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; 
lean_del_object(v___x_5333_);
v_a_5339_ = lean_ctor_get(v_a_5331_, 0);
lean_inc(v_a_5339_);
lean_dec_ref(v_a_5331_);
v___x_5340_ = lean_unsigned_to_nat(1u);
v___x_5341_ = lean_nat_add(v_a_5321_, v___x_5340_);
lean_dec(v_a_5321_);
v_a_5321_ = v___x_5341_;
v_b_5322_ = v_a_5339_;
goto _start;
}
}
}
else
{
lean_object* v_a_5344_; lean_object* v___x_5346_; uint8_t v_isShared_5347_; uint8_t v_isSharedCheck_5351_; 
lean_dec(v_a_5321_);
lean_dec(v_numDiscrEqs_5320_);
lean_dec(v_extraEqualities_5319_);
lean_dec_ref(v_onAlt_5317_);
v_a_5344_ = lean_ctor_get(v___x_5330_, 0);
v_isSharedCheck_5351_ = !lean_is_exclusive(v___x_5330_);
if (v_isSharedCheck_5351_ == 0)
{
v___x_5346_ = v___x_5330_;
v_isShared_5347_ = v_isSharedCheck_5351_;
goto v_resetjp_5345_;
}
else
{
lean_inc(v_a_5344_);
lean_dec(v___x_5330_);
v___x_5346_ = lean_box(0);
v_isShared_5347_ = v_isSharedCheck_5351_;
goto v_resetjp_5345_;
}
v_resetjp_5345_:
{
lean_object* v___x_5349_; 
if (v_isShared_5347_ == 0)
{
v___x_5349_ = v___x_5346_;
goto v_reusejp_5348_;
}
else
{
lean_object* v_reuseFailAlloc_5350_; 
v_reuseFailAlloc_5350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5350_, 0, v_a_5344_);
v___x_5349_ = v_reuseFailAlloc_5350_;
goto v_reusejp_5348_;
}
v_reusejp_5348_:
{
return v___x_5349_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___boxed(lean_object* v_upperBound_5567_, lean_object* v_onAlt_5568_, lean_object* v_useSplitter_5569_, lean_object* v_extraEqualities_5570_, lean_object* v_numDiscrEqs_5571_, lean_object* v_a_5572_, lean_object* v_b_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_, lean_object* v___y_5576_, lean_object* v___y_5577_, lean_object* v___y_5578_){
_start:
{
uint8_t v_useSplitter_boxed_5579_; lean_object* v_res_5580_; 
v_useSplitter_boxed_5579_ = lean_unbox(v_useSplitter_5569_);
v_res_5580_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v_upperBound_5567_, v_onAlt_5568_, v_useSplitter_boxed_5579_, v_extraEqualities_5570_, v_numDiscrEqs_5571_, v_a_5572_, v_b_5573_, v___y_5574_, v___y_5575_, v___y_5576_, v___y_5577_);
lean_dec(v___y_5577_);
lean_dec_ref(v___y_5576_);
lean_dec(v___y_5575_);
lean_dec_ref(v___y_5574_);
lean_dec(v_upperBound_5567_);
return v_res_5580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(uint8_t v_addEqualities_5581_, lean_object* v_as_5582_, size_t v_sz_5583_, size_t v_i_5584_, lean_object* v_b_5585_, lean_object* v___y_5586_, lean_object* v___y_5587_, lean_object* v___y_5588_, lean_object* v___y_5589_){
_start:
{
lean_object* v_a_5592_; uint8_t v___x_5596_; 
v___x_5596_ = lean_usize_dec_lt(v_i_5584_, v_sz_5583_);
if (v___x_5596_ == 0)
{
lean_object* v___x_5597_; 
v___x_5597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5597_, 0, v_b_5585_);
return v___x_5597_;
}
else
{
lean_object* v_snd_5598_; lean_object* v_snd_5599_; lean_object* v_snd_5600_; lean_object* v_snd_5601_; lean_object* v_fst_5602_; lean_object* v___x_5604_; uint8_t v_isShared_5605_; uint8_t v_isSharedCheck_5748_; 
v_snd_5598_ = lean_ctor_get(v_b_5585_, 1);
lean_inc(v_snd_5598_);
v_snd_5599_ = lean_ctor_get(v_snd_5598_, 1);
lean_inc(v_snd_5599_);
v_snd_5600_ = lean_ctor_get(v_snd_5599_, 1);
lean_inc(v_snd_5600_);
v_snd_5601_ = lean_ctor_get(v_snd_5600_, 1);
lean_inc(v_snd_5601_);
v_fst_5602_ = lean_ctor_get(v_b_5585_, 0);
v_isSharedCheck_5748_ = !lean_is_exclusive(v_b_5585_);
if (v_isSharedCheck_5748_ == 0)
{
lean_object* v_unused_5749_; 
v_unused_5749_ = lean_ctor_get(v_b_5585_, 1);
lean_dec(v_unused_5749_);
v___x_5604_ = v_b_5585_;
v_isShared_5605_ = v_isSharedCheck_5748_;
goto v_resetjp_5603_;
}
else
{
lean_inc(v_fst_5602_);
lean_dec(v_b_5585_);
v___x_5604_ = lean_box(0);
v_isShared_5605_ = v_isSharedCheck_5748_;
goto v_resetjp_5603_;
}
v_resetjp_5603_:
{
lean_object* v_fst_5606_; lean_object* v___x_5608_; uint8_t v_isShared_5609_; uint8_t v_isSharedCheck_5746_; 
v_fst_5606_ = lean_ctor_get(v_snd_5598_, 0);
v_isSharedCheck_5746_ = !lean_is_exclusive(v_snd_5598_);
if (v_isSharedCheck_5746_ == 0)
{
lean_object* v_unused_5747_; 
v_unused_5747_ = lean_ctor_get(v_snd_5598_, 1);
lean_dec(v_unused_5747_);
v___x_5608_ = v_snd_5598_;
v_isShared_5609_ = v_isSharedCheck_5746_;
goto v_resetjp_5607_;
}
else
{
lean_inc(v_fst_5606_);
lean_dec(v_snd_5598_);
v___x_5608_ = lean_box(0);
v_isShared_5609_ = v_isSharedCheck_5746_;
goto v_resetjp_5607_;
}
v_resetjp_5607_:
{
lean_object* v_fst_5610_; lean_object* v___x_5612_; uint8_t v_isShared_5613_; uint8_t v_isSharedCheck_5744_; 
v_fst_5610_ = lean_ctor_get(v_snd_5599_, 0);
v_isSharedCheck_5744_ = !lean_is_exclusive(v_snd_5599_);
if (v_isSharedCheck_5744_ == 0)
{
lean_object* v_unused_5745_; 
v_unused_5745_ = lean_ctor_get(v_snd_5599_, 1);
lean_dec(v_unused_5745_);
v___x_5612_ = v_snd_5599_;
v_isShared_5613_ = v_isSharedCheck_5744_;
goto v_resetjp_5611_;
}
else
{
lean_inc(v_fst_5610_);
lean_dec(v_snd_5599_);
v___x_5612_ = lean_box(0);
v_isShared_5613_ = v_isSharedCheck_5744_;
goto v_resetjp_5611_;
}
v_resetjp_5611_:
{
lean_object* v_fst_5614_; lean_object* v___x_5616_; uint8_t v_isShared_5617_; uint8_t v_isSharedCheck_5742_; 
v_fst_5614_ = lean_ctor_get(v_snd_5600_, 0);
v_isSharedCheck_5742_ = !lean_is_exclusive(v_snd_5600_);
if (v_isSharedCheck_5742_ == 0)
{
lean_object* v_unused_5743_; 
v_unused_5743_ = lean_ctor_get(v_snd_5600_, 1);
lean_dec(v_unused_5743_);
v___x_5616_ = v_snd_5600_;
v_isShared_5617_ = v_isSharedCheck_5742_;
goto v_resetjp_5615_;
}
else
{
lean_inc(v_fst_5614_);
lean_dec(v_snd_5600_);
v___x_5616_ = lean_box(0);
v_isShared_5617_ = v_isSharedCheck_5742_;
goto v_resetjp_5615_;
}
v_resetjp_5615_:
{
lean_object* v_array_5618_; lean_object* v_start_5619_; lean_object* v_stop_5620_; uint8_t v___x_5621_; 
v_array_5618_ = lean_ctor_get(v_snd_5601_, 0);
v_start_5619_ = lean_ctor_get(v_snd_5601_, 1);
v_stop_5620_ = lean_ctor_get(v_snd_5601_, 2);
v___x_5621_ = lean_nat_dec_lt(v_start_5619_, v_stop_5620_);
if (v___x_5621_ == 0)
{
lean_object* v___x_5623_; 
if (v_isShared_5617_ == 0)
{
v___x_5623_ = v___x_5616_;
goto v_reusejp_5622_;
}
else
{
lean_object* v_reuseFailAlloc_5634_; 
v_reuseFailAlloc_5634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5634_, 0, v_fst_5614_);
lean_ctor_set(v_reuseFailAlloc_5634_, 1, v_snd_5601_);
v___x_5623_ = v_reuseFailAlloc_5634_;
goto v_reusejp_5622_;
}
v_reusejp_5622_:
{
lean_object* v___x_5625_; 
if (v_isShared_5613_ == 0)
{
lean_ctor_set(v___x_5612_, 1, v___x_5623_);
v___x_5625_ = v___x_5612_;
goto v_reusejp_5624_;
}
else
{
lean_object* v_reuseFailAlloc_5633_; 
v_reuseFailAlloc_5633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5633_, 0, v_fst_5610_);
lean_ctor_set(v_reuseFailAlloc_5633_, 1, v___x_5623_);
v___x_5625_ = v_reuseFailAlloc_5633_;
goto v_reusejp_5624_;
}
v_reusejp_5624_:
{
lean_object* v___x_5627_; 
if (v_isShared_5609_ == 0)
{
lean_ctor_set(v___x_5608_, 1, v___x_5625_);
v___x_5627_ = v___x_5608_;
goto v_reusejp_5626_;
}
else
{
lean_object* v_reuseFailAlloc_5632_; 
v_reuseFailAlloc_5632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5632_, 0, v_fst_5606_);
lean_ctor_set(v_reuseFailAlloc_5632_, 1, v___x_5625_);
v___x_5627_ = v_reuseFailAlloc_5632_;
goto v_reusejp_5626_;
}
v_reusejp_5626_:
{
lean_object* v___x_5629_; 
if (v_isShared_5605_ == 0)
{
lean_ctor_set(v___x_5604_, 1, v___x_5627_);
v___x_5629_ = v___x_5604_;
goto v_reusejp_5628_;
}
else
{
lean_object* v_reuseFailAlloc_5631_; 
v_reuseFailAlloc_5631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5631_, 0, v_fst_5602_);
lean_ctor_set(v_reuseFailAlloc_5631_, 1, v___x_5627_);
v___x_5629_ = v_reuseFailAlloc_5631_;
goto v_reusejp_5628_;
}
v_reusejp_5628_:
{
lean_object* v___x_5630_; 
v___x_5630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5630_, 0, v___x_5629_);
return v___x_5630_;
}
}
}
}
}
else
{
lean_object* v___x_5636_; uint8_t v_isShared_5637_; uint8_t v_isSharedCheck_5738_; 
lean_inc(v_stop_5620_);
lean_inc(v_start_5619_);
lean_inc_ref(v_array_5618_);
v_isSharedCheck_5738_ = !lean_is_exclusive(v_snd_5601_);
if (v_isSharedCheck_5738_ == 0)
{
lean_object* v_unused_5739_; lean_object* v_unused_5740_; lean_object* v_unused_5741_; 
v_unused_5739_ = lean_ctor_get(v_snd_5601_, 2);
lean_dec(v_unused_5739_);
v_unused_5740_ = lean_ctor_get(v_snd_5601_, 1);
lean_dec(v_unused_5740_);
v_unused_5741_ = lean_ctor_get(v_snd_5601_, 0);
lean_dec(v_unused_5741_);
v___x_5636_ = v_snd_5601_;
v_isShared_5637_ = v_isSharedCheck_5738_;
goto v_resetjp_5635_;
}
else
{
lean_dec(v_snd_5601_);
v___x_5636_ = lean_box(0);
v_isShared_5637_ = v_isSharedCheck_5738_;
goto v_resetjp_5635_;
}
v_resetjp_5635_:
{
lean_object* v_array_5638_; lean_object* v_start_5639_; lean_object* v_stop_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5645_; 
v_array_5638_ = lean_ctor_get(v_fst_5614_, 0);
v_start_5639_ = lean_ctor_get(v_fst_5614_, 1);
v_stop_5640_ = lean_ctor_get(v_fst_5614_, 2);
v___x_5641_ = lean_array_fget(v_array_5618_, v_start_5619_);
v___x_5642_ = lean_unsigned_to_nat(1u);
v___x_5643_ = lean_nat_add(v_start_5619_, v___x_5642_);
lean_dec(v_start_5619_);
if (v_isShared_5637_ == 0)
{
lean_ctor_set(v___x_5636_, 1, v___x_5643_);
v___x_5645_ = v___x_5636_;
goto v_reusejp_5644_;
}
else
{
lean_object* v_reuseFailAlloc_5737_; 
v_reuseFailAlloc_5737_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5737_, 0, v_array_5618_);
lean_ctor_set(v_reuseFailAlloc_5737_, 1, v___x_5643_);
lean_ctor_set(v_reuseFailAlloc_5737_, 2, v_stop_5620_);
v___x_5645_ = v_reuseFailAlloc_5737_;
goto v_reusejp_5644_;
}
v_reusejp_5644_:
{
uint8_t v___x_5646_; 
v___x_5646_ = lean_nat_dec_lt(v_start_5639_, v_stop_5640_);
if (v___x_5646_ == 0)
{
lean_object* v___x_5648_; 
lean_dec(v___x_5641_);
if (v_isShared_5617_ == 0)
{
lean_ctor_set(v___x_5616_, 1, v___x_5645_);
v___x_5648_ = v___x_5616_;
goto v_reusejp_5647_;
}
else
{
lean_object* v_reuseFailAlloc_5659_; 
v_reuseFailAlloc_5659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5659_, 0, v_fst_5614_);
lean_ctor_set(v_reuseFailAlloc_5659_, 1, v___x_5645_);
v___x_5648_ = v_reuseFailAlloc_5659_;
goto v_reusejp_5647_;
}
v_reusejp_5647_:
{
lean_object* v___x_5650_; 
if (v_isShared_5613_ == 0)
{
lean_ctor_set(v___x_5612_, 1, v___x_5648_);
v___x_5650_ = v___x_5612_;
goto v_reusejp_5649_;
}
else
{
lean_object* v_reuseFailAlloc_5658_; 
v_reuseFailAlloc_5658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5658_, 0, v_fst_5610_);
lean_ctor_set(v_reuseFailAlloc_5658_, 1, v___x_5648_);
v___x_5650_ = v_reuseFailAlloc_5658_;
goto v_reusejp_5649_;
}
v_reusejp_5649_:
{
lean_object* v___x_5652_; 
if (v_isShared_5609_ == 0)
{
lean_ctor_set(v___x_5608_, 1, v___x_5650_);
v___x_5652_ = v___x_5608_;
goto v_reusejp_5651_;
}
else
{
lean_object* v_reuseFailAlloc_5657_; 
v_reuseFailAlloc_5657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5657_, 0, v_fst_5606_);
lean_ctor_set(v_reuseFailAlloc_5657_, 1, v___x_5650_);
v___x_5652_ = v_reuseFailAlloc_5657_;
goto v_reusejp_5651_;
}
v_reusejp_5651_:
{
lean_object* v___x_5654_; 
if (v_isShared_5605_ == 0)
{
lean_ctor_set(v___x_5604_, 1, v___x_5652_);
v___x_5654_ = v___x_5604_;
goto v_reusejp_5653_;
}
else
{
lean_object* v_reuseFailAlloc_5656_; 
v_reuseFailAlloc_5656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5656_, 0, v_fst_5602_);
lean_ctor_set(v_reuseFailAlloc_5656_, 1, v___x_5652_);
v___x_5654_ = v_reuseFailAlloc_5656_;
goto v_reusejp_5653_;
}
v_reusejp_5653_:
{
lean_object* v___x_5655_; 
v___x_5655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5655_, 0, v___x_5654_);
return v___x_5655_;
}
}
}
}
}
else
{
lean_object* v___x_5661_; uint8_t v_isShared_5662_; uint8_t v_isSharedCheck_5733_; 
lean_inc(v_stop_5640_);
lean_inc(v_start_5639_);
lean_inc_ref(v_array_5638_);
v_isSharedCheck_5733_ = !lean_is_exclusive(v_fst_5614_);
if (v_isSharedCheck_5733_ == 0)
{
lean_object* v_unused_5734_; lean_object* v_unused_5735_; lean_object* v_unused_5736_; 
v_unused_5734_ = lean_ctor_get(v_fst_5614_, 2);
lean_dec(v_unused_5734_);
v_unused_5735_ = lean_ctor_get(v_fst_5614_, 1);
lean_dec(v_unused_5735_);
v_unused_5736_ = lean_ctor_get(v_fst_5614_, 0);
lean_dec(v_unused_5736_);
v___x_5661_ = v_fst_5614_;
v_isShared_5662_ = v_isSharedCheck_5733_;
goto v_resetjp_5660_;
}
else
{
lean_dec(v_fst_5614_);
v___x_5661_ = lean_box(0);
v_isShared_5662_ = v_isSharedCheck_5733_;
goto v_resetjp_5660_;
}
v_resetjp_5660_:
{
lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5666_; 
v___x_5663_ = lean_array_fget(v_array_5638_, v_start_5639_);
v___x_5664_ = lean_nat_add(v_start_5639_, v___x_5642_);
lean_dec(v_start_5639_);
if (v_isShared_5662_ == 0)
{
lean_ctor_set(v___x_5661_, 1, v___x_5664_);
v___x_5666_ = v___x_5661_;
goto v_reusejp_5665_;
}
else
{
lean_object* v_reuseFailAlloc_5732_; 
v_reuseFailAlloc_5732_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5732_, 0, v_array_5638_);
lean_ctor_set(v_reuseFailAlloc_5732_, 1, v___x_5664_);
lean_ctor_set(v_reuseFailAlloc_5732_, 2, v_stop_5640_);
v___x_5666_ = v_reuseFailAlloc_5732_;
goto v_reusejp_5665_;
}
v_reusejp_5665_:
{
if (v_addEqualities_5581_ == 0)
{
lean_dec(v___x_5663_);
goto v___jp_5667_;
}
else
{
if (lean_obj_tag(v___x_5641_) == 0)
{
lean_object* v_a_5683_; lean_object* v___x_5684_; 
lean_del_object(v___x_5616_);
lean_del_object(v___x_5612_);
lean_del_object(v___x_5608_);
lean_del_object(v___x_5604_);
v_a_5683_ = lean_array_uget_borrowed(v_as_5582_, v_i_5584_);
lean_inc(v_a_5683_);
v___x_5684_ = l_Lean_Meta_isProof(v_a_5683_, v___y_5586_, v___y_5587_, v___y_5588_, v___y_5589_);
if (lean_obj_tag(v___x_5684_) == 0)
{
lean_object* v_a_5685_; uint8_t v___x_5686_; 
v_a_5685_ = lean_ctor_get(v___x_5684_, 0);
lean_inc(v_a_5685_);
lean_dec_ref(v___x_5684_);
v___x_5686_ = lean_unbox(v_a_5685_);
lean_dec(v_a_5685_);
if (v___x_5686_ == 0)
{
lean_object* v___x_5687_; 
lean_inc(v_a_5683_);
v___x_5687_ = l_Lean_Meta_mkEqHEq(v___x_5663_, v_a_5683_, v___y_5586_, v___y_5587_, v___y_5588_, v___y_5589_);
if (lean_obj_tag(v___x_5687_) == 0)
{
lean_object* v_a_5688_; lean_object* v___x_5689_; 
v_a_5688_ = lean_ctor_get(v___x_5687_, 0);
lean_inc_n(v_a_5688_, 2);
lean_dec_ref(v___x_5687_);
v___x_5689_ = l_Lean_mkArrow(v_a_5688_, v_fst_5602_, v___y_5588_, v___y_5589_);
if (lean_obj_tag(v___x_5689_) == 0)
{
lean_object* v_a_5690_; uint8_t v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; 
v_a_5690_ = lean_ctor_get(v___x_5689_, 0);
lean_inc(v_a_5690_);
lean_dec_ref(v___x_5689_);
v___x_5691_ = l_Lean_Expr_isHEq(v_a_5688_);
lean_dec(v_a_5688_);
v___x_5692_ = lean_box(v___x_5691_);
v___x_5693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5693_, 0, v___x_5692_);
v___x_5694_ = lean_array_push(v_fst_5606_, v___x_5693_);
v___x_5695_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9___closed__0));
v___x_5696_ = lean_array_push(v_fst_5610_, v___x_5695_);
v___x_5697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5697_, 0, v___x_5666_);
lean_ctor_set(v___x_5697_, 1, v___x_5645_);
v___x_5698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5698_, 0, v___x_5696_);
lean_ctor_set(v___x_5698_, 1, v___x_5697_);
v___x_5699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5699_, 0, v___x_5694_);
lean_ctor_set(v___x_5699_, 1, v___x_5698_);
v___x_5700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5700_, 0, v_a_5690_);
lean_ctor_set(v___x_5700_, 1, v___x_5699_);
v_a_5592_ = v___x_5700_;
goto v___jp_5591_;
}
else
{
lean_object* v_a_5701_; lean_object* v___x_5703_; uint8_t v_isShared_5704_; uint8_t v_isSharedCheck_5708_; 
lean_dec(v_a_5688_);
lean_dec_ref(v___x_5666_);
lean_dec_ref(v___x_5645_);
lean_dec(v_fst_5610_);
lean_dec(v_fst_5606_);
v_a_5701_ = lean_ctor_get(v___x_5689_, 0);
v_isSharedCheck_5708_ = !lean_is_exclusive(v___x_5689_);
if (v_isSharedCheck_5708_ == 0)
{
v___x_5703_ = v___x_5689_;
v_isShared_5704_ = v_isSharedCheck_5708_;
goto v_resetjp_5702_;
}
else
{
lean_inc(v_a_5701_);
lean_dec(v___x_5689_);
v___x_5703_ = lean_box(0);
v_isShared_5704_ = v_isSharedCheck_5708_;
goto v_resetjp_5702_;
}
v_resetjp_5702_:
{
lean_object* v___x_5706_; 
if (v_isShared_5704_ == 0)
{
v___x_5706_ = v___x_5703_;
goto v_reusejp_5705_;
}
else
{
lean_object* v_reuseFailAlloc_5707_; 
v_reuseFailAlloc_5707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5707_, 0, v_a_5701_);
v___x_5706_ = v_reuseFailAlloc_5707_;
goto v_reusejp_5705_;
}
v_reusejp_5705_:
{
return v___x_5706_;
}
}
}
}
else
{
lean_object* v_a_5709_; lean_object* v___x_5711_; uint8_t v_isShared_5712_; uint8_t v_isSharedCheck_5716_; 
lean_dec_ref(v___x_5666_);
lean_dec_ref(v___x_5645_);
lean_dec(v_fst_5610_);
lean_dec(v_fst_5606_);
lean_dec(v_fst_5602_);
v_a_5709_ = lean_ctor_get(v___x_5687_, 0);
v_isSharedCheck_5716_ = !lean_is_exclusive(v___x_5687_);
if (v_isSharedCheck_5716_ == 0)
{
v___x_5711_ = v___x_5687_;
v_isShared_5712_ = v_isSharedCheck_5716_;
goto v_resetjp_5710_;
}
else
{
lean_inc(v_a_5709_);
lean_dec(v___x_5687_);
v___x_5711_ = lean_box(0);
v_isShared_5712_ = v_isSharedCheck_5716_;
goto v_resetjp_5710_;
}
v_resetjp_5710_:
{
lean_object* v___x_5714_; 
if (v_isShared_5712_ == 0)
{
v___x_5714_ = v___x_5711_;
goto v_reusejp_5713_;
}
else
{
lean_object* v_reuseFailAlloc_5715_; 
v_reuseFailAlloc_5715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5715_, 0, v_a_5709_);
v___x_5714_ = v_reuseFailAlloc_5715_;
goto v_reusejp_5713_;
}
v_reusejp_5713_:
{
return v___x_5714_;
}
}
}
}
else
{
lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; 
lean_dec(v___x_5663_);
v___x_5717_ = lean_box(0);
v___x_5718_ = lean_array_push(v_fst_5606_, v___x_5717_);
v___x_5719_ = lean_array_push(v_fst_5610_, v___x_5641_);
v___x_5720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5720_, 0, v___x_5666_);
lean_ctor_set(v___x_5720_, 1, v___x_5645_);
v___x_5721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5721_, 0, v___x_5719_);
lean_ctor_set(v___x_5721_, 1, v___x_5720_);
v___x_5722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5722_, 0, v___x_5718_);
lean_ctor_set(v___x_5722_, 1, v___x_5721_);
v___x_5723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5723_, 0, v_fst_5602_);
lean_ctor_set(v___x_5723_, 1, v___x_5722_);
v_a_5592_ = v___x_5723_;
goto v___jp_5591_;
}
}
else
{
lean_object* v_a_5724_; lean_object* v___x_5726_; uint8_t v_isShared_5727_; uint8_t v_isSharedCheck_5731_; 
lean_dec_ref(v___x_5666_);
lean_dec(v___x_5663_);
lean_dec_ref(v___x_5645_);
lean_dec(v_fst_5610_);
lean_dec(v_fst_5606_);
lean_dec(v_fst_5602_);
v_a_5724_ = lean_ctor_get(v___x_5684_, 0);
v_isSharedCheck_5731_ = !lean_is_exclusive(v___x_5684_);
if (v_isSharedCheck_5731_ == 0)
{
v___x_5726_ = v___x_5684_;
v_isShared_5727_ = v_isSharedCheck_5731_;
goto v_resetjp_5725_;
}
else
{
lean_inc(v_a_5724_);
lean_dec(v___x_5684_);
v___x_5726_ = lean_box(0);
v_isShared_5727_ = v_isSharedCheck_5731_;
goto v_resetjp_5725_;
}
v_resetjp_5725_:
{
lean_object* v___x_5729_; 
if (v_isShared_5727_ == 0)
{
v___x_5729_ = v___x_5726_;
goto v_reusejp_5728_;
}
else
{
lean_object* v_reuseFailAlloc_5730_; 
v_reuseFailAlloc_5730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5730_, 0, v_a_5724_);
v___x_5729_ = v_reuseFailAlloc_5730_;
goto v_reusejp_5728_;
}
v_reusejp_5728_:
{
return v___x_5729_;
}
}
}
}
else
{
lean_dec(v___x_5663_);
goto v___jp_5667_;
}
}
v___jp_5667_:
{
lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5672_; 
v___x_5668_ = lean_box(0);
v___x_5669_ = lean_array_push(v_fst_5606_, v___x_5668_);
v___x_5670_ = lean_array_push(v_fst_5610_, v___x_5641_);
if (v_isShared_5617_ == 0)
{
lean_ctor_set(v___x_5616_, 1, v___x_5645_);
lean_ctor_set(v___x_5616_, 0, v___x_5666_);
v___x_5672_ = v___x_5616_;
goto v_reusejp_5671_;
}
else
{
lean_object* v_reuseFailAlloc_5682_; 
v_reuseFailAlloc_5682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5682_, 0, v___x_5666_);
lean_ctor_set(v_reuseFailAlloc_5682_, 1, v___x_5645_);
v___x_5672_ = v_reuseFailAlloc_5682_;
goto v_reusejp_5671_;
}
v_reusejp_5671_:
{
lean_object* v___x_5674_; 
if (v_isShared_5613_ == 0)
{
lean_ctor_set(v___x_5612_, 1, v___x_5672_);
lean_ctor_set(v___x_5612_, 0, v___x_5670_);
v___x_5674_ = v___x_5612_;
goto v_reusejp_5673_;
}
else
{
lean_object* v_reuseFailAlloc_5681_; 
v_reuseFailAlloc_5681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5681_, 0, v___x_5670_);
lean_ctor_set(v_reuseFailAlloc_5681_, 1, v___x_5672_);
v___x_5674_ = v_reuseFailAlloc_5681_;
goto v_reusejp_5673_;
}
v_reusejp_5673_:
{
lean_object* v___x_5676_; 
if (v_isShared_5609_ == 0)
{
lean_ctor_set(v___x_5608_, 1, v___x_5674_);
lean_ctor_set(v___x_5608_, 0, v___x_5669_);
v___x_5676_ = v___x_5608_;
goto v_reusejp_5675_;
}
else
{
lean_object* v_reuseFailAlloc_5680_; 
v_reuseFailAlloc_5680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5680_, 0, v___x_5669_);
lean_ctor_set(v_reuseFailAlloc_5680_, 1, v___x_5674_);
v___x_5676_ = v_reuseFailAlloc_5680_;
goto v_reusejp_5675_;
}
v_reusejp_5675_:
{
lean_object* v___x_5678_; 
if (v_isShared_5605_ == 0)
{
lean_ctor_set(v___x_5604_, 1, v___x_5676_);
v___x_5678_ = v___x_5604_;
goto v_reusejp_5677_;
}
else
{
lean_object* v_reuseFailAlloc_5679_; 
v_reuseFailAlloc_5679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5679_, 0, v_fst_5602_);
lean_ctor_set(v_reuseFailAlloc_5679_, 1, v___x_5676_);
v___x_5678_ = v_reuseFailAlloc_5679_;
goto v_reusejp_5677_;
}
v_reusejp_5677_:
{
v_a_5592_ = v___x_5678_;
goto v___jp_5591_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_5591_:
{
size_t v___x_5593_; size_t v___x_5594_; 
v___x_5593_ = ((size_t)1ULL);
v___x_5594_ = lean_usize_add(v_i_5584_, v___x_5593_);
v_i_5584_ = v___x_5594_;
v_b_5585_ = v_a_5592_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7___boxed(lean_object* v_addEqualities_5750_, lean_object* v_as_5751_, lean_object* v_sz_5752_, lean_object* v_i_5753_, lean_object* v_b_5754_, lean_object* v___y_5755_, lean_object* v___y_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_){
_start:
{
uint8_t v_addEqualities_boxed_5760_; size_t v_sz_boxed_5761_; size_t v_i_boxed_5762_; lean_object* v_res_5763_; 
v_addEqualities_boxed_5760_ = lean_unbox(v_addEqualities_5750_);
v_sz_boxed_5761_ = lean_unbox_usize(v_sz_5752_);
lean_dec(v_sz_5752_);
v_i_boxed_5762_ = lean_unbox_usize(v_i_5753_);
lean_dec(v_i_5753_);
v_res_5763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(v_addEqualities_boxed_5760_, v_as_5751_, v_sz_boxed_5761_, v_i_boxed_5762_, v_b_5754_, v___y_5755_, v___y_5756_, v___y_5757_, v___y_5758_);
lean_dec(v___y_5758_);
lean_dec_ref(v___y_5757_);
lean_dec(v___y_5756_);
lean_dec_ref(v___y_5755_);
lean_dec_ref(v_as_5751_);
return v_res_5763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(lean_object* v_onMotive_5764_, lean_object* v_toMatcherInfo_5765_, lean_object* v_a_5766_, uint8_t v_addEqualities_5767_, size_t v___x_5768_, lean_object* v_discrs_5769_, lean_object* v_motiveArgs_5770_, lean_object* v_motiveBody_5771_, lean_object* v___y_5772_, lean_object* v___y_5773_, lean_object* v___y_5774_, lean_object* v___y_5775_){
_start:
{
lean_object* v___x_5869_; lean_object* v___x_5870_; uint8_t v___x_5871_; 
v___x_5869_ = lean_array_get_size(v_motiveArgs_5770_);
v___x_5870_ = lean_array_get_size(v_discrs_5769_);
v___x_5871_ = lean_nat_dec_eq(v___x_5869_, v___x_5870_);
if (v___x_5871_ == 0)
{
lean_object* v___x_5872_; lean_object* v___x_5873_; lean_object* v___x_5874_; lean_object* v___x_5875_; lean_object* v___x_5876_; lean_object* v___x_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; lean_object* v_a_5880_; lean_object* v___x_5882_; uint8_t v_isShared_5883_; uint8_t v_isSharedCheck_5887_; 
lean_dec_ref(v_motiveBody_5771_);
lean_dec_ref(v_motiveArgs_5770_);
lean_dec_ref(v_a_5766_);
lean_dec_ref(v_toMatcherInfo_5765_);
lean_dec_ref(v_onMotive_5764_);
v___x_5872_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_5873_ = l_Nat_reprFast(v___x_5870_);
v___x_5874_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5874_, 0, v___x_5873_);
v___x_5875_ = l_Lean_MessageData_ofFormat(v___x_5874_);
v___x_5876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5876_, 0, v___x_5872_);
lean_ctor_set(v___x_5876_, 1, v___x_5875_);
v___x_5877_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_5878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5878_, 0, v___x_5876_);
lean_ctor_set(v___x_5878_, 1, v___x_5877_);
v___x_5879_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_5878_, v___y_5772_, v___y_5773_, v___y_5774_, v___y_5775_);
v_a_5880_ = lean_ctor_get(v___x_5879_, 0);
v_isSharedCheck_5887_ = !lean_is_exclusive(v___x_5879_);
if (v_isSharedCheck_5887_ == 0)
{
v___x_5882_ = v___x_5879_;
v_isShared_5883_ = v_isSharedCheck_5887_;
goto v_resetjp_5881_;
}
else
{
lean_inc(v_a_5880_);
lean_dec(v___x_5879_);
v___x_5882_ = lean_box(0);
v_isShared_5883_ = v_isSharedCheck_5887_;
goto v_resetjp_5881_;
}
v_resetjp_5881_:
{
lean_object* v___x_5885_; 
if (v_isShared_5883_ == 0)
{
v___x_5885_ = v___x_5882_;
goto v_reusejp_5884_;
}
else
{
lean_object* v_reuseFailAlloc_5886_; 
v_reuseFailAlloc_5886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5886_, 0, v_a_5880_);
v___x_5885_ = v_reuseFailAlloc_5886_;
goto v_reusejp_5884_;
}
v_reusejp_5884_:
{
return v___x_5885_;
}
}
}
else
{
goto v___jp_5777_;
}
v___jp_5777_:
{
lean_object* v___x_5778_; 
lean_inc(v___y_5775_);
lean_inc_ref(v___y_5774_);
lean_inc(v___y_5773_);
lean_inc_ref(v___y_5772_);
lean_inc_ref(v_motiveArgs_5770_);
v___x_5778_ = lean_apply_7(v_onMotive_5764_, v_motiveArgs_5770_, v_motiveBody_5771_, v___y_5772_, v___y_5773_, v___y_5774_, v___y_5775_, lean_box(0));
if (lean_obj_tag(v___x_5778_) == 0)
{
lean_object* v_a_5779_; lean_object* v_discrInfos_5780_; lean_object* v___x_5781_; lean_object* v_addHEqualities_5782_; lean_object* v___x_5783_; lean_object* v___x_5784_; lean_object* v___x_5785_; lean_object* v___x_5786_; lean_object* v___x_5787_; lean_object* v___x_5788_; lean_object* v___x_5789_; lean_object* v___x_5790_; size_t v_sz_5791_; lean_object* v___x_5792_; 
v_a_5779_ = lean_ctor_get(v___x_5778_, 0);
lean_inc(v_a_5779_);
lean_dec_ref(v___x_5778_);
v_discrInfos_5780_ = lean_ctor_get(v_toMatcherInfo_5765_, 4);
lean_inc_ref(v_discrInfos_5780_);
lean_dec_ref(v_toMatcherInfo_5765_);
v___x_5781_ = lean_unsigned_to_nat(0u);
v_addHEqualities_5782_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___closed__0));
v___x_5783_ = lean_array_get_size(v_a_5766_);
v___x_5784_ = l_Array_toSubarray___redArg(v_a_5766_, v___x_5781_, v___x_5783_);
v___x_5785_ = lean_array_get_size(v_discrInfos_5780_);
v___x_5786_ = l_Array_toSubarray___redArg(v_discrInfos_5780_, v___x_5781_, v___x_5785_);
v___x_5787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5787_, 0, v___x_5784_);
lean_ctor_set(v___x_5787_, 1, v___x_5786_);
v___x_5788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5788_, 0, v_addHEqualities_5782_);
lean_ctor_set(v___x_5788_, 1, v___x_5787_);
v___x_5789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5789_, 0, v_addHEqualities_5782_);
lean_ctor_set(v___x_5789_, 1, v___x_5788_);
v___x_5790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5790_, 0, v_a_5779_);
lean_ctor_set(v___x_5790_, 1, v___x_5789_);
v_sz_5791_ = lean_array_size(v_motiveArgs_5770_);
v___x_5792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(v_addEqualities_5767_, v_motiveArgs_5770_, v_sz_5791_, v___x_5768_, v___x_5790_, v___y_5772_, v___y_5773_, v___y_5774_, v___y_5775_);
if (lean_obj_tag(v___x_5792_) == 0)
{
lean_object* v_a_5793_; lean_object* v_snd_5794_; lean_object* v_snd_5795_; lean_object* v_fst_5796_; lean_object* v___x_5798_; uint8_t v_isShared_5799_; uint8_t v_isSharedCheck_5851_; 
v_a_5793_ = lean_ctor_get(v___x_5792_, 0);
lean_inc(v_a_5793_);
lean_dec_ref(v___x_5792_);
v_snd_5794_ = lean_ctor_get(v_a_5793_, 1);
lean_inc(v_snd_5794_);
v_snd_5795_ = lean_ctor_get(v_snd_5794_, 1);
lean_inc(v_snd_5795_);
v_fst_5796_ = lean_ctor_get(v_a_5793_, 0);
v_isSharedCheck_5851_ = !lean_is_exclusive(v_a_5793_);
if (v_isSharedCheck_5851_ == 0)
{
lean_object* v_unused_5852_; 
v_unused_5852_ = lean_ctor_get(v_a_5793_, 1);
lean_dec(v_unused_5852_);
v___x_5798_ = v_a_5793_;
v_isShared_5799_ = v_isSharedCheck_5851_;
goto v_resetjp_5797_;
}
else
{
lean_inc(v_fst_5796_);
lean_dec(v_a_5793_);
v___x_5798_ = lean_box(0);
v_isShared_5799_ = v_isSharedCheck_5851_;
goto v_resetjp_5797_;
}
v_resetjp_5797_:
{
lean_object* v_fst_5800_; lean_object* v___x_5802_; uint8_t v_isShared_5803_; uint8_t v_isSharedCheck_5849_; 
v_fst_5800_ = lean_ctor_get(v_snd_5794_, 0);
v_isSharedCheck_5849_ = !lean_is_exclusive(v_snd_5794_);
if (v_isSharedCheck_5849_ == 0)
{
lean_object* v_unused_5850_; 
v_unused_5850_ = lean_ctor_get(v_snd_5794_, 1);
lean_dec(v_unused_5850_);
v___x_5802_ = v_snd_5794_;
v_isShared_5803_ = v_isSharedCheck_5849_;
goto v_resetjp_5801_;
}
else
{
lean_inc(v_fst_5800_);
lean_dec(v_snd_5794_);
v___x_5802_ = lean_box(0);
v_isShared_5803_ = v_isSharedCheck_5849_;
goto v_resetjp_5801_;
}
v_resetjp_5801_:
{
lean_object* v_fst_5804_; lean_object* v___x_5806_; uint8_t v_isShared_5807_; uint8_t v_isSharedCheck_5847_; 
v_fst_5804_ = lean_ctor_get(v_snd_5795_, 0);
v_isSharedCheck_5847_ = !lean_is_exclusive(v_snd_5795_);
if (v_isSharedCheck_5847_ == 0)
{
lean_object* v_unused_5848_; 
v_unused_5848_ = lean_ctor_get(v_snd_5795_, 1);
lean_dec(v_unused_5848_);
v___x_5806_ = v_snd_5795_;
v_isShared_5807_ = v_isSharedCheck_5847_;
goto v_resetjp_5805_;
}
else
{
lean_inc(v_fst_5804_);
lean_dec(v_snd_5795_);
v___x_5806_ = lean_box(0);
v_isShared_5807_ = v_isSharedCheck_5847_;
goto v_resetjp_5805_;
}
v_resetjp_5805_:
{
uint8_t v___x_5808_; uint8_t v___x_5809_; uint8_t v___x_5810_; lean_object* v___x_5811_; 
v___x_5808_ = 0;
v___x_5809_ = 1;
v___x_5810_ = 1;
lean_inc(v_fst_5796_);
v___x_5811_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_5770_, v_fst_5796_, v___x_5808_, v___x_5809_, v___x_5808_, v___x_5809_, v___x_5810_, v___y_5772_, v___y_5773_, v___y_5774_, v___y_5775_);
lean_dec_ref(v_motiveArgs_5770_);
if (lean_obj_tag(v___x_5811_) == 0)
{
lean_object* v_a_5812_; lean_object* v___x_5813_; 
v_a_5812_ = lean_ctor_get(v___x_5811_, 0);
lean_inc(v_a_5812_);
lean_dec_ref(v___x_5811_);
v___x_5813_ = l_Lean_Meta_getLevel(v_fst_5796_, v___y_5772_, v___y_5773_, v___y_5774_, v___y_5775_);
if (lean_obj_tag(v___x_5813_) == 0)
{
lean_object* v_a_5814_; lean_object* v___x_5816_; uint8_t v_isShared_5817_; uint8_t v_isSharedCheck_5830_; 
v_a_5814_ = lean_ctor_get(v___x_5813_, 0);
v_isSharedCheck_5830_ = !lean_is_exclusive(v___x_5813_);
if (v_isSharedCheck_5830_ == 0)
{
v___x_5816_ = v___x_5813_;
v_isShared_5817_ = v_isSharedCheck_5830_;
goto v_resetjp_5815_;
}
else
{
lean_inc(v_a_5814_);
lean_dec(v___x_5813_);
v___x_5816_ = lean_box(0);
v_isShared_5817_ = v_isSharedCheck_5830_;
goto v_resetjp_5815_;
}
v_resetjp_5815_:
{
lean_object* v___x_5819_; 
if (v_isShared_5807_ == 0)
{
lean_ctor_set(v___x_5806_, 1, v_fst_5804_);
lean_ctor_set(v___x_5806_, 0, v_fst_5800_);
v___x_5819_ = v___x_5806_;
goto v_reusejp_5818_;
}
else
{
lean_object* v_reuseFailAlloc_5829_; 
v_reuseFailAlloc_5829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5829_, 0, v_fst_5800_);
lean_ctor_set(v_reuseFailAlloc_5829_, 1, v_fst_5804_);
v___x_5819_ = v_reuseFailAlloc_5829_;
goto v_reusejp_5818_;
}
v_reusejp_5818_:
{
lean_object* v___x_5821_; 
if (v_isShared_5803_ == 0)
{
lean_ctor_set(v___x_5802_, 1, v___x_5819_);
lean_ctor_set(v___x_5802_, 0, v_a_5814_);
v___x_5821_ = v___x_5802_;
goto v_reusejp_5820_;
}
else
{
lean_object* v_reuseFailAlloc_5828_; 
v_reuseFailAlloc_5828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5828_, 0, v_a_5814_);
lean_ctor_set(v_reuseFailAlloc_5828_, 1, v___x_5819_);
v___x_5821_ = v_reuseFailAlloc_5828_;
goto v_reusejp_5820_;
}
v_reusejp_5820_:
{
lean_object* v___x_5823_; 
if (v_isShared_5799_ == 0)
{
lean_ctor_set(v___x_5798_, 1, v___x_5821_);
lean_ctor_set(v___x_5798_, 0, v_a_5812_);
v___x_5823_ = v___x_5798_;
goto v_reusejp_5822_;
}
else
{
lean_object* v_reuseFailAlloc_5827_; 
v_reuseFailAlloc_5827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5827_, 0, v_a_5812_);
lean_ctor_set(v_reuseFailAlloc_5827_, 1, v___x_5821_);
v___x_5823_ = v_reuseFailAlloc_5827_;
goto v_reusejp_5822_;
}
v_reusejp_5822_:
{
lean_object* v___x_5825_; 
if (v_isShared_5817_ == 0)
{
lean_ctor_set(v___x_5816_, 0, v___x_5823_);
v___x_5825_ = v___x_5816_;
goto v_reusejp_5824_;
}
else
{
lean_object* v_reuseFailAlloc_5826_; 
v_reuseFailAlloc_5826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5826_, 0, v___x_5823_);
v___x_5825_ = v_reuseFailAlloc_5826_;
goto v_reusejp_5824_;
}
v_reusejp_5824_:
{
return v___x_5825_;
}
}
}
}
}
}
else
{
lean_object* v_a_5831_; lean_object* v___x_5833_; uint8_t v_isShared_5834_; uint8_t v_isSharedCheck_5838_; 
lean_dec(v_a_5812_);
lean_del_object(v___x_5806_);
lean_dec(v_fst_5804_);
lean_del_object(v___x_5802_);
lean_dec(v_fst_5800_);
lean_del_object(v___x_5798_);
v_a_5831_ = lean_ctor_get(v___x_5813_, 0);
v_isSharedCheck_5838_ = !lean_is_exclusive(v___x_5813_);
if (v_isSharedCheck_5838_ == 0)
{
v___x_5833_ = v___x_5813_;
v_isShared_5834_ = v_isSharedCheck_5838_;
goto v_resetjp_5832_;
}
else
{
lean_inc(v_a_5831_);
lean_dec(v___x_5813_);
v___x_5833_ = lean_box(0);
v_isShared_5834_ = v_isSharedCheck_5838_;
goto v_resetjp_5832_;
}
v_resetjp_5832_:
{
lean_object* v___x_5836_; 
if (v_isShared_5834_ == 0)
{
v___x_5836_ = v___x_5833_;
goto v_reusejp_5835_;
}
else
{
lean_object* v_reuseFailAlloc_5837_; 
v_reuseFailAlloc_5837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5837_, 0, v_a_5831_);
v___x_5836_ = v_reuseFailAlloc_5837_;
goto v_reusejp_5835_;
}
v_reusejp_5835_:
{
return v___x_5836_;
}
}
}
}
else
{
lean_object* v_a_5839_; lean_object* v___x_5841_; uint8_t v_isShared_5842_; uint8_t v_isSharedCheck_5846_; 
lean_del_object(v___x_5806_);
lean_dec(v_fst_5804_);
lean_del_object(v___x_5802_);
lean_dec(v_fst_5800_);
lean_del_object(v___x_5798_);
lean_dec(v_fst_5796_);
v_a_5839_ = lean_ctor_get(v___x_5811_, 0);
v_isSharedCheck_5846_ = !lean_is_exclusive(v___x_5811_);
if (v_isSharedCheck_5846_ == 0)
{
v___x_5841_ = v___x_5811_;
v_isShared_5842_ = v_isSharedCheck_5846_;
goto v_resetjp_5840_;
}
else
{
lean_inc(v_a_5839_);
lean_dec(v___x_5811_);
v___x_5841_ = lean_box(0);
v_isShared_5842_ = v_isSharedCheck_5846_;
goto v_resetjp_5840_;
}
v_resetjp_5840_:
{
lean_object* v___x_5844_; 
if (v_isShared_5842_ == 0)
{
v___x_5844_ = v___x_5841_;
goto v_reusejp_5843_;
}
else
{
lean_object* v_reuseFailAlloc_5845_; 
v_reuseFailAlloc_5845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5845_, 0, v_a_5839_);
v___x_5844_ = v_reuseFailAlloc_5845_;
goto v_reusejp_5843_;
}
v_reusejp_5843_:
{
return v___x_5844_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5853_; lean_object* v___x_5855_; uint8_t v_isShared_5856_; uint8_t v_isSharedCheck_5860_; 
lean_dec_ref(v_motiveArgs_5770_);
v_a_5853_ = lean_ctor_get(v___x_5792_, 0);
v_isSharedCheck_5860_ = !lean_is_exclusive(v___x_5792_);
if (v_isSharedCheck_5860_ == 0)
{
v___x_5855_ = v___x_5792_;
v_isShared_5856_ = v_isSharedCheck_5860_;
goto v_resetjp_5854_;
}
else
{
lean_inc(v_a_5853_);
lean_dec(v___x_5792_);
v___x_5855_ = lean_box(0);
v_isShared_5856_ = v_isSharedCheck_5860_;
goto v_resetjp_5854_;
}
v_resetjp_5854_:
{
lean_object* v___x_5858_; 
if (v_isShared_5856_ == 0)
{
v___x_5858_ = v___x_5855_;
goto v_reusejp_5857_;
}
else
{
lean_object* v_reuseFailAlloc_5859_; 
v_reuseFailAlloc_5859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5859_, 0, v_a_5853_);
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
else
{
lean_object* v_a_5861_; lean_object* v___x_5863_; uint8_t v_isShared_5864_; uint8_t v_isSharedCheck_5868_; 
lean_dec_ref(v_motiveArgs_5770_);
lean_dec_ref(v_a_5766_);
lean_dec_ref(v_toMatcherInfo_5765_);
v_a_5861_ = lean_ctor_get(v___x_5778_, 0);
v_isSharedCheck_5868_ = !lean_is_exclusive(v___x_5778_);
if (v_isSharedCheck_5868_ == 0)
{
v___x_5863_ = v___x_5778_;
v_isShared_5864_ = v_isSharedCheck_5868_;
goto v_resetjp_5862_;
}
else
{
lean_inc(v_a_5861_);
lean_dec(v___x_5778_);
v___x_5863_ = lean_box(0);
v_isShared_5864_ = v_isSharedCheck_5868_;
goto v_resetjp_5862_;
}
v_resetjp_5862_:
{
lean_object* v___x_5866_; 
if (v_isShared_5864_ == 0)
{
v___x_5866_ = v___x_5863_;
goto v_reusejp_5865_;
}
else
{
lean_object* v_reuseFailAlloc_5867_; 
v_reuseFailAlloc_5867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5867_, 0, v_a_5861_);
v___x_5866_ = v_reuseFailAlloc_5867_;
goto v_reusejp_5865_;
}
v_reusejp_5865_:
{
return v___x_5866_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed(lean_object* v_onMotive_5888_, lean_object* v_toMatcherInfo_5889_, lean_object* v_a_5890_, lean_object* v_addEqualities_5891_, lean_object* v___x_5892_, lean_object* v_discrs_5893_, lean_object* v_motiveArgs_5894_, lean_object* v_motiveBody_5895_, lean_object* v___y_5896_, lean_object* v___y_5897_, lean_object* v___y_5898_, lean_object* v___y_5899_, lean_object* v___y_5900_){
_start:
{
uint8_t v_addEqualities_boxed_5901_; size_t v___x_34352__boxed_5902_; lean_object* v_res_5903_; 
v_addEqualities_boxed_5901_ = lean_unbox(v_addEqualities_5891_);
v___x_34352__boxed_5902_ = lean_unbox_usize(v___x_5892_);
lean_dec(v___x_5892_);
v_res_5903_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(v_onMotive_5888_, v_toMatcherInfo_5889_, v_a_5890_, v_addEqualities_boxed_5901_, v___x_34352__boxed_5902_, v_discrs_5893_, v_motiveArgs_5894_, v_motiveBody_5895_, v___y_5896_, v___y_5897_, v___y_5898_, v___y_5899_);
lean_dec(v___y_5899_);
lean_dec_ref(v___y_5898_);
lean_dec(v___y_5897_);
lean_dec_ref(v___y_5896_);
lean_dec_ref(v_discrs_5893_);
return v_res_5903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(lean_object* v_as_5904_, size_t v_sz_5905_, size_t v_i_5906_, lean_object* v_b_5907_, lean_object* v___y_5908_, lean_object* v___y_5909_, lean_object* v___y_5910_, lean_object* v___y_5911_){
_start:
{
lean_object* v_a_5914_; uint8_t v___x_5918_; 
v___x_5918_ = lean_usize_dec_lt(v_i_5906_, v_sz_5905_);
if (v___x_5918_ == 0)
{
lean_object* v___x_5919_; 
v___x_5919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5919_, 0, v_b_5907_);
return v___x_5919_;
}
else
{
lean_object* v_snd_5920_; lean_object* v_snd_5921_; lean_object* v_fst_5922_; lean_object* v___x_5924_; uint8_t v_isShared_5925_; uint8_t v_isSharedCheck_5982_; 
v_snd_5920_ = lean_ctor_get(v_b_5907_, 1);
lean_inc(v_snd_5920_);
v_snd_5921_ = lean_ctor_get(v_snd_5920_, 1);
lean_inc(v_snd_5921_);
v_fst_5922_ = lean_ctor_get(v_b_5907_, 0);
v_isSharedCheck_5982_ = !lean_is_exclusive(v_b_5907_);
if (v_isSharedCheck_5982_ == 0)
{
lean_object* v_unused_5983_; 
v_unused_5983_ = lean_ctor_get(v_b_5907_, 1);
lean_dec(v_unused_5983_);
v___x_5924_ = v_b_5907_;
v_isShared_5925_ = v_isSharedCheck_5982_;
goto v_resetjp_5923_;
}
else
{
lean_inc(v_fst_5922_);
lean_dec(v_b_5907_);
v___x_5924_ = lean_box(0);
v_isShared_5925_ = v_isSharedCheck_5982_;
goto v_resetjp_5923_;
}
v_resetjp_5923_:
{
lean_object* v_fst_5926_; lean_object* v___x_5928_; uint8_t v_isShared_5929_; uint8_t v_isSharedCheck_5980_; 
v_fst_5926_ = lean_ctor_get(v_snd_5920_, 0);
v_isSharedCheck_5980_ = !lean_is_exclusive(v_snd_5920_);
if (v_isSharedCheck_5980_ == 0)
{
lean_object* v_unused_5981_; 
v_unused_5981_ = lean_ctor_get(v_snd_5920_, 1);
lean_dec(v_unused_5981_);
v___x_5928_ = v_snd_5920_;
v_isShared_5929_ = v_isSharedCheck_5980_;
goto v_resetjp_5927_;
}
else
{
lean_inc(v_fst_5926_);
lean_dec(v_snd_5920_);
v___x_5928_ = lean_box(0);
v_isShared_5929_ = v_isSharedCheck_5980_;
goto v_resetjp_5927_;
}
v_resetjp_5927_:
{
lean_object* v_array_5930_; lean_object* v_start_5931_; lean_object* v_stop_5932_; uint8_t v___x_5933_; 
v_array_5930_ = lean_ctor_get(v_snd_5921_, 0);
v_start_5931_ = lean_ctor_get(v_snd_5921_, 1);
v_stop_5932_ = lean_ctor_get(v_snd_5921_, 2);
v___x_5933_ = lean_nat_dec_lt(v_start_5931_, v_stop_5932_);
if (v___x_5933_ == 0)
{
lean_object* v___x_5935_; 
if (v_isShared_5929_ == 0)
{
v___x_5935_ = v___x_5928_;
goto v_reusejp_5934_;
}
else
{
lean_object* v_reuseFailAlloc_5940_; 
v_reuseFailAlloc_5940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5940_, 0, v_fst_5926_);
lean_ctor_set(v_reuseFailAlloc_5940_, 1, v_snd_5921_);
v___x_5935_ = v_reuseFailAlloc_5940_;
goto v_reusejp_5934_;
}
v_reusejp_5934_:
{
lean_object* v___x_5937_; 
if (v_isShared_5925_ == 0)
{
lean_ctor_set(v___x_5924_, 1, v___x_5935_);
v___x_5937_ = v___x_5924_;
goto v_reusejp_5936_;
}
else
{
lean_object* v_reuseFailAlloc_5939_; 
v_reuseFailAlloc_5939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5939_, 0, v_fst_5922_);
lean_ctor_set(v_reuseFailAlloc_5939_, 1, v___x_5935_);
v___x_5937_ = v_reuseFailAlloc_5939_;
goto v_reusejp_5936_;
}
v_reusejp_5936_:
{
lean_object* v___x_5938_; 
v___x_5938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5938_, 0, v___x_5937_);
return v___x_5938_;
}
}
}
else
{
lean_object* v___x_5942_; uint8_t v_isShared_5943_; uint8_t v_isSharedCheck_5976_; 
lean_inc(v_stop_5932_);
lean_inc(v_start_5931_);
lean_inc_ref(v_array_5930_);
v_isSharedCheck_5976_ = !lean_is_exclusive(v_snd_5921_);
if (v_isSharedCheck_5976_ == 0)
{
lean_object* v_unused_5977_; lean_object* v_unused_5978_; lean_object* v_unused_5979_; 
v_unused_5977_ = lean_ctor_get(v_snd_5921_, 2);
lean_dec(v_unused_5977_);
v_unused_5978_ = lean_ctor_get(v_snd_5921_, 1);
lean_dec(v_unused_5978_);
v_unused_5979_ = lean_ctor_get(v_snd_5921_, 0);
lean_dec(v_unused_5979_);
v___x_5942_ = v_snd_5921_;
v_isShared_5943_ = v_isSharedCheck_5976_;
goto v_resetjp_5941_;
}
else
{
lean_dec(v_snd_5921_);
v___x_5942_ = lean_box(0);
v_isShared_5943_ = v_isSharedCheck_5976_;
goto v_resetjp_5941_;
}
v_resetjp_5941_:
{
lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_5948_; 
v___x_5944_ = lean_array_fget(v_array_5930_, v_start_5931_);
v___x_5945_ = lean_unsigned_to_nat(1u);
v___x_5946_ = lean_nat_add(v_start_5931_, v___x_5945_);
lean_dec(v_start_5931_);
if (v_isShared_5943_ == 0)
{
lean_ctor_set(v___x_5942_, 1, v___x_5946_);
v___x_5948_ = v___x_5942_;
goto v_reusejp_5947_;
}
else
{
lean_object* v_reuseFailAlloc_5975_; 
v_reuseFailAlloc_5975_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5975_, 0, v_array_5930_);
lean_ctor_set(v_reuseFailAlloc_5975_, 1, v___x_5946_);
lean_ctor_set(v_reuseFailAlloc_5975_, 2, v_stop_5932_);
v___x_5948_ = v_reuseFailAlloc_5975_;
goto v_reusejp_5947_;
}
v_reusejp_5947_:
{
lean_object* v___y_5950_; 
if (lean_obj_tag(v___x_5944_) == 0)
{
lean_object* v___x_5968_; lean_object* v___x_5969_; 
lean_del_object(v___x_5928_);
lean_del_object(v___x_5924_);
v___x_5968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5968_, 0, v_fst_5926_);
lean_ctor_set(v___x_5968_, 1, v___x_5948_);
v___x_5969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5969_, 0, v_fst_5922_);
lean_ctor_set(v___x_5969_, 1, v___x_5968_);
v_a_5914_ = v___x_5969_;
goto v___jp_5913_;
}
else
{
lean_object* v_val_5970_; lean_object* v_a_5971_; uint8_t v___x_5972_; 
v_val_5970_ = lean_ctor_get(v___x_5944_, 0);
lean_inc(v_val_5970_);
lean_dec_ref(v___x_5944_);
v_a_5971_ = lean_array_uget_borrowed(v_as_5904_, v_i_5906_);
v___x_5972_ = lean_unbox(v_val_5970_);
lean_dec(v_val_5970_);
if (v___x_5972_ == 0)
{
lean_object* v___x_5973_; 
lean_inc(v_a_5971_);
v___x_5973_ = l_Lean_Meta_mkEqRefl(v_a_5971_, v___y_5908_, v___y_5909_, v___y_5910_, v___y_5911_);
v___y_5950_ = v___x_5973_;
goto v___jp_5949_;
}
else
{
lean_object* v___x_5974_; 
lean_inc(v_a_5971_);
v___x_5974_ = l_Lean_Meta_mkHEqRefl(v_a_5971_, v___y_5908_, v___y_5909_, v___y_5910_, v___y_5911_);
v___y_5950_ = v___x_5974_;
goto v___jp_5949_;
}
}
v___jp_5949_:
{
if (lean_obj_tag(v___y_5950_) == 0)
{
lean_object* v_a_5951_; lean_object* v___x_5952_; lean_object* v___x_5953_; lean_object* v___x_5955_; 
v_a_5951_ = lean_ctor_get(v___y_5950_, 0);
lean_inc(v_a_5951_);
lean_dec_ref(v___y_5950_);
v___x_5952_ = lean_array_push(v_fst_5922_, v_a_5951_);
v___x_5953_ = lean_nat_add(v_fst_5926_, v___x_5945_);
lean_dec(v_fst_5926_);
if (v_isShared_5929_ == 0)
{
lean_ctor_set(v___x_5928_, 1, v___x_5948_);
lean_ctor_set(v___x_5928_, 0, v___x_5953_);
v___x_5955_ = v___x_5928_;
goto v_reusejp_5954_;
}
else
{
lean_object* v_reuseFailAlloc_5959_; 
v_reuseFailAlloc_5959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5959_, 0, v___x_5953_);
lean_ctor_set(v_reuseFailAlloc_5959_, 1, v___x_5948_);
v___x_5955_ = v_reuseFailAlloc_5959_;
goto v_reusejp_5954_;
}
v_reusejp_5954_:
{
lean_object* v___x_5957_; 
if (v_isShared_5925_ == 0)
{
lean_ctor_set(v___x_5924_, 1, v___x_5955_);
lean_ctor_set(v___x_5924_, 0, v___x_5952_);
v___x_5957_ = v___x_5924_;
goto v_reusejp_5956_;
}
else
{
lean_object* v_reuseFailAlloc_5958_; 
v_reuseFailAlloc_5958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5958_, 0, v___x_5952_);
lean_ctor_set(v_reuseFailAlloc_5958_, 1, v___x_5955_);
v___x_5957_ = v_reuseFailAlloc_5958_;
goto v_reusejp_5956_;
}
v_reusejp_5956_:
{
v_a_5914_ = v___x_5957_;
goto v___jp_5913_;
}
}
}
else
{
lean_object* v_a_5960_; lean_object* v___x_5962_; uint8_t v_isShared_5963_; uint8_t v_isSharedCheck_5967_; 
lean_dec_ref(v___x_5948_);
lean_del_object(v___x_5928_);
lean_dec(v_fst_5926_);
lean_del_object(v___x_5924_);
lean_dec(v_fst_5922_);
v_a_5960_ = lean_ctor_get(v___y_5950_, 0);
v_isSharedCheck_5967_ = !lean_is_exclusive(v___y_5950_);
if (v_isSharedCheck_5967_ == 0)
{
v___x_5962_ = v___y_5950_;
v_isShared_5963_ = v_isSharedCheck_5967_;
goto v_resetjp_5961_;
}
else
{
lean_inc(v_a_5960_);
lean_dec(v___y_5950_);
v___x_5962_ = lean_box(0);
v_isShared_5963_ = v_isSharedCheck_5967_;
goto v_resetjp_5961_;
}
v_resetjp_5961_:
{
lean_object* v___x_5965_; 
if (v_isShared_5963_ == 0)
{
v___x_5965_ = v___x_5962_;
goto v_reusejp_5964_;
}
else
{
lean_object* v_reuseFailAlloc_5966_; 
v_reuseFailAlloc_5966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5966_, 0, v_a_5960_);
v___x_5965_ = v_reuseFailAlloc_5966_;
goto v_reusejp_5964_;
}
v_reusejp_5964_:
{
return v___x_5965_;
}
}
}
}
}
}
}
}
}
}
v___jp_5913_:
{
size_t v___x_5915_; size_t v___x_5916_; 
v___x_5915_ = ((size_t)1ULL);
v___x_5916_ = lean_usize_add(v_i_5906_, v___x_5915_);
v_i_5906_ = v___x_5916_;
v_b_5907_ = v_a_5914_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8___boxed(lean_object* v_as_5984_, lean_object* v_sz_5985_, lean_object* v_i_5986_, lean_object* v_b_5987_, lean_object* v___y_5988_, lean_object* v___y_5989_, lean_object* v___y_5990_, lean_object* v___y_5991_, lean_object* v___y_5992_){
_start:
{
size_t v_sz_boxed_5993_; size_t v_i_boxed_5994_; lean_object* v_res_5995_; 
v_sz_boxed_5993_ = lean_unbox_usize(v_sz_5985_);
lean_dec(v_sz_5985_);
v_i_boxed_5994_ = lean_unbox_usize(v_i_5986_);
lean_dec(v_i_5986_);
v_res_5995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(v_as_5984_, v_sz_boxed_5993_, v_i_boxed_5994_, v_b_5987_, v___y_5988_, v___y_5989_, v___y_5990_, v___y_5991_);
lean_dec(v___y_5991_);
lean_dec_ref(v___y_5990_);
lean_dec(v___y_5989_);
lean_dec_ref(v___y_5988_);
lean_dec_ref(v_as_5984_);
return v_res_5995_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(lean_object* v___x_5996_, lean_object* v___y_5997_, lean_object* v___y_5998_, lean_object* v___y_5999_, lean_object* v___y_6000_){
_start:
{
lean_object* v___x_6002_; 
v___x_6002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6002_, 0, v___x_5996_);
return v___x_6002_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed(lean_object* v___x_6003_, lean_object* v___y_6004_, lean_object* v___y_6005_, lean_object* v___y_6006_, lean_object* v___y_6007_, lean_object* v___y_6008_){
_start:
{
lean_object* v_res_6009_; 
v_res_6009_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(v___x_6003_, v___y_6004_, v___y_6005_, v___y_6006_, v___y_6007_);
lean_dec(v___y_6007_);
lean_dec_ref(v___y_6006_);
lean_dec(v___y_6005_);
lean_dec_ref(v___y_6004_);
return v_res_6009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(size_t v_sz_6010_, size_t v_i_6011_, lean_object* v_bs_6012_, lean_object* v___y_6013_, lean_object* v___y_6014_, lean_object* v___y_6015_){
_start:
{
uint8_t v___x_6017_; 
v___x_6017_ = lean_usize_dec_lt(v_i_6011_, v_sz_6010_);
if (v___x_6017_ == 0)
{
lean_object* v___x_6018_; 
v___x_6018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6018_, 0, v_bs_6012_);
return v___x_6018_;
}
else
{
lean_object* v_v_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; 
v_v_6019_ = lean_array_uget_borrowed(v_bs_6012_, v_i_6011_);
v___x_6020_ = l_Lean_Expr_fvarId_x21(v_v_6019_);
v___x_6021_ = l_Lean_FVarId_getUserName___redArg(v___x_6020_, v___y_6013_, v___y_6014_, v___y_6015_);
if (lean_obj_tag(v___x_6021_) == 0)
{
lean_object* v_a_6022_; lean_object* v___x_6023_; lean_object* v_bs_x27_6024_; size_t v___x_6025_; size_t v___x_6026_; lean_object* v___x_6027_; 
v_a_6022_ = lean_ctor_get(v___x_6021_, 0);
lean_inc(v_a_6022_);
lean_dec_ref(v___x_6021_);
v___x_6023_ = lean_unsigned_to_nat(0u);
v_bs_x27_6024_ = lean_array_uset(v_bs_6012_, v_i_6011_, v___x_6023_);
v___x_6025_ = ((size_t)1ULL);
v___x_6026_ = lean_usize_add(v_i_6011_, v___x_6025_);
v___x_6027_ = lean_array_uset(v_bs_x27_6024_, v_i_6011_, v_a_6022_);
v_i_6011_ = v___x_6026_;
v_bs_6012_ = v___x_6027_;
goto _start;
}
else
{
lean_object* v_a_6029_; lean_object* v___x_6031_; uint8_t v_isShared_6032_; uint8_t v_isSharedCheck_6036_; 
lean_dec_ref(v_bs_6012_);
v_a_6029_ = lean_ctor_get(v___x_6021_, 0);
v_isSharedCheck_6036_ = !lean_is_exclusive(v___x_6021_);
if (v_isSharedCheck_6036_ == 0)
{
v___x_6031_ = v___x_6021_;
v_isShared_6032_ = v_isSharedCheck_6036_;
goto v_resetjp_6030_;
}
else
{
lean_inc(v_a_6029_);
lean_dec(v___x_6021_);
v___x_6031_ = lean_box(0);
v_isShared_6032_ = v_isSharedCheck_6036_;
goto v_resetjp_6030_;
}
v_resetjp_6030_:
{
lean_object* v___x_6034_; 
if (v_isShared_6032_ == 0)
{
v___x_6034_ = v___x_6031_;
goto v_reusejp_6033_;
}
else
{
lean_object* v_reuseFailAlloc_6035_; 
v_reuseFailAlloc_6035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6035_, 0, v_a_6029_);
v___x_6034_ = v_reuseFailAlloc_6035_;
goto v_reusejp_6033_;
}
v_reusejp_6033_:
{
return v___x_6034_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg___boxed(lean_object* v_sz_6037_, lean_object* v_i_6038_, lean_object* v_bs_6039_, lean_object* v___y_6040_, lean_object* v___y_6041_, lean_object* v___y_6042_, lean_object* v___y_6043_){
_start:
{
size_t v_sz_boxed_6044_; size_t v_i_boxed_6045_; lean_object* v_res_6046_; 
v_sz_boxed_6044_ = lean_unbox_usize(v_sz_6037_);
lean_dec(v_sz_6037_);
v_i_boxed_6045_ = lean_unbox_usize(v_i_6038_);
lean_dec(v_i_6038_);
v_res_6046_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_boxed_6044_, v_i_boxed_6045_, v_bs_6039_, v___y_6040_, v___y_6041_, v___y_6042_);
lean_dec(v___y_6042_);
lean_dec_ref(v___y_6041_);
lean_dec_ref(v___y_6040_);
return v_res_6046_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(lean_object* v_xs_6047_, lean_object* v_x_6048_, lean_object* v___y_6049_, lean_object* v___y_6050_, lean_object* v___y_6051_, lean_object* v___y_6052_){
_start:
{
size_t v_sz_6054_; size_t v___x_6055_; lean_object* v___x_6056_; 
v_sz_6054_ = lean_array_size(v_xs_6047_);
v___x_6055_ = ((size_t)0ULL);
v___x_6056_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_6054_, v___x_6055_, v_xs_6047_, v___y_6049_, v___y_6051_, v___y_6052_);
return v___x_6056_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3___boxed(lean_object* v_xs_6057_, lean_object* v_x_6058_, lean_object* v___y_6059_, lean_object* v___y_6060_, lean_object* v___y_6061_, lean_object* v___y_6062_, lean_object* v___y_6063_){
_start:
{
lean_object* v_res_6064_; 
v_res_6064_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(v_xs_6057_, v_x_6058_, v___y_6059_, v___y_6060_, v___y_6061_, v___y_6062_);
lean_dec(v___y_6062_);
lean_dec_ref(v___y_6061_);
lean_dec(v___y_6060_);
lean_dec_ref(v___y_6059_);
lean_dec_ref(v_x_6058_);
return v_res_6064_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(lean_object* v___x_6065_, lean_object* v___x_6066_, lean_object* v___f_6067_, uint8_t v___x_6068_, lean_object* v_fst_6069_, lean_object* v___x_6070_, lean_object* v___x_6071_, lean_object* v___x_6072_, lean_object* v___y_6073_, lean_object* v___y_6074_, lean_object* v___y_6075_, lean_object* v___y_6076_){
_start:
{
lean_object* v___x_6078_; 
v___x_6078_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v___x_6065_, v___x_6066_, v___f_6067_, v___x_6068_, v___x_6068_, v___y_6073_, v___y_6074_, v___y_6075_, v___y_6076_);
if (lean_obj_tag(v___x_6078_) == 0)
{
lean_object* v_a_6079_; lean_object* v___x_6081_; uint8_t v_isShared_6082_; uint8_t v_isSharedCheck_6091_; 
v_a_6079_ = lean_ctor_get(v___x_6078_, 0);
v_isSharedCheck_6091_ = !lean_is_exclusive(v___x_6078_);
if (v_isSharedCheck_6091_ == 0)
{
v___x_6081_ = v___x_6078_;
v_isShared_6082_ = v_isSharedCheck_6091_;
goto v_resetjp_6080_;
}
else
{
lean_inc(v_a_6079_);
lean_dec(v___x_6078_);
v___x_6081_ = lean_box(0);
v_isShared_6082_ = v_isSharedCheck_6091_;
goto v_resetjp_6080_;
}
v_resetjp_6080_:
{
lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6089_; 
v___x_6083_ = lean_array_push(v_fst_6069_, v_a_6079_);
v___x_6084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6084_, 0, v___x_6070_);
lean_ctor_set(v___x_6084_, 1, v___x_6071_);
v___x_6085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6085_, 0, v___x_6072_);
lean_ctor_set(v___x_6085_, 1, v___x_6084_);
v___x_6086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6086_, 0, v___x_6083_);
lean_ctor_set(v___x_6086_, 1, v___x_6085_);
v___x_6087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6087_, 0, v___x_6086_);
if (v_isShared_6082_ == 0)
{
lean_ctor_set(v___x_6081_, 0, v___x_6087_);
v___x_6089_ = v___x_6081_;
goto v_reusejp_6088_;
}
else
{
lean_object* v_reuseFailAlloc_6090_; 
v_reuseFailAlloc_6090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6090_, 0, v___x_6087_);
v___x_6089_ = v_reuseFailAlloc_6090_;
goto v_reusejp_6088_;
}
v_reusejp_6088_:
{
return v___x_6089_;
}
}
}
else
{
lean_object* v_a_6092_; lean_object* v___x_6094_; uint8_t v_isShared_6095_; uint8_t v_isSharedCheck_6099_; 
lean_dec_ref(v___x_6072_);
lean_dec_ref(v___x_6071_);
lean_dec_ref(v___x_6070_);
lean_dec(v_fst_6069_);
v_a_6092_ = lean_ctor_get(v___x_6078_, 0);
v_isSharedCheck_6099_ = !lean_is_exclusive(v___x_6078_);
if (v_isSharedCheck_6099_ == 0)
{
v___x_6094_ = v___x_6078_;
v_isShared_6095_ = v_isSharedCheck_6099_;
goto v_resetjp_6093_;
}
else
{
lean_inc(v_a_6092_);
lean_dec(v___x_6078_);
v___x_6094_ = lean_box(0);
v_isShared_6095_ = v_isSharedCheck_6099_;
goto v_resetjp_6093_;
}
v_resetjp_6093_:
{
lean_object* v___x_6097_; 
if (v_isShared_6095_ == 0)
{
v___x_6097_ = v___x_6094_;
goto v_reusejp_6096_;
}
else
{
lean_object* v_reuseFailAlloc_6098_; 
v_reuseFailAlloc_6098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6098_, 0, v_a_6092_);
v___x_6097_ = v_reuseFailAlloc_6098_;
goto v_reusejp_6096_;
}
v_reusejp_6096_:
{
return v___x_6097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed(lean_object* v___x_6100_, lean_object* v___x_6101_, lean_object* v___f_6102_, lean_object* v___x_6103_, lean_object* v_fst_6104_, lean_object* v___x_6105_, lean_object* v___x_6106_, lean_object* v___x_6107_, lean_object* v___y_6108_, lean_object* v___y_6109_, lean_object* v___y_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_){
_start:
{
uint8_t v___x_34815__boxed_6113_; lean_object* v_res_6114_; 
v___x_34815__boxed_6113_ = lean_unbox(v___x_6103_);
v_res_6114_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(v___x_6100_, v___x_6101_, v___f_6102_, v___x_34815__boxed_6113_, v_fst_6104_, v___x_6105_, v___x_6106_, v___x_6107_, v___y_6108_, v___y_6109_, v___y_6110_, v___y_6111_);
lean_dec(v___y_6111_);
lean_dec_ref(v___y_6110_);
lean_dec(v___y_6109_);
lean_dec_ref(v___y_6108_);
return v_res_6114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(lean_object* v_fvars_6115_, lean_object* v_names_6116_, lean_object* v_k_6117_, lean_object* v___y_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_){
_start:
{
lean_object* v___x_6123_; 
v___x_6123_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_6115_, v_names_6116_, v_k_6117_, v___y_6118_, v___y_6119_, v___y_6120_, v___y_6121_);
if (lean_obj_tag(v___x_6123_) == 0)
{
lean_object* v_a_6124_; lean_object* v___x_6126_; uint8_t v_isShared_6127_; uint8_t v_isSharedCheck_6131_; 
v_a_6124_ = lean_ctor_get(v___x_6123_, 0);
v_isSharedCheck_6131_ = !lean_is_exclusive(v___x_6123_);
if (v_isSharedCheck_6131_ == 0)
{
v___x_6126_ = v___x_6123_;
v_isShared_6127_ = v_isSharedCheck_6131_;
goto v_resetjp_6125_;
}
else
{
lean_inc(v_a_6124_);
lean_dec(v___x_6123_);
v___x_6126_ = lean_box(0);
v_isShared_6127_ = v_isSharedCheck_6131_;
goto v_resetjp_6125_;
}
v_resetjp_6125_:
{
lean_object* v___x_6129_; 
if (v_isShared_6127_ == 0)
{
v___x_6129_ = v___x_6126_;
goto v_reusejp_6128_;
}
else
{
lean_object* v_reuseFailAlloc_6130_; 
v_reuseFailAlloc_6130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6130_, 0, v_a_6124_);
v___x_6129_ = v_reuseFailAlloc_6130_;
goto v_reusejp_6128_;
}
v_reusejp_6128_:
{
return v___x_6129_;
}
}
}
else
{
lean_object* v_a_6132_; lean_object* v___x_6134_; uint8_t v_isShared_6135_; uint8_t v_isSharedCheck_6139_; 
v_a_6132_ = lean_ctor_get(v___x_6123_, 0);
v_isSharedCheck_6139_ = !lean_is_exclusive(v___x_6123_);
if (v_isSharedCheck_6139_ == 0)
{
v___x_6134_ = v___x_6123_;
v_isShared_6135_ = v_isSharedCheck_6139_;
goto v_resetjp_6133_;
}
else
{
lean_inc(v_a_6132_);
lean_dec(v___x_6123_);
v___x_6134_ = lean_box(0);
v_isShared_6135_ = v_isSharedCheck_6139_;
goto v_resetjp_6133_;
}
v_resetjp_6133_:
{
lean_object* v___x_6137_; 
if (v_isShared_6135_ == 0)
{
v___x_6137_ = v___x_6134_;
goto v_reusejp_6136_;
}
else
{
lean_object* v_reuseFailAlloc_6138_; 
v_reuseFailAlloc_6138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6138_, 0, v_a_6132_);
v___x_6137_ = v_reuseFailAlloc_6138_;
goto v_reusejp_6136_;
}
v_reusejp_6136_:
{
return v___x_6137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg___boxed(lean_object* v_fvars_6140_, lean_object* v_names_6141_, lean_object* v_k_6142_, lean_object* v___y_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_, lean_object* v___y_6147_){
_start:
{
lean_object* v_res_6148_; 
v_res_6148_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_fvars_6140_, v_names_6141_, v_k_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_);
lean_dec(v___y_6146_);
lean_dec_ref(v___y_6145_);
lean_dec(v___y_6144_);
lean_dec_ref(v___y_6143_);
lean_dec_ref(v_names_6141_);
lean_dec_ref(v_fvars_6140_);
return v_res_6148_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(lean_object* v___x_6149_, lean_object* v_xs_6150_, lean_object* v_remaining_x27_6151_, lean_object* v_ys4_6152_, lean_object* v_onAlt_6153_, lean_object* v_a_6154_, lean_object* v_altType_6155_, uint8_t v___x_6156_, uint8_t v___x_6157_, lean_object* v___y_6158_, lean_object* v___y_6159_, lean_object* v___y_6160_, lean_object* v___y_6161_){
_start:
{
lean_object* v___x_6163_; 
v___x_6163_ = l_Lean_Meta_instantiateLambda(v___x_6149_, v_xs_6150_, v___y_6158_, v___y_6159_, v___y_6160_, v___y_6161_);
if (lean_obj_tag(v___x_6163_) == 0)
{
lean_object* v_a_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; 
v_a_6164_ = lean_ctor_get(v___x_6163_, 0);
lean_inc(v_a_6164_);
lean_dec_ref(v___x_6163_);
lean_inc_ref(v_ys4_6152_);
lean_inc_ref(v_remaining_x27_6151_);
lean_inc_ref_n(v_xs_6150_, 2);
v___x_6165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6165_, 0, v_xs_6150_);
lean_ctor_set(v___x_6165_, 1, v_xs_6150_);
lean_ctor_set(v___x_6165_, 2, v_remaining_x27_6151_);
lean_ctor_set(v___x_6165_, 3, v_remaining_x27_6151_);
lean_ctor_set(v___x_6165_, 4, v_ys4_6152_);
lean_inc(v___y_6161_);
lean_inc_ref(v___y_6160_);
lean_inc(v___y_6159_);
lean_inc_ref(v___y_6158_);
v___x_6166_ = lean_apply_9(v_onAlt_6153_, v_a_6154_, v_altType_6155_, v___x_6165_, v_a_6164_, v___y_6158_, v___y_6159_, v___y_6160_, v___y_6161_, lean_box(0));
if (lean_obj_tag(v___x_6166_) == 0)
{
lean_object* v_a_6167_; lean_object* v___x_6168_; uint8_t v___x_6169_; lean_object* v___x_6170_; 
v_a_6167_ = lean_ctor_get(v___x_6166_, 0);
lean_inc(v_a_6167_);
lean_dec_ref(v___x_6166_);
v___x_6168_ = l_Array_append___redArg(v_xs_6150_, v_ys4_6152_);
lean_dec_ref(v_ys4_6152_);
v___x_6169_ = 1;
v___x_6170_ = l_Lean_Meta_mkLambdaFVars(v___x_6168_, v_a_6167_, v___x_6156_, v___x_6157_, v___x_6156_, v___x_6157_, v___x_6169_, v___y_6158_, v___y_6159_, v___y_6160_, v___y_6161_);
lean_dec(v___y_6161_);
lean_dec_ref(v___y_6160_);
lean_dec(v___y_6159_);
lean_dec_ref(v___y_6158_);
lean_dec_ref(v___x_6168_);
return v___x_6170_;
}
else
{
lean_dec(v___y_6161_);
lean_dec_ref(v___y_6160_);
lean_dec(v___y_6159_);
lean_dec_ref(v___y_6158_);
lean_dec_ref(v_ys4_6152_);
lean_dec_ref(v_xs_6150_);
return v___x_6166_;
}
}
else
{
lean_dec(v___y_6161_);
lean_dec_ref(v___y_6160_);
lean_dec(v___y_6159_);
lean_dec_ref(v___y_6158_);
lean_dec_ref(v_altType_6155_);
lean_dec(v_a_6154_);
lean_dec_ref(v_onAlt_6153_);
lean_dec_ref(v_ys4_6152_);
lean_dec_ref(v_remaining_x27_6151_);
lean_dec_ref(v_xs_6150_);
return v___x_6163_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed(lean_object* v___x_6171_, lean_object* v_xs_6172_, lean_object* v_remaining_x27_6173_, lean_object* v_ys4_6174_, lean_object* v_onAlt_6175_, lean_object* v_a_6176_, lean_object* v_altType_6177_, lean_object* v___x_6178_, lean_object* v___x_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_, lean_object* v___y_6182_, lean_object* v___y_6183_, lean_object* v___y_6184_){
_start:
{
uint8_t v___x_34942__boxed_6185_; uint8_t v___x_34943__boxed_6186_; lean_object* v_res_6187_; 
v___x_34942__boxed_6185_ = lean_unbox(v___x_6178_);
v___x_34943__boxed_6186_ = lean_unbox(v___x_6179_);
v_res_6187_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(v___x_6171_, v_xs_6172_, v_remaining_x27_6173_, v_ys4_6174_, v_onAlt_6175_, v_a_6176_, v_altType_6177_, v___x_34942__boxed_6185_, v___x_34943__boxed_6186_, v___y_6180_, v___y_6181_, v___y_6182_, v___y_6183_);
return v_res_6187_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(lean_object* v___x_6188_, lean_object* v___f_6189_, uint8_t v___x_6190_, lean_object* v_xs_6191_, lean_object* v_remaining_x27_6192_, lean_object* v_onAlt_6193_, lean_object* v_a_6194_, uint8_t v___x_6195_, lean_object* v_ys4_6196_, lean_object* v_altType_6197_, lean_object* v___y_6198_, lean_object* v___y_6199_, lean_object* v___y_6200_, lean_object* v___y_6201_){
_start:
{
lean_object* v___x_6203_; 
lean_inc_ref(v___x_6188_);
v___x_6203_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v___x_6188_, v___f_6189_, v___x_6190_, v___y_6198_, v___y_6199_, v___y_6200_, v___y_6201_);
if (lean_obj_tag(v___x_6203_) == 0)
{
lean_object* v_a_6204_; lean_object* v___x_6205_; lean_object* v___x_6206_; lean_object* v___f_6207_; lean_object* v___x_6208_; 
v_a_6204_ = lean_ctor_get(v___x_6203_, 0);
lean_inc(v_a_6204_);
lean_dec_ref(v___x_6203_);
v___x_6205_ = lean_box(v___x_6190_);
v___x_6206_ = lean_box(v___x_6195_);
lean_inc_ref(v_xs_6191_);
v___f_6207_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_6207_, 0, v___x_6188_);
lean_closure_set(v___f_6207_, 1, v_xs_6191_);
lean_closure_set(v___f_6207_, 2, v_remaining_x27_6192_);
lean_closure_set(v___f_6207_, 3, v_ys4_6196_);
lean_closure_set(v___f_6207_, 4, v_onAlt_6193_);
lean_closure_set(v___f_6207_, 5, v_a_6194_);
lean_closure_set(v___f_6207_, 6, v_altType_6197_);
lean_closure_set(v___f_6207_, 7, v___x_6205_);
lean_closure_set(v___f_6207_, 8, v___x_6206_);
v___x_6208_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_xs_6191_, v_a_6204_, v___f_6207_, v___y_6198_, v___y_6199_, v___y_6200_, v___y_6201_);
lean_dec(v_a_6204_);
lean_dec_ref(v_xs_6191_);
return v___x_6208_;
}
else
{
lean_object* v_a_6209_; lean_object* v___x_6211_; uint8_t v_isShared_6212_; uint8_t v_isSharedCheck_6216_; 
lean_dec_ref(v_altType_6197_);
lean_dec_ref(v_ys4_6196_);
lean_dec(v_a_6194_);
lean_dec_ref(v_onAlt_6193_);
lean_dec_ref(v_remaining_x27_6192_);
lean_dec_ref(v_xs_6191_);
lean_dec_ref(v___x_6188_);
v_a_6209_ = lean_ctor_get(v___x_6203_, 0);
v_isSharedCheck_6216_ = !lean_is_exclusive(v___x_6203_);
if (v_isSharedCheck_6216_ == 0)
{
v___x_6211_ = v___x_6203_;
v_isShared_6212_ = v_isSharedCheck_6216_;
goto v_resetjp_6210_;
}
else
{
lean_inc(v_a_6209_);
lean_dec(v___x_6203_);
v___x_6211_ = lean_box(0);
v_isShared_6212_ = v_isSharedCheck_6216_;
goto v_resetjp_6210_;
}
v_resetjp_6210_:
{
lean_object* v___x_6214_; 
if (v_isShared_6212_ == 0)
{
v___x_6214_ = v___x_6211_;
goto v_reusejp_6213_;
}
else
{
lean_object* v_reuseFailAlloc_6215_; 
v_reuseFailAlloc_6215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6215_, 0, v_a_6209_);
v___x_6214_ = v_reuseFailAlloc_6215_;
goto v_reusejp_6213_;
}
v_reusejp_6213_:
{
return v___x_6214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed(lean_object* v___x_6217_, lean_object* v___f_6218_, lean_object* v___x_6219_, lean_object* v_xs_6220_, lean_object* v_remaining_x27_6221_, lean_object* v_onAlt_6222_, lean_object* v_a_6223_, lean_object* v___x_6224_, lean_object* v_ys4_6225_, lean_object* v_altType_6226_, lean_object* v___y_6227_, lean_object* v___y_6228_, lean_object* v___y_6229_, lean_object* v___y_6230_, lean_object* v___y_6231_){
_start:
{
uint8_t v___x_34985__boxed_6232_; uint8_t v___x_34986__boxed_6233_; lean_object* v_res_6234_; 
v___x_34985__boxed_6232_ = lean_unbox(v___x_6219_);
v___x_34986__boxed_6233_ = lean_unbox(v___x_6224_);
v_res_6234_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(v___x_6217_, v___f_6218_, v___x_34985__boxed_6232_, v_xs_6220_, v_remaining_x27_6221_, v_onAlt_6222_, v_a_6223_, v___x_34986__boxed_6233_, v_ys4_6225_, v_altType_6226_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_);
lean_dec(v___y_6230_);
lean_dec_ref(v___y_6229_);
lean_dec(v___y_6228_);
lean_dec_ref(v___y_6227_);
return v_res_6234_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(lean_object* v___x_6235_, lean_object* v___f_6236_, uint8_t v___x_6237_, lean_object* v_remaining_x27_6238_, lean_object* v_onAlt_6239_, lean_object* v_a_6240_, uint8_t v___x_6241_, lean_object* v_extraEqualities_6242_, lean_object* v_xs_6243_, lean_object* v_altType_6244_, lean_object* v___y_6245_, lean_object* v___y_6246_, lean_object* v___y_6247_, lean_object* v___y_6248_){
_start:
{
lean_object* v___x_6250_; lean_object* v___x_6251_; lean_object* v___f_6252_; lean_object* v___x_6253_; lean_object* v___x_6254_; 
v___x_6250_ = lean_box(v___x_6237_);
v___x_6251_ = lean_box(v___x_6241_);
v___f_6252_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed), 15, 8);
lean_closure_set(v___f_6252_, 0, v___x_6235_);
lean_closure_set(v___f_6252_, 1, v___f_6236_);
lean_closure_set(v___f_6252_, 2, v___x_6250_);
lean_closure_set(v___f_6252_, 3, v_xs_6243_);
lean_closure_set(v___f_6252_, 4, v_remaining_x27_6238_);
lean_closure_set(v___f_6252_, 5, v_onAlt_6239_);
lean_closure_set(v___f_6252_, 6, v_a_6240_);
lean_closure_set(v___f_6252_, 7, v___x_6251_);
v___x_6253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6253_, 0, v_extraEqualities_6242_);
v___x_6254_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_6244_, v___x_6253_, v___f_6252_, v___x_6237_, v___x_6237_, v___y_6245_, v___y_6246_, v___y_6247_, v___y_6248_);
return v___x_6254_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed(lean_object* v___x_6255_, lean_object* v___f_6256_, lean_object* v___x_6257_, lean_object* v_remaining_x27_6258_, lean_object* v_onAlt_6259_, lean_object* v_a_6260_, lean_object* v___x_6261_, lean_object* v_extraEqualities_6262_, lean_object* v_xs_6263_, lean_object* v_altType_6264_, lean_object* v___y_6265_, lean_object* v___y_6266_, lean_object* v___y_6267_, lean_object* v___y_6268_, lean_object* v___y_6269_){
_start:
{
uint8_t v___x_35040__boxed_6270_; uint8_t v___x_35041__boxed_6271_; lean_object* v_res_6272_; 
v___x_35040__boxed_6270_ = lean_unbox(v___x_6257_);
v___x_35041__boxed_6271_ = lean_unbox(v___x_6261_);
v_res_6272_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(v___x_6255_, v___f_6256_, v___x_35040__boxed_6270_, v_remaining_x27_6258_, v_onAlt_6259_, v_a_6260_, v___x_35041__boxed_6271_, v_extraEqualities_6262_, v_xs_6263_, v_altType_6264_, v___y_6265_, v___y_6266_, v___y_6267_, v___y_6268_);
lean_dec(v___y_6268_);
lean_dec_ref(v___y_6267_);
lean_dec(v___y_6266_);
lean_dec_ref(v___y_6265_);
return v_res_6272_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(lean_object* v_upperBound_6274_, lean_object* v_onAlt_6275_, lean_object* v_extraEqualities_6276_, lean_object* v_a_6277_, lean_object* v_b_6278_, lean_object* v___y_6279_, lean_object* v___y_6280_, lean_object* v___y_6281_, lean_object* v___y_6282_){
_start:
{
lean_object* v___y_6285_; uint8_t v___x_6308_; 
v___x_6308_ = lean_nat_dec_lt(v_a_6277_, v_upperBound_6274_);
if (v___x_6308_ == 0)
{
lean_object* v___x_6309_; 
lean_dec(v_a_6277_);
lean_dec(v_extraEqualities_6276_);
lean_dec_ref(v_onAlt_6275_);
v___x_6309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6309_, 0, v_b_6278_);
return v___x_6309_;
}
else
{
lean_object* v_snd_6310_; lean_object* v_snd_6311_; lean_object* v_snd_6312_; lean_object* v_fst_6313_; lean_object* v___x_6315_; uint8_t v_isShared_6316_; uint8_t v_isSharedCheck_6420_; 
v_snd_6310_ = lean_ctor_get(v_b_6278_, 1);
lean_inc(v_snd_6310_);
v_snd_6311_ = lean_ctor_get(v_snd_6310_, 1);
lean_inc(v_snd_6311_);
v_snd_6312_ = lean_ctor_get(v_snd_6311_, 1);
lean_inc(v_snd_6312_);
v_fst_6313_ = lean_ctor_get(v_b_6278_, 0);
v_isSharedCheck_6420_ = !lean_is_exclusive(v_b_6278_);
if (v_isSharedCheck_6420_ == 0)
{
lean_object* v_unused_6421_; 
v_unused_6421_ = lean_ctor_get(v_b_6278_, 1);
lean_dec(v_unused_6421_);
v___x_6315_ = v_b_6278_;
v_isShared_6316_ = v_isSharedCheck_6420_;
goto v_resetjp_6314_;
}
else
{
lean_inc(v_fst_6313_);
lean_dec(v_b_6278_);
v___x_6315_ = lean_box(0);
v_isShared_6316_ = v_isSharedCheck_6420_;
goto v_resetjp_6314_;
}
v_resetjp_6314_:
{
lean_object* v_fst_6317_; lean_object* v___x_6319_; uint8_t v_isShared_6320_; uint8_t v_isSharedCheck_6418_; 
v_fst_6317_ = lean_ctor_get(v_snd_6310_, 0);
v_isSharedCheck_6418_ = !lean_is_exclusive(v_snd_6310_);
if (v_isSharedCheck_6418_ == 0)
{
lean_object* v_unused_6419_; 
v_unused_6419_ = lean_ctor_get(v_snd_6310_, 1);
lean_dec(v_unused_6419_);
v___x_6319_ = v_snd_6310_;
v_isShared_6320_ = v_isSharedCheck_6418_;
goto v_resetjp_6318_;
}
else
{
lean_inc(v_fst_6317_);
lean_dec(v_snd_6310_);
v___x_6319_ = lean_box(0);
v_isShared_6320_ = v_isSharedCheck_6418_;
goto v_resetjp_6318_;
}
v_resetjp_6318_:
{
lean_object* v_fst_6321_; lean_object* v___x_6323_; uint8_t v_isShared_6324_; uint8_t v_isSharedCheck_6416_; 
v_fst_6321_ = lean_ctor_get(v_snd_6311_, 0);
v_isSharedCheck_6416_ = !lean_is_exclusive(v_snd_6311_);
if (v_isSharedCheck_6416_ == 0)
{
lean_object* v_unused_6417_; 
v_unused_6417_ = lean_ctor_get(v_snd_6311_, 1);
lean_dec(v_unused_6417_);
v___x_6323_ = v_snd_6311_;
v_isShared_6324_ = v_isSharedCheck_6416_;
goto v_resetjp_6322_;
}
else
{
lean_inc(v_fst_6321_);
lean_dec(v_snd_6311_);
v___x_6323_ = lean_box(0);
v_isShared_6324_ = v_isSharedCheck_6416_;
goto v_resetjp_6322_;
}
v_resetjp_6322_:
{
lean_object* v_array_6325_; lean_object* v_start_6326_; lean_object* v_stop_6327_; uint8_t v___x_6328_; 
v_array_6325_ = lean_ctor_get(v_snd_6312_, 0);
v_start_6326_ = lean_ctor_get(v_snd_6312_, 1);
v_stop_6327_ = lean_ctor_get(v_snd_6312_, 2);
v___x_6328_ = lean_nat_dec_lt(v_start_6326_, v_stop_6327_);
if (v___x_6328_ == 0)
{
lean_object* v___x_6330_; 
if (v_isShared_6324_ == 0)
{
v___x_6330_ = v___x_6323_;
goto v_reusejp_6329_;
}
else
{
lean_object* v_reuseFailAlloc_6339_; 
v_reuseFailAlloc_6339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6339_, 0, v_fst_6321_);
lean_ctor_set(v_reuseFailAlloc_6339_, 1, v_snd_6312_);
v___x_6330_ = v_reuseFailAlloc_6339_;
goto v_reusejp_6329_;
}
v_reusejp_6329_:
{
lean_object* v___x_6332_; 
if (v_isShared_6320_ == 0)
{
lean_ctor_set(v___x_6319_, 1, v___x_6330_);
v___x_6332_ = v___x_6319_;
goto v_reusejp_6331_;
}
else
{
lean_object* v_reuseFailAlloc_6338_; 
v_reuseFailAlloc_6338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6338_, 0, v_fst_6317_);
lean_ctor_set(v_reuseFailAlloc_6338_, 1, v___x_6330_);
v___x_6332_ = v_reuseFailAlloc_6338_;
goto v_reusejp_6331_;
}
v_reusejp_6331_:
{
lean_object* v___x_6334_; 
if (v_isShared_6316_ == 0)
{
lean_ctor_set(v___x_6315_, 1, v___x_6332_);
v___x_6334_ = v___x_6315_;
goto v_reusejp_6333_;
}
else
{
lean_object* v_reuseFailAlloc_6337_; 
v_reuseFailAlloc_6337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6337_, 0, v_fst_6313_);
lean_ctor_set(v_reuseFailAlloc_6337_, 1, v___x_6332_);
v___x_6334_ = v_reuseFailAlloc_6337_;
goto v_reusejp_6333_;
}
v_reusejp_6333_:
{
lean_object* v___x_6335_; lean_object* v___f_6336_; 
v___x_6335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6335_, 0, v___x_6334_);
v___f_6336_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6336_, 0, v___x_6335_);
v___y_6285_ = v___f_6336_;
goto v___jp_6284_;
}
}
}
}
else
{
lean_object* v___x_6341_; uint8_t v_isShared_6342_; uint8_t v_isSharedCheck_6412_; 
lean_inc(v_stop_6327_);
lean_inc(v_start_6326_);
lean_inc_ref(v_array_6325_);
v_isSharedCheck_6412_ = !lean_is_exclusive(v_snd_6312_);
if (v_isSharedCheck_6412_ == 0)
{
lean_object* v_unused_6413_; lean_object* v_unused_6414_; lean_object* v_unused_6415_; 
v_unused_6413_ = lean_ctor_get(v_snd_6312_, 2);
lean_dec(v_unused_6413_);
v_unused_6414_ = lean_ctor_get(v_snd_6312_, 1);
lean_dec(v_unused_6414_);
v_unused_6415_ = lean_ctor_get(v_snd_6312_, 0);
lean_dec(v_unused_6415_);
v___x_6341_ = v_snd_6312_;
v_isShared_6342_ = v_isSharedCheck_6412_;
goto v_resetjp_6340_;
}
else
{
lean_dec(v_snd_6312_);
v___x_6341_ = lean_box(0);
v_isShared_6342_ = v_isSharedCheck_6412_;
goto v_resetjp_6340_;
}
v_resetjp_6340_:
{
lean_object* v_array_6343_; lean_object* v_start_6344_; lean_object* v_stop_6345_; lean_object* v___x_6346_; lean_object* v___x_6347_; lean_object* v___x_6348_; lean_object* v___x_6350_; 
v_array_6343_ = lean_ctor_get(v_fst_6321_, 0);
v_start_6344_ = lean_ctor_get(v_fst_6321_, 1);
v_stop_6345_ = lean_ctor_get(v_fst_6321_, 2);
v___x_6346_ = lean_array_fget(v_array_6325_, v_start_6326_);
v___x_6347_ = lean_unsigned_to_nat(1u);
v___x_6348_ = lean_nat_add(v_start_6326_, v___x_6347_);
lean_dec(v_start_6326_);
if (v_isShared_6342_ == 0)
{
lean_ctor_set(v___x_6341_, 1, v___x_6348_);
v___x_6350_ = v___x_6341_;
goto v_reusejp_6349_;
}
else
{
lean_object* v_reuseFailAlloc_6411_; 
v_reuseFailAlloc_6411_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6411_, 0, v_array_6325_);
lean_ctor_set(v_reuseFailAlloc_6411_, 1, v___x_6348_);
lean_ctor_set(v_reuseFailAlloc_6411_, 2, v_stop_6327_);
v___x_6350_ = v_reuseFailAlloc_6411_;
goto v_reusejp_6349_;
}
v_reusejp_6349_:
{
uint8_t v___x_6351_; 
v___x_6351_ = lean_nat_dec_lt(v_start_6344_, v_stop_6345_);
if (v___x_6351_ == 0)
{
lean_object* v___x_6353_; 
lean_dec(v___x_6346_);
if (v_isShared_6324_ == 0)
{
lean_ctor_set(v___x_6323_, 1, v___x_6350_);
v___x_6353_ = v___x_6323_;
goto v_reusejp_6352_;
}
else
{
lean_object* v_reuseFailAlloc_6362_; 
v_reuseFailAlloc_6362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6362_, 0, v_fst_6321_);
lean_ctor_set(v_reuseFailAlloc_6362_, 1, v___x_6350_);
v___x_6353_ = v_reuseFailAlloc_6362_;
goto v_reusejp_6352_;
}
v_reusejp_6352_:
{
lean_object* v___x_6355_; 
if (v_isShared_6320_ == 0)
{
lean_ctor_set(v___x_6319_, 1, v___x_6353_);
v___x_6355_ = v___x_6319_;
goto v_reusejp_6354_;
}
else
{
lean_object* v_reuseFailAlloc_6361_; 
v_reuseFailAlloc_6361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6361_, 0, v_fst_6317_);
lean_ctor_set(v_reuseFailAlloc_6361_, 1, v___x_6353_);
v___x_6355_ = v_reuseFailAlloc_6361_;
goto v_reusejp_6354_;
}
v_reusejp_6354_:
{
lean_object* v___x_6357_; 
if (v_isShared_6316_ == 0)
{
lean_ctor_set(v___x_6315_, 1, v___x_6355_);
v___x_6357_ = v___x_6315_;
goto v_reusejp_6356_;
}
else
{
lean_object* v_reuseFailAlloc_6360_; 
v_reuseFailAlloc_6360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6360_, 0, v_fst_6313_);
lean_ctor_set(v_reuseFailAlloc_6360_, 1, v___x_6355_);
v___x_6357_ = v_reuseFailAlloc_6360_;
goto v_reusejp_6356_;
}
v_reusejp_6356_:
{
lean_object* v___x_6358_; lean_object* v___f_6359_; 
v___x_6358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6358_, 0, v___x_6357_);
v___f_6359_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6359_, 0, v___x_6358_);
v___y_6285_ = v___f_6359_;
goto v___jp_6284_;
}
}
}
}
else
{
lean_object* v___x_6364_; uint8_t v_isShared_6365_; uint8_t v_isSharedCheck_6407_; 
lean_inc(v_stop_6345_);
lean_inc(v_start_6344_);
lean_inc_ref(v_array_6343_);
v_isSharedCheck_6407_ = !lean_is_exclusive(v_fst_6321_);
if (v_isSharedCheck_6407_ == 0)
{
lean_object* v_unused_6408_; lean_object* v_unused_6409_; lean_object* v_unused_6410_; 
v_unused_6408_ = lean_ctor_get(v_fst_6321_, 2);
lean_dec(v_unused_6408_);
v_unused_6409_ = lean_ctor_get(v_fst_6321_, 1);
lean_dec(v_unused_6409_);
v_unused_6410_ = lean_ctor_get(v_fst_6321_, 0);
lean_dec(v_unused_6410_);
v___x_6364_ = v_fst_6321_;
v_isShared_6365_ = v_isSharedCheck_6407_;
goto v_resetjp_6363_;
}
else
{
lean_dec(v_fst_6321_);
v___x_6364_ = lean_box(0);
v_isShared_6365_ = v_isSharedCheck_6407_;
goto v_resetjp_6363_;
}
v_resetjp_6363_:
{
lean_object* v_array_6366_; lean_object* v_start_6367_; lean_object* v_stop_6368_; lean_object* v___x_6369_; lean_object* v___x_6370_; lean_object* v___x_6372_; 
v_array_6366_ = lean_ctor_get(v_fst_6317_, 0);
v_start_6367_ = lean_ctor_get(v_fst_6317_, 1);
v_stop_6368_ = lean_ctor_get(v_fst_6317_, 2);
v___x_6369_ = lean_array_fget(v_array_6343_, v_start_6344_);
v___x_6370_ = lean_nat_add(v_start_6344_, v___x_6347_);
lean_dec(v_start_6344_);
if (v_isShared_6365_ == 0)
{
lean_ctor_set(v___x_6364_, 1, v___x_6370_);
v___x_6372_ = v___x_6364_;
goto v_reusejp_6371_;
}
else
{
lean_object* v_reuseFailAlloc_6406_; 
v_reuseFailAlloc_6406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6406_, 0, v_array_6343_);
lean_ctor_set(v_reuseFailAlloc_6406_, 1, v___x_6370_);
lean_ctor_set(v_reuseFailAlloc_6406_, 2, v_stop_6345_);
v___x_6372_ = v_reuseFailAlloc_6406_;
goto v_reusejp_6371_;
}
v_reusejp_6371_:
{
uint8_t v___x_6373_; 
v___x_6373_ = lean_nat_dec_lt(v_start_6367_, v_stop_6368_);
if (v___x_6373_ == 0)
{
lean_object* v___x_6375_; 
lean_dec(v___x_6369_);
lean_dec(v___x_6346_);
if (v_isShared_6324_ == 0)
{
lean_ctor_set(v___x_6323_, 1, v___x_6350_);
lean_ctor_set(v___x_6323_, 0, v___x_6372_);
v___x_6375_ = v___x_6323_;
goto v_reusejp_6374_;
}
else
{
lean_object* v_reuseFailAlloc_6384_; 
v_reuseFailAlloc_6384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6384_, 0, v___x_6372_);
lean_ctor_set(v_reuseFailAlloc_6384_, 1, v___x_6350_);
v___x_6375_ = v_reuseFailAlloc_6384_;
goto v_reusejp_6374_;
}
v_reusejp_6374_:
{
lean_object* v___x_6377_; 
if (v_isShared_6320_ == 0)
{
lean_ctor_set(v___x_6319_, 1, v___x_6375_);
v___x_6377_ = v___x_6319_;
goto v_reusejp_6376_;
}
else
{
lean_object* v_reuseFailAlloc_6383_; 
v_reuseFailAlloc_6383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6383_, 0, v_fst_6317_);
lean_ctor_set(v_reuseFailAlloc_6383_, 1, v___x_6375_);
v___x_6377_ = v_reuseFailAlloc_6383_;
goto v_reusejp_6376_;
}
v_reusejp_6376_:
{
lean_object* v___x_6379_; 
if (v_isShared_6316_ == 0)
{
lean_ctor_set(v___x_6315_, 1, v___x_6377_);
v___x_6379_ = v___x_6315_;
goto v_reusejp_6378_;
}
else
{
lean_object* v_reuseFailAlloc_6382_; 
v_reuseFailAlloc_6382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6382_, 0, v_fst_6313_);
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
v___y_6285_ = v___f_6381_;
goto v___jp_6284_;
}
}
}
}
else
{
lean_object* v___x_6386_; uint8_t v_isShared_6387_; uint8_t v_isSharedCheck_6402_; 
lean_inc(v_stop_6368_);
lean_inc(v_start_6367_);
lean_inc_ref(v_array_6366_);
lean_del_object(v___x_6323_);
lean_del_object(v___x_6319_);
lean_del_object(v___x_6315_);
v_isSharedCheck_6402_ = !lean_is_exclusive(v_fst_6317_);
if (v_isSharedCheck_6402_ == 0)
{
lean_object* v_unused_6403_; lean_object* v_unused_6404_; lean_object* v_unused_6405_; 
v_unused_6403_ = lean_ctor_get(v_fst_6317_, 2);
lean_dec(v_unused_6403_);
v_unused_6404_ = lean_ctor_get(v_fst_6317_, 1);
lean_dec(v_unused_6404_);
v_unused_6405_ = lean_ctor_get(v_fst_6317_, 0);
lean_dec(v_unused_6405_);
v___x_6386_ = v_fst_6317_;
v_isShared_6387_ = v_isSharedCheck_6402_;
goto v_resetjp_6385_;
}
else
{
lean_dec(v_fst_6317_);
v___x_6386_ = lean_box(0);
v_isShared_6387_ = v_isSharedCheck_6402_;
goto v_resetjp_6385_;
}
v_resetjp_6385_:
{
lean_object* v___f_6388_; uint8_t v___x_6389_; lean_object* v_remaining_x27_6390_; lean_object* v___x_6391_; lean_object* v___x_6392_; lean_object* v___x_6393_; lean_object* v___f_6394_; lean_object* v___x_6395_; lean_object* v___x_6397_; 
v___f_6388_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___closed__0));
v___x_6389_ = 0;
v_remaining_x27_6390_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_6391_ = lean_array_fget_borrowed(v_array_6366_, v_start_6367_);
v___x_6392_ = lean_box(v___x_6389_);
v___x_6393_ = lean_box(v___x_6373_);
lean_inc(v_extraEqualities_6276_);
lean_inc(v_a_6277_);
lean_inc_ref(v_onAlt_6275_);
lean_inc(v___x_6391_);
v___f_6394_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed), 15, 8);
lean_closure_set(v___f_6394_, 0, v___x_6391_);
lean_closure_set(v___f_6394_, 1, v___f_6388_);
lean_closure_set(v___f_6394_, 2, v___x_6392_);
lean_closure_set(v___f_6394_, 3, v_remaining_x27_6390_);
lean_closure_set(v___f_6394_, 4, v_onAlt_6275_);
lean_closure_set(v___f_6394_, 5, v_a_6277_);
lean_closure_set(v___f_6394_, 6, v___x_6393_);
lean_closure_set(v___f_6394_, 7, v_extraEqualities_6276_);
v___x_6395_ = lean_nat_add(v_start_6367_, v___x_6347_);
lean_dec(v_start_6367_);
if (v_isShared_6387_ == 0)
{
lean_ctor_set(v___x_6386_, 1, v___x_6395_);
v___x_6397_ = v___x_6386_;
goto v_reusejp_6396_;
}
else
{
lean_object* v_reuseFailAlloc_6401_; 
v_reuseFailAlloc_6401_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6401_, 0, v_array_6366_);
lean_ctor_set(v_reuseFailAlloc_6401_, 1, v___x_6395_);
lean_ctor_set(v_reuseFailAlloc_6401_, 2, v_stop_6368_);
v___x_6397_ = v_reuseFailAlloc_6401_;
goto v_reusejp_6396_;
}
v_reusejp_6396_:
{
lean_object* v___x_6398_; lean_object* v___x_6399_; lean_object* v___f_6400_; 
v___x_6398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6398_, 0, v___x_6369_);
v___x_6399_ = lean_box(v___x_6389_);
v___f_6400_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed), 13, 8);
lean_closure_set(v___f_6400_, 0, v___x_6346_);
lean_closure_set(v___f_6400_, 1, v___x_6398_);
lean_closure_set(v___f_6400_, 2, v___f_6394_);
lean_closure_set(v___f_6400_, 3, v___x_6399_);
lean_closure_set(v___f_6400_, 4, v_fst_6313_);
lean_closure_set(v___f_6400_, 5, v___x_6372_);
lean_closure_set(v___f_6400_, 6, v___x_6350_);
lean_closure_set(v___f_6400_, 7, v___x_6397_);
v___y_6285_ = v___f_6400_;
goto v___jp_6284_;
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_6284_:
{
lean_object* v___x_6286_; 
lean_inc(v___y_6282_);
lean_inc_ref(v___y_6281_);
lean_inc(v___y_6280_);
lean_inc_ref(v___y_6279_);
v___x_6286_ = lean_apply_5(v___y_6285_, v___y_6279_, v___y_6280_, v___y_6281_, v___y_6282_, lean_box(0));
if (lean_obj_tag(v___x_6286_) == 0)
{
lean_object* v_a_6287_; lean_object* v___x_6289_; uint8_t v_isShared_6290_; uint8_t v_isSharedCheck_6299_; 
v_a_6287_ = lean_ctor_get(v___x_6286_, 0);
v_isSharedCheck_6299_ = !lean_is_exclusive(v___x_6286_);
if (v_isSharedCheck_6299_ == 0)
{
v___x_6289_ = v___x_6286_;
v_isShared_6290_ = v_isSharedCheck_6299_;
goto v_resetjp_6288_;
}
else
{
lean_inc(v_a_6287_);
lean_dec(v___x_6286_);
v___x_6289_ = lean_box(0);
v_isShared_6290_ = v_isSharedCheck_6299_;
goto v_resetjp_6288_;
}
v_resetjp_6288_:
{
if (lean_obj_tag(v_a_6287_) == 0)
{
lean_object* v_a_6291_; lean_object* v___x_6293_; 
lean_dec(v_a_6277_);
lean_dec(v_extraEqualities_6276_);
lean_dec_ref(v_onAlt_6275_);
v_a_6291_ = lean_ctor_get(v_a_6287_, 0);
lean_inc(v_a_6291_);
lean_dec_ref(v_a_6287_);
if (v_isShared_6290_ == 0)
{
lean_ctor_set(v___x_6289_, 0, v_a_6291_);
v___x_6293_ = v___x_6289_;
goto v_reusejp_6292_;
}
else
{
lean_object* v_reuseFailAlloc_6294_; 
v_reuseFailAlloc_6294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6294_, 0, v_a_6291_);
v___x_6293_ = v_reuseFailAlloc_6294_;
goto v_reusejp_6292_;
}
v_reusejp_6292_:
{
return v___x_6293_;
}
}
else
{
lean_object* v_a_6295_; lean_object* v___x_6296_; lean_object* v___x_6297_; 
lean_del_object(v___x_6289_);
v_a_6295_ = lean_ctor_get(v_a_6287_, 0);
lean_inc(v_a_6295_);
lean_dec_ref(v_a_6287_);
v___x_6296_ = lean_unsigned_to_nat(1u);
v___x_6297_ = lean_nat_add(v_a_6277_, v___x_6296_);
lean_dec(v_a_6277_);
v_a_6277_ = v___x_6297_;
v_b_6278_ = v_a_6295_;
goto _start;
}
}
}
else
{
lean_object* v_a_6300_; lean_object* v___x_6302_; uint8_t v_isShared_6303_; uint8_t v_isSharedCheck_6307_; 
lean_dec(v_a_6277_);
lean_dec(v_extraEqualities_6276_);
lean_dec_ref(v_onAlt_6275_);
v_a_6300_ = lean_ctor_get(v___x_6286_, 0);
v_isSharedCheck_6307_ = !lean_is_exclusive(v___x_6286_);
if (v_isSharedCheck_6307_ == 0)
{
v___x_6302_ = v___x_6286_;
v_isShared_6303_ = v_isSharedCheck_6307_;
goto v_resetjp_6301_;
}
else
{
lean_inc(v_a_6300_);
lean_dec(v___x_6286_);
v___x_6302_ = lean_box(0);
v_isShared_6303_ = v_isSharedCheck_6307_;
goto v_resetjp_6301_;
}
v_resetjp_6301_:
{
lean_object* v___x_6305_; 
if (v_isShared_6303_ == 0)
{
v___x_6305_ = v___x_6302_;
goto v_reusejp_6304_;
}
else
{
lean_object* v_reuseFailAlloc_6306_; 
v_reuseFailAlloc_6306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6306_, 0, v_a_6300_);
v___x_6305_ = v_reuseFailAlloc_6306_;
goto v_reusejp_6304_;
}
v_reusejp_6304_:
{
return v___x_6305_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___boxed(lean_object* v_upperBound_6422_, lean_object* v_onAlt_6423_, lean_object* v_extraEqualities_6424_, lean_object* v_a_6425_, lean_object* v_b_6426_, lean_object* v___y_6427_, lean_object* v___y_6428_, lean_object* v___y_6429_, lean_object* v___y_6430_, lean_object* v___y_6431_){
_start:
{
lean_object* v_res_6432_; 
v_res_6432_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v_upperBound_6422_, v_onAlt_6423_, v_extraEqualities_6424_, v_a_6425_, v_b_6426_, v___y_6427_, v___y_6428_, v___y_6429_, v___y_6430_);
lean_dec(v___y_6430_);
lean_dec_ref(v___y_6429_);
lean_dec(v___y_6428_);
lean_dec_ref(v___y_6427_);
lean_dec(v_upperBound_6422_);
return v_res_6432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(lean_object* v_onParams_6433_, size_t v_sz_6434_, size_t v_i_6435_, lean_object* v_bs_6436_, lean_object* v___y_6437_, lean_object* v___y_6438_, lean_object* v___y_6439_, lean_object* v___y_6440_){
_start:
{
uint8_t v___x_6442_; 
v___x_6442_ = lean_usize_dec_lt(v_i_6435_, v_sz_6434_);
if (v___x_6442_ == 0)
{
lean_object* v___x_6443_; 
lean_dec_ref(v_onParams_6433_);
v___x_6443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6443_, 0, v_bs_6436_);
return v___x_6443_;
}
else
{
lean_object* v_v_6444_; lean_object* v___x_6445_; 
v_v_6444_ = lean_array_uget_borrowed(v_bs_6436_, v_i_6435_);
lean_inc_ref(v_onParams_6433_);
lean_inc(v___y_6440_);
lean_inc_ref(v___y_6439_);
lean_inc(v___y_6438_);
lean_inc_ref(v___y_6437_);
lean_inc(v_v_6444_);
v___x_6445_ = lean_apply_6(v_onParams_6433_, v_v_6444_, v___y_6437_, v___y_6438_, v___y_6439_, v___y_6440_, lean_box(0));
if (lean_obj_tag(v___x_6445_) == 0)
{
lean_object* v_a_6446_; lean_object* v___x_6447_; lean_object* v_bs_x27_6448_; size_t v___x_6449_; size_t v___x_6450_; lean_object* v___x_6451_; 
v_a_6446_ = lean_ctor_get(v___x_6445_, 0);
lean_inc(v_a_6446_);
lean_dec_ref(v___x_6445_);
v___x_6447_ = lean_unsigned_to_nat(0u);
v_bs_x27_6448_ = lean_array_uset(v_bs_6436_, v_i_6435_, v___x_6447_);
v___x_6449_ = ((size_t)1ULL);
v___x_6450_ = lean_usize_add(v_i_6435_, v___x_6449_);
v___x_6451_ = lean_array_uset(v_bs_x27_6448_, v_i_6435_, v_a_6446_);
v_i_6435_ = v___x_6450_;
v_bs_6436_ = v___x_6451_;
goto _start;
}
else
{
lean_object* v_a_6453_; lean_object* v___x_6455_; uint8_t v_isShared_6456_; uint8_t v_isSharedCheck_6460_; 
lean_dec_ref(v_bs_6436_);
lean_dec_ref(v_onParams_6433_);
v_a_6453_ = lean_ctor_get(v___x_6445_, 0);
v_isSharedCheck_6460_ = !lean_is_exclusive(v___x_6445_);
if (v_isSharedCheck_6460_ == 0)
{
v___x_6455_ = v___x_6445_;
v_isShared_6456_ = v_isSharedCheck_6460_;
goto v_resetjp_6454_;
}
else
{
lean_inc(v_a_6453_);
lean_dec(v___x_6445_);
v___x_6455_ = lean_box(0);
v_isShared_6456_ = v_isSharedCheck_6460_;
goto v_resetjp_6454_;
}
v_resetjp_6454_:
{
lean_object* v___x_6458_; 
if (v_isShared_6456_ == 0)
{
v___x_6458_ = v___x_6455_;
goto v_reusejp_6457_;
}
else
{
lean_object* v_reuseFailAlloc_6459_; 
v_reuseFailAlloc_6459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6459_, 0, v_a_6453_);
v___x_6458_ = v_reuseFailAlloc_6459_;
goto v_reusejp_6457_;
}
v_reusejp_6457_:
{
return v___x_6458_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6___boxed(lean_object* v_onParams_6461_, lean_object* v_sz_6462_, lean_object* v_i_6463_, lean_object* v_bs_6464_, lean_object* v___y_6465_, lean_object* v___y_6466_, lean_object* v___y_6467_, lean_object* v___y_6468_, lean_object* v___y_6469_){
_start:
{
size_t v_sz_boxed_6470_; size_t v_i_boxed_6471_; lean_object* v_res_6472_; 
v_sz_boxed_6470_ = lean_unbox_usize(v_sz_6462_);
lean_dec(v_sz_6462_);
v_i_boxed_6471_ = lean_unbox_usize(v_i_6463_);
lean_dec(v_i_6463_);
v_res_6472_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6461_, v_sz_boxed_6470_, v_i_boxed_6471_, v_bs_6464_, v___y_6465_, v___y_6466_, v___y_6467_, v___y_6468_);
lean_dec(v___y_6468_);
lean_dec_ref(v___y_6467_);
lean_dec(v___y_6466_);
lean_dec_ref(v___y_6465_);
return v_res_6472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(lean_object* v_declName_6473_, lean_object* v___y_6474_){
_start:
{
lean_object* v___x_6476_; lean_object* v_env_6477_; lean_object* v___x_6478_; lean_object* v___x_6479_; 
v___x_6476_ = lean_st_ref_get(v___y_6474_);
v_env_6477_ = lean_ctor_get(v___x_6476_, 0);
lean_inc_ref(v_env_6477_);
lean_dec(v___x_6476_);
v___x_6478_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_6477_, v_declName_6473_);
v___x_6479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6479_, 0, v___x_6478_);
return v___x_6479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg___boxed(lean_object* v_declName_6480_, lean_object* v___y_6481_, lean_object* v___y_6482_){
_start:
{
lean_object* v_res_6483_; 
v_res_6483_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_declName_6480_, v___y_6481_);
lean_dec(v___y_6481_);
return v_res_6483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(lean_object* v_matcherApp_6486_, uint8_t v_useSplitter_6487_, uint8_t v_addEqualities_6488_, lean_object* v_onParams_6489_, lean_object* v_onMotive_6490_, lean_object* v_onAlt_6491_, lean_object* v_onRemaining_6492_, lean_object* v___y_6493_, lean_object* v___y_6494_, lean_object* v___y_6495_, lean_object* v___y_6496_){
_start:
{
lean_object* v___x_6498_; lean_object* v_env_6499_; lean_object* v_toMatcherInfo_6500_; lean_object* v_matcherName_6501_; lean_object* v_matcherLevels_6502_; lean_object* v_params_6503_; lean_object* v_motive_6504_; lean_object* v_discrs_6505_; lean_object* v_alts_6506_; lean_object* v_remaining_6507_; lean_object* v___y_6509_; lean_object* v___y_6510_; lean_object* v___y_6511_; lean_object* v___y_6512_; lean_object* v___y_6513_; lean_object* v___y_6514_; lean_object* v___y_6515_; lean_object* v___y_6516_; lean_object* v___y_6517_; lean_object* v___y_6518_; lean_object* v___y_6519_; lean_object* v___y_6520_; lean_object* v___y_6521_; uint8_t v_isCasesOn_6604_; lean_object* v___y_6606_; lean_object* v___y_6607_; lean_object* v___y_6608_; lean_object* v___y_6609_; lean_object* v___y_6610_; lean_object* v___y_6611_; size_t v___y_6612_; lean_object* v_matcherLevels_6613_; lean_object* v___y_6614_; lean_object* v___y_6615_; lean_object* v___y_6616_; lean_object* v___y_6617_; lean_object* v_numDiscrEqs_6808_; lean_object* v___y_6809_; lean_object* v___y_6810_; lean_object* v___y_6811_; lean_object* v___y_6812_; 
v___x_6498_ = lean_st_ref_get(v___y_6496_);
v_env_6499_ = lean_ctor_get(v___x_6498_, 0);
lean_inc_ref(v_env_6499_);
lean_dec(v___x_6498_);
v_toMatcherInfo_6500_ = lean_ctor_get(v_matcherApp_6486_, 0);
lean_inc_ref(v_toMatcherInfo_6500_);
v_matcherName_6501_ = lean_ctor_get(v_matcherApp_6486_, 1);
lean_inc_n(v_matcherName_6501_, 2);
v_matcherLevels_6502_ = lean_ctor_get(v_matcherApp_6486_, 2);
v_params_6503_ = lean_ctor_get(v_matcherApp_6486_, 3);
v_motive_6504_ = lean_ctor_get(v_matcherApp_6486_, 4);
v_discrs_6505_ = lean_ctor_get(v_matcherApp_6486_, 5);
v_alts_6506_ = lean_ctor_get(v_matcherApp_6486_, 6);
lean_inc_ref(v_alts_6506_);
v_remaining_6507_ = lean_ctor_get(v_matcherApp_6486_, 7);
lean_inc_ref(v_remaining_6507_);
v_isCasesOn_6604_ = l_Lean_isCasesOnRecursor(v_env_6499_, v_matcherName_6501_);
if (v_isCasesOn_6604_ == 0)
{
lean_object* v___x_6862_; lean_object* v_a_6863_; 
lean_inc(v_matcherName_6501_);
v___x_6862_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_matcherName_6501_, v___y_6496_);
v_a_6863_ = lean_ctor_get(v___x_6862_, 0);
lean_inc(v_a_6863_);
lean_dec_ref(v___x_6862_);
if (lean_obj_tag(v_a_6863_) == 0)
{
lean_object* v___x_6864_; lean_object* v___x_6865_; lean_object* v___x_6866_; lean_object* v___x_6867_; lean_object* v___x_6868_; lean_object* v___x_6869_; lean_object* v_a_6870_; lean_object* v___x_6872_; uint8_t v_isShared_6873_; uint8_t v_isSharedCheck_6877_; 
lean_dec_ref(v_remaining_6507_);
lean_dec_ref(v_alts_6506_);
lean_dec_ref(v_toMatcherInfo_6500_);
lean_dec_ref(v_onRemaining_6492_);
lean_dec_ref(v_onAlt_6491_);
lean_dec_ref(v_onMotive_6490_);
lean_dec_ref(v_onParams_6489_);
lean_dec_ref(v_matcherApp_6486_);
v___x_6864_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1);
v___x_6865_ = l_Lean_MessageData_ofName(v_matcherName_6501_);
v___x_6866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6866_, 0, v___x_6864_);
lean_ctor_set(v___x_6866_, 1, v___x_6865_);
v___x_6867_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3);
v___x_6868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6868_, 0, v___x_6866_);
lean_ctor_set(v___x_6868_, 1, v___x_6867_);
v___x_6869_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_6868_, v___y_6493_, v___y_6494_, v___y_6495_, v___y_6496_);
v_a_6870_ = lean_ctor_get(v___x_6869_, 0);
v_isSharedCheck_6877_ = !lean_is_exclusive(v___x_6869_);
if (v_isSharedCheck_6877_ == 0)
{
v___x_6872_ = v___x_6869_;
v_isShared_6873_ = v_isSharedCheck_6877_;
goto v_resetjp_6871_;
}
else
{
lean_inc(v_a_6870_);
lean_dec(v___x_6869_);
v___x_6872_ = lean_box(0);
v_isShared_6873_ = v_isSharedCheck_6877_;
goto v_resetjp_6871_;
}
v_resetjp_6871_:
{
lean_object* v___x_6875_; 
if (v_isShared_6873_ == 0)
{
v___x_6875_ = v___x_6872_;
goto v_reusejp_6874_;
}
else
{
lean_object* v_reuseFailAlloc_6876_; 
v_reuseFailAlloc_6876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6876_, 0, v_a_6870_);
v___x_6875_ = v_reuseFailAlloc_6876_;
goto v_reusejp_6874_;
}
v_reusejp_6874_:
{
return v___x_6875_;
}
}
}
else
{
lean_object* v_val_6878_; lean_object* v___x_6879_; 
v_val_6878_ = lean_ctor_get(v_a_6863_, 0);
lean_inc(v_val_6878_);
lean_dec_ref(v_a_6863_);
v___x_6879_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_6878_);
lean_dec(v_val_6878_);
v_numDiscrEqs_6808_ = v___x_6879_;
v___y_6809_ = v___y_6493_;
v___y_6810_ = v___y_6494_;
v___y_6811_ = v___y_6495_;
v___y_6812_ = v___y_6496_;
goto v___jp_6807_;
}
}
else
{
lean_object* v___x_6880_; 
v___x_6880_ = lean_unsigned_to_nat(0u);
v_numDiscrEqs_6808_ = v___x_6880_;
v___y_6809_ = v___y_6493_;
v___y_6810_ = v___y_6494_;
v___y_6811_ = v___y_6495_;
v___y_6812_ = v___y_6496_;
goto v___jp_6807_;
}
v___jp_6508_:
{
lean_object* v___x_6522_; lean_object* v___x_6523_; lean_object* v_aux_6524_; lean_object* v_aux_6525_; lean_object* v_aux_6526_; lean_object* v___x_6527_; lean_object* v___x_6528_; lean_object* v___x_6529_; lean_object* v___f_6530_; lean_object* v___x_6531_; lean_object* v___x_6532_; 
lean_inc_ref(v___y_6516_);
v___x_6522_ = lean_array_to_list(v___y_6516_);
lean_inc(v_matcherName_6501_);
v___x_6523_ = l_Lean_mkConst(v_matcherName_6501_, v___x_6522_);
v_aux_6524_ = l_Lean_mkAppN(v___x_6523_, v___y_6517_);
lean_inc_ref(v___y_6509_);
v_aux_6525_ = l_Lean_Expr_app___override(v_aux_6524_, v___y_6509_);
v_aux_6526_ = l_Lean_mkAppN(v_aux_6525_, v___y_6518_);
v___x_6527_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__1);
lean_inc_ref_n(v_aux_6526_, 2);
v___x_6528_ = l_Lean_indentExpr(v_aux_6526_);
v___x_6529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6529_, 0, v___x_6527_);
lean_ctor_set(v___x_6529_, 1, v___x_6528_);
v___f_6530_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6530_, 0, v___x_6529_);
v___x_6531_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(v___x_6531_, 0, v_aux_6526_);
v___x_6532_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6531_, v___f_6530_, v___y_6521_, v___y_6510_, v___y_6515_, v___y_6519_);
if (lean_obj_tag(v___x_6532_) == 0)
{
lean_object* v___x_6533_; lean_object* v___x_6534_; 
lean_dec_ref(v___x_6532_);
v___x_6533_ = lean_array_get_size(v_alts_6506_);
v___x_6534_ = l_Lean_Meta_inferArgumentTypesN(v___x_6533_, v_aux_6526_, v___y_6521_, v___y_6510_, v___y_6515_, v___y_6519_);
if (lean_obj_tag(v___x_6534_) == 0)
{
lean_object* v_a_6535_; lean_object* v___x_6536_; lean_object* v___x_6537_; lean_object* v___x_6538_; lean_object* v___x_6539_; lean_object* v___x_6540_; lean_object* v___x_6541_; lean_object* v___x_6542_; lean_object* v___x_6543_; lean_object* v___x_6544_; lean_object* v___x_6545_; 
v_a_6535_ = lean_ctor_get(v___x_6534_, 0);
lean_inc(v_a_6535_);
lean_dec_ref(v___x_6534_);
v___x_6536_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_6486_);
v___x_6537_ = lean_array_get_size(v___x_6536_);
v___x_6538_ = lean_array_get_size(v_a_6535_);
lean_inc_n(v___y_6513_, 3);
v___x_6539_ = l_Array_toSubarray___redArg(v_alts_6506_, v___y_6513_, v___x_6533_);
v___x_6540_ = l_Array_toSubarray___redArg(v___x_6536_, v___y_6513_, v___x_6537_);
v___x_6541_ = l_Array_toSubarray___redArg(v_a_6535_, v___y_6513_, v___x_6538_);
v___x_6542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6542_, 0, v___x_6540_);
lean_ctor_set(v___x_6542_, 1, v___x_6541_);
v___x_6543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6543_, 0, v___x_6539_);
lean_ctor_set(v___x_6543_, 1, v___x_6542_);
lean_inc_ref(v___y_6512_);
v___x_6544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6544_, 0, v___y_6512_);
lean_ctor_set(v___x_6544_, 1, v___x_6543_);
v___x_6545_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v___x_6533_, v_onAlt_6491_, v___y_6514_, v___y_6513_, v___x_6544_, v___y_6521_, v___y_6510_, v___y_6515_, v___y_6519_);
if (lean_obj_tag(v___x_6545_) == 0)
{
lean_object* v_a_6546_; lean_object* v_fst_6547_; lean_object* v___x_6548_; 
v_a_6546_ = lean_ctor_get(v___x_6545_, 0);
lean_inc(v_a_6546_);
lean_dec_ref(v___x_6545_);
v_fst_6547_ = lean_ctor_get(v_a_6546_, 0);
lean_inc(v_fst_6547_);
lean_dec(v_a_6546_);
lean_inc(v___y_6519_);
lean_inc_ref(v___y_6515_);
lean_inc(v___y_6510_);
lean_inc_ref(v___y_6521_);
v___x_6548_ = lean_apply_6(v_onRemaining_6492_, v_remaining_6507_, v___y_6521_, v___y_6510_, v___y_6515_, v___y_6519_, lean_box(0));
if (lean_obj_tag(v___x_6548_) == 0)
{
lean_object* v_a_6549_; lean_object* v___x_6551_; uint8_t v_isShared_6552_; uint8_t v_isSharedCheck_6571_; 
v_a_6549_ = lean_ctor_get(v___x_6548_, 0);
v_isSharedCheck_6571_ = !lean_is_exclusive(v___x_6548_);
if (v_isSharedCheck_6571_ == 0)
{
v___x_6551_ = v___x_6548_;
v_isShared_6552_ = v_isSharedCheck_6571_;
goto v_resetjp_6550_;
}
else
{
lean_inc(v_a_6549_);
lean_dec(v___x_6548_);
v___x_6551_ = lean_box(0);
v_isShared_6552_ = v_isSharedCheck_6571_;
goto v_resetjp_6550_;
}
v_resetjp_6550_:
{
lean_object* v_numParams_6553_; lean_object* v_numDiscrs_6554_; lean_object* v_altInfos_6555_; lean_object* v_uElimPos_x3f_6556_; lean_object* v_overlaps_6557_; lean_object* v___x_6559_; uint8_t v_isShared_6560_; uint8_t v_isSharedCheck_6569_; 
v_numParams_6553_ = lean_ctor_get(v_toMatcherInfo_6500_, 0);
v_numDiscrs_6554_ = lean_ctor_get(v_toMatcherInfo_6500_, 1);
v_altInfos_6555_ = lean_ctor_get(v_toMatcherInfo_6500_, 2);
v_uElimPos_x3f_6556_ = lean_ctor_get(v_toMatcherInfo_6500_, 3);
v_overlaps_6557_ = lean_ctor_get(v_toMatcherInfo_6500_, 5);
v_isSharedCheck_6569_ = !lean_is_exclusive(v_toMatcherInfo_6500_);
if (v_isSharedCheck_6569_ == 0)
{
lean_object* v_unused_6570_; 
v_unused_6570_ = lean_ctor_get(v_toMatcherInfo_6500_, 4);
lean_dec(v_unused_6570_);
v___x_6559_ = v_toMatcherInfo_6500_;
v_isShared_6560_ = v_isSharedCheck_6569_;
goto v_resetjp_6558_;
}
else
{
lean_inc(v_overlaps_6557_);
lean_inc(v_uElimPos_x3f_6556_);
lean_inc(v_altInfos_6555_);
lean_inc(v_numDiscrs_6554_);
lean_inc(v_numParams_6553_);
lean_dec(v_toMatcherInfo_6500_);
v___x_6559_ = lean_box(0);
v_isShared_6560_ = v_isSharedCheck_6569_;
goto v_resetjp_6558_;
}
v_resetjp_6558_:
{
lean_object* v_remaining_x27_6561_; lean_object* v___x_6563_; 
v_remaining_x27_6561_ = l_Array_append___redArg(v___y_6520_, v_a_6549_);
lean_dec(v_a_6549_);
if (v_isShared_6560_ == 0)
{
lean_ctor_set(v___x_6559_, 4, v___y_6511_);
v___x_6563_ = v___x_6559_;
goto v_reusejp_6562_;
}
else
{
lean_object* v_reuseFailAlloc_6568_; 
v_reuseFailAlloc_6568_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6568_, 0, v_numParams_6553_);
lean_ctor_set(v_reuseFailAlloc_6568_, 1, v_numDiscrs_6554_);
lean_ctor_set(v_reuseFailAlloc_6568_, 2, v_altInfos_6555_);
lean_ctor_set(v_reuseFailAlloc_6568_, 3, v_uElimPos_x3f_6556_);
lean_ctor_set(v_reuseFailAlloc_6568_, 4, v___y_6511_);
lean_ctor_set(v_reuseFailAlloc_6568_, 5, v_overlaps_6557_);
v___x_6563_ = v_reuseFailAlloc_6568_;
goto v_reusejp_6562_;
}
v_reusejp_6562_:
{
lean_object* v___x_6564_; lean_object* v___x_6566_; 
v___x_6564_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6564_, 0, v___x_6563_);
lean_ctor_set(v___x_6564_, 1, v_matcherName_6501_);
lean_ctor_set(v___x_6564_, 2, v___y_6516_);
lean_ctor_set(v___x_6564_, 3, v___y_6517_);
lean_ctor_set(v___x_6564_, 4, v___y_6509_);
lean_ctor_set(v___x_6564_, 5, v___y_6518_);
lean_ctor_set(v___x_6564_, 6, v_fst_6547_);
lean_ctor_set(v___x_6564_, 7, v_remaining_x27_6561_);
if (v_isShared_6552_ == 0)
{
lean_ctor_set(v___x_6551_, 0, v___x_6564_);
v___x_6566_ = v___x_6551_;
goto v_reusejp_6565_;
}
else
{
lean_object* v_reuseFailAlloc_6567_; 
v_reuseFailAlloc_6567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6567_, 0, v___x_6564_);
v___x_6566_ = v_reuseFailAlloc_6567_;
goto v_reusejp_6565_;
}
v_reusejp_6565_:
{
return v___x_6566_;
}
}
}
}
}
else
{
lean_object* v_a_6572_; lean_object* v___x_6574_; uint8_t v_isShared_6575_; uint8_t v_isSharedCheck_6579_; 
lean_dec(v_fst_6547_);
lean_dec(v___y_6520_);
lean_dec_ref(v___y_6518_);
lean_dec_ref(v___y_6517_);
lean_dec_ref(v___y_6516_);
lean_dec_ref(v___y_6511_);
lean_dec_ref(v___y_6509_);
lean_dec(v_matcherName_6501_);
lean_dec_ref(v_toMatcherInfo_6500_);
v_a_6572_ = lean_ctor_get(v___x_6548_, 0);
v_isSharedCheck_6579_ = !lean_is_exclusive(v___x_6548_);
if (v_isSharedCheck_6579_ == 0)
{
v___x_6574_ = v___x_6548_;
v_isShared_6575_ = v_isSharedCheck_6579_;
goto v_resetjp_6573_;
}
else
{
lean_inc(v_a_6572_);
lean_dec(v___x_6548_);
v___x_6574_ = lean_box(0);
v_isShared_6575_ = v_isSharedCheck_6579_;
goto v_resetjp_6573_;
}
v_resetjp_6573_:
{
lean_object* v___x_6577_; 
if (v_isShared_6575_ == 0)
{
v___x_6577_ = v___x_6574_;
goto v_reusejp_6576_;
}
else
{
lean_object* v_reuseFailAlloc_6578_; 
v_reuseFailAlloc_6578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6578_, 0, v_a_6572_);
v___x_6577_ = v_reuseFailAlloc_6578_;
goto v_reusejp_6576_;
}
v_reusejp_6576_:
{
return v___x_6577_;
}
}
}
}
else
{
lean_object* v_a_6580_; lean_object* v___x_6582_; uint8_t v_isShared_6583_; uint8_t v_isSharedCheck_6587_; 
lean_dec(v___y_6520_);
lean_dec_ref(v___y_6518_);
lean_dec_ref(v___y_6517_);
lean_dec_ref(v___y_6516_);
lean_dec_ref(v___y_6511_);
lean_dec_ref(v___y_6509_);
lean_dec_ref(v_remaining_6507_);
lean_dec(v_matcherName_6501_);
lean_dec_ref(v_toMatcherInfo_6500_);
lean_dec_ref(v_onRemaining_6492_);
v_a_6580_ = lean_ctor_get(v___x_6545_, 0);
v_isSharedCheck_6587_ = !lean_is_exclusive(v___x_6545_);
if (v_isSharedCheck_6587_ == 0)
{
v___x_6582_ = v___x_6545_;
v_isShared_6583_ = v_isSharedCheck_6587_;
goto v_resetjp_6581_;
}
else
{
lean_inc(v_a_6580_);
lean_dec(v___x_6545_);
v___x_6582_ = lean_box(0);
v_isShared_6583_ = v_isSharedCheck_6587_;
goto v_resetjp_6581_;
}
v_resetjp_6581_:
{
lean_object* v___x_6585_; 
if (v_isShared_6583_ == 0)
{
v___x_6585_ = v___x_6582_;
goto v_reusejp_6584_;
}
else
{
lean_object* v_reuseFailAlloc_6586_; 
v_reuseFailAlloc_6586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6586_, 0, v_a_6580_);
v___x_6585_ = v_reuseFailAlloc_6586_;
goto v_reusejp_6584_;
}
v_reusejp_6584_:
{
return v___x_6585_;
}
}
}
}
else
{
lean_object* v_a_6588_; lean_object* v___x_6590_; uint8_t v_isShared_6591_; uint8_t v_isSharedCheck_6595_; 
lean_dec(v___y_6520_);
lean_dec_ref(v___y_6518_);
lean_dec_ref(v___y_6517_);
lean_dec_ref(v___y_6516_);
lean_dec(v___y_6514_);
lean_dec(v___y_6513_);
lean_dec_ref(v___y_6511_);
lean_dec_ref(v___y_6509_);
lean_dec_ref(v_remaining_6507_);
lean_dec_ref(v_alts_6506_);
lean_dec(v_matcherName_6501_);
lean_dec_ref(v_toMatcherInfo_6500_);
lean_dec_ref(v_onRemaining_6492_);
lean_dec_ref(v_onAlt_6491_);
lean_dec_ref(v_matcherApp_6486_);
v_a_6588_ = lean_ctor_get(v___x_6534_, 0);
v_isSharedCheck_6595_ = !lean_is_exclusive(v___x_6534_);
if (v_isSharedCheck_6595_ == 0)
{
v___x_6590_ = v___x_6534_;
v_isShared_6591_ = v_isSharedCheck_6595_;
goto v_resetjp_6589_;
}
else
{
lean_inc(v_a_6588_);
lean_dec(v___x_6534_);
v___x_6590_ = lean_box(0);
v_isShared_6591_ = v_isSharedCheck_6595_;
goto v_resetjp_6589_;
}
v_resetjp_6589_:
{
lean_object* v___x_6593_; 
if (v_isShared_6591_ == 0)
{
v___x_6593_ = v___x_6590_;
goto v_reusejp_6592_;
}
else
{
lean_object* v_reuseFailAlloc_6594_; 
v_reuseFailAlloc_6594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6594_, 0, v_a_6588_);
v___x_6593_ = v_reuseFailAlloc_6594_;
goto v_reusejp_6592_;
}
v_reusejp_6592_:
{
return v___x_6593_;
}
}
}
}
else
{
lean_object* v_a_6596_; lean_object* v___x_6598_; uint8_t v_isShared_6599_; uint8_t v_isSharedCheck_6603_; 
lean_dec_ref(v_aux_6526_);
lean_dec(v___y_6520_);
lean_dec_ref(v___y_6518_);
lean_dec_ref(v___y_6517_);
lean_dec_ref(v___y_6516_);
lean_dec(v___y_6514_);
lean_dec(v___y_6513_);
lean_dec_ref(v___y_6511_);
lean_dec_ref(v___y_6509_);
lean_dec_ref(v_remaining_6507_);
lean_dec_ref(v_alts_6506_);
lean_dec(v_matcherName_6501_);
lean_dec_ref(v_toMatcherInfo_6500_);
lean_dec_ref(v_onRemaining_6492_);
lean_dec_ref(v_onAlt_6491_);
lean_dec_ref(v_matcherApp_6486_);
v_a_6596_ = lean_ctor_get(v___x_6532_, 0);
v_isSharedCheck_6603_ = !lean_is_exclusive(v___x_6532_);
if (v_isSharedCheck_6603_ == 0)
{
v___x_6598_ = v___x_6532_;
v_isShared_6599_ = v_isSharedCheck_6603_;
goto v_resetjp_6597_;
}
else
{
lean_inc(v_a_6596_);
lean_dec(v___x_6532_);
v___x_6598_ = lean_box(0);
v_isShared_6599_ = v_isSharedCheck_6603_;
goto v_resetjp_6597_;
}
v_resetjp_6597_:
{
lean_object* v___x_6601_; 
if (v_isShared_6599_ == 0)
{
v___x_6601_ = v___x_6598_;
goto v_reusejp_6600_;
}
else
{
lean_object* v_reuseFailAlloc_6602_; 
v_reuseFailAlloc_6602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6602_, 0, v_a_6596_);
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
v___jp_6605_:
{
lean_object* v___x_6618_; lean_object* v_remaining_x27_6619_; lean_object* v___x_6620_; lean_object* v___x_6621_; lean_object* v___x_6622_; lean_object* v___x_6623_; lean_object* v___x_6624_; lean_object* v___x_6625_; size_t v_sz_6626_; lean_object* v___x_6627_; 
v___x_6618_ = lean_unsigned_to_nat(0u);
v_remaining_x27_6619_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_6620_ = l_Array_reverse___redArg(v___y_6609_);
v___x_6621_ = lean_array_get_size(v___x_6620_);
v___x_6622_ = l_Array_toSubarray___redArg(v___x_6620_, v___x_6618_, v___x_6621_);
lean_inc_ref(v___y_6611_);
v___x_6623_ = l_Array_reverse___redArg(v___y_6611_);
v___x_6624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6624_, 0, v___x_6618_);
lean_ctor_set(v___x_6624_, 1, v___x_6622_);
v___x_6625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6625_, 0, v_remaining_x27_6619_);
lean_ctor_set(v___x_6625_, 1, v___x_6624_);
v_sz_6626_ = lean_array_size(v___x_6623_);
v___x_6627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(v___x_6623_, v_sz_6626_, v___y_6612_, v___x_6625_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_);
lean_dec_ref(v___x_6623_);
if (lean_obj_tag(v___x_6627_) == 0)
{
lean_object* v_a_6628_; lean_object* v_snd_6629_; 
v_a_6628_ = lean_ctor_get(v___x_6627_, 0);
lean_inc(v_a_6628_);
lean_dec_ref(v___x_6627_);
v_snd_6629_ = lean_ctor_get(v_a_6628_, 1);
lean_inc(v_snd_6629_);
if (v_useSplitter_6487_ == 0)
{
lean_object* v_fst_6630_; lean_object* v_fst_6631_; 
lean_dec(v___y_6606_);
v_fst_6630_ = lean_ctor_get(v_a_6628_, 0);
lean_inc(v_fst_6630_);
lean_dec(v_a_6628_);
v_fst_6631_ = lean_ctor_get(v_snd_6629_, 0);
lean_inc(v_fst_6631_);
lean_dec(v_snd_6629_);
v___y_6509_ = v___y_6607_;
v___y_6510_ = v___y_6615_;
v___y_6511_ = v___y_6608_;
v___y_6512_ = v_remaining_x27_6619_;
v___y_6513_ = v___x_6618_;
v___y_6514_ = v_fst_6631_;
v___y_6515_ = v___y_6616_;
v___y_6516_ = v_matcherLevels_6613_;
v___y_6517_ = v___y_6610_;
v___y_6518_ = v___y_6611_;
v___y_6519_ = v___y_6617_;
v___y_6520_ = v_fst_6630_;
v___y_6521_ = v___y_6614_;
goto v___jp_6508_;
}
else
{
if (v_isCasesOn_6604_ == 0)
{
lean_object* v___x_6633_; uint8_t v_isShared_6634_; uint8_t v_isSharedCheck_6788_; 
v_isSharedCheck_6788_ = !lean_is_exclusive(v_matcherApp_6486_);
if (v_isSharedCheck_6788_ == 0)
{
lean_object* v_unused_6789_; lean_object* v_unused_6790_; lean_object* v_unused_6791_; lean_object* v_unused_6792_; lean_object* v_unused_6793_; lean_object* v_unused_6794_; lean_object* v_unused_6795_; lean_object* v_unused_6796_; 
v_unused_6789_ = lean_ctor_get(v_matcherApp_6486_, 7);
lean_dec(v_unused_6789_);
v_unused_6790_ = lean_ctor_get(v_matcherApp_6486_, 6);
lean_dec(v_unused_6790_);
v_unused_6791_ = lean_ctor_get(v_matcherApp_6486_, 5);
lean_dec(v_unused_6791_);
v_unused_6792_ = lean_ctor_get(v_matcherApp_6486_, 4);
lean_dec(v_unused_6792_);
v_unused_6793_ = lean_ctor_get(v_matcherApp_6486_, 3);
lean_dec(v_unused_6793_);
v_unused_6794_ = lean_ctor_get(v_matcherApp_6486_, 2);
lean_dec(v_unused_6794_);
v_unused_6795_ = lean_ctor_get(v_matcherApp_6486_, 1);
lean_dec(v_unused_6795_);
v_unused_6796_ = lean_ctor_get(v_matcherApp_6486_, 0);
lean_dec(v_unused_6796_);
v___x_6633_ = v_matcherApp_6486_;
v_isShared_6634_ = v_isSharedCheck_6788_;
goto v_resetjp_6632_;
}
else
{
lean_dec(v_matcherApp_6486_);
v___x_6633_ = lean_box(0);
v_isShared_6634_ = v_isSharedCheck_6788_;
goto v_resetjp_6632_;
}
v_resetjp_6632_:
{
lean_object* v_fst_6635_; lean_object* v___x_6637_; uint8_t v_isShared_6638_; uint8_t v_isSharedCheck_6786_; 
v_fst_6635_ = lean_ctor_get(v_a_6628_, 0);
v_isSharedCheck_6786_ = !lean_is_exclusive(v_a_6628_);
if (v_isSharedCheck_6786_ == 0)
{
lean_object* v_unused_6787_; 
v_unused_6787_ = lean_ctor_get(v_a_6628_, 1);
lean_dec(v_unused_6787_);
v___x_6637_ = v_a_6628_;
v_isShared_6638_ = v_isSharedCheck_6786_;
goto v_resetjp_6636_;
}
else
{
lean_inc(v_fst_6635_);
lean_dec(v_a_6628_);
v___x_6637_ = lean_box(0);
v_isShared_6638_ = v_isSharedCheck_6786_;
goto v_resetjp_6636_;
}
v_resetjp_6636_:
{
lean_object* v_fst_6639_; lean_object* v___x_6641_; uint8_t v_isShared_6642_; uint8_t v_isSharedCheck_6784_; 
v_fst_6639_ = lean_ctor_get(v_snd_6629_, 0);
v_isSharedCheck_6784_ = !lean_is_exclusive(v_snd_6629_);
if (v_isSharedCheck_6784_ == 0)
{
lean_object* v_unused_6785_; 
v_unused_6785_ = lean_ctor_get(v_snd_6629_, 1);
lean_dec(v_unused_6785_);
v___x_6641_ = v_snd_6629_;
v_isShared_6642_ = v_isSharedCheck_6784_;
goto v_resetjp_6640_;
}
else
{
lean_inc(v_fst_6639_);
lean_dec(v_snd_6629_);
v___x_6641_ = lean_box(0);
v_isShared_6642_ = v_isSharedCheck_6784_;
goto v_resetjp_6640_;
}
v_resetjp_6640_:
{
lean_object* v___x_6643_; lean_object* v___x_6644_; lean_object* v_aux1_6645_; lean_object* v_aux1_6646_; lean_object* v_aux1_6647_; lean_object* v___x_6648_; lean_object* v___x_6649_; lean_object* v___x_6650_; lean_object* v___x_6651_; lean_object* v___x_6652_; lean_object* v___f_6653_; lean_object* v___x_6654_; lean_object* v___x_6655_; 
lean_inc_ref(v_matcherLevels_6613_);
v___x_6643_ = lean_array_to_list(v_matcherLevels_6613_);
lean_inc(v___x_6643_);
lean_inc(v_matcherName_6501_);
v___x_6644_ = l_Lean_mkConst(v_matcherName_6501_, v___x_6643_);
v_aux1_6645_ = l_Lean_mkAppN(v___x_6644_, v___y_6610_);
lean_inc_ref(v___y_6607_);
v_aux1_6646_ = l_Lean_Expr_app___override(v_aux1_6645_, v___y_6607_);
v_aux1_6647_ = l_Lean_mkAppN(v_aux1_6646_, v___y_6611_);
v___x_6648_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__3);
lean_inc_ref_n(v_aux1_6647_, 2);
v___x_6649_ = l_Lean_indentExpr(v_aux1_6647_);
v___x_6650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6650_, 0, v___x_6648_);
lean_ctor_set(v___x_6650_, 1, v___x_6649_);
v___x_6651_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__56___closed__5);
v___x_6652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6652_, 0, v___x_6650_);
lean_ctor_set(v___x_6652_, 1, v___x_6651_);
v___f_6653_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6653_, 0, v___x_6652_);
v___x_6654_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(v___x_6654_, 0, v_aux1_6647_);
v___x_6655_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6654_, v___f_6653_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_);
if (lean_obj_tag(v___x_6655_) == 0)
{
lean_object* v___x_6656_; lean_object* v___x_6657_; 
lean_dec_ref(v___x_6655_);
v___x_6656_ = lean_array_get_size(v_alts_6506_);
v___x_6657_ = l_Lean_Meta_inferArgumentTypesN(v___x_6656_, v_aux1_6647_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_);
if (lean_obj_tag(v___x_6657_) == 0)
{
lean_object* v_a_6658_; lean_object* v___x_6659_; 
v_a_6658_ = lean_ctor_get(v___x_6657_, 0);
lean_inc(v_a_6658_);
lean_dec_ref(v___x_6657_);
lean_inc(v___y_6617_);
lean_inc_ref(v___y_6616_);
lean_inc(v___y_6615_);
lean_inc_ref(v___y_6614_);
v___x_6659_ = lean_get_match_equations_for(v_matcherName_6501_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_);
if (lean_obj_tag(v___x_6659_) == 0)
{
lean_object* v_a_6660_; lean_object* v_splitterName_6661_; lean_object* v_splitterMatchInfo_6662_; lean_object* v___x_6663_; lean_object* v_aux2_6664_; lean_object* v_aux2_6665_; lean_object* v_aux2_6666_; lean_object* v___x_6667_; lean_object* v___x_6668_; lean_object* v___x_6669_; lean_object* v___x_6670_; lean_object* v___f_6671_; lean_object* v___x_6672_; lean_object* v___x_6673_; 
v_a_6660_ = lean_ctor_get(v___x_6659_, 0);
lean_inc(v_a_6660_);
lean_dec_ref(v___x_6659_);
v_splitterName_6661_ = lean_ctor_get(v_a_6660_, 1);
lean_inc_n(v_splitterName_6661_, 2);
v_splitterMatchInfo_6662_ = lean_ctor_get(v_a_6660_, 2);
lean_inc_ref(v_splitterMatchInfo_6662_);
lean_dec(v_a_6660_);
v___x_6663_ = l_Lean_mkConst(v_splitterName_6661_, v___x_6643_);
v_aux2_6664_ = l_Lean_mkAppN(v___x_6663_, v___y_6610_);
lean_inc_ref(v___y_6607_);
v_aux2_6665_ = l_Lean_Expr_app___override(v_aux2_6664_, v___y_6607_);
v_aux2_6666_ = l_Lean_mkAppN(v_aux2_6665_, v___y_6611_);
v___x_6667_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1);
lean_inc_ref_n(v_aux2_6666_, 2);
v___x_6668_ = l_Lean_indentExpr(v_aux2_6666_);
v___x_6669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6669_, 0, v___x_6667_);
lean_ctor_set(v___x_6669_, 1, v___x_6668_);
v___x_6670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6670_, 0, v___x_6669_);
lean_ctor_set(v___x_6670_, 1, v___x_6651_);
v___f_6671_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6671_, 0, v___x_6670_);
v___x_6672_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 6, 1);
lean_closure_set(v___x_6672_, 0, v_aux2_6666_);
v___x_6673_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6672_, v___f_6671_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_);
if (lean_obj_tag(v___x_6673_) == 0)
{
lean_object* v___x_6674_; 
lean_dec_ref(v___x_6673_);
v___x_6674_ = l_Lean_Meta_inferArgumentTypesN(v___x_6656_, v_aux2_6666_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_);
if (lean_obj_tag(v___x_6674_) == 0)
{
lean_object* v_a_6675_; lean_object* v_numParams_6676_; lean_object* v_numDiscrs_6677_; lean_object* v_altInfos_6678_; lean_object* v_uElimPos_x3f_6679_; lean_object* v_overlaps_6680_; lean_object* v_altInfos_6681_; lean_object* v___x_6683_; uint8_t v_isShared_6684_; uint8_t v_isSharedCheck_6738_; 
v_a_6675_ = lean_ctor_get(v___x_6674_, 0);
lean_inc(v_a_6675_);
lean_dec_ref(v___x_6674_);
v_numParams_6676_ = lean_ctor_get(v_toMatcherInfo_6500_, 0);
lean_inc(v_numParams_6676_);
v_numDiscrs_6677_ = lean_ctor_get(v_toMatcherInfo_6500_, 1);
lean_inc(v_numDiscrs_6677_);
v_altInfos_6678_ = lean_ctor_get(v_toMatcherInfo_6500_, 2);
lean_inc_ref(v_altInfos_6678_);
v_uElimPos_x3f_6679_ = lean_ctor_get(v_toMatcherInfo_6500_, 3);
lean_inc(v_uElimPos_x3f_6679_);
v_overlaps_6680_ = lean_ctor_get(v_toMatcherInfo_6500_, 5);
lean_inc_ref(v_overlaps_6680_);
lean_dec_ref(v_toMatcherInfo_6500_);
v_altInfos_6681_ = lean_ctor_get(v_splitterMatchInfo_6662_, 2);
v_isSharedCheck_6738_ = !lean_is_exclusive(v_splitterMatchInfo_6662_);
if (v_isSharedCheck_6738_ == 0)
{
lean_object* v_unused_6739_; lean_object* v_unused_6740_; lean_object* v_unused_6741_; lean_object* v_unused_6742_; lean_object* v_unused_6743_; 
v_unused_6739_ = lean_ctor_get(v_splitterMatchInfo_6662_, 5);
lean_dec(v_unused_6739_);
v_unused_6740_ = lean_ctor_get(v_splitterMatchInfo_6662_, 4);
lean_dec(v_unused_6740_);
v_unused_6741_ = lean_ctor_get(v_splitterMatchInfo_6662_, 3);
lean_dec(v_unused_6741_);
v_unused_6742_ = lean_ctor_get(v_splitterMatchInfo_6662_, 1);
lean_dec(v_unused_6742_);
v_unused_6743_ = lean_ctor_get(v_splitterMatchInfo_6662_, 0);
lean_dec(v_unused_6743_);
v___x_6683_ = v_splitterMatchInfo_6662_;
v_isShared_6684_ = v_isSharedCheck_6738_;
goto v_resetjp_6682_;
}
else
{
lean_inc(v_altInfos_6681_);
lean_dec(v_splitterMatchInfo_6662_);
v___x_6683_ = lean_box(0);
v_isShared_6684_ = v_isSharedCheck_6738_;
goto v_resetjp_6682_;
}
v_resetjp_6682_:
{
lean_object* v___x_6685_; lean_object* v___x_6686_; lean_object* v___x_6687_; lean_object* v___x_6688_; lean_object* v___x_6689_; lean_object* v___x_6690_; lean_object* v___x_6691_; lean_object* v___x_6692_; lean_object* v___x_6693_; lean_object* v___x_6695_; 
v___x_6685_ = lean_array_get_size(v_altInfos_6678_);
v___x_6686_ = lean_array_get_size(v_altInfos_6681_);
v___x_6687_ = lean_array_get_size(v_a_6658_);
v___x_6688_ = lean_array_get_size(v_a_6675_);
v___x_6689_ = l_Array_toSubarray___redArg(v_alts_6506_, v___x_6618_, v___x_6656_);
lean_inc_ref(v_altInfos_6678_);
v___x_6690_ = l_Array_toSubarray___redArg(v_altInfos_6678_, v___x_6618_, v___x_6685_);
v___x_6691_ = l_Array_toSubarray___redArg(v_altInfos_6681_, v___x_6618_, v___x_6686_);
v___x_6692_ = l_Array_toSubarray___redArg(v_a_6658_, v___x_6618_, v___x_6687_);
v___x_6693_ = l_Array_toSubarray___redArg(v_a_6675_, v___x_6618_, v___x_6688_);
if (v_isShared_6642_ == 0)
{
lean_ctor_set(v___x_6641_, 1, v___x_6693_);
lean_ctor_set(v___x_6641_, 0, v___x_6692_);
v___x_6695_ = v___x_6641_;
goto v_reusejp_6694_;
}
else
{
lean_object* v_reuseFailAlloc_6737_; 
v_reuseFailAlloc_6737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6737_, 0, v___x_6692_);
lean_ctor_set(v_reuseFailAlloc_6737_, 1, v___x_6693_);
v___x_6695_ = v_reuseFailAlloc_6737_;
goto v_reusejp_6694_;
}
v_reusejp_6694_:
{
lean_object* v___x_6697_; 
if (v_isShared_6638_ == 0)
{
lean_ctor_set(v___x_6637_, 1, v___x_6695_);
lean_ctor_set(v___x_6637_, 0, v___x_6691_);
v___x_6697_ = v___x_6637_;
goto v_reusejp_6696_;
}
else
{
lean_object* v_reuseFailAlloc_6736_; 
v_reuseFailAlloc_6736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6736_, 0, v___x_6691_);
lean_ctor_set(v_reuseFailAlloc_6736_, 1, v___x_6695_);
v___x_6697_ = v_reuseFailAlloc_6736_;
goto v_reusejp_6696_;
}
v_reusejp_6696_:
{
lean_object* v___x_6698_; lean_object* v___x_6699_; lean_object* v___x_6700_; lean_object* v___x_6701_; 
v___x_6698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6698_, 0, v___x_6690_);
lean_ctor_set(v___x_6698_, 1, v___x_6697_);
v___x_6699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6699_, 0, v___x_6689_);
lean_ctor_set(v___x_6699_, 1, v___x_6698_);
v___x_6700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6700_, 0, v_remaining_x27_6619_);
lean_ctor_set(v___x_6700_, 1, v___x_6699_);
v___x_6701_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v___x_6656_, v_onAlt_6491_, v_useSplitter_6487_, v_fst_6639_, v___y_6606_, v___x_6618_, v___x_6700_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_);
if (lean_obj_tag(v___x_6701_) == 0)
{
lean_object* v_a_6702_; lean_object* v_fst_6703_; lean_object* v___x_6704_; 
v_a_6702_ = lean_ctor_get(v___x_6701_, 0);
lean_inc(v_a_6702_);
lean_dec_ref(v___x_6701_);
v_fst_6703_ = lean_ctor_get(v_a_6702_, 0);
lean_inc(v_fst_6703_);
lean_dec(v_a_6702_);
lean_inc(v___y_6617_);
lean_inc_ref(v___y_6616_);
lean_inc(v___y_6615_);
lean_inc_ref(v___y_6614_);
v___x_6704_ = lean_apply_6(v_onRemaining_6492_, v_remaining_6507_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_, lean_box(0));
if (lean_obj_tag(v___x_6704_) == 0)
{
lean_object* v_a_6705_; lean_object* v___x_6707_; uint8_t v_isShared_6708_; uint8_t v_isSharedCheck_6719_; 
v_a_6705_ = lean_ctor_get(v___x_6704_, 0);
v_isSharedCheck_6719_ = !lean_is_exclusive(v___x_6704_);
if (v_isSharedCheck_6719_ == 0)
{
v___x_6707_ = v___x_6704_;
v_isShared_6708_ = v_isSharedCheck_6719_;
goto v_resetjp_6706_;
}
else
{
lean_inc(v_a_6705_);
lean_dec(v___x_6704_);
v___x_6707_ = lean_box(0);
v_isShared_6708_ = v_isSharedCheck_6719_;
goto v_resetjp_6706_;
}
v_resetjp_6706_:
{
lean_object* v_remaining_x27_6709_; lean_object* v___x_6711_; 
v_remaining_x27_6709_ = l_Array_append___redArg(v_fst_6635_, v_a_6705_);
lean_dec(v_a_6705_);
if (v_isShared_6684_ == 0)
{
lean_ctor_set(v___x_6683_, 5, v_overlaps_6680_);
lean_ctor_set(v___x_6683_, 4, v___y_6608_);
lean_ctor_set(v___x_6683_, 3, v_uElimPos_x3f_6679_);
lean_ctor_set(v___x_6683_, 2, v_altInfos_6678_);
lean_ctor_set(v___x_6683_, 1, v_numDiscrs_6677_);
lean_ctor_set(v___x_6683_, 0, v_numParams_6676_);
v___x_6711_ = v___x_6683_;
goto v_reusejp_6710_;
}
else
{
lean_object* v_reuseFailAlloc_6718_; 
v_reuseFailAlloc_6718_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6718_, 0, v_numParams_6676_);
lean_ctor_set(v_reuseFailAlloc_6718_, 1, v_numDiscrs_6677_);
lean_ctor_set(v_reuseFailAlloc_6718_, 2, v_altInfos_6678_);
lean_ctor_set(v_reuseFailAlloc_6718_, 3, v_uElimPos_x3f_6679_);
lean_ctor_set(v_reuseFailAlloc_6718_, 4, v___y_6608_);
lean_ctor_set(v_reuseFailAlloc_6718_, 5, v_overlaps_6680_);
v___x_6711_ = v_reuseFailAlloc_6718_;
goto v_reusejp_6710_;
}
v_reusejp_6710_:
{
lean_object* v___x_6713_; 
if (v_isShared_6634_ == 0)
{
lean_ctor_set(v___x_6633_, 7, v_remaining_x27_6709_);
lean_ctor_set(v___x_6633_, 6, v_fst_6703_);
lean_ctor_set(v___x_6633_, 5, v___y_6611_);
lean_ctor_set(v___x_6633_, 4, v___y_6607_);
lean_ctor_set(v___x_6633_, 3, v___y_6610_);
lean_ctor_set(v___x_6633_, 2, v_matcherLevels_6613_);
lean_ctor_set(v___x_6633_, 1, v_splitterName_6661_);
lean_ctor_set(v___x_6633_, 0, v___x_6711_);
v___x_6713_ = v___x_6633_;
goto v_reusejp_6712_;
}
else
{
lean_object* v_reuseFailAlloc_6717_; 
v_reuseFailAlloc_6717_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_6717_, 0, v___x_6711_);
lean_ctor_set(v_reuseFailAlloc_6717_, 1, v_splitterName_6661_);
lean_ctor_set(v_reuseFailAlloc_6717_, 2, v_matcherLevels_6613_);
lean_ctor_set(v_reuseFailAlloc_6717_, 3, v___y_6610_);
lean_ctor_set(v_reuseFailAlloc_6717_, 4, v___y_6607_);
lean_ctor_set(v_reuseFailAlloc_6717_, 5, v___y_6611_);
lean_ctor_set(v_reuseFailAlloc_6717_, 6, v_fst_6703_);
lean_ctor_set(v_reuseFailAlloc_6717_, 7, v_remaining_x27_6709_);
v___x_6713_ = v_reuseFailAlloc_6717_;
goto v_reusejp_6712_;
}
v_reusejp_6712_:
{
lean_object* v___x_6715_; 
if (v_isShared_6708_ == 0)
{
lean_ctor_set(v___x_6707_, 0, v___x_6713_);
v___x_6715_ = v___x_6707_;
goto v_reusejp_6714_;
}
else
{
lean_object* v_reuseFailAlloc_6716_; 
v_reuseFailAlloc_6716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6716_, 0, v___x_6713_);
v___x_6715_ = v_reuseFailAlloc_6716_;
goto v_reusejp_6714_;
}
v_reusejp_6714_:
{
return v___x_6715_;
}
}
}
}
}
else
{
lean_object* v_a_6720_; lean_object* v___x_6722_; uint8_t v_isShared_6723_; uint8_t v_isSharedCheck_6727_; 
lean_dec(v_fst_6703_);
lean_del_object(v___x_6683_);
lean_dec_ref(v_overlaps_6680_);
lean_dec(v_uElimPos_x3f_6679_);
lean_dec_ref(v_altInfos_6678_);
lean_dec(v_numDiscrs_6677_);
lean_dec(v_numParams_6676_);
lean_dec(v_splitterName_6661_);
lean_dec(v_fst_6635_);
lean_del_object(v___x_6633_);
lean_dec_ref(v_matcherLevels_6613_);
lean_dec_ref(v___y_6611_);
lean_dec_ref(v___y_6610_);
lean_dec_ref(v___y_6608_);
lean_dec_ref(v___y_6607_);
v_a_6720_ = lean_ctor_get(v___x_6704_, 0);
v_isSharedCheck_6727_ = !lean_is_exclusive(v___x_6704_);
if (v_isSharedCheck_6727_ == 0)
{
v___x_6722_ = v___x_6704_;
v_isShared_6723_ = v_isSharedCheck_6727_;
goto v_resetjp_6721_;
}
else
{
lean_inc(v_a_6720_);
lean_dec(v___x_6704_);
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
lean_del_object(v___x_6683_);
lean_dec_ref(v_overlaps_6680_);
lean_dec(v_uElimPos_x3f_6679_);
lean_dec_ref(v_altInfos_6678_);
lean_dec(v_numDiscrs_6677_);
lean_dec(v_numParams_6676_);
lean_dec(v_splitterName_6661_);
lean_dec(v_fst_6635_);
lean_del_object(v___x_6633_);
lean_dec_ref(v_matcherLevels_6613_);
lean_dec_ref(v___y_6611_);
lean_dec_ref(v___y_6610_);
lean_dec_ref(v___y_6608_);
lean_dec_ref(v___y_6607_);
lean_dec_ref(v_remaining_6507_);
lean_dec_ref(v_onRemaining_6492_);
v_a_6728_ = lean_ctor_get(v___x_6701_, 0);
v_isSharedCheck_6735_ = !lean_is_exclusive(v___x_6701_);
if (v_isSharedCheck_6735_ == 0)
{
v___x_6730_ = v___x_6701_;
v_isShared_6731_ = v_isSharedCheck_6735_;
goto v_resetjp_6729_;
}
else
{
lean_inc(v_a_6728_);
lean_dec(v___x_6701_);
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
}
}
}
else
{
lean_object* v_a_6744_; lean_object* v___x_6746_; uint8_t v_isShared_6747_; uint8_t v_isSharedCheck_6751_; 
lean_dec_ref(v_splitterMatchInfo_6662_);
lean_dec(v_splitterName_6661_);
lean_dec(v_a_6658_);
lean_del_object(v___x_6641_);
lean_dec(v_fst_6639_);
lean_del_object(v___x_6637_);
lean_dec(v_fst_6635_);
lean_del_object(v___x_6633_);
lean_dec_ref(v_matcherLevels_6613_);
lean_dec_ref(v___y_6611_);
lean_dec_ref(v___y_6610_);
lean_dec_ref(v___y_6608_);
lean_dec_ref(v___y_6607_);
lean_dec(v___y_6606_);
lean_dec_ref(v_remaining_6507_);
lean_dec_ref(v_alts_6506_);
lean_dec_ref(v_toMatcherInfo_6500_);
lean_dec_ref(v_onRemaining_6492_);
lean_dec_ref(v_onAlt_6491_);
v_a_6744_ = lean_ctor_get(v___x_6674_, 0);
v_isSharedCheck_6751_ = !lean_is_exclusive(v___x_6674_);
if (v_isSharedCheck_6751_ == 0)
{
v___x_6746_ = v___x_6674_;
v_isShared_6747_ = v_isSharedCheck_6751_;
goto v_resetjp_6745_;
}
else
{
lean_inc(v_a_6744_);
lean_dec(v___x_6674_);
v___x_6746_ = lean_box(0);
v_isShared_6747_ = v_isSharedCheck_6751_;
goto v_resetjp_6745_;
}
v_resetjp_6745_:
{
lean_object* v___x_6749_; 
if (v_isShared_6747_ == 0)
{
v___x_6749_ = v___x_6746_;
goto v_reusejp_6748_;
}
else
{
lean_object* v_reuseFailAlloc_6750_; 
v_reuseFailAlloc_6750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6750_, 0, v_a_6744_);
v___x_6749_ = v_reuseFailAlloc_6750_;
goto v_reusejp_6748_;
}
v_reusejp_6748_:
{
return v___x_6749_;
}
}
}
}
else
{
lean_object* v_a_6752_; lean_object* v___x_6754_; uint8_t v_isShared_6755_; uint8_t v_isSharedCheck_6759_; 
lean_dec_ref(v_aux2_6666_);
lean_dec_ref(v_splitterMatchInfo_6662_);
lean_dec(v_splitterName_6661_);
lean_dec(v_a_6658_);
lean_del_object(v___x_6641_);
lean_dec(v_fst_6639_);
lean_del_object(v___x_6637_);
lean_dec(v_fst_6635_);
lean_del_object(v___x_6633_);
lean_dec_ref(v_matcherLevels_6613_);
lean_dec_ref(v___y_6611_);
lean_dec_ref(v___y_6610_);
lean_dec_ref(v___y_6608_);
lean_dec_ref(v___y_6607_);
lean_dec(v___y_6606_);
lean_dec_ref(v_remaining_6507_);
lean_dec_ref(v_alts_6506_);
lean_dec_ref(v_toMatcherInfo_6500_);
lean_dec_ref(v_onRemaining_6492_);
lean_dec_ref(v_onAlt_6491_);
v_a_6752_ = lean_ctor_get(v___x_6673_, 0);
v_isSharedCheck_6759_ = !lean_is_exclusive(v___x_6673_);
if (v_isSharedCheck_6759_ == 0)
{
v___x_6754_ = v___x_6673_;
v_isShared_6755_ = v_isSharedCheck_6759_;
goto v_resetjp_6753_;
}
else
{
lean_inc(v_a_6752_);
lean_dec(v___x_6673_);
v___x_6754_ = lean_box(0);
v_isShared_6755_ = v_isSharedCheck_6759_;
goto v_resetjp_6753_;
}
v_resetjp_6753_:
{
lean_object* v___x_6757_; 
if (v_isShared_6755_ == 0)
{
v___x_6757_ = v___x_6754_;
goto v_reusejp_6756_;
}
else
{
lean_object* v_reuseFailAlloc_6758_; 
v_reuseFailAlloc_6758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6758_, 0, v_a_6752_);
v___x_6757_ = v_reuseFailAlloc_6758_;
goto v_reusejp_6756_;
}
v_reusejp_6756_:
{
return v___x_6757_;
}
}
}
}
else
{
lean_object* v_a_6760_; lean_object* v___x_6762_; uint8_t v_isShared_6763_; uint8_t v_isSharedCheck_6767_; 
lean_dec(v_a_6658_);
lean_dec(v___x_6643_);
lean_del_object(v___x_6641_);
lean_dec(v_fst_6639_);
lean_del_object(v___x_6637_);
lean_dec(v_fst_6635_);
lean_del_object(v___x_6633_);
lean_dec_ref(v_matcherLevels_6613_);
lean_dec_ref(v___y_6611_);
lean_dec_ref(v___y_6610_);
lean_dec_ref(v___y_6608_);
lean_dec_ref(v___y_6607_);
lean_dec(v___y_6606_);
lean_dec_ref(v_remaining_6507_);
lean_dec_ref(v_alts_6506_);
lean_dec_ref(v_toMatcherInfo_6500_);
lean_dec_ref(v_onRemaining_6492_);
lean_dec_ref(v_onAlt_6491_);
v_a_6760_ = lean_ctor_get(v___x_6659_, 0);
v_isSharedCheck_6767_ = !lean_is_exclusive(v___x_6659_);
if (v_isSharedCheck_6767_ == 0)
{
v___x_6762_ = v___x_6659_;
v_isShared_6763_ = v_isSharedCheck_6767_;
goto v_resetjp_6761_;
}
else
{
lean_inc(v_a_6760_);
lean_dec(v___x_6659_);
v___x_6762_ = lean_box(0);
v_isShared_6763_ = v_isSharedCheck_6767_;
goto v_resetjp_6761_;
}
v_resetjp_6761_:
{
lean_object* v___x_6765_; 
if (v_isShared_6763_ == 0)
{
v___x_6765_ = v___x_6762_;
goto v_reusejp_6764_;
}
else
{
lean_object* v_reuseFailAlloc_6766_; 
v_reuseFailAlloc_6766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6766_, 0, v_a_6760_);
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
else
{
lean_object* v_a_6768_; lean_object* v___x_6770_; uint8_t v_isShared_6771_; uint8_t v_isSharedCheck_6775_; 
lean_dec(v___x_6643_);
lean_del_object(v___x_6641_);
lean_dec(v_fst_6639_);
lean_del_object(v___x_6637_);
lean_dec(v_fst_6635_);
lean_del_object(v___x_6633_);
lean_dec_ref(v_matcherLevels_6613_);
lean_dec_ref(v___y_6611_);
lean_dec_ref(v___y_6610_);
lean_dec_ref(v___y_6608_);
lean_dec_ref(v___y_6607_);
lean_dec(v___y_6606_);
lean_dec_ref(v_remaining_6507_);
lean_dec_ref(v_alts_6506_);
lean_dec(v_matcherName_6501_);
lean_dec_ref(v_toMatcherInfo_6500_);
lean_dec_ref(v_onRemaining_6492_);
lean_dec_ref(v_onAlt_6491_);
v_a_6768_ = lean_ctor_get(v___x_6657_, 0);
v_isSharedCheck_6775_ = !lean_is_exclusive(v___x_6657_);
if (v_isSharedCheck_6775_ == 0)
{
v___x_6770_ = v___x_6657_;
v_isShared_6771_ = v_isSharedCheck_6775_;
goto v_resetjp_6769_;
}
else
{
lean_inc(v_a_6768_);
lean_dec(v___x_6657_);
v___x_6770_ = lean_box(0);
v_isShared_6771_ = v_isSharedCheck_6775_;
goto v_resetjp_6769_;
}
v_resetjp_6769_:
{
lean_object* v___x_6773_; 
if (v_isShared_6771_ == 0)
{
v___x_6773_ = v___x_6770_;
goto v_reusejp_6772_;
}
else
{
lean_object* v_reuseFailAlloc_6774_; 
v_reuseFailAlloc_6774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6774_, 0, v_a_6768_);
v___x_6773_ = v_reuseFailAlloc_6774_;
goto v_reusejp_6772_;
}
v_reusejp_6772_:
{
return v___x_6773_;
}
}
}
}
else
{
lean_object* v_a_6776_; lean_object* v___x_6778_; uint8_t v_isShared_6779_; uint8_t v_isSharedCheck_6783_; 
lean_dec_ref(v_aux1_6647_);
lean_dec(v___x_6643_);
lean_del_object(v___x_6641_);
lean_dec(v_fst_6639_);
lean_del_object(v___x_6637_);
lean_dec(v_fst_6635_);
lean_del_object(v___x_6633_);
lean_dec_ref(v_matcherLevels_6613_);
lean_dec_ref(v___y_6611_);
lean_dec_ref(v___y_6610_);
lean_dec_ref(v___y_6608_);
lean_dec_ref(v___y_6607_);
lean_dec(v___y_6606_);
lean_dec_ref(v_remaining_6507_);
lean_dec_ref(v_alts_6506_);
lean_dec(v_matcherName_6501_);
lean_dec_ref(v_toMatcherInfo_6500_);
lean_dec_ref(v_onRemaining_6492_);
lean_dec_ref(v_onAlt_6491_);
v_a_6776_ = lean_ctor_get(v___x_6655_, 0);
v_isSharedCheck_6783_ = !lean_is_exclusive(v___x_6655_);
if (v_isSharedCheck_6783_ == 0)
{
v___x_6778_ = v___x_6655_;
v_isShared_6779_ = v_isSharedCheck_6783_;
goto v_resetjp_6777_;
}
else
{
lean_inc(v_a_6776_);
lean_dec(v___x_6655_);
v___x_6778_ = lean_box(0);
v_isShared_6779_ = v_isSharedCheck_6783_;
goto v_resetjp_6777_;
}
v_resetjp_6777_:
{
lean_object* v___x_6781_; 
if (v_isShared_6779_ == 0)
{
v___x_6781_ = v___x_6778_;
goto v_reusejp_6780_;
}
else
{
lean_object* v_reuseFailAlloc_6782_; 
v_reuseFailAlloc_6782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6782_, 0, v_a_6776_);
v___x_6781_ = v_reuseFailAlloc_6782_;
goto v_reusejp_6780_;
}
v_reusejp_6780_:
{
return v___x_6781_;
}
}
}
}
}
}
}
else
{
lean_object* v_fst_6797_; lean_object* v_fst_6798_; 
lean_dec(v___y_6606_);
v_fst_6797_ = lean_ctor_get(v_a_6628_, 0);
lean_inc(v_fst_6797_);
lean_dec(v_a_6628_);
v_fst_6798_ = lean_ctor_get(v_snd_6629_, 0);
lean_inc(v_fst_6798_);
lean_dec(v_snd_6629_);
v___y_6509_ = v___y_6607_;
v___y_6510_ = v___y_6615_;
v___y_6511_ = v___y_6608_;
v___y_6512_ = v_remaining_x27_6619_;
v___y_6513_ = v___x_6618_;
v___y_6514_ = v_fst_6798_;
v___y_6515_ = v___y_6616_;
v___y_6516_ = v_matcherLevels_6613_;
v___y_6517_ = v___y_6610_;
v___y_6518_ = v___y_6611_;
v___y_6519_ = v___y_6617_;
v___y_6520_ = v_fst_6797_;
v___y_6521_ = v___y_6614_;
goto v___jp_6508_;
}
}
}
else
{
lean_object* v_a_6799_; lean_object* v___x_6801_; uint8_t v_isShared_6802_; uint8_t v_isSharedCheck_6806_; 
lean_dec_ref(v_matcherLevels_6613_);
lean_dec_ref(v___y_6611_);
lean_dec_ref(v___y_6610_);
lean_dec_ref(v___y_6608_);
lean_dec_ref(v___y_6607_);
lean_dec(v___y_6606_);
lean_dec_ref(v_remaining_6507_);
lean_dec_ref(v_alts_6506_);
lean_dec(v_matcherName_6501_);
lean_dec_ref(v_toMatcherInfo_6500_);
lean_dec_ref(v_onRemaining_6492_);
lean_dec_ref(v_onAlt_6491_);
lean_dec_ref(v_matcherApp_6486_);
v_a_6799_ = lean_ctor_get(v___x_6627_, 0);
v_isSharedCheck_6806_ = !lean_is_exclusive(v___x_6627_);
if (v_isSharedCheck_6806_ == 0)
{
v___x_6801_ = v___x_6627_;
v_isShared_6802_ = v_isSharedCheck_6806_;
goto v_resetjp_6800_;
}
else
{
lean_inc(v_a_6799_);
lean_dec(v___x_6627_);
v___x_6801_ = lean_box(0);
v_isShared_6802_ = v_isSharedCheck_6806_;
goto v_resetjp_6800_;
}
v_resetjp_6800_:
{
lean_object* v___x_6804_; 
if (v_isShared_6802_ == 0)
{
v___x_6804_ = v___x_6801_;
goto v_reusejp_6803_;
}
else
{
lean_object* v_reuseFailAlloc_6805_; 
v_reuseFailAlloc_6805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6805_, 0, v_a_6799_);
v___x_6804_ = v_reuseFailAlloc_6805_;
goto v_reusejp_6803_;
}
v_reusejp_6803_:
{
return v___x_6804_;
}
}
}
}
v___jp_6807_:
{
size_t v_sz_6813_; size_t v___x_6814_; lean_object* v___x_6815_; 
v_sz_6813_ = lean_array_size(v_params_6503_);
v___x_6814_ = ((size_t)0ULL);
lean_inc_ref(v_params_6503_);
lean_inc_ref(v_onParams_6489_);
v___x_6815_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6489_, v_sz_6813_, v___x_6814_, v_params_6503_, v___y_6809_, v___y_6810_, v___y_6811_, v___y_6812_);
if (lean_obj_tag(v___x_6815_) == 0)
{
lean_object* v_a_6816_; size_t v_sz_6817_; lean_object* v___x_6818_; 
v_a_6816_ = lean_ctor_get(v___x_6815_, 0);
lean_inc(v_a_6816_);
lean_dec_ref(v___x_6815_);
v_sz_6817_ = lean_array_size(v_discrs_6505_);
lean_inc_ref(v_discrs_6505_);
v___x_6818_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6489_, v_sz_6817_, v___x_6814_, v_discrs_6505_, v___y_6809_, v___y_6810_, v___y_6811_, v___y_6812_);
if (lean_obj_tag(v___x_6818_) == 0)
{
lean_object* v_a_6819_; lean_object* v___x_6820_; lean_object* v___x_6821_; lean_object* v___f_6822_; uint8_t v___x_6823_; lean_object* v___x_6824_; 
v_a_6819_ = lean_ctor_get(v___x_6818_, 0);
lean_inc_n(v_a_6819_, 2);
lean_dec_ref(v___x_6818_);
v___x_6820_ = lean_box(v_addEqualities_6488_);
v___x_6821_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed__const__1));
lean_inc_ref(v_discrs_6505_);
lean_inc_ref(v_toMatcherInfo_6500_);
v___f_6822_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed), 13, 6);
lean_closure_set(v___f_6822_, 0, v_onMotive_6490_);
lean_closure_set(v___f_6822_, 1, v_toMatcherInfo_6500_);
lean_closure_set(v___f_6822_, 2, v_a_6819_);
lean_closure_set(v___f_6822_, 3, v___x_6820_);
lean_closure_set(v___f_6822_, 4, v___x_6821_);
lean_closure_set(v___f_6822_, 5, v_discrs_6505_);
v___x_6823_ = 0;
lean_inc_ref(v_motive_6504_);
v___x_6824_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_6504_, v___f_6822_, v___x_6823_, v___y_6809_, v___y_6810_, v___y_6811_, v___y_6812_);
if (lean_obj_tag(v___x_6824_) == 0)
{
lean_object* v_a_6825_; lean_object* v_snd_6826_; lean_object* v_snd_6827_; lean_object* v_uElimPos_x3f_6828_; 
v_a_6825_ = lean_ctor_get(v___x_6824_, 0);
lean_inc(v_a_6825_);
lean_dec_ref(v___x_6824_);
v_snd_6826_ = lean_ctor_get(v_a_6825_, 1);
v_snd_6827_ = lean_ctor_get(v_snd_6826_, 1);
lean_inc(v_snd_6827_);
v_uElimPos_x3f_6828_ = lean_ctor_get(v_toMatcherInfo_6500_, 3);
if (lean_obj_tag(v_uElimPos_x3f_6828_) == 0)
{
lean_object* v_fst_6829_; lean_object* v_fst_6830_; lean_object* v_snd_6831_; 
v_fst_6829_ = lean_ctor_get(v_a_6825_, 0);
lean_inc(v_fst_6829_);
lean_dec(v_a_6825_);
v_fst_6830_ = lean_ctor_get(v_snd_6827_, 0);
lean_inc(v_fst_6830_);
v_snd_6831_ = lean_ctor_get(v_snd_6827_, 1);
lean_inc(v_snd_6831_);
lean_dec(v_snd_6827_);
lean_inc_ref(v_matcherLevels_6502_);
v___y_6606_ = v_numDiscrEqs_6808_;
v___y_6607_ = v_fst_6829_;
v___y_6608_ = v_snd_6831_;
v___y_6609_ = v_fst_6830_;
v___y_6610_ = v_a_6816_;
v___y_6611_ = v_a_6819_;
v___y_6612_ = v___x_6814_;
v_matcherLevels_6613_ = v_matcherLevels_6502_;
v___y_6614_ = v___y_6809_;
v___y_6615_ = v___y_6810_;
v___y_6616_ = v___y_6811_;
v___y_6617_ = v___y_6812_;
goto v___jp_6605_;
}
else
{
lean_object* v_fst_6832_; lean_object* v_fst_6833_; lean_object* v_fst_6834_; lean_object* v_snd_6835_; lean_object* v_val_6836_; lean_object* v___x_6837_; 
lean_inc(v_snd_6826_);
v_fst_6832_ = lean_ctor_get(v_a_6825_, 0);
lean_inc(v_fst_6832_);
lean_dec(v_a_6825_);
v_fst_6833_ = lean_ctor_get(v_snd_6826_, 0);
lean_inc(v_fst_6833_);
lean_dec(v_snd_6826_);
v_fst_6834_ = lean_ctor_get(v_snd_6827_, 0);
lean_inc(v_fst_6834_);
v_snd_6835_ = lean_ctor_get(v_snd_6827_, 1);
lean_inc(v_snd_6835_);
lean_dec(v_snd_6827_);
v_val_6836_ = lean_ctor_get(v_uElimPos_x3f_6828_, 0);
lean_inc_ref(v_matcherLevels_6502_);
v___x_6837_ = lean_array_set(v_matcherLevels_6502_, v_val_6836_, v_fst_6833_);
v___y_6606_ = v_numDiscrEqs_6808_;
v___y_6607_ = v_fst_6832_;
v___y_6608_ = v_snd_6835_;
v___y_6609_ = v_fst_6834_;
v___y_6610_ = v_a_6816_;
v___y_6611_ = v_a_6819_;
v___y_6612_ = v___x_6814_;
v_matcherLevels_6613_ = v___x_6837_;
v___y_6614_ = v___y_6809_;
v___y_6615_ = v___y_6810_;
v___y_6616_ = v___y_6811_;
v___y_6617_ = v___y_6812_;
goto v___jp_6605_;
}
}
else
{
lean_object* v_a_6838_; lean_object* v___x_6840_; uint8_t v_isShared_6841_; uint8_t v_isSharedCheck_6845_; 
lean_dec(v_a_6819_);
lean_dec(v_a_6816_);
lean_dec(v_numDiscrEqs_6808_);
lean_dec_ref(v_remaining_6507_);
lean_dec_ref(v_alts_6506_);
lean_dec(v_matcherName_6501_);
lean_dec_ref(v_toMatcherInfo_6500_);
lean_dec_ref(v_onRemaining_6492_);
lean_dec_ref(v_onAlt_6491_);
lean_dec_ref(v_matcherApp_6486_);
v_a_6838_ = lean_ctor_get(v___x_6824_, 0);
v_isSharedCheck_6845_ = !lean_is_exclusive(v___x_6824_);
if (v_isSharedCheck_6845_ == 0)
{
v___x_6840_ = v___x_6824_;
v_isShared_6841_ = v_isSharedCheck_6845_;
goto v_resetjp_6839_;
}
else
{
lean_inc(v_a_6838_);
lean_dec(v___x_6824_);
v___x_6840_ = lean_box(0);
v_isShared_6841_ = v_isSharedCheck_6845_;
goto v_resetjp_6839_;
}
v_resetjp_6839_:
{
lean_object* v___x_6843_; 
if (v_isShared_6841_ == 0)
{
v___x_6843_ = v___x_6840_;
goto v_reusejp_6842_;
}
else
{
lean_object* v_reuseFailAlloc_6844_; 
v_reuseFailAlloc_6844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6844_, 0, v_a_6838_);
v___x_6843_ = v_reuseFailAlloc_6844_;
goto v_reusejp_6842_;
}
v_reusejp_6842_:
{
return v___x_6843_;
}
}
}
}
else
{
lean_object* v_a_6846_; lean_object* v___x_6848_; uint8_t v_isShared_6849_; uint8_t v_isSharedCheck_6853_; 
lean_dec(v_a_6816_);
lean_dec(v_numDiscrEqs_6808_);
lean_dec_ref(v_remaining_6507_);
lean_dec_ref(v_alts_6506_);
lean_dec(v_matcherName_6501_);
lean_dec_ref(v_toMatcherInfo_6500_);
lean_dec_ref(v_onRemaining_6492_);
lean_dec_ref(v_onAlt_6491_);
lean_dec_ref(v_onMotive_6490_);
lean_dec_ref(v_matcherApp_6486_);
v_a_6846_ = lean_ctor_get(v___x_6818_, 0);
v_isSharedCheck_6853_ = !lean_is_exclusive(v___x_6818_);
if (v_isSharedCheck_6853_ == 0)
{
v___x_6848_ = v___x_6818_;
v_isShared_6849_ = v_isSharedCheck_6853_;
goto v_resetjp_6847_;
}
else
{
lean_inc(v_a_6846_);
lean_dec(v___x_6818_);
v___x_6848_ = lean_box(0);
v_isShared_6849_ = v_isSharedCheck_6853_;
goto v_resetjp_6847_;
}
v_resetjp_6847_:
{
lean_object* v___x_6851_; 
if (v_isShared_6849_ == 0)
{
v___x_6851_ = v___x_6848_;
goto v_reusejp_6850_;
}
else
{
lean_object* v_reuseFailAlloc_6852_; 
v_reuseFailAlloc_6852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6852_, 0, v_a_6846_);
v___x_6851_ = v_reuseFailAlloc_6852_;
goto v_reusejp_6850_;
}
v_reusejp_6850_:
{
return v___x_6851_;
}
}
}
}
else
{
lean_object* v_a_6854_; lean_object* v___x_6856_; uint8_t v_isShared_6857_; uint8_t v_isSharedCheck_6861_; 
lean_dec(v_numDiscrEqs_6808_);
lean_dec_ref(v_remaining_6507_);
lean_dec_ref(v_alts_6506_);
lean_dec(v_matcherName_6501_);
lean_dec_ref(v_toMatcherInfo_6500_);
lean_dec_ref(v_onRemaining_6492_);
lean_dec_ref(v_onAlt_6491_);
lean_dec_ref(v_onMotive_6490_);
lean_dec_ref(v_onParams_6489_);
lean_dec_ref(v_matcherApp_6486_);
v_a_6854_ = lean_ctor_get(v___x_6815_, 0);
v_isSharedCheck_6861_ = !lean_is_exclusive(v___x_6815_);
if (v_isSharedCheck_6861_ == 0)
{
v___x_6856_ = v___x_6815_;
v_isShared_6857_ = v_isSharedCheck_6861_;
goto v_resetjp_6855_;
}
else
{
lean_inc(v_a_6854_);
lean_dec(v___x_6815_);
v___x_6856_ = lean_box(0);
v_isShared_6857_ = v_isSharedCheck_6861_;
goto v_resetjp_6855_;
}
v_resetjp_6855_:
{
lean_object* v___x_6859_; 
if (v_isShared_6857_ == 0)
{
v___x_6859_ = v___x_6856_;
goto v_reusejp_6858_;
}
else
{
lean_object* v_reuseFailAlloc_6860_; 
v_reuseFailAlloc_6860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6860_, 0, v_a_6854_);
v___x_6859_ = v_reuseFailAlloc_6860_;
goto v_reusejp_6858_;
}
v_reusejp_6858_:
{
return v___x_6859_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed(lean_object* v_matcherApp_6881_, lean_object* v_useSplitter_6882_, lean_object* v_addEqualities_6883_, lean_object* v_onParams_6884_, lean_object* v_onMotive_6885_, lean_object* v_onAlt_6886_, lean_object* v_onRemaining_6887_, lean_object* v___y_6888_, lean_object* v___y_6889_, lean_object* v___y_6890_, lean_object* v___y_6891_, lean_object* v___y_6892_){
_start:
{
uint8_t v_useSplitter_boxed_6893_; uint8_t v_addEqualities_boxed_6894_; lean_object* v_res_6895_; 
v_useSplitter_boxed_6893_ = lean_unbox(v_useSplitter_6882_);
v_addEqualities_boxed_6894_ = lean_unbox(v_addEqualities_6883_);
v_res_6895_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(v_matcherApp_6881_, v_useSplitter_boxed_6893_, v_addEqualities_boxed_6894_, v_onParams_6884_, v_onMotive_6885_, v_onAlt_6886_, v_onRemaining_6887_, v___y_6888_, v___y_6889_, v___y_6890_, v___y_6891_);
lean_dec(v___y_6891_);
lean_dec_ref(v___y_6890_);
lean_dec(v___y_6889_);
lean_dec_ref(v___y_6888_);
return v_res_6895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType(lean_object* v_matcherApp_6901_, lean_object* v_a_6902_, lean_object* v_a_6903_, lean_object* v_a_6904_, lean_object* v_a_6905_){
_start:
{
lean_object* v_toMatcherInfo_6907_; lean_object* v_matcherName_6908_; lean_object* v_matcherLevels_6909_; lean_object* v_params_6910_; lean_object* v_alts_6911_; lean_object* v_remaining_6912_; lean_object* v___f_6913_; lean_object* v___f_6914_; lean_object* v_nExtra_6915_; uint8_t v___x_6916_; lean_object* v___f_6917_; uint8_t v___x_6918_; lean_object* v___x_6919_; lean_object* v___x_6920_; lean_object* v___f_6921_; lean_object* v___x_6922_; 
v_toMatcherInfo_6907_ = lean_ctor_get(v_matcherApp_6901_, 0);
v_matcherName_6908_ = lean_ctor_get(v_matcherApp_6901_, 1);
v_matcherLevels_6909_ = lean_ctor_get(v_matcherApp_6901_, 2);
v_params_6910_ = lean_ctor_get(v_matcherApp_6901_, 3);
v_alts_6911_ = lean_ctor_get(v_matcherApp_6901_, 6);
v_remaining_6912_ = lean_ctor_get(v_matcherApp_6901_, 7);
v___f_6913_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__0));
v___f_6914_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__1));
v_nExtra_6915_ = lean_array_get_size(v_remaining_6912_);
v___x_6916_ = 1;
v___f_6917_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__2));
v___x_6918_ = 0;
v___x_6919_ = lean_box(v___x_6918_);
v___x_6920_ = lean_box(v___x_6916_);
lean_inc_ref(v_matcherLevels_6909_);
lean_inc_ref(v_params_6910_);
lean_inc(v_matcherName_6908_);
lean_inc_ref(v_toMatcherInfo_6907_);
lean_inc_ref(v_alts_6911_);
v___f_6921_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed), 15, 8);
lean_closure_set(v___f_6921_, 0, v_nExtra_6915_);
lean_closure_set(v___f_6921_, 1, v___x_6919_);
lean_closure_set(v___f_6921_, 2, v___x_6920_);
lean_closure_set(v___f_6921_, 3, v_alts_6911_);
lean_closure_set(v___f_6921_, 4, v_toMatcherInfo_6907_);
lean_closure_set(v___f_6921_, 5, v_matcherName_6908_);
lean_closure_set(v___f_6921_, 6, v_params_6910_);
lean_closure_set(v___f_6921_, 7, v_matcherLevels_6909_);
v___x_6922_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(v_matcherApp_6901_, v___x_6916_, v___x_6918_, v___f_6913_, v___f_6921_, v___f_6917_, v___f_6914_, v_a_6902_, v_a_6903_, v_a_6904_, v_a_6905_);
return v___x_6922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___boxed(lean_object* v_matcherApp_6923_, lean_object* v_a_6924_, lean_object* v_a_6925_, lean_object* v_a_6926_, lean_object* v_a_6927_, lean_object* v_a_6928_){
_start:
{
lean_object* v_res_6929_; 
v_res_6929_ = l_Lean_Meta_MatcherApp_inferMatchType(v_matcherApp_6923_, v_a_6924_, v_a_6925_, v_a_6926_, v_a_6927_);
lean_dec(v_a_6927_);
lean_dec_ref(v_a_6926_);
lean_dec(v_a_6925_);
lean_dec_ref(v_a_6924_);
return v_res_6929_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(lean_object* v_a_6930_, lean_object* v_termAlt_6931_, lean_object* v_inst_6932_, lean_object* v_R_6933_, lean_object* v_a_6934_, lean_object* v_b_6935_, lean_object* v_c_6936_, lean_object* v___y_6937_, lean_object* v___y_6938_, lean_object* v___y_6939_, lean_object* v___y_6940_){
_start:
{
lean_object* v___x_6942_; 
v___x_6942_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_6930_, v_termAlt_6931_, v_a_6934_, v_b_6935_, v___y_6937_, v___y_6938_, v___y_6939_, v___y_6940_);
return v___x_6942_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___boxed(lean_object* v_a_6943_, lean_object* v_termAlt_6944_, lean_object* v_inst_6945_, lean_object* v_R_6946_, lean_object* v_a_6947_, lean_object* v_b_6948_, lean_object* v_c_6949_, lean_object* v___y_6950_, lean_object* v___y_6951_, lean_object* v___y_6952_, lean_object* v___y_6953_, lean_object* v___y_6954_){
_start:
{
lean_object* v_res_6955_; 
v_res_6955_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(v_a_6943_, v_termAlt_6944_, v_inst_6945_, v_R_6946_, v_a_6947_, v_b_6948_, v_c_6949_, v___y_6950_, v___y_6951_, v___y_6952_, v___y_6953_);
lean_dec(v___y_6953_);
lean_dec_ref(v___y_6952_);
lean_dec(v___y_6951_);
lean_dec_ref(v___y_6950_);
return v_res_6955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(lean_object* v_00_u03b1_6956_, lean_object* v_fvars_6957_, lean_object* v_names_6958_, lean_object* v_k_6959_, lean_object* v___y_6960_, lean_object* v___y_6961_, lean_object* v___y_6962_, lean_object* v___y_6963_){
_start:
{
lean_object* v___x_6965_; 
v___x_6965_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_fvars_6957_, v_names_6958_, v_k_6959_, v___y_6960_, v___y_6961_, v___y_6962_, v___y_6963_);
return v___x_6965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___boxed(lean_object* v_00_u03b1_6966_, lean_object* v_fvars_6967_, lean_object* v_names_6968_, lean_object* v_k_6969_, lean_object* v___y_6970_, lean_object* v___y_6971_, lean_object* v___y_6972_, lean_object* v___y_6973_, lean_object* v___y_6974_){
_start:
{
lean_object* v_res_6975_; 
v_res_6975_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(v_00_u03b1_6966_, v_fvars_6967_, v_names_6968_, v_k_6969_, v___y_6970_, v___y_6971_, v___y_6972_, v___y_6973_);
lean_dec(v___y_6973_);
lean_dec_ref(v___y_6972_);
lean_dec(v___y_6971_);
lean_dec_ref(v___y_6970_);
lean_dec_ref(v_names_6968_);
lean_dec_ref(v_fvars_6967_);
return v_res_6975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(lean_object* v_00_u03b1_6976_, lean_object* v_origAltType_6977_, lean_object* v_altInfo_6978_, lean_object* v_k_6979_, lean_object* v___y_6980_, lean_object* v___y_6981_, lean_object* v___y_6982_, lean_object* v___y_6983_){
_start:
{
lean_object* v___x_6985_; 
v___x_6985_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v_origAltType_6977_, v_altInfo_6978_, v_k_6979_, v___y_6980_, v___y_6981_, v___y_6982_, v___y_6983_);
return v___x_6985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___boxed(lean_object* v_00_u03b1_6986_, lean_object* v_origAltType_6987_, lean_object* v_altInfo_6988_, lean_object* v_k_6989_, lean_object* v___y_6990_, lean_object* v___y_6991_, lean_object* v___y_6992_, lean_object* v___y_6993_, lean_object* v___y_6994_){
_start:
{
lean_object* v_res_6995_; 
v_res_6995_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(v_00_u03b1_6986_, v_origAltType_6987_, v_altInfo_6988_, v_k_6989_, v___y_6990_, v___y_6991_, v___y_6992_, v___y_6993_);
lean_dec(v___y_6993_);
lean_dec_ref(v___y_6992_);
lean_dec(v___y_6991_);
lean_dec_ref(v___y_6990_);
return v_res_6995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(lean_object* v_declName_6996_, lean_object* v___y_6997_, lean_object* v___y_6998_, lean_object* v___y_6999_, lean_object* v___y_7000_){
_start:
{
lean_object* v___x_7002_; 
v___x_7002_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_declName_6996_, v___y_7000_);
return v___x_7002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___boxed(lean_object* v_declName_7003_, lean_object* v___y_7004_, lean_object* v___y_7005_, lean_object* v___y_7006_, lean_object* v___y_7007_, lean_object* v___y_7008_){
_start:
{
lean_object* v_res_7009_; 
v_res_7009_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(v_declName_7003_, v___y_7004_, v___y_7005_, v___y_7006_, v___y_7007_);
lean_dec(v___y_7007_);
lean_dec_ref(v___y_7006_);
lean_dec(v___y_7005_);
lean_dec_ref(v___y_7004_);
return v_res_7009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(size_t v_sz_7010_, size_t v_i_7011_, lean_object* v_bs_7012_, lean_object* v___y_7013_, lean_object* v___y_7014_, lean_object* v___y_7015_, lean_object* v___y_7016_){
_start:
{
lean_object* v___x_7018_; 
v___x_7018_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_7010_, v_i_7011_, v_bs_7012_, v___y_7013_, v___y_7015_, v___y_7016_);
return v___x_7018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___boxed(lean_object* v_sz_7019_, lean_object* v_i_7020_, lean_object* v_bs_7021_, lean_object* v___y_7022_, lean_object* v___y_7023_, lean_object* v___y_7024_, lean_object* v___y_7025_, lean_object* v___y_7026_){
_start:
{
size_t v_sz_boxed_7027_; size_t v_i_boxed_7028_; lean_object* v_res_7029_; 
v_sz_boxed_7027_ = lean_unbox_usize(v_sz_7019_);
lean_dec(v_sz_7019_);
v_i_boxed_7028_ = lean_unbox_usize(v_i_7020_);
lean_dec(v_i_7020_);
v_res_7029_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(v_sz_boxed_7027_, v_i_boxed_7028_, v_bs_7021_, v___y_7022_, v___y_7023_, v___y_7024_, v___y_7025_);
lean_dec(v___y_7025_);
lean_dec_ref(v___y_7024_);
lean_dec(v___y_7023_);
lean_dec_ref(v___y_7022_);
return v_res_7029_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(lean_object* v_upperBound_7030_, lean_object* v_onAlt_7031_, lean_object* v_extraEqualities_7032_, lean_object* v_inst_7033_, lean_object* v_R_7034_, lean_object* v_a_7035_, lean_object* v_b_7036_, lean_object* v_c_7037_, lean_object* v___y_7038_, lean_object* v___y_7039_, lean_object* v___y_7040_, lean_object* v___y_7041_){
_start:
{
lean_object* v___x_7043_; 
v___x_7043_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v_upperBound_7030_, v_onAlt_7031_, v_extraEqualities_7032_, v_a_7035_, v_b_7036_, v___y_7038_, v___y_7039_, v___y_7040_, v___y_7041_);
return v___x_7043_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___boxed(lean_object* v_upperBound_7044_, lean_object* v_onAlt_7045_, lean_object* v_extraEqualities_7046_, lean_object* v_inst_7047_, lean_object* v_R_7048_, lean_object* v_a_7049_, lean_object* v_b_7050_, lean_object* v_c_7051_, lean_object* v___y_7052_, lean_object* v___y_7053_, lean_object* v___y_7054_, lean_object* v___y_7055_, lean_object* v___y_7056_){
_start:
{
lean_object* v_res_7057_; 
v_res_7057_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(v_upperBound_7044_, v_onAlt_7045_, v_extraEqualities_7046_, v_inst_7047_, v_R_7048_, v_a_7049_, v_b_7050_, v_c_7051_, v___y_7052_, v___y_7053_, v___y_7054_, v___y_7055_);
lean_dec(v___y_7055_);
lean_dec_ref(v___y_7054_);
lean_dec(v___y_7053_);
lean_dec_ref(v___y_7052_);
lean_dec(v_upperBound_7044_);
return v_res_7057_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(lean_object* v_upperBound_7058_, lean_object* v_onAlt_7059_, uint8_t v_useSplitter_7060_, lean_object* v_extraEqualities_7061_, lean_object* v_numDiscrEqs_7062_, lean_object* v_inst_7063_, lean_object* v_R_7064_, lean_object* v_a_7065_, lean_object* v_b_7066_, lean_object* v_c_7067_, lean_object* v___y_7068_, lean_object* v___y_7069_, lean_object* v___y_7070_, lean_object* v___y_7071_){
_start:
{
lean_object* v___x_7073_; 
v___x_7073_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v_upperBound_7058_, v_onAlt_7059_, v_useSplitter_7060_, v_extraEqualities_7061_, v_numDiscrEqs_7062_, v_a_7065_, v_b_7066_, v___y_7068_, v___y_7069_, v___y_7070_, v___y_7071_);
return v___x_7073_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___boxed(lean_object* v_upperBound_7074_, lean_object* v_onAlt_7075_, lean_object* v_useSplitter_7076_, lean_object* v_extraEqualities_7077_, lean_object* v_numDiscrEqs_7078_, lean_object* v_inst_7079_, lean_object* v_R_7080_, lean_object* v_a_7081_, lean_object* v_b_7082_, lean_object* v_c_7083_, lean_object* v___y_7084_, lean_object* v___y_7085_, lean_object* v___y_7086_, lean_object* v___y_7087_, lean_object* v___y_7088_){
_start:
{
uint8_t v_useSplitter_boxed_7089_; lean_object* v_res_7090_; 
v_useSplitter_boxed_7089_ = lean_unbox(v_useSplitter_7076_);
v_res_7090_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(v_upperBound_7074_, v_onAlt_7075_, v_useSplitter_boxed_7089_, v_extraEqualities_7077_, v_numDiscrEqs_7078_, v_inst_7079_, v_R_7080_, v_a_7081_, v_b_7082_, v_c_7083_, v___y_7084_, v___y_7085_, v___y_7086_, v___y_7087_);
lean_dec(v___y_7087_);
lean_dec_ref(v___y_7086_);
lean_dec(v___y_7085_);
lean_dec_ref(v___y_7084_);
lean_dec(v_upperBound_7074_);
return v_res_7090_;
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
