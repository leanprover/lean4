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
uint8_t v___x_4707__boxed_235_; uint8_t v_refined_boxed_236_; lean_object* v_res_237_; 
v___x_4707__boxed_235_ = lean_unbox(v___x_224_);
v_refined_boxed_236_ = lean_unbox(v_refined_226_);
v_res_237_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(v_alt_223_, v___x_4707__boxed_235_, v_xs_225_, v_refined_boxed_236_, v_unrefinedArgType_227_, v_x_228_, v_x_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
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
v___x_319_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_a_316_, v___x_317_, v___f_309_, v___x_318_, v___x_318_, v___y_314_, v___y_312_, v___y_313_, v___y_311_);
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
lean_dec_ref(v___y_332_);
v___x_335_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2);
v___x_336_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_335_, v___y_333_, v___y_330_, v___y_331_, v___y_329_);
v___y_311_ = v___y_329_;
v___y_312_ = v___y_330_;
v___y_313_ = v___y_331_;
v___y_314_ = v___y_333_;
v___y_315_ = v___x_336_;
goto v___jp_310_;
}
else
{
v___y_311_ = v___y_329_;
v___y_312_ = v___y_330_;
v___y_313_ = v___y_331_;
v___y_314_ = v___y_333_;
v___y_315_ = v___y_332_;
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
v___y_312_ = v___y_303_;
v___y_313_ = v___y_304_;
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
v___y_330_ = v___y_303_;
v___y_331_ = v___y_304_;
v___y_332_ = v___x_338_;
v___y_333_ = v___y_302_;
v___y_334_ = v___x_341_;
goto v___jp_328_;
}
else
{
lean_dec(v_a_339_);
v___y_329_ = v___y_305_;
v___y_330_ = v___y_303_;
v___y_331_ = v___y_304_;
v___y_332_ = v___x_338_;
v___y_333_ = v___y_302_;
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
uint8_t v___x_4931__boxed_372_; uint8_t v_refined_boxed_373_; lean_object* v_res_374_; 
v___x_4931__boxed_372_ = lean_unbox(v___x_360_);
v_refined_boxed_373_ = lean_unbox(v_refined_361_);
v_res_374_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(v___x_4931__boxed_372_, v_refined_boxed_373_, v_unrefinedArgType_362_, v_binderType_363_, v_numParams_364_, v_xs_365_, v_alt_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0(lean_object* v_matcherApp_574_, lean_object* v_e_575_, lean_object* v_discrs_576_, lean_object* v_toMatcherInfo_577_, lean_object* v_matcherName_578_, lean_object* v_alts_579_, lean_object* v_remaining_580_, lean_object* v_params_581_, lean_object* v_matcherLevels_582_, lean_object* v_motiveArgs_583_, lean_object* v_motiveBody_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; uint8_t v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v_matcherLevels_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_734_ = lean_array_get_size(v_motiveArgs_583_);
v___x_735_ = lean_array_get_size(v_discrs_576_);
v___x_736_ = lean_nat_dec_eq(v___x_734_, v___x_735_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec_ref(v_motiveBody_584_);
lean_dec_ref(v_matcherLevels_582_);
lean_dec_ref(v_params_581_);
lean_dec_ref(v_alts_579_);
lean_dec(v_matcherName_578_);
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
v___x_606_ = lean_infer_type(v___y_594_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref(v___x_606_);
v___x_608_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_574_);
v___x_609_ = lean_unsigned_to_nat(0u);
v___x_610_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(v___y_600_, v_a_607_, v___x_608_, v___y_598_, v___y_595_, v___x_609_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
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
v___x_618_ = l_Array_append___redArg(v___x_617_, v___y_599_);
v___x_619_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_619_, 0, v___y_597_);
lean_ctor_set(v___x_619_, 1, v___y_591_);
lean_ctor_set(v___x_619_, 2, v___y_593_);
lean_ctor_set(v___x_619_, 3, v___y_601_);
lean_ctor_set(v___x_619_, 4, v___y_592_);
lean_ctor_set(v___x_619_, 5, v___y_596_);
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
lean_dec_ref(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec_ref(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
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
lean_dec_ref(v___y_600_);
lean_dec_ref(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec_ref(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
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
v___x_657_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_583_, v___y_648_, v___x_654_, v___x_655_, v___x_654_, v___x_655_, v___x_656_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc_n(v_a_658_, 2);
lean_dec_ref(v___x_657_);
lean_inc_ref(v_matcherLevels_649_);
v___x_659_ = lean_array_to_list(v_matcherLevels_649_);
lean_inc(v___y_641_);
v___x_660_ = l_Lean_mkConst(v___y_641_, v___x_659_);
v___x_661_ = l_Lean_mkAppN(v___x_660_, v___y_647_);
v___x_662_ = l_Lean_Expr_app___override(v___x_661_, v_a_658_);
v___x_663_ = l_Lean_mkAppN(v___x_662_, v___y_642_);
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
lean_dec_ref(v___y_647_);
lean_dec_ref(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
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
v___y_591_ = v___y_641_;
v___y_592_ = v_a_658_;
v___y_593_ = v_matcherLevels_649_;
v___y_594_ = v___x_663_;
v___y_595_ = v___x_654_;
v___y_596_ = v___y_642_;
v___y_597_ = v___y_643_;
v___y_598_ = v___y_644_;
v___y_599_ = v___y_646_;
v___y_600_ = v___y_645_;
v___y_601_ = v___y_647_;
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
lean_dec_ref(v___y_647_);
lean_dec_ref(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
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
lean_dec_ref(v___y_647_);
lean_dec_ref(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
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
v___y_641_ = v_matcherName_578_;
v___y_642_ = v_discrs_576_;
v___y_643_ = v_toMatcherInfo_577_;
v___y_644_ = v_alts_579_;
v___y_645_ = v_a_699_;
v___y_646_ = v_remaining_580_;
v___y_647_ = v_params_581_;
v___y_648_ = v_a_704_;
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
v___y_641_ = v_matcherName_578_;
v___y_642_ = v_discrs_576_;
v___y_643_ = v_toMatcherInfo_577_;
v___y_644_ = v_alts_579_;
v___y_645_ = v_a_699_;
v___y_646_ = v_remaining_580_;
v___y_647_ = v_params_581_;
v___y_648_ = v_a_705_;
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
lean_dec_ref(v_alts_579_);
lean_dec(v_matcherName_578_);
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
lean_dec_ref(v_alts_579_);
lean_dec(v_matcherName_578_);
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
lean_dec_ref(v_alts_579_);
lean_dec(v_matcherName_578_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___boxed(lean_object* v_matcherApp_753_, lean_object* v_e_754_, lean_object* v_discrs_755_, lean_object* v_toMatcherInfo_756_, lean_object* v_matcherName_757_, lean_object* v_alts_758_, lean_object* v_remaining_759_, lean_object* v_params_760_, lean_object* v_matcherLevels_761_, lean_object* v_motiveArgs_762_, lean_object* v_motiveBody_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_Meta_MatcherApp_addArg___lam__0(v_matcherApp_753_, v_e_754_, v_discrs_755_, v_toMatcherInfo_756_, v_matcherName_757_, v_alts_758_, v_remaining_759_, v_params_760_, v_matcherLevels_761_, v_motiveArgs_762_, v_motiveBody_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec_ref(v_motiveArgs_762_);
lean_dec_ref(v_remaining_759_);
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
lean_closure_set(v___f_785_, 4, v_matcherName_778_);
lean_closure_set(v___f_785_, 5, v_alts_783_);
lean_closure_set(v___f_785_, 6, v_remaining_784_);
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
uint8_t v___x_4262__boxed_985_; uint8_t v___x_4263__boxed_986_; uint8_t v___x_4264__boxed_987_; lean_object* v_res_988_; 
v___x_4262__boxed_985_ = lean_unbox(v___x_974_);
v___x_4263__boxed_986_ = lean_unbox(v___x_975_);
v___x_4264__boxed_987_ = lean_unbox(v___x_976_);
v_res_988_ = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0(v___x_4262__boxed_985_, v___x_4263__boxed_986_, v___x_4264__boxed_987_, v_a_977_, v_fvs_978_, v_body_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
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
v___x_1128_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg(v_a_1127_, v___y_1121_, v___y_1119_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
return v___x_1128_;
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_dec_ref(v___y_1121_);
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
v___x_1153_ = l_Lean_mkConst(v___y_1141_, v___x_1152_);
v___x_1154_ = l_Lean_mkAppN(v___x_1153_, v___y_1139_);
v___x_1155_ = l_Lean_Expr_app___override(v___x_1154_, v_a_1151_);
v___x_1156_ = l_Lean_mkAppN(v___x_1155_, v___y_1138_);
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
v___y_1119_ = v___x_1147_;
v___y_1120_ = v___x_1156_;
v___y_1121_ = v___f_1104_;
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
lean_dec(v___y_1141_);
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
v___y_1138_ = v_discrs_1105_;
v___y_1139_ = v_params_1108_;
v___y_1140_ = v_a_1196_;
v___y_1141_ = v_matcherName_1109_;
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
v___y_1138_ = v_discrs_1105_;
v___y_1139_ = v_params_1108_;
v___y_1140_ = v_a_1197_;
v___y_1141_ = v_matcherName_1109_;
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
uint8_t v_val_14325__boxed_1648_; lean_object* v_res_1649_; 
v_val_14325__boxed_1648_ = lean_unbox(v_val_1641_);
v_res_1649_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__6(v_val_14325__boxed_1648_, v_a_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
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
uint8_t v_____do__lift_14516__boxed_1804_; lean_object* v_res_1805_; 
v_____do__lift_14516__boxed_1804_ = lean_unbox(v_____do__lift_1803_);
v_res_1805_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__11(v___x_1791_, v_a_1792_, v_inst_1793_, v_toBind_1794_, v___f_1795_, v_fst_1796_, v_fst_1797_, v___x_1798_, v___x_1799_, v___x_1800_, v_fst_1801_, v_toPure_1802_, v_____do__lift_14516__boxed_1804_);
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
uint8_t v___x_14961__boxed_2165_; uint8_t v___x_14962__boxed_2166_; lean_object* v_res_2167_; 
v___x_14961__boxed_2165_ = lean_unbox(v___x_2161_);
v___x_14962__boxed_2166_ = lean_unbox(v___x_2162_);
v_res_2167_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__23(v_xs_2159_, v_ys4_2160_, v___x_14961__boxed_2165_, v___x_14962__boxed_2166_, v_inst_2163_, v_alt_x27_2164_);
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
uint8_t v___x_15014__boxed_2227_; uint8_t v___x_15015__boxed_2228_; lean_object* v_res_2229_; 
v___x_15014__boxed_2227_ = lean_unbox(v___x_2214_);
v___x_15015__boxed_2228_ = lean_unbox(v___x_2215_);
v_res_2229_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__26(v_xs_2213_, v___x_15014__boxed_2227_, v___x_15015__boxed_2228_, v_inst_2216_, v_remaining_x27_2217_, v_onAlt_2218_, v_next_2219_, v_toBind_2220_, v___x_2221_, v_inst_2222_, v_inst_2223_, v___f_2224_, v_ys4_2225_, v_altType_2226_);
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
uint8_t v___x_15049__boxed_2263_; uint8_t v___x_15050__boxed_2264_; lean_object* v_res_2265_; 
v___x_15049__boxed_2263_ = lean_unbox(v___x_2249_);
v___x_15050__boxed_2264_ = lean_unbox(v___x_2250_);
v_res_2265_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__27(v___x_15049__boxed_2263_, v___x_15050__boxed_2264_, v_inst_2251_, v_remaining_x27_2252_, v_onAlt_2253_, v_next_2254_, v_toBind_2255_, v___x_2256_, v_inst_2257_, v_inst_2258_, v___f_2259_, v_fst_2260_, v_xs_2261_, v_altType_2262_);
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
uint8_t v___x_15100__boxed_2429_; uint8_t v___x_15101__boxed_2430_; lean_object* v_res_2431_; 
v___x_15100__boxed_2429_ = lean_unbox(v___x_2416_);
v___x_15101__boxed_2430_ = lean_unbox(v___x_2417_);
v_res_2431_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__29(v___x_2412_, v_toPure_2413_, v_toBind_2414_, v___f_2415_, v___x_15100__boxed_2429_, v___x_15101__boxed_2430_, v_inst_2418_, v_remaining_x27_2419_, v_onAlt_2420_, v_inst_2421_, v_inst_2422_, v___f_2423_, v_fst_2424_, v_next_2425_, v_acc_2426_, v_h_2427_, v_G_2428_);
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
uint8_t v___x_15357__boxed_2496_; uint8_t v___x_15358__boxed_2497_; lean_object* v_res_2498_; 
v___x_15357__boxed_2496_ = lean_unbox(v___x_2482_);
v___x_15358__boxed_2497_ = lean_unbox(v___x_2483_);
v_res_2498_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__31(v_alts_2478_, v_toPure_2479_, v_toBind_2480_, v___f_2481_, v___x_15357__boxed_2496_, v___x_15358__boxed_2497_, v_inst_2484_, v_remaining_x27_2485_, v_onAlt_2486_, v_inst_2487_, v_inst_2488_, v___f_2489_, v_fst_2490_, v_matcherApp_2491_, v___x_2492_, v___f_2493_, v_aux_2494_, v_____r_2495_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35(lean_object* v_toPure_2522_, lean_object* v_next_2523_, lean_object* v_G_2524_, lean_object* v_____do__lift_2525_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed(lean_object* v_toPure_2532_, lean_object* v_next_2533_, lean_object* v_G_2534_, lean_object* v_____do__lift_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__35(v_toPure_2532_, v_next_2533_, v_G_2534_, v_____do__lift_2535_);
lean_dec(v_next_2533_);
return v_res_2536_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5(void){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2545_ = lean_box(0);
v___x_2546_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__4));
v___x_2547_ = l_Lean_mkConst(v___x_2546_, v___x_2545_);
return v___x_2547_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2548_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5);
v___x_2549_ = lean_unsigned_to_nat(2u);
v___x_2550_ = lean_mk_empty_array_with_capacity(v___x_2549_);
v___x_2551_ = lean_array_push(v___x_2550_, v___x_2548_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34(lean_object* v___x_2552_, lean_object* v_toPure_2553_, lean_object* v_inst_2554_, lean_object* v_alt_x27_2555_){
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
v___x_2558_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__2));
v___x_2559_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6);
v___x_2560_ = lean_array_push(v___x_2559_, v_alt_x27_2555_);
v___x_2561_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___boxed), 7, 2);
lean_closure_set(v___x_2561_, 0, v___x_2558_);
lean_closure_set(v___x_2561_, 1, v___x_2560_);
v___x_2562_ = lean_apply_2(v_inst_2554_, lean_box(0), v___x_2561_);
return v___x_2562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed(lean_object* v___x_2563_, lean_object* v_toPure_2564_, lean_object* v_inst_2565_, lean_object* v_alt_x27_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__34(v___x_2563_, v_toPure_2564_, v_inst_2565_, v_alt_x27_2566_);
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
uint8_t v___x_15511__boxed_2595_; uint8_t v_useSplitter_boxed_2596_; lean_object* v_res_2597_; 
v___x_15511__boxed_2595_ = lean_unbox(v___x_2591_);
v_useSplitter_boxed_2596_ = lean_unbox(v_useSplitter_2592_);
v_res_2597_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__36(v_ys_2587_, v_ys2_2588_, v_ys3_2589_, v_ys4_2590_, v___x_15511__boxed_2595_, v_useSplitter_boxed_2596_, v_inst_2593_, v_alt_x27_2594_);
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
uint8_t v___x_15548__boxed_2653_; uint8_t v_useSplitter_boxed_2654_; lean_object* v_res_2655_; 
v___x_15548__boxed_2653_ = lean_unbox(v___x_2642_);
v_useSplitter_boxed_2654_ = lean_unbox(v_useSplitter_2643_);
v_res_2655_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__38(v_inst_2638_, v_ys_2639_, v_ys2_2640_, v_ys3_2641_, v___x_15548__boxed_2653_, v_useSplitter_boxed_2654_, v_inst_2644_, v_args_2645_, v_onAlt_2646_, v_next_2647_, v_toBind_2648_, v___x_2649_, v___f_2650_, v_ys4_2651_, v_altType_2652_);
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
uint8_t v___x_15581__boxed_2695_; uint8_t v_useSplitter_boxed_2696_; lean_object* v_res_2697_; 
v___x_15581__boxed_2695_ = lean_unbox(v___x_2681_);
v_useSplitter_boxed_2696_ = lean_unbox(v_useSplitter_2682_);
v_res_2697_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__39(v_inst_2678_, v_ys_2679_, v_ys2_2680_, v___x_15581__boxed_2695_, v_useSplitter_boxed_2696_, v_inst_2683_, v_args_2684_, v_onAlt_2685_, v_next_2686_, v_toBind_2687_, v___x_2688_, v___f_2689_, v_fst_2690_, v_inst_2691_, v_inst_2692_, v_ys3_2693_, v_altType_2694_);
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
uint8_t v___x_15612__boxed_2737_; uint8_t v_useSplitter_boxed_2738_; lean_object* v_res_2739_; 
v___x_15612__boxed_2737_ = lean_unbox(v___x_2722_);
v_useSplitter_boxed_2738_ = lean_unbox(v_useSplitter_2723_);
v_res_2739_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__40(v_inst_2720_, v_ys_2721_, v___x_15612__boxed_2737_, v_useSplitter_boxed_2738_, v_inst_2724_, v_args_2725_, v_onAlt_2726_, v_next_2727_, v_toBind_2728_, v___x_2729_, v___f_2730_, v_fst_2731_, v_inst_2732_, v_inst_2733_, v_numDiscrEqs_2734_, v_ys2_2735_, v_altType_2736_);
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
uint8_t v___x_15646__boxed_2760_; lean_object* v_res_2761_; 
v___x_15646__boxed_2760_ = lean_unbox(v___x_2756_);
v_res_2761_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__41(v___x_2752_, v_inst_2753_, v_inst_2754_, v___f_2755_, v___x_15646__boxed_2760_, v_toBind_2757_, v___f_2758_, v_altType_2759_);
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
uint8_t v___x_15741__boxed_2867_; uint8_t v_useSplitter_boxed_2868_; uint8_t v_hasUnitThunk_boxed_2869_; lean_object* v_res_2870_; 
v___x_15741__boxed_2867_ = lean_unbox(v___x_2849_);
v_useSplitter_boxed_2868_ = lean_unbox(v_useSplitter_2850_);
v_hasUnitThunk_boxed_2869_ = lean_unbox(v_hasUnitThunk_2861_);
v_res_2870_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__43(v___x_2846_, v_inst_2847_, v_inst_2848_, v___x_15741__boxed_2867_, v_useSplitter_boxed_2868_, v_inst_2851_, v_onAlt_2852_, v_next_2853_, v_toBind_2854_, v___x_2855_, v___f_2856_, v_fst_2857_, v_inst_2858_, v_numDiscrEqs_2859_, v___f_2860_, v_hasUnitThunk_boxed_2869_, v_toPure_2862_, v___x_2863_, v___x_2864_, v_ys_2865_, v_args_2866_);
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
v___f_2961_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed), 4, 3);
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
v___f_3107_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed), 4, 3);
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
uint8_t v___x_15900__boxed_3173_; uint8_t v_useSplitter_boxed_3174_; lean_object* v_res_3175_; 
v___x_15900__boxed_3173_ = lean_unbox(v___x_3162_);
v_useSplitter_boxed_3174_ = lean_unbox(v_useSplitter_3163_);
v_res_3175_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__46(v___x_3154_, v_toPure_3155_, v_toBind_3156_, v___f_3157_, v___x_3158_, v_inst_3159_, v_inst_3160_, v_inst_3161_, v___x_15900__boxed_3173_, v_useSplitter_boxed_3174_, v_onAlt_3164_, v___f_3165_, v_fst_3166_, v_inst_3167_, v_numDiscrEqs_3168_, v_next_3169_, v_acc_3170_, v_h_3171_, v_G_3172_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53(lean_object* v___x_3329_, lean_object* v_params_x27_3330_, lean_object* v_fst_3331_, lean_object* v_discrs_x27_3332_, lean_object* v_fst_3333_, lean_object* v_numParams_3334_, lean_object* v_numDiscrs_3335_, lean_object* v_altInfos_3336_, lean_object* v_uElimPos_x3f_3337_, lean_object* v_snd_3338_, lean_object* v_overlaps_3339_, lean_object* v_matcherLevels_3340_, lean_object* v_toPure_3341_, lean_object* v_onRemaining_3342_, lean_object* v_remaining_3343_, lean_object* v_toBind_3344_, lean_object* v_origAltTypes_3345_, lean_object* v_alts_3346_, lean_object* v___x_3347_, lean_object* v___x_3348_, lean_object* v_remaining_x27_3349_, lean_object* v___f_3350_, lean_object* v_inst_3351_, lean_object* v___x_3352_, uint8_t v___x_3353_, lean_object* v_liftWith_3354_, lean_object* v_restoreM_3355_, lean_object* v_matchEqns_3356_){
_start:
{
lean_object* v_splitterName_3357_; lean_object* v_splitterMatchInfo_3358_; lean_object* v___x_3359_; lean_object* v_aux2_3360_; lean_object* v_aux2_3361_; lean_object* v_aux2_3362_; lean_object* v___x_3363_; lean_object* v___f_3364_; lean_object* v___f_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___f_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___f_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v_splitterName_3357_ = lean_ctor_get(v_matchEqns_3356_, 1);
lean_inc_n(v_splitterName_3357_, 2);
v_splitterMatchInfo_3358_ = lean_ctor_get(v_matchEqns_3356_, 2);
lean_inc_ref(v_splitterMatchInfo_3358_);
lean_dec_ref(v_matchEqns_3356_);
v___x_3359_ = l_Lean_mkConst(v_splitterName_3357_, v___x_3329_);
v_aux2_3360_ = l_Lean_mkAppN(v___x_3359_, v_params_x27_3330_);
lean_inc_ref(v_fst_3331_);
v_aux2_3361_ = l_Lean_Expr_app___override(v_aux2_3360_, v_fst_3331_);
v_aux2_3362_ = l_Lean_mkAppN(v_aux2_3361_, v_discrs_x27_3332_);
lean_inc_ref_n(v_aux2_3362_, 2);
v___x_3363_ = l_Lean_indentExpr(v_aux2_3362_);
lean_inc(v___x_3348_);
lean_inc_n(v_toBind_3344_, 3);
v___f_3364_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed), 24, 23);
lean_closure_set(v___f_3364_, 0, v_splitterMatchInfo_3358_);
lean_closure_set(v___f_3364_, 1, v_fst_3333_);
lean_closure_set(v___f_3364_, 2, v_numParams_3334_);
lean_closure_set(v___f_3364_, 3, v_numDiscrs_3335_);
lean_closure_set(v___f_3364_, 4, v_altInfos_3336_);
lean_closure_set(v___f_3364_, 5, v_uElimPos_x3f_3337_);
lean_closure_set(v___f_3364_, 6, v_snd_3338_);
lean_closure_set(v___f_3364_, 7, v_overlaps_3339_);
lean_closure_set(v___f_3364_, 8, v_splitterName_3357_);
lean_closure_set(v___f_3364_, 9, v_matcherLevels_3340_);
lean_closure_set(v___f_3364_, 10, v_params_x27_3330_);
lean_closure_set(v___f_3364_, 11, v_fst_3331_);
lean_closure_set(v___f_3364_, 12, v_discrs_x27_3332_);
lean_closure_set(v___f_3364_, 13, v_toPure_3341_);
lean_closure_set(v___f_3364_, 14, v_onRemaining_3342_);
lean_closure_set(v___f_3364_, 15, v_remaining_3343_);
lean_closure_set(v___f_3364_, 16, v_toBind_3344_);
lean_closure_set(v___f_3364_, 17, v_origAltTypes_3345_);
lean_closure_set(v___f_3364_, 18, v_alts_3346_);
lean_closure_set(v___f_3364_, 19, v___x_3347_);
lean_closure_set(v___f_3364_, 20, v___x_3348_);
lean_closure_set(v___f_3364_, 21, v_remaining_x27_3349_);
lean_closure_set(v___f_3364_, 22, v___f_3350_);
lean_inc(v_inst_3351_);
v___f_3365_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__50), 6, 5);
lean_closure_set(v___f_3365_, 0, v___x_3348_);
lean_closure_set(v___f_3365_, 1, v_aux2_3362_);
lean_closure_set(v___f_3365_, 2, v_inst_3351_);
lean_closure_set(v___f_3365_, 3, v_toBind_3344_);
lean_closure_set(v___f_3365_, 4, v___f_3364_);
v___x_3366_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1);
v___x_3367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3366_);
lean_ctor_set(v___x_3367_, 1, v___x_3363_);
v___x_3368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3367_);
lean_ctor_set(v___x_3368_, 1, v___x_3352_);
v___f_3369_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3369_, 0, v___x_3368_);
v___x_3370_ = lean_box(v___x_3353_);
v___x_3371_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_3371_, 0, v_aux2_3362_);
lean_closure_set(v___x_3371_, 1, v___x_3370_);
v___x_3372_ = lean_apply_2(v_inst_3351_, lean_box(0), v___x_3371_);
v___f_3373_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3373_, 0, v___x_3372_);
lean_closure_set(v___f_3373_, 1, v___f_3369_);
v___x_3374_ = lean_apply_2(v_liftWith_3354_, lean_box(0), v___f_3373_);
v___x_3375_ = lean_apply_1(v_restoreM_3355_, lean_box(0));
v___x_3376_ = lean_apply_4(v_toBind_3344_, lean_box(0), lean_box(0), v___x_3374_, v___x_3375_);
v___x_3377_ = lean_apply_4(v_toBind_3344_, lean_box(0), lean_box(0), v___x_3376_, v___f_3365_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed(lean_object** _args){
lean_object* v___x_3378_ = _args[0];
lean_object* v_params_x27_3379_ = _args[1];
lean_object* v_fst_3380_ = _args[2];
lean_object* v_discrs_x27_3381_ = _args[3];
lean_object* v_fst_3382_ = _args[4];
lean_object* v_numParams_3383_ = _args[5];
lean_object* v_numDiscrs_3384_ = _args[6];
lean_object* v_altInfos_3385_ = _args[7];
lean_object* v_uElimPos_x3f_3386_ = _args[8];
lean_object* v_snd_3387_ = _args[9];
lean_object* v_overlaps_3388_ = _args[10];
lean_object* v_matcherLevels_3389_ = _args[11];
lean_object* v_toPure_3390_ = _args[12];
lean_object* v_onRemaining_3391_ = _args[13];
lean_object* v_remaining_3392_ = _args[14];
lean_object* v_toBind_3393_ = _args[15];
lean_object* v_origAltTypes_3394_ = _args[16];
lean_object* v_alts_3395_ = _args[17];
lean_object* v___x_3396_ = _args[18];
lean_object* v___x_3397_ = _args[19];
lean_object* v_remaining_x27_3398_ = _args[20];
lean_object* v___f_3399_ = _args[21];
lean_object* v_inst_3400_ = _args[22];
lean_object* v___x_3401_ = _args[23];
lean_object* v___x_3402_ = _args[24];
lean_object* v_liftWith_3403_ = _args[25];
lean_object* v_restoreM_3404_ = _args[26];
lean_object* v_matchEqns_3405_ = _args[27];
_start:
{
uint8_t v___x_16445__boxed_3406_; lean_object* v_res_3407_; 
v___x_16445__boxed_3406_ = lean_unbox(v___x_3402_);
v_res_3407_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__53(v___x_3378_, v_params_x27_3379_, v_fst_3380_, v_discrs_x27_3381_, v_fst_3382_, v_numParams_3383_, v_numDiscrs_3384_, v_altInfos_3385_, v_uElimPos_x3f_3386_, v_snd_3387_, v_overlaps_3388_, v_matcherLevels_3389_, v_toPure_3390_, v_onRemaining_3391_, v_remaining_3392_, v_toBind_3393_, v_origAltTypes_3394_, v_alts_3395_, v___x_3396_, v___x_3397_, v_remaining_x27_3398_, v___f_3399_, v_inst_3400_, v___x_3401_, v___x_16445__boxed_3406_, v_liftWith_3403_, v_restoreM_3404_, v_matchEqns_3405_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51(lean_object* v___x_3408_, lean_object* v_params_x27_3409_, lean_object* v_fst_3410_, lean_object* v_discrs_x27_3411_, lean_object* v_fst_3412_, lean_object* v_numParams_3413_, lean_object* v_numDiscrs_3414_, lean_object* v_altInfos_3415_, lean_object* v_uElimPos_x3f_3416_, lean_object* v_snd_3417_, lean_object* v_overlaps_3418_, lean_object* v_matcherLevels_3419_, lean_object* v_toPure_3420_, lean_object* v_onRemaining_3421_, lean_object* v_remaining_3422_, lean_object* v_toBind_3423_, lean_object* v_alts_3424_, lean_object* v___x_3425_, lean_object* v___x_3426_, lean_object* v_remaining_x27_3427_, lean_object* v___f_3428_, lean_object* v_inst_3429_, lean_object* v___x_3430_, uint8_t v___x_3431_, lean_object* v_liftWith_3432_, lean_object* v_restoreM_3433_, lean_object* v_matcherName_3434_, lean_object* v_origAltTypes_3435_){
_start:
{
lean_object* v___x_3436_; lean_object* v___f_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3436_ = lean_box(v___x_3431_);
lean_inc(v_inst_3429_);
lean_inc(v_toBind_3423_);
v___f_3437_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed), 28, 27);
lean_closure_set(v___f_3437_, 0, v___x_3408_);
lean_closure_set(v___f_3437_, 1, v_params_x27_3409_);
lean_closure_set(v___f_3437_, 2, v_fst_3410_);
lean_closure_set(v___f_3437_, 3, v_discrs_x27_3411_);
lean_closure_set(v___f_3437_, 4, v_fst_3412_);
lean_closure_set(v___f_3437_, 5, v_numParams_3413_);
lean_closure_set(v___f_3437_, 6, v_numDiscrs_3414_);
lean_closure_set(v___f_3437_, 7, v_altInfos_3415_);
lean_closure_set(v___f_3437_, 8, v_uElimPos_x3f_3416_);
lean_closure_set(v___f_3437_, 9, v_snd_3417_);
lean_closure_set(v___f_3437_, 10, v_overlaps_3418_);
lean_closure_set(v___f_3437_, 11, v_matcherLevels_3419_);
lean_closure_set(v___f_3437_, 12, v_toPure_3420_);
lean_closure_set(v___f_3437_, 13, v_onRemaining_3421_);
lean_closure_set(v___f_3437_, 14, v_remaining_3422_);
lean_closure_set(v___f_3437_, 15, v_toBind_3423_);
lean_closure_set(v___f_3437_, 16, v_origAltTypes_3435_);
lean_closure_set(v___f_3437_, 17, v_alts_3424_);
lean_closure_set(v___f_3437_, 18, v___x_3425_);
lean_closure_set(v___f_3437_, 19, v___x_3426_);
lean_closure_set(v___f_3437_, 20, v_remaining_x27_3427_);
lean_closure_set(v___f_3437_, 21, v___f_3428_);
lean_closure_set(v___f_3437_, 22, v_inst_3429_);
lean_closure_set(v___f_3437_, 23, v___x_3430_);
lean_closure_set(v___f_3437_, 24, v___x_3436_);
lean_closure_set(v___f_3437_, 25, v_liftWith_3432_);
lean_closure_set(v___f_3437_, 26, v_restoreM_3433_);
v___x_3438_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_getEquationsFor___boxed), 6, 1);
lean_closure_set(v___x_3438_, 0, v_matcherName_3434_);
v___x_3439_ = lean_apply_2(v_inst_3429_, lean_box(0), v___x_3438_);
v___x_3440_ = lean_apply_4(v_toBind_3423_, lean_box(0), lean_box(0), v___x_3439_, v___f_3437_);
return v___x_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed(lean_object** _args){
lean_object* v___x_3441_ = _args[0];
lean_object* v_params_x27_3442_ = _args[1];
lean_object* v_fst_3443_ = _args[2];
lean_object* v_discrs_x27_3444_ = _args[3];
lean_object* v_fst_3445_ = _args[4];
lean_object* v_numParams_3446_ = _args[5];
lean_object* v_numDiscrs_3447_ = _args[6];
lean_object* v_altInfos_3448_ = _args[7];
lean_object* v_uElimPos_x3f_3449_ = _args[8];
lean_object* v_snd_3450_ = _args[9];
lean_object* v_overlaps_3451_ = _args[10];
lean_object* v_matcherLevels_3452_ = _args[11];
lean_object* v_toPure_3453_ = _args[12];
lean_object* v_onRemaining_3454_ = _args[13];
lean_object* v_remaining_3455_ = _args[14];
lean_object* v_toBind_3456_ = _args[15];
lean_object* v_alts_3457_ = _args[16];
lean_object* v___x_3458_ = _args[17];
lean_object* v___x_3459_ = _args[18];
lean_object* v_remaining_x27_3460_ = _args[19];
lean_object* v___f_3461_ = _args[20];
lean_object* v_inst_3462_ = _args[21];
lean_object* v___x_3463_ = _args[22];
lean_object* v___x_3464_ = _args[23];
lean_object* v_liftWith_3465_ = _args[24];
lean_object* v_restoreM_3466_ = _args[25];
lean_object* v_matcherName_3467_ = _args[26];
lean_object* v_origAltTypes_3468_ = _args[27];
_start:
{
uint8_t v___x_16507__boxed_3469_; lean_object* v_res_3470_; 
v___x_16507__boxed_3469_ = lean_unbox(v___x_3464_);
v_res_3470_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__51(v___x_3441_, v_params_x27_3442_, v_fst_3443_, v_discrs_x27_3444_, v_fst_3445_, v_numParams_3446_, v_numDiscrs_3447_, v_altInfos_3448_, v_uElimPos_x3f_3449_, v_snd_3450_, v_overlaps_3451_, v_matcherLevels_3452_, v_toPure_3453_, v_onRemaining_3454_, v_remaining_3455_, v_toBind_3456_, v_alts_3457_, v___x_3458_, v___x_3459_, v_remaining_x27_3460_, v___f_3461_, v_inst_3462_, v___x_3463_, v___x_16507__boxed_3469_, v_liftWith_3465_, v_restoreM_3466_, v_matcherName_3467_, v_origAltTypes_3468_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52(lean_object* v_alts_3471_, lean_object* v_toPure_3472_, lean_object* v_toBind_3473_, lean_object* v___f_3474_, lean_object* v___x_3475_, lean_object* v_inst_3476_, lean_object* v_inst_3477_, lean_object* v_inst_3478_, uint8_t v___x_3479_, uint8_t v_useSplitter_3480_, lean_object* v_onAlt_3481_, lean_object* v___f_3482_, lean_object* v_fst_3483_, lean_object* v_inst_3484_, lean_object* v_numDiscrEqs_3485_, lean_object* v___x_3486_, lean_object* v_params_x27_3487_, lean_object* v_fst_3488_, lean_object* v_discrs_x27_3489_, lean_object* v_fst_3490_, lean_object* v_numParams_3491_, lean_object* v_numDiscrs_3492_, lean_object* v_altInfos_3493_, lean_object* v_uElimPos_x3f_3494_, lean_object* v_snd_3495_, lean_object* v_overlaps_3496_, lean_object* v_matcherLevels_3497_, lean_object* v_onRemaining_3498_, lean_object* v_remaining_3499_, lean_object* v_remaining_x27_3500_, lean_object* v___x_3501_, uint8_t v___x_3502_, lean_object* v_liftWith_3503_, lean_object* v_restoreM_3504_, lean_object* v_matcherName_3505_, lean_object* v_aux1_3506_, lean_object* v_____r_3507_){
_start:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___f_3511_; lean_object* v___x_3512_; lean_object* v___f_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3508_ = lean_array_get_size(v_alts_3471_);
v___x_3509_ = lean_box(v___x_3479_);
v___x_3510_ = lean_box(v_useSplitter_3480_);
lean_inc_n(v_inst_3477_, 2);
lean_inc(v___x_3475_);
lean_inc_n(v_toBind_3473_, 2);
lean_inc(v_toPure_3472_);
v___f_3511_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46___boxed), 19, 15);
lean_closure_set(v___f_3511_, 0, v___x_3508_);
lean_closure_set(v___f_3511_, 1, v_toPure_3472_);
lean_closure_set(v___f_3511_, 2, v_toBind_3473_);
lean_closure_set(v___f_3511_, 3, v___f_3474_);
lean_closure_set(v___f_3511_, 4, v___x_3475_);
lean_closure_set(v___f_3511_, 5, v_inst_3476_);
lean_closure_set(v___f_3511_, 6, v_inst_3477_);
lean_closure_set(v___f_3511_, 7, v_inst_3478_);
lean_closure_set(v___f_3511_, 8, v___x_3509_);
lean_closure_set(v___f_3511_, 9, v___x_3510_);
lean_closure_set(v___f_3511_, 10, v_onAlt_3481_);
lean_closure_set(v___f_3511_, 11, v___f_3482_);
lean_closure_set(v___f_3511_, 12, v_fst_3483_);
lean_closure_set(v___f_3511_, 13, v_inst_3484_);
lean_closure_set(v___f_3511_, 14, v_numDiscrEqs_3485_);
v___x_3512_ = lean_box(v___x_3502_);
v___f_3513_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed), 28, 27);
lean_closure_set(v___f_3513_, 0, v___x_3486_);
lean_closure_set(v___f_3513_, 1, v_params_x27_3487_);
lean_closure_set(v___f_3513_, 2, v_fst_3488_);
lean_closure_set(v___f_3513_, 3, v_discrs_x27_3489_);
lean_closure_set(v___f_3513_, 4, v_fst_3490_);
lean_closure_set(v___f_3513_, 5, v_numParams_3491_);
lean_closure_set(v___f_3513_, 6, v_numDiscrs_3492_);
lean_closure_set(v___f_3513_, 7, v_altInfos_3493_);
lean_closure_set(v___f_3513_, 8, v_uElimPos_x3f_3494_);
lean_closure_set(v___f_3513_, 9, v_snd_3495_);
lean_closure_set(v___f_3513_, 10, v_overlaps_3496_);
lean_closure_set(v___f_3513_, 11, v_matcherLevels_3497_);
lean_closure_set(v___f_3513_, 12, v_toPure_3472_);
lean_closure_set(v___f_3513_, 13, v_onRemaining_3498_);
lean_closure_set(v___f_3513_, 14, v_remaining_3499_);
lean_closure_set(v___f_3513_, 15, v_toBind_3473_);
lean_closure_set(v___f_3513_, 16, v_alts_3471_);
lean_closure_set(v___f_3513_, 17, v___x_3475_);
lean_closure_set(v___f_3513_, 18, v___x_3508_);
lean_closure_set(v___f_3513_, 19, v_remaining_x27_3500_);
lean_closure_set(v___f_3513_, 20, v___f_3511_);
lean_closure_set(v___f_3513_, 21, v_inst_3477_);
lean_closure_set(v___f_3513_, 22, v___x_3501_);
lean_closure_set(v___f_3513_, 23, v___x_3512_);
lean_closure_set(v___f_3513_, 24, v_liftWith_3503_);
lean_closure_set(v___f_3513_, 25, v_restoreM_3504_);
lean_closure_set(v___f_3513_, 26, v_matcherName_3505_);
v___x_3514_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_3514_, 0, v___x_3508_);
lean_closure_set(v___x_3514_, 1, v_aux1_3506_);
v___x_3515_ = lean_apply_2(v_inst_3477_, lean_box(0), v___x_3514_);
v___x_3516_ = lean_apply_4(v_toBind_3473_, lean_box(0), lean_box(0), v___x_3515_, v___f_3513_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed(lean_object** _args){
lean_object* v_alts_3517_ = _args[0];
lean_object* v_toPure_3518_ = _args[1];
lean_object* v_toBind_3519_ = _args[2];
lean_object* v___f_3520_ = _args[3];
lean_object* v___x_3521_ = _args[4];
lean_object* v_inst_3522_ = _args[5];
lean_object* v_inst_3523_ = _args[6];
lean_object* v_inst_3524_ = _args[7];
lean_object* v___x_3525_ = _args[8];
lean_object* v_useSplitter_3526_ = _args[9];
lean_object* v_onAlt_3527_ = _args[10];
lean_object* v___f_3528_ = _args[11];
lean_object* v_fst_3529_ = _args[12];
lean_object* v_inst_3530_ = _args[13];
lean_object* v_numDiscrEqs_3531_ = _args[14];
lean_object* v___x_3532_ = _args[15];
lean_object* v_params_x27_3533_ = _args[16];
lean_object* v_fst_3534_ = _args[17];
lean_object* v_discrs_x27_3535_ = _args[18];
lean_object* v_fst_3536_ = _args[19];
lean_object* v_numParams_3537_ = _args[20];
lean_object* v_numDiscrs_3538_ = _args[21];
lean_object* v_altInfos_3539_ = _args[22];
lean_object* v_uElimPos_x3f_3540_ = _args[23];
lean_object* v_snd_3541_ = _args[24];
lean_object* v_overlaps_3542_ = _args[25];
lean_object* v_matcherLevels_3543_ = _args[26];
lean_object* v_onRemaining_3544_ = _args[27];
lean_object* v_remaining_3545_ = _args[28];
lean_object* v_remaining_x27_3546_ = _args[29];
lean_object* v___x_3547_ = _args[30];
lean_object* v___x_3548_ = _args[31];
lean_object* v_liftWith_3549_ = _args[32];
lean_object* v_restoreM_3550_ = _args[33];
lean_object* v_matcherName_3551_ = _args[34];
lean_object* v_aux1_3552_ = _args[35];
lean_object* v_____r_3553_ = _args[36];
_start:
{
uint8_t v___x_16541__boxed_3554_; uint8_t v_useSplitter_boxed_3555_; uint8_t v___x_16548__boxed_3556_; lean_object* v_res_3557_; 
v___x_16541__boxed_3554_ = lean_unbox(v___x_3525_);
v_useSplitter_boxed_3555_ = lean_unbox(v_useSplitter_3526_);
v___x_16548__boxed_3556_ = lean_unbox(v___x_3548_);
v_res_3557_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__52(v_alts_3517_, v_toPure_3518_, v_toBind_3519_, v___f_3520_, v___x_3521_, v_inst_3522_, v_inst_3523_, v_inst_3524_, v___x_16541__boxed_3554_, v_useSplitter_boxed_3555_, v_onAlt_3527_, v___f_3528_, v_fst_3529_, v_inst_3530_, v_numDiscrEqs_3531_, v___x_3532_, v_params_x27_3533_, v_fst_3534_, v_discrs_x27_3535_, v_fst_3536_, v_numParams_3537_, v_numDiscrs_3538_, v_altInfos_3539_, v_uElimPos_x3f_3540_, v_snd_3541_, v_overlaps_3542_, v_matcherLevels_3543_, v_onRemaining_3544_, v_remaining_3545_, v_remaining_x27_3546_, v___x_3547_, v___x_16548__boxed_3556_, v_liftWith_3549_, v_restoreM_3550_, v_matcherName_3551_, v_aux1_3552_, v_____r_3553_);
return v_res_3557_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1(void){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3559_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__0));
v___x_3560_ = l_Lean_stringToMessageData(v___x_3559_);
return v___x_3560_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3(void){
_start:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3562_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__2));
v___x_3563_ = l_Lean_stringToMessageData(v___x_3562_);
return v___x_3563_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5(void){
_start:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3565_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__4));
v___x_3566_ = l_Lean_stringToMessageData(v___x_3565_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55(lean_object* v_numParams_3567_, lean_object* v_numDiscrs_3568_, lean_object* v_altInfos_3569_, lean_object* v_uElimPos_x3f_3570_, lean_object* v_snd_3571_, lean_object* v_overlaps_3572_, lean_object* v_matcherName_3573_, lean_object* v_matcherLevels_3574_, lean_object* v_params_x27_3575_, lean_object* v_fst_3576_, lean_object* v_discrs_x27_3577_, lean_object* v_toPure_3578_, lean_object* v_onRemaining_3579_, lean_object* v_remaining_3580_, lean_object* v_toBind_3581_, lean_object* v_inst_3582_, lean_object* v_alts_3583_, lean_object* v___f_3584_, uint8_t v___x_3585_, lean_object* v_inst_3586_, lean_object* v_remaining_x27_3587_, lean_object* v_onAlt_3588_, lean_object* v_inst_3589_, lean_object* v___f_3590_, lean_object* v_matcherApp_3591_, lean_object* v___x_3592_, uint8_t v_useSplitter_3593_, uint8_t v_isCasesOn_3594_, lean_object* v___f_3595_, lean_object* v_inst_3596_, lean_object* v___f_3597_, lean_object* v_numDiscrEqs_3598_, lean_object* v_____s_3599_){
_start:
{
lean_object* v_snd_3600_; lean_object* v_fst_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3667_; 
v_snd_3600_ = lean_ctor_get(v_____s_3599_, 1);
v_fst_3601_ = lean_ctor_get(v_____s_3599_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v_____s_3599_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3603_ = v_____s_3599_;
v_isShared_3604_ = v_isSharedCheck_3667_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_snd_3600_);
lean_inc(v_fst_3601_);
lean_dec(v_____s_3599_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3667_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v_fst_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3665_; 
v_fst_3605_ = lean_ctor_get(v_snd_3600_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v_snd_3600_);
if (v_isSharedCheck_3665_ == 0)
{
lean_object* v_unused_3666_; 
v_unused_3666_ = lean_ctor_get(v_snd_3600_, 1);
lean_dec(v_unused_3666_);
v___x_3607_ = v_snd_3600_;
v_isShared_3608_ = v_isSharedCheck_3665_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_fst_3605_);
lean_dec(v_snd_3600_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3665_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___f_3609_; 
lean_inc(v_toBind_3581_);
lean_inc_ref(v_remaining_3580_);
lean_inc(v_onRemaining_3579_);
lean_inc(v_toPure_3578_);
lean_inc_ref(v_discrs_x27_3577_);
lean_inc_ref(v_fst_3576_);
lean_inc_ref(v_params_x27_3575_);
lean_inc_ref(v_matcherLevels_3574_);
lean_inc(v_matcherName_3573_);
lean_inc_ref(v_overlaps_3572_);
lean_inc_ref(v_snd_3571_);
lean_inc(v_uElimPos_x3f_3570_);
lean_inc_ref(v_altInfos_3569_);
lean_inc(v_numDiscrs_3568_);
lean_inc(v_numParams_3567_);
lean_inc(v_fst_3601_);
v___f_3609_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed), 17, 16);
lean_closure_set(v___f_3609_, 0, v_fst_3601_);
lean_closure_set(v___f_3609_, 1, v_numParams_3567_);
lean_closure_set(v___f_3609_, 2, v_numDiscrs_3568_);
lean_closure_set(v___f_3609_, 3, v_altInfos_3569_);
lean_closure_set(v___f_3609_, 4, v_uElimPos_x3f_3570_);
lean_closure_set(v___f_3609_, 5, v_snd_3571_);
lean_closure_set(v___f_3609_, 6, v_overlaps_3572_);
lean_closure_set(v___f_3609_, 7, v_matcherName_3573_);
lean_closure_set(v___f_3609_, 8, v_matcherLevels_3574_);
lean_closure_set(v___f_3609_, 9, v_params_x27_3575_);
lean_closure_set(v___f_3609_, 10, v_fst_3576_);
lean_closure_set(v___f_3609_, 11, v_discrs_x27_3577_);
lean_closure_set(v___f_3609_, 12, v_toPure_3578_);
lean_closure_set(v___f_3609_, 13, v_onRemaining_3579_);
lean_closure_set(v___f_3609_, 14, v_remaining_3580_);
lean_closure_set(v___f_3609_, 15, v_toBind_3581_);
if (v_useSplitter_3593_ == 0)
{
lean_del_object(v___x_3603_);
lean_dec(v_fst_3601_);
lean_dec(v_numDiscrEqs_3598_);
lean_dec(v___f_3597_);
lean_dec_ref(v_inst_3596_);
lean_dec(v___f_3595_);
lean_dec_ref(v_remaining_3580_);
lean_dec(v_onRemaining_3579_);
lean_dec_ref(v_overlaps_3572_);
lean_dec_ref(v_snd_3571_);
lean_dec(v_uElimPos_x3f_3570_);
lean_dec_ref(v_altInfos_3569_);
lean_dec(v_numDiscrs_3568_);
lean_dec(v_numParams_3567_);
goto v___jp_3610_;
}
else
{
if (v_isCasesOn_3594_ == 0)
{
lean_object* v_liftWith_3637_; lean_object* v_restoreM_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v_aux1_3641_; lean_object* v_aux1_3642_; lean_object* v_aux1_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3647_; 
lean_dec_ref(v___f_3609_);
lean_del_object(v___x_3607_);
lean_dec_ref(v_matcherApp_3591_);
lean_dec(v___f_3590_);
lean_dec(v___f_3584_);
v_liftWith_3637_ = lean_ctor_get(v_inst_3582_, 0);
lean_inc(v_liftWith_3637_);
v_restoreM_3638_ = lean_ctor_get(v_inst_3582_, 1);
lean_inc(v_restoreM_3638_);
lean_inc_ref(v_matcherLevels_3574_);
v___x_3639_ = lean_array_to_list(v_matcherLevels_3574_);
lean_inc(v___x_3639_);
lean_inc(v_matcherName_3573_);
v___x_3640_ = l_Lean_mkConst(v_matcherName_3573_, v___x_3639_);
v_aux1_3641_ = l_Lean_mkAppN(v___x_3640_, v_params_x27_3575_);
lean_inc_ref(v_fst_3576_);
v_aux1_3642_ = l_Lean_Expr_app___override(v_aux1_3641_, v_fst_3576_);
v_aux1_3643_ = l_Lean_mkAppN(v_aux1_3642_, v_discrs_x27_3577_);
lean_inc_ref(v_aux1_3643_);
v___x_3644_ = l_Lean_indentExpr(v_aux1_3643_);
v___x_3645_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3);
if (v_isShared_3604_ == 0)
{
lean_ctor_set_tag(v___x_3603_, 7);
lean_ctor_set(v___x_3603_, 1, v___x_3644_);
lean_ctor_set(v___x_3603_, 0, v___x_3645_);
v___x_3647_ = v___x_3603_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v___x_3645_);
lean_ctor_set(v_reuseFailAlloc_3664_, 1, v___x_3644_);
v___x_3647_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___f_3650_; uint8_t v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___f_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___f_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3648_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5);
v___x_3649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3647_);
lean_ctor_set(v___x_3649_, 1, v___x_3648_);
v___f_3650_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3650_, 0, v___x_3649_);
v___x_3651_ = 0;
v___x_3652_ = lean_box(v___x_3585_);
v___x_3653_ = lean_box(v_useSplitter_3593_);
v___x_3654_ = lean_box(v___x_3651_);
lean_inc_ref(v_aux1_3643_);
lean_inc(v_restoreM_3638_);
lean_inc(v_liftWith_3637_);
lean_inc(v_inst_3586_);
lean_inc_n(v_toBind_3581_, 2);
v___f_3655_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed), 37, 36);
lean_closure_set(v___f_3655_, 0, v_alts_3583_);
lean_closure_set(v___f_3655_, 1, v_toPure_3578_);
lean_closure_set(v___f_3655_, 2, v_toBind_3581_);
lean_closure_set(v___f_3655_, 3, v___f_3595_);
lean_closure_set(v___f_3655_, 4, v___x_3592_);
lean_closure_set(v___f_3655_, 5, v_inst_3589_);
lean_closure_set(v___f_3655_, 6, v_inst_3586_);
lean_closure_set(v___f_3655_, 7, v_inst_3596_);
lean_closure_set(v___f_3655_, 8, v___x_3652_);
lean_closure_set(v___f_3655_, 9, v___x_3653_);
lean_closure_set(v___f_3655_, 10, v_onAlt_3588_);
lean_closure_set(v___f_3655_, 11, v___f_3597_);
lean_closure_set(v___f_3655_, 12, v_fst_3605_);
lean_closure_set(v___f_3655_, 13, v_inst_3582_);
lean_closure_set(v___f_3655_, 14, v_numDiscrEqs_3598_);
lean_closure_set(v___f_3655_, 15, v___x_3639_);
lean_closure_set(v___f_3655_, 16, v_params_x27_3575_);
lean_closure_set(v___f_3655_, 17, v_fst_3576_);
lean_closure_set(v___f_3655_, 18, v_discrs_x27_3577_);
lean_closure_set(v___f_3655_, 19, v_fst_3601_);
lean_closure_set(v___f_3655_, 20, v_numParams_3567_);
lean_closure_set(v___f_3655_, 21, v_numDiscrs_3568_);
lean_closure_set(v___f_3655_, 22, v_altInfos_3569_);
lean_closure_set(v___f_3655_, 23, v_uElimPos_x3f_3570_);
lean_closure_set(v___f_3655_, 24, v_snd_3571_);
lean_closure_set(v___f_3655_, 25, v_overlaps_3572_);
lean_closure_set(v___f_3655_, 26, v_matcherLevels_3574_);
lean_closure_set(v___f_3655_, 27, v_onRemaining_3579_);
lean_closure_set(v___f_3655_, 28, v_remaining_3580_);
lean_closure_set(v___f_3655_, 29, v_remaining_x27_3587_);
lean_closure_set(v___f_3655_, 30, v___x_3648_);
lean_closure_set(v___f_3655_, 31, v___x_3654_);
lean_closure_set(v___f_3655_, 32, v_liftWith_3637_);
lean_closure_set(v___f_3655_, 33, v_restoreM_3638_);
lean_closure_set(v___f_3655_, 34, v_matcherName_3573_);
lean_closure_set(v___f_3655_, 35, v_aux1_3643_);
v___x_3656_ = lean_box(v___x_3651_);
v___x_3657_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_3657_, 0, v_aux1_3643_);
lean_closure_set(v___x_3657_, 1, v___x_3656_);
v___x_3658_ = lean_apply_2(v_inst_3586_, lean_box(0), v___x_3657_);
v___f_3659_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3659_, 0, v___x_3658_);
lean_closure_set(v___f_3659_, 1, v___f_3650_);
v___x_3660_ = lean_apply_2(v_liftWith_3637_, lean_box(0), v___f_3659_);
v___x_3661_ = lean_apply_1(v_restoreM_3638_, lean_box(0));
v___x_3662_ = lean_apply_4(v_toBind_3581_, lean_box(0), lean_box(0), v___x_3660_, v___x_3661_);
v___x_3663_ = lean_apply_4(v_toBind_3581_, lean_box(0), lean_box(0), v___x_3662_, v___f_3655_);
return v___x_3663_;
}
}
else
{
lean_del_object(v___x_3603_);
lean_dec(v_fst_3601_);
lean_dec(v_numDiscrEqs_3598_);
lean_dec(v___f_3597_);
lean_dec_ref(v_inst_3596_);
lean_dec(v___f_3595_);
lean_dec_ref(v_remaining_3580_);
lean_dec(v_onRemaining_3579_);
lean_dec_ref(v_overlaps_3572_);
lean_dec_ref(v_snd_3571_);
lean_dec(v_uElimPos_x3f_3570_);
lean_dec_ref(v_altInfos_3569_);
lean_dec(v_numDiscrs_3568_);
lean_dec(v_numParams_3567_);
goto v___jp_3610_;
}
}
v___jp_3610_:
{
lean_object* v_liftWith_3611_; lean_object* v_restoreM_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v_aux_3615_; lean_object* v_aux_3616_; lean_object* v_aux_3617_; lean_object* v___x_3618_; uint8_t v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___f_3622_; lean_object* v___x_3623_; lean_object* v___x_3625_; 
v_liftWith_3611_ = lean_ctor_get(v_inst_3582_, 0);
lean_inc(v_liftWith_3611_);
v_restoreM_3612_ = lean_ctor_get(v_inst_3582_, 1);
lean_inc(v_restoreM_3612_);
v___x_3613_ = lean_array_to_list(v_matcherLevels_3574_);
v___x_3614_ = l_Lean_mkConst(v_matcherName_3573_, v___x_3613_);
v_aux_3615_ = l_Lean_mkAppN(v___x_3614_, v_params_x27_3575_);
lean_dec_ref(v_params_x27_3575_);
v_aux_3616_ = l_Lean_Expr_app___override(v_aux_3615_, v_fst_3576_);
v_aux_3617_ = l_Lean_mkAppN(v_aux_3616_, v_discrs_x27_3577_);
lean_dec_ref(v_discrs_x27_3577_);
lean_inc_ref_n(v_aux_3617_, 2);
v___x_3618_ = l_Lean_indentExpr(v_aux_3617_);
v___x_3619_ = 1;
v___x_3620_ = lean_box(v___x_3585_);
v___x_3621_ = lean_box(v___x_3619_);
lean_inc(v_inst_3586_);
lean_inc(v_toBind_3581_);
v___f_3622_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 18, 17);
lean_closure_set(v___f_3622_, 0, v_alts_3583_);
lean_closure_set(v___f_3622_, 1, v_toPure_3578_);
lean_closure_set(v___f_3622_, 2, v_toBind_3581_);
lean_closure_set(v___f_3622_, 3, v___f_3584_);
lean_closure_set(v___f_3622_, 4, v___x_3620_);
lean_closure_set(v___f_3622_, 5, v___x_3621_);
lean_closure_set(v___f_3622_, 6, v_inst_3586_);
lean_closure_set(v___f_3622_, 7, v_remaining_x27_3587_);
lean_closure_set(v___f_3622_, 8, v_onAlt_3588_);
lean_closure_set(v___f_3622_, 9, v_inst_3582_);
lean_closure_set(v___f_3622_, 10, v_inst_3589_);
lean_closure_set(v___f_3622_, 11, v___f_3590_);
lean_closure_set(v___f_3622_, 12, v_fst_3605_);
lean_closure_set(v___f_3622_, 13, v_matcherApp_3591_);
lean_closure_set(v___f_3622_, 14, v___x_3592_);
lean_closure_set(v___f_3622_, 15, v___f_3609_);
lean_closure_set(v___f_3622_, 16, v_aux_3617_);
v___x_3623_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1);
if (v_isShared_3608_ == 0)
{
lean_ctor_set_tag(v___x_3607_, 7);
lean_ctor_set(v___x_3607_, 1, v___x_3618_);
lean_ctor_set(v___x_3607_, 0, v___x_3623_);
v___x_3625_ = v___x_3607_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v___x_3623_);
lean_ctor_set(v_reuseFailAlloc_3636_, 1, v___x_3618_);
v___x_3625_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
lean_object* v___f_3626_; uint8_t v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___f_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___f_3626_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3626_, 0, v___x_3625_);
v___x_3627_ = 0;
v___x_3628_ = lean_box(v___x_3627_);
v___x_3629_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_3629_, 0, v_aux_3617_);
lean_closure_set(v___x_3629_, 1, v___x_3628_);
v___x_3630_ = lean_apply_2(v_inst_3586_, lean_box(0), v___x_3629_);
v___f_3631_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3631_, 0, v___x_3630_);
lean_closure_set(v___f_3631_, 1, v___f_3626_);
v___x_3632_ = lean_apply_2(v_liftWith_3611_, lean_box(0), v___f_3631_);
v___x_3633_ = lean_apply_1(v_restoreM_3612_, lean_box(0));
lean_inc(v_toBind_3581_);
v___x_3634_ = lean_apply_4(v_toBind_3581_, lean_box(0), lean_box(0), v___x_3632_, v___x_3633_);
v___x_3635_ = lean_apply_4(v_toBind_3581_, lean_box(0), lean_box(0), v___x_3634_, v___f_3622_);
return v___x_3635_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___boxed(lean_object** _args){
lean_object* v_numParams_3668_ = _args[0];
lean_object* v_numDiscrs_3669_ = _args[1];
lean_object* v_altInfos_3670_ = _args[2];
lean_object* v_uElimPos_x3f_3671_ = _args[3];
lean_object* v_snd_3672_ = _args[4];
lean_object* v_overlaps_3673_ = _args[5];
lean_object* v_matcherName_3674_ = _args[6];
lean_object* v_matcherLevels_3675_ = _args[7];
lean_object* v_params_x27_3676_ = _args[8];
lean_object* v_fst_3677_ = _args[9];
lean_object* v_discrs_x27_3678_ = _args[10];
lean_object* v_toPure_3679_ = _args[11];
lean_object* v_onRemaining_3680_ = _args[12];
lean_object* v_remaining_3681_ = _args[13];
lean_object* v_toBind_3682_ = _args[14];
lean_object* v_inst_3683_ = _args[15];
lean_object* v_alts_3684_ = _args[16];
lean_object* v___f_3685_ = _args[17];
lean_object* v___x_3686_ = _args[18];
lean_object* v_inst_3687_ = _args[19];
lean_object* v_remaining_x27_3688_ = _args[20];
lean_object* v_onAlt_3689_ = _args[21];
lean_object* v_inst_3690_ = _args[22];
lean_object* v___f_3691_ = _args[23];
lean_object* v_matcherApp_3692_ = _args[24];
lean_object* v___x_3693_ = _args[25];
lean_object* v_useSplitter_3694_ = _args[26];
lean_object* v_isCasesOn_3695_ = _args[27];
lean_object* v___f_3696_ = _args[28];
lean_object* v_inst_3697_ = _args[29];
lean_object* v___f_3698_ = _args[30];
lean_object* v_numDiscrEqs_3699_ = _args[31];
lean_object* v_____s_3700_ = _args[32];
_start:
{
uint8_t v___x_16618__boxed_3701_; uint8_t v_useSplitter_boxed_3702_; uint8_t v_isCasesOn_boxed_3703_; lean_object* v_res_3704_; 
v___x_16618__boxed_3701_ = lean_unbox(v___x_3686_);
v_useSplitter_boxed_3702_ = lean_unbox(v_useSplitter_3694_);
v_isCasesOn_boxed_3703_ = lean_unbox(v_isCasesOn_3695_);
v_res_3704_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__55(v_numParams_3668_, v_numDiscrs_3669_, v_altInfos_3670_, v_uElimPos_x3f_3671_, v_snd_3672_, v_overlaps_3673_, v_matcherName_3674_, v_matcherLevels_3675_, v_params_x27_3676_, v_fst_3677_, v_discrs_x27_3678_, v_toPure_3679_, v_onRemaining_3680_, v_remaining_3681_, v_toBind_3682_, v_inst_3683_, v_alts_3684_, v___f_3685_, v___x_16618__boxed_3701_, v_inst_3687_, v_remaining_x27_3688_, v_onAlt_3689_, v_inst_3690_, v___f_3691_, v_matcherApp_3692_, v___x_3693_, v_useSplitter_boxed_3702_, v_isCasesOn_boxed_3703_, v___f_3696_, v_inst_3697_, v___f_3698_, v_numDiscrEqs_3699_, v_____s_3700_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54(lean_object* v_numParams_3705_, lean_object* v_numDiscrs_3706_, lean_object* v_altInfos_3707_, lean_object* v_uElimPos_x3f_3708_, lean_object* v_snd_3709_, lean_object* v_overlaps_3710_, lean_object* v_matcherName_3711_, lean_object* v_params_x27_3712_, lean_object* v_fst_3713_, lean_object* v_discrs_x27_3714_, lean_object* v_toPure_3715_, lean_object* v_onRemaining_3716_, lean_object* v_remaining_3717_, lean_object* v_toBind_3718_, lean_object* v_inst_3719_, lean_object* v_alts_3720_, lean_object* v___f_3721_, uint8_t v___x_3722_, lean_object* v_inst_3723_, lean_object* v_onAlt_3724_, lean_object* v_inst_3725_, lean_object* v___f_3726_, lean_object* v_matcherApp_3727_, uint8_t v_useSplitter_3728_, uint8_t v_isCasesOn_3729_, lean_object* v___f_3730_, lean_object* v_inst_3731_, lean_object* v___f_3732_, lean_object* v_numDiscrEqs_3733_, lean_object* v_fst_3734_, lean_object* v___f_3735_, lean_object* v_matcherLevels_3736_){
_start:
{
lean_object* v___x_3737_; lean_object* v_remaining_x27_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___f_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; size_t v_sz_3749_; size_t v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
v___x_3737_ = lean_unsigned_to_nat(0u);
v_remaining_x27_3738_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_3739_ = lean_box(v___x_3722_);
v___x_3740_ = lean_box(v_useSplitter_3728_);
v___x_3741_ = lean_box(v_isCasesOn_3729_);
lean_inc_ref(v_inst_3725_);
lean_inc(v_toBind_3718_);
lean_inc_ref(v_discrs_x27_3714_);
v___f_3742_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___boxed), 33, 32);
lean_closure_set(v___f_3742_, 0, v_numParams_3705_);
lean_closure_set(v___f_3742_, 1, v_numDiscrs_3706_);
lean_closure_set(v___f_3742_, 2, v_altInfos_3707_);
lean_closure_set(v___f_3742_, 3, v_uElimPos_x3f_3708_);
lean_closure_set(v___f_3742_, 4, v_snd_3709_);
lean_closure_set(v___f_3742_, 5, v_overlaps_3710_);
lean_closure_set(v___f_3742_, 6, v_matcherName_3711_);
lean_closure_set(v___f_3742_, 7, v_matcherLevels_3736_);
lean_closure_set(v___f_3742_, 8, v_params_x27_3712_);
lean_closure_set(v___f_3742_, 9, v_fst_3713_);
lean_closure_set(v___f_3742_, 10, v_discrs_x27_3714_);
lean_closure_set(v___f_3742_, 11, v_toPure_3715_);
lean_closure_set(v___f_3742_, 12, v_onRemaining_3716_);
lean_closure_set(v___f_3742_, 13, v_remaining_3717_);
lean_closure_set(v___f_3742_, 14, v_toBind_3718_);
lean_closure_set(v___f_3742_, 15, v_inst_3719_);
lean_closure_set(v___f_3742_, 16, v_alts_3720_);
lean_closure_set(v___f_3742_, 17, v___f_3721_);
lean_closure_set(v___f_3742_, 18, v___x_3739_);
lean_closure_set(v___f_3742_, 19, v_inst_3723_);
lean_closure_set(v___f_3742_, 20, v_remaining_x27_3738_);
lean_closure_set(v___f_3742_, 21, v_onAlt_3724_);
lean_closure_set(v___f_3742_, 22, v_inst_3725_);
lean_closure_set(v___f_3742_, 23, v___f_3726_);
lean_closure_set(v___f_3742_, 24, v_matcherApp_3727_);
lean_closure_set(v___f_3742_, 25, v___x_3737_);
lean_closure_set(v___f_3742_, 26, v___x_3740_);
lean_closure_set(v___f_3742_, 27, v___x_3741_);
lean_closure_set(v___f_3742_, 28, v___f_3730_);
lean_closure_set(v___f_3742_, 29, v_inst_3731_);
lean_closure_set(v___f_3742_, 30, v___f_3732_);
lean_closure_set(v___f_3742_, 31, v_numDiscrEqs_3733_);
v___x_3743_ = l_Array_reverse___redArg(v_fst_3734_);
v___x_3744_ = lean_array_get_size(v___x_3743_);
v___x_3745_ = l_Array_toSubarray___redArg(v___x_3743_, v___x_3737_, v___x_3744_);
v___x_3746_ = l_Array_reverse___redArg(v_discrs_x27_3714_);
v___x_3747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3737_);
lean_ctor_set(v___x_3747_, 1, v___x_3745_);
v___x_3748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3748_, 0, v_remaining_x27_3738_);
lean_ctor_set(v___x_3748_, 1, v___x_3747_);
v_sz_3749_ = lean_array_size(v___x_3746_);
v___x_3750_ = ((size_t)0ULL);
v___x_3751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3725_, v___x_3746_, v___f_3735_, v_sz_3749_, v___x_3750_, v___x_3748_);
v___x_3752_ = lean_apply_4(v_toBind_3718_, lean_box(0), lean_box(0), v___x_3751_, v___f_3742_);
return v___x_3752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed(lean_object** _args){
lean_object* v_numParams_3753_ = _args[0];
lean_object* v_numDiscrs_3754_ = _args[1];
lean_object* v_altInfos_3755_ = _args[2];
lean_object* v_uElimPos_x3f_3756_ = _args[3];
lean_object* v_snd_3757_ = _args[4];
lean_object* v_overlaps_3758_ = _args[5];
lean_object* v_matcherName_3759_ = _args[6];
lean_object* v_params_x27_3760_ = _args[7];
lean_object* v_fst_3761_ = _args[8];
lean_object* v_discrs_x27_3762_ = _args[9];
lean_object* v_toPure_3763_ = _args[10];
lean_object* v_onRemaining_3764_ = _args[11];
lean_object* v_remaining_3765_ = _args[12];
lean_object* v_toBind_3766_ = _args[13];
lean_object* v_inst_3767_ = _args[14];
lean_object* v_alts_3768_ = _args[15];
lean_object* v___f_3769_ = _args[16];
lean_object* v___x_3770_ = _args[17];
lean_object* v_inst_3771_ = _args[18];
lean_object* v_onAlt_3772_ = _args[19];
lean_object* v_inst_3773_ = _args[20];
lean_object* v___f_3774_ = _args[21];
lean_object* v_matcherApp_3775_ = _args[22];
lean_object* v_useSplitter_3776_ = _args[23];
lean_object* v_isCasesOn_3777_ = _args[24];
lean_object* v___f_3778_ = _args[25];
lean_object* v_inst_3779_ = _args[26];
lean_object* v___f_3780_ = _args[27];
lean_object* v_numDiscrEqs_3781_ = _args[28];
lean_object* v_fst_3782_ = _args[29];
lean_object* v___f_3783_ = _args[30];
lean_object* v_matcherLevels_3784_ = _args[31];
_start:
{
uint8_t v___x_16777__boxed_3785_; uint8_t v_useSplitter_boxed_3786_; uint8_t v_isCasesOn_boxed_3787_; lean_object* v_res_3788_; 
v___x_16777__boxed_3785_ = lean_unbox(v___x_3770_);
v_useSplitter_boxed_3786_ = lean_unbox(v_useSplitter_3776_);
v_isCasesOn_boxed_3787_ = lean_unbox(v_isCasesOn_3777_);
v_res_3788_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__54(v_numParams_3753_, v_numDiscrs_3754_, v_altInfos_3755_, v_uElimPos_x3f_3756_, v_snd_3757_, v_overlaps_3758_, v_matcherName_3759_, v_params_x27_3760_, v_fst_3761_, v_discrs_x27_3762_, v_toPure_3763_, v_onRemaining_3764_, v_remaining_3765_, v_toBind_3766_, v_inst_3767_, v_alts_3768_, v___f_3769_, v___x_16777__boxed_3785_, v_inst_3771_, v_onAlt_3772_, v_inst_3773_, v___f_3774_, v_matcherApp_3775_, v_useSplitter_boxed_3786_, v_isCasesOn_boxed_3787_, v___f_3778_, v_inst_3779_, v___f_3780_, v_numDiscrEqs_3781_, v_fst_3782_, v___f_3783_, v_matcherLevels_3784_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56(lean_object* v___f_3789_, lean_object* v_matcherLevels_3790_){
_start:
{
lean_object* v___x_3791_; 
v___x_3791_ = lean_apply_1(v___f_3789_, v_matcherLevels_3790_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58(lean_object* v_toMatcherInfo_3792_, lean_object* v_matcherName_3793_, lean_object* v_params_x27_3794_, lean_object* v_discrs_x27_3795_, lean_object* v_toPure_3796_, lean_object* v_onRemaining_3797_, lean_object* v_remaining_3798_, lean_object* v_toBind_3799_, lean_object* v_inst_3800_, lean_object* v_alts_3801_, lean_object* v___f_3802_, uint8_t v___x_3803_, lean_object* v_inst_3804_, lean_object* v_onAlt_3805_, lean_object* v_inst_3806_, lean_object* v___f_3807_, lean_object* v_matcherApp_3808_, uint8_t v_useSplitter_3809_, uint8_t v_isCasesOn_3810_, lean_object* v___f_3811_, lean_object* v_inst_3812_, lean_object* v___f_3813_, lean_object* v_numDiscrEqs_3814_, lean_object* v___f_3815_, lean_object* v_matcherLevels_3816_, lean_object* v_____x_3817_){
_start:
{
lean_object* v_snd_3818_; lean_object* v_snd_3819_; lean_object* v_fst_3820_; lean_object* v_fst_3821_; lean_object* v_fst_3822_; lean_object* v_snd_3823_; lean_object* v_numParams_3824_; lean_object* v_numDiscrs_3825_; lean_object* v_altInfos_3826_; lean_object* v_uElimPos_x3f_3827_; lean_object* v_overlaps_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___f_3832_; 
v_snd_3818_ = lean_ctor_get(v_____x_3817_, 1);
lean_inc(v_snd_3818_);
v_snd_3819_ = lean_ctor_get(v_snd_3818_, 1);
lean_inc(v_snd_3819_);
v_fst_3820_ = lean_ctor_get(v_____x_3817_, 0);
lean_inc(v_fst_3820_);
lean_dec_ref(v_____x_3817_);
v_fst_3821_ = lean_ctor_get(v_snd_3818_, 0);
lean_inc(v_fst_3821_);
lean_dec(v_snd_3818_);
v_fst_3822_ = lean_ctor_get(v_snd_3819_, 0);
lean_inc(v_fst_3822_);
v_snd_3823_ = lean_ctor_get(v_snd_3819_, 1);
lean_inc(v_snd_3823_);
lean_dec(v_snd_3819_);
v_numParams_3824_ = lean_ctor_get(v_toMatcherInfo_3792_, 0);
lean_inc(v_numParams_3824_);
v_numDiscrs_3825_ = lean_ctor_get(v_toMatcherInfo_3792_, 1);
lean_inc(v_numDiscrs_3825_);
v_altInfos_3826_ = lean_ctor_get(v_toMatcherInfo_3792_, 2);
lean_inc_ref(v_altInfos_3826_);
v_uElimPos_x3f_3827_ = lean_ctor_get(v_toMatcherInfo_3792_, 3);
lean_inc_n(v_uElimPos_x3f_3827_, 2);
v_overlaps_3828_ = lean_ctor_get(v_toMatcherInfo_3792_, 5);
lean_inc_ref(v_overlaps_3828_);
lean_dec_ref(v_toMatcherInfo_3792_);
v___x_3829_ = lean_box(v___x_3803_);
v___x_3830_ = lean_box(v_useSplitter_3809_);
v___x_3831_ = lean_box(v_isCasesOn_3810_);
lean_inc(v_toBind_3799_);
lean_inc(v_toPure_3796_);
v___f_3832_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed), 32, 31);
lean_closure_set(v___f_3832_, 0, v_numParams_3824_);
lean_closure_set(v___f_3832_, 1, v_numDiscrs_3825_);
lean_closure_set(v___f_3832_, 2, v_altInfos_3826_);
lean_closure_set(v___f_3832_, 3, v_uElimPos_x3f_3827_);
lean_closure_set(v___f_3832_, 4, v_snd_3823_);
lean_closure_set(v___f_3832_, 5, v_overlaps_3828_);
lean_closure_set(v___f_3832_, 6, v_matcherName_3793_);
lean_closure_set(v___f_3832_, 7, v_params_x27_3794_);
lean_closure_set(v___f_3832_, 8, v_fst_3820_);
lean_closure_set(v___f_3832_, 9, v_discrs_x27_3795_);
lean_closure_set(v___f_3832_, 10, v_toPure_3796_);
lean_closure_set(v___f_3832_, 11, v_onRemaining_3797_);
lean_closure_set(v___f_3832_, 12, v_remaining_3798_);
lean_closure_set(v___f_3832_, 13, v_toBind_3799_);
lean_closure_set(v___f_3832_, 14, v_inst_3800_);
lean_closure_set(v___f_3832_, 15, v_alts_3801_);
lean_closure_set(v___f_3832_, 16, v___f_3802_);
lean_closure_set(v___f_3832_, 17, v___x_3829_);
lean_closure_set(v___f_3832_, 18, v_inst_3804_);
lean_closure_set(v___f_3832_, 19, v_onAlt_3805_);
lean_closure_set(v___f_3832_, 20, v_inst_3806_);
lean_closure_set(v___f_3832_, 21, v___f_3807_);
lean_closure_set(v___f_3832_, 22, v_matcherApp_3808_);
lean_closure_set(v___f_3832_, 23, v___x_3830_);
lean_closure_set(v___f_3832_, 24, v___x_3831_);
lean_closure_set(v___f_3832_, 25, v___f_3811_);
lean_closure_set(v___f_3832_, 26, v_inst_3812_);
lean_closure_set(v___f_3832_, 27, v___f_3813_);
lean_closure_set(v___f_3832_, 28, v_numDiscrEqs_3814_);
lean_closure_set(v___f_3832_, 29, v_fst_3822_);
lean_closure_set(v___f_3832_, 30, v___f_3815_);
if (lean_obj_tag(v_uElimPos_x3f_3827_) == 0)
{
lean_object* v___f_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; 
lean_dec(v_fst_3821_);
v___f_3833_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56), 2, 1);
lean_closure_set(v___f_3833_, 0, v___f_3832_);
v___x_3834_ = lean_apply_2(v_toPure_3796_, lean_box(0), v_matcherLevels_3816_);
v___x_3835_ = lean_apply_4(v_toBind_3799_, lean_box(0), lean_box(0), v___x_3834_, v___f_3833_);
return v___x_3835_;
}
else
{
lean_object* v_val_3836_; lean_object* v___f_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; 
v_val_3836_ = lean_ctor_get(v_uElimPos_x3f_3827_, 0);
lean_inc(v_val_3836_);
lean_dec_ref(v_uElimPos_x3f_3827_);
v___f_3837_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56), 2, 1);
lean_closure_set(v___f_3837_, 0, v___f_3832_);
v___x_3838_ = lean_array_set(v_matcherLevels_3816_, v_val_3836_, v_fst_3821_);
lean_dec(v_val_3836_);
v___x_3839_ = lean_apply_2(v_toPure_3796_, lean_box(0), v___x_3838_);
v___x_3840_ = lean_apply_4(v_toBind_3799_, lean_box(0), lean_box(0), v___x_3839_, v___f_3837_);
return v___x_3840_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed(lean_object** _args){
lean_object* v_toMatcherInfo_3841_ = _args[0];
lean_object* v_matcherName_3842_ = _args[1];
lean_object* v_params_x27_3843_ = _args[2];
lean_object* v_discrs_x27_3844_ = _args[3];
lean_object* v_toPure_3845_ = _args[4];
lean_object* v_onRemaining_3846_ = _args[5];
lean_object* v_remaining_3847_ = _args[6];
lean_object* v_toBind_3848_ = _args[7];
lean_object* v_inst_3849_ = _args[8];
lean_object* v_alts_3850_ = _args[9];
lean_object* v___f_3851_ = _args[10];
lean_object* v___x_3852_ = _args[11];
lean_object* v_inst_3853_ = _args[12];
lean_object* v_onAlt_3854_ = _args[13];
lean_object* v_inst_3855_ = _args[14];
lean_object* v___f_3856_ = _args[15];
lean_object* v_matcherApp_3857_ = _args[16];
lean_object* v_useSplitter_3858_ = _args[17];
lean_object* v_isCasesOn_3859_ = _args[18];
lean_object* v___f_3860_ = _args[19];
lean_object* v_inst_3861_ = _args[20];
lean_object* v___f_3862_ = _args[21];
lean_object* v_numDiscrEqs_3863_ = _args[22];
lean_object* v___f_3864_ = _args[23];
lean_object* v_matcherLevels_3865_ = _args[24];
lean_object* v_____x_3866_ = _args[25];
_start:
{
uint8_t v___x_16846__boxed_3867_; uint8_t v_useSplitter_boxed_3868_; uint8_t v_isCasesOn_boxed_3869_; lean_object* v_res_3870_; 
v___x_16846__boxed_3867_ = lean_unbox(v___x_3852_);
v_useSplitter_boxed_3868_ = lean_unbox(v_useSplitter_3858_);
v_isCasesOn_boxed_3869_ = lean_unbox(v_isCasesOn_3859_);
v_res_3870_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__58(v_toMatcherInfo_3841_, v_matcherName_3842_, v_params_x27_3843_, v_discrs_x27_3844_, v_toPure_3845_, v_onRemaining_3846_, v_remaining_3847_, v_toBind_3848_, v_inst_3849_, v_alts_3850_, v___f_3851_, v___x_16846__boxed_3867_, v_inst_3853_, v_onAlt_3854_, v_inst_3855_, v___f_3856_, v_matcherApp_3857_, v_useSplitter_boxed_3868_, v_isCasesOn_boxed_3869_, v___f_3860_, v_inst_3861_, v___f_3862_, v_numDiscrEqs_3863_, v___f_3864_, v_matcherLevels_3865_, v_____x_3866_);
return v_res_3870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57(lean_object* v_toPure_3871_, lean_object* v_inst_3872_, lean_object* v_toBind_3873_, lean_object* v_toMatcherInfo_3874_, lean_object* v_inst_3875_, lean_object* v___f_3876_, lean_object* v_onMotive_3877_, lean_object* v_discrs_3878_, lean_object* v_inst_3879_, lean_object* v_matcherName_3880_, lean_object* v_params_x27_3881_, lean_object* v_onRemaining_3882_, lean_object* v_remaining_3883_, lean_object* v_inst_3884_, lean_object* v_alts_3885_, lean_object* v___f_3886_, lean_object* v_onAlt_3887_, lean_object* v___f_3888_, lean_object* v_matcherApp_3889_, uint8_t v_useSplitter_3890_, uint8_t v_isCasesOn_3891_, lean_object* v___f_3892_, lean_object* v___f_3893_, lean_object* v_numDiscrEqs_3894_, lean_object* v___f_3895_, lean_object* v_matcherLevels_3896_, lean_object* v_motive_3897_, lean_object* v_discrs_x27_3898_){
_start:
{
lean_object* v___f_3899_; uint8_t v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___f_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; 
lean_inc_ref(v_inst_3879_);
lean_inc_ref_n(v_inst_3875_, 2);
lean_inc_ref(v_discrs_x27_3898_);
lean_inc_ref(v_toMatcherInfo_3874_);
lean_inc_n(v_toBind_3873_, 2);
lean_inc(v_inst_3872_);
lean_inc(v_toPure_3871_);
v___f_3899_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__19___boxed), 12, 10);
lean_closure_set(v___f_3899_, 0, v_toPure_3871_);
lean_closure_set(v___f_3899_, 1, v_inst_3872_);
lean_closure_set(v___f_3899_, 2, v_toBind_3873_);
lean_closure_set(v___f_3899_, 3, v_toMatcherInfo_3874_);
lean_closure_set(v___f_3899_, 4, v_discrs_x27_3898_);
lean_closure_set(v___f_3899_, 5, v_inst_3875_);
lean_closure_set(v___f_3899_, 6, v___f_3876_);
lean_closure_set(v___f_3899_, 7, v_onMotive_3877_);
lean_closure_set(v___f_3899_, 8, v_discrs_3878_);
lean_closure_set(v___f_3899_, 9, v_inst_3879_);
v___x_3900_ = 0;
v___x_3901_ = lean_box(v___x_3900_);
v___x_3902_ = lean_box(v_useSplitter_3890_);
v___x_3903_ = lean_box(v_isCasesOn_3891_);
lean_inc_ref(v_inst_3884_);
v___f_3904_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed), 26, 25);
lean_closure_set(v___f_3904_, 0, v_toMatcherInfo_3874_);
lean_closure_set(v___f_3904_, 1, v_matcherName_3880_);
lean_closure_set(v___f_3904_, 2, v_params_x27_3881_);
lean_closure_set(v___f_3904_, 3, v_discrs_x27_3898_);
lean_closure_set(v___f_3904_, 4, v_toPure_3871_);
lean_closure_set(v___f_3904_, 5, v_onRemaining_3882_);
lean_closure_set(v___f_3904_, 6, v_remaining_3883_);
lean_closure_set(v___f_3904_, 7, v_toBind_3873_);
lean_closure_set(v___f_3904_, 8, v_inst_3884_);
lean_closure_set(v___f_3904_, 9, v_alts_3885_);
lean_closure_set(v___f_3904_, 10, v___f_3886_);
lean_closure_set(v___f_3904_, 11, v___x_3901_);
lean_closure_set(v___f_3904_, 12, v_inst_3872_);
lean_closure_set(v___f_3904_, 13, v_onAlt_3887_);
lean_closure_set(v___f_3904_, 14, v_inst_3875_);
lean_closure_set(v___f_3904_, 15, v___f_3888_);
lean_closure_set(v___f_3904_, 16, v_matcherApp_3889_);
lean_closure_set(v___f_3904_, 17, v___x_3902_);
lean_closure_set(v___f_3904_, 18, v___x_3903_);
lean_closure_set(v___f_3904_, 19, v___f_3892_);
lean_closure_set(v___f_3904_, 20, v_inst_3879_);
lean_closure_set(v___f_3904_, 21, v___f_3893_);
lean_closure_set(v___f_3904_, 22, v_numDiscrEqs_3894_);
lean_closure_set(v___f_3904_, 23, v___f_3895_);
lean_closure_set(v___f_3904_, 24, v_matcherLevels_3896_);
v___x_3905_ = l_Lean_Meta_lambdaTelescope___redArg(v_inst_3884_, v_inst_3875_, v_motive_3897_, v___f_3899_, v___x_3900_);
v___x_3906_ = lean_apply_4(v_toBind_3873_, lean_box(0), lean_box(0), v___x_3905_, v___f_3904_);
return v___x_3906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed(lean_object** _args){
lean_object* v_toPure_3907_ = _args[0];
lean_object* v_inst_3908_ = _args[1];
lean_object* v_toBind_3909_ = _args[2];
lean_object* v_toMatcherInfo_3910_ = _args[3];
lean_object* v_inst_3911_ = _args[4];
lean_object* v___f_3912_ = _args[5];
lean_object* v_onMotive_3913_ = _args[6];
lean_object* v_discrs_3914_ = _args[7];
lean_object* v_inst_3915_ = _args[8];
lean_object* v_matcherName_3916_ = _args[9];
lean_object* v_params_x27_3917_ = _args[10];
lean_object* v_onRemaining_3918_ = _args[11];
lean_object* v_remaining_3919_ = _args[12];
lean_object* v_inst_3920_ = _args[13];
lean_object* v_alts_3921_ = _args[14];
lean_object* v___f_3922_ = _args[15];
lean_object* v_onAlt_3923_ = _args[16];
lean_object* v___f_3924_ = _args[17];
lean_object* v_matcherApp_3925_ = _args[18];
lean_object* v_useSplitter_3926_ = _args[19];
lean_object* v_isCasesOn_3927_ = _args[20];
lean_object* v___f_3928_ = _args[21];
lean_object* v___f_3929_ = _args[22];
lean_object* v_numDiscrEqs_3930_ = _args[23];
lean_object* v___f_3931_ = _args[24];
lean_object* v_matcherLevels_3932_ = _args[25];
lean_object* v_motive_3933_ = _args[26];
lean_object* v_discrs_x27_3934_ = _args[27];
_start:
{
uint8_t v_useSplitter_boxed_3935_; uint8_t v_isCasesOn_boxed_3936_; lean_object* v_res_3937_; 
v_useSplitter_boxed_3935_ = lean_unbox(v_useSplitter_3926_);
v_isCasesOn_boxed_3936_ = lean_unbox(v_isCasesOn_3927_);
v_res_3937_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__57(v_toPure_3907_, v_inst_3908_, v_toBind_3909_, v_toMatcherInfo_3910_, v_inst_3911_, v___f_3912_, v_onMotive_3913_, v_discrs_3914_, v_inst_3915_, v_matcherName_3916_, v_params_x27_3917_, v_onRemaining_3918_, v_remaining_3919_, v_inst_3920_, v_alts_3921_, v___f_3922_, v_onAlt_3923_, v___f_3924_, v_matcherApp_3925_, v_useSplitter_boxed_3935_, v_isCasesOn_boxed_3936_, v___f_3928_, v___f_3929_, v_numDiscrEqs_3930_, v___f_3931_, v_matcherLevels_3932_, v_motive_3933_, v_discrs_x27_3934_);
return v_res_3937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59(lean_object* v_toPure_3938_, lean_object* v_inst_3939_, lean_object* v_toBind_3940_, lean_object* v_toMatcherInfo_3941_, lean_object* v_inst_3942_, lean_object* v___f_3943_, lean_object* v_onMotive_3944_, lean_object* v_discrs_3945_, lean_object* v_inst_3946_, lean_object* v_matcherName_3947_, lean_object* v_onRemaining_3948_, lean_object* v_remaining_3949_, lean_object* v_inst_3950_, lean_object* v_alts_3951_, lean_object* v___f_3952_, lean_object* v_onAlt_3953_, lean_object* v___f_3954_, lean_object* v_matcherApp_3955_, uint8_t v_useSplitter_3956_, uint8_t v_isCasesOn_3957_, lean_object* v___f_3958_, lean_object* v___f_3959_, lean_object* v_numDiscrEqs_3960_, lean_object* v___f_3961_, lean_object* v_matcherLevels_3962_, lean_object* v_motive_3963_, lean_object* v_onParams_3964_, lean_object* v_params_x27_3965_){
_start:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___f_3968_; size_t v_sz_3969_; size_t v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3966_ = lean_box(v_useSplitter_3956_);
v___x_3967_ = lean_box(v_isCasesOn_3957_);
lean_inc_ref(v_discrs_3945_);
lean_inc_ref(v_inst_3942_);
lean_inc(v_toBind_3940_);
v___f_3968_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed), 28, 27);
lean_closure_set(v___f_3968_, 0, v_toPure_3938_);
lean_closure_set(v___f_3968_, 1, v_inst_3939_);
lean_closure_set(v___f_3968_, 2, v_toBind_3940_);
lean_closure_set(v___f_3968_, 3, v_toMatcherInfo_3941_);
lean_closure_set(v___f_3968_, 4, v_inst_3942_);
lean_closure_set(v___f_3968_, 5, v___f_3943_);
lean_closure_set(v___f_3968_, 6, v_onMotive_3944_);
lean_closure_set(v___f_3968_, 7, v_discrs_3945_);
lean_closure_set(v___f_3968_, 8, v_inst_3946_);
lean_closure_set(v___f_3968_, 9, v_matcherName_3947_);
lean_closure_set(v___f_3968_, 10, v_params_x27_3965_);
lean_closure_set(v___f_3968_, 11, v_onRemaining_3948_);
lean_closure_set(v___f_3968_, 12, v_remaining_3949_);
lean_closure_set(v___f_3968_, 13, v_inst_3950_);
lean_closure_set(v___f_3968_, 14, v_alts_3951_);
lean_closure_set(v___f_3968_, 15, v___f_3952_);
lean_closure_set(v___f_3968_, 16, v_onAlt_3953_);
lean_closure_set(v___f_3968_, 17, v___f_3954_);
lean_closure_set(v___f_3968_, 18, v_matcherApp_3955_);
lean_closure_set(v___f_3968_, 19, v___x_3966_);
lean_closure_set(v___f_3968_, 20, v___x_3967_);
lean_closure_set(v___f_3968_, 21, v___f_3958_);
lean_closure_set(v___f_3968_, 22, v___f_3959_);
lean_closure_set(v___f_3968_, 23, v_numDiscrEqs_3960_);
lean_closure_set(v___f_3968_, 24, v___f_3961_);
lean_closure_set(v___f_3968_, 25, v_matcherLevels_3962_);
lean_closure_set(v___f_3968_, 26, v_motive_3963_);
v_sz_3969_ = lean_array_size(v_discrs_3945_);
v___x_3970_ = ((size_t)0ULL);
v___x_3971_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_3942_, v_onParams_3964_, v_sz_3969_, v___x_3970_, v_discrs_3945_);
v___x_3972_ = lean_apply_4(v_toBind_3940_, lean_box(0), lean_box(0), v___x_3971_, v___f_3968_);
return v___x_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed(lean_object** _args){
lean_object* v_toPure_3973_ = _args[0];
lean_object* v_inst_3974_ = _args[1];
lean_object* v_toBind_3975_ = _args[2];
lean_object* v_toMatcherInfo_3976_ = _args[3];
lean_object* v_inst_3977_ = _args[4];
lean_object* v___f_3978_ = _args[5];
lean_object* v_onMotive_3979_ = _args[6];
lean_object* v_discrs_3980_ = _args[7];
lean_object* v_inst_3981_ = _args[8];
lean_object* v_matcherName_3982_ = _args[9];
lean_object* v_onRemaining_3983_ = _args[10];
lean_object* v_remaining_3984_ = _args[11];
lean_object* v_inst_3985_ = _args[12];
lean_object* v_alts_3986_ = _args[13];
lean_object* v___f_3987_ = _args[14];
lean_object* v_onAlt_3988_ = _args[15];
lean_object* v___f_3989_ = _args[16];
lean_object* v_matcherApp_3990_ = _args[17];
lean_object* v_useSplitter_3991_ = _args[18];
lean_object* v_isCasesOn_3992_ = _args[19];
lean_object* v___f_3993_ = _args[20];
lean_object* v___f_3994_ = _args[21];
lean_object* v_numDiscrEqs_3995_ = _args[22];
lean_object* v___f_3996_ = _args[23];
lean_object* v_matcherLevels_3997_ = _args[24];
lean_object* v_motive_3998_ = _args[25];
lean_object* v_onParams_3999_ = _args[26];
lean_object* v_params_x27_4000_ = _args[27];
_start:
{
uint8_t v_useSplitter_boxed_4001_; uint8_t v_isCasesOn_boxed_4002_; lean_object* v_res_4003_; 
v_useSplitter_boxed_4001_ = lean_unbox(v_useSplitter_3991_);
v_isCasesOn_boxed_4002_ = lean_unbox(v_isCasesOn_3992_);
v_res_4003_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__59(v_toPure_3973_, v_inst_3974_, v_toBind_3975_, v_toMatcherInfo_3976_, v_inst_3977_, v___f_3978_, v_onMotive_3979_, v_discrs_3980_, v_inst_3981_, v_matcherName_3982_, v_onRemaining_3983_, v_remaining_3984_, v_inst_3985_, v_alts_3986_, v___f_3987_, v_onAlt_3988_, v___f_3989_, v_matcherApp_3990_, v_useSplitter_boxed_4001_, v_isCasesOn_boxed_4002_, v___f_3993_, v___f_3994_, v_numDiscrEqs_3995_, v___f_3996_, v_matcherLevels_3997_, v_motive_3998_, v_onParams_3999_, v_params_x27_4000_);
return v_res_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60(lean_object* v_toPure_4004_, lean_object* v_inst_4005_, lean_object* v_toBind_4006_, lean_object* v_toMatcherInfo_4007_, lean_object* v_inst_4008_, lean_object* v___f_4009_, lean_object* v_onMotive_4010_, lean_object* v_discrs_4011_, lean_object* v_inst_4012_, lean_object* v_matcherName_4013_, lean_object* v_onRemaining_4014_, lean_object* v_remaining_4015_, lean_object* v_inst_4016_, lean_object* v_alts_4017_, lean_object* v___f_4018_, lean_object* v_onAlt_4019_, lean_object* v___f_4020_, lean_object* v_matcherApp_4021_, uint8_t v_useSplitter_4022_, uint8_t v_isCasesOn_4023_, lean_object* v___f_4024_, lean_object* v___f_4025_, lean_object* v___f_4026_, lean_object* v_matcherLevels_4027_, lean_object* v_motive_4028_, lean_object* v_onParams_4029_, lean_object* v_params_4030_, lean_object* v_numDiscrEqs_4031_){
_start:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___f_4034_; size_t v_sz_4035_; size_t v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___x_4032_ = lean_box(v_useSplitter_4022_);
v___x_4033_ = lean_box(v_isCasesOn_4023_);
lean_inc(v_onParams_4029_);
lean_inc_ref(v_inst_4008_);
lean_inc(v_toBind_4006_);
v___f_4034_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed), 28, 27);
lean_closure_set(v___f_4034_, 0, v_toPure_4004_);
lean_closure_set(v___f_4034_, 1, v_inst_4005_);
lean_closure_set(v___f_4034_, 2, v_toBind_4006_);
lean_closure_set(v___f_4034_, 3, v_toMatcherInfo_4007_);
lean_closure_set(v___f_4034_, 4, v_inst_4008_);
lean_closure_set(v___f_4034_, 5, v___f_4009_);
lean_closure_set(v___f_4034_, 6, v_onMotive_4010_);
lean_closure_set(v___f_4034_, 7, v_discrs_4011_);
lean_closure_set(v___f_4034_, 8, v_inst_4012_);
lean_closure_set(v___f_4034_, 9, v_matcherName_4013_);
lean_closure_set(v___f_4034_, 10, v_onRemaining_4014_);
lean_closure_set(v___f_4034_, 11, v_remaining_4015_);
lean_closure_set(v___f_4034_, 12, v_inst_4016_);
lean_closure_set(v___f_4034_, 13, v_alts_4017_);
lean_closure_set(v___f_4034_, 14, v___f_4018_);
lean_closure_set(v___f_4034_, 15, v_onAlt_4019_);
lean_closure_set(v___f_4034_, 16, v___f_4020_);
lean_closure_set(v___f_4034_, 17, v_matcherApp_4021_);
lean_closure_set(v___f_4034_, 18, v___x_4032_);
lean_closure_set(v___f_4034_, 19, v___x_4033_);
lean_closure_set(v___f_4034_, 20, v___f_4024_);
lean_closure_set(v___f_4034_, 21, v___f_4025_);
lean_closure_set(v___f_4034_, 22, v_numDiscrEqs_4031_);
lean_closure_set(v___f_4034_, 23, v___f_4026_);
lean_closure_set(v___f_4034_, 24, v_matcherLevels_4027_);
lean_closure_set(v___f_4034_, 25, v_motive_4028_);
lean_closure_set(v___f_4034_, 26, v_onParams_4029_);
v_sz_4035_ = lean_array_size(v_params_4030_);
v___x_4036_ = ((size_t)0ULL);
v___x_4037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_4008_, v_onParams_4029_, v_sz_4035_, v___x_4036_, v_params_4030_);
v___x_4038_ = lean_apply_4(v_toBind_4006_, lean_box(0), lean_box(0), v___x_4037_, v___f_4034_);
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
lean_object* v___f_4060_ = _args[21];
lean_object* v___f_4061_ = _args[22];
lean_object* v_matcherLevels_4062_ = _args[23];
lean_object* v_motive_4063_ = _args[24];
lean_object* v_onParams_4064_ = _args[25];
lean_object* v_params_4065_ = _args[26];
lean_object* v_numDiscrEqs_4066_ = _args[27];
_start:
{
uint8_t v_useSplitter_boxed_4067_; uint8_t v_isCasesOn_boxed_4068_; lean_object* v_res_4069_; 
v_useSplitter_boxed_4067_ = lean_unbox(v_useSplitter_4057_);
v_isCasesOn_boxed_4068_ = lean_unbox(v_isCasesOn_4058_);
v_res_4069_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__60(v_toPure_4039_, v_inst_4040_, v_toBind_4041_, v_toMatcherInfo_4042_, v_inst_4043_, v___f_4044_, v_onMotive_4045_, v_discrs_4046_, v_inst_4047_, v_matcherName_4048_, v_onRemaining_4049_, v_remaining_4050_, v_inst_4051_, v_alts_4052_, v___f_4053_, v_onAlt_4054_, v___f_4055_, v_matcherApp_4056_, v_useSplitter_boxed_4067_, v_isCasesOn_boxed_4068_, v___f_4059_, v___f_4060_, v___f_4061_, v_matcherLevels_4062_, v_motive_4063_, v_onParams_4064_, v_params_4065_, v_numDiscrEqs_4066_);
return v_res_4069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__61(lean_object* v___f_4070_, lean_object* v_numDiscrEqs_4071_){
_start:
{
lean_object* v___x_4072_; 
v___x_4072_ = lean_apply_1(v___f_4070_, v_numDiscrEqs_4071_);
return v___x_4072_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1(void){
_start:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; 
v___x_4074_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__0));
v___x_4075_ = l_Lean_stringToMessageData(v___x_4074_);
return v___x_4075_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3(void){
_start:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4077_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__2));
v___x_4078_ = l_Lean_stringToMessageData(v___x_4077_);
return v___x_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63(lean_object* v_matcherName_4079_, lean_object* v_inst_4080_, lean_object* v_inst_4081_, lean_object* v_toBind_4082_, lean_object* v___f_4083_, lean_object* v_toPure_4084_, lean_object* v___f_4085_, lean_object* v_____do__lift_4086_){
_start:
{
if (lean_obj_tag(v_____do__lift_4086_) == 0)
{
lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; 
lean_dec(v___f_4085_);
lean_dec(v_toPure_4084_);
v___x_4087_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1);
v___x_4088_ = l_Lean_MessageData_ofName(v_matcherName_4079_);
v___x_4089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4087_);
lean_ctor_set(v___x_4089_, 1, v___x_4088_);
v___x_4090_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3);
v___x_4091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4091_, 0, v___x_4089_);
lean_ctor_set(v___x_4091_, 1, v___x_4090_);
v___x_4092_ = l_Lean_throwError___redArg(v_inst_4080_, v_inst_4081_, v___x_4091_);
v___x_4093_ = lean_apply_4(v_toBind_4082_, lean_box(0), lean_box(0), v___x_4092_, v___f_4083_);
return v___x_4093_;
}
else
{
lean_object* v_val_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; 
lean_dec(v___f_4083_);
lean_dec_ref(v_inst_4081_);
lean_dec_ref(v_inst_4080_);
lean_dec(v_matcherName_4079_);
v_val_4094_ = lean_ctor_get(v_____do__lift_4086_, 0);
v___x_4095_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_4094_);
v___x_4096_ = lean_apply_2(v_toPure_4084_, lean_box(0), v___x_4095_);
v___x_4097_ = lean_apply_4(v_toBind_4082_, lean_box(0), lean_box(0), v___x_4096_, v___f_4085_);
return v___x_4097_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed(lean_object* v_matcherName_4098_, lean_object* v_inst_4099_, lean_object* v_inst_4100_, lean_object* v_toBind_4101_, lean_object* v___f_4102_, lean_object* v_toPure_4103_, lean_object* v___f_4104_, lean_object* v_____do__lift_4105_){
_start:
{
lean_object* v_res_4106_; 
v_res_4106_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__63(v_matcherName_4098_, v_inst_4099_, v_inst_4100_, v_toBind_4101_, v___f_4102_, v_toPure_4103_, v___f_4104_, v_____do__lift_4105_);
lean_dec(v_____do__lift_4105_);
return v_res_4106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64(lean_object* v_matcherApp_4107_, lean_object* v_toPure_4108_, lean_object* v_inst_4109_, lean_object* v_toBind_4110_, lean_object* v_inst_4111_, lean_object* v___f_4112_, lean_object* v_onMotive_4113_, lean_object* v_inst_4114_, lean_object* v_onRemaining_4115_, lean_object* v_inst_4116_, lean_object* v___f_4117_, lean_object* v_onAlt_4118_, lean_object* v___f_4119_, uint8_t v_useSplitter_4120_, lean_object* v___f_4121_, lean_object* v___f_4122_, lean_object* v___f_4123_, lean_object* v_onParams_4124_, lean_object* v_inst_4125_, lean_object* v_____do__lift_4126_){
_start:
{
lean_object* v_toMatcherInfo_4127_; lean_object* v_matcherName_4128_; lean_object* v_matcherLevels_4129_; lean_object* v_params_4130_; lean_object* v_motive_4131_; lean_object* v_discrs_4132_; lean_object* v_alts_4133_; lean_object* v_remaining_4134_; uint8_t v_isCasesOn_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___f_4138_; 
v_toMatcherInfo_4127_ = lean_ctor_get(v_matcherApp_4107_, 0);
lean_inc_ref(v_toMatcherInfo_4127_);
v_matcherName_4128_ = lean_ctor_get(v_matcherApp_4107_, 1);
lean_inc_n(v_matcherName_4128_, 3);
v_matcherLevels_4129_ = lean_ctor_get(v_matcherApp_4107_, 2);
lean_inc_ref(v_matcherLevels_4129_);
v_params_4130_ = lean_ctor_get(v_matcherApp_4107_, 3);
lean_inc_ref(v_params_4130_);
v_motive_4131_ = lean_ctor_get(v_matcherApp_4107_, 4);
lean_inc_ref(v_motive_4131_);
v_discrs_4132_ = lean_ctor_get(v_matcherApp_4107_, 5);
lean_inc_ref(v_discrs_4132_);
v_alts_4133_ = lean_ctor_get(v_matcherApp_4107_, 6);
lean_inc_ref(v_alts_4133_);
v_remaining_4134_ = lean_ctor_get(v_matcherApp_4107_, 7);
lean_inc_ref(v_remaining_4134_);
v_isCasesOn_4135_ = l_Lean_isCasesOnRecursor(v_____do__lift_4126_, v_matcherName_4128_);
v___x_4136_ = lean_box(v_useSplitter_4120_);
v___x_4137_ = lean_box(v_isCasesOn_4135_);
lean_inc_ref(v_inst_4114_);
lean_inc_ref(v_inst_4111_);
lean_inc(v_toBind_4110_);
lean_inc(v_toPure_4108_);
v___f_4138_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed), 28, 27);
lean_closure_set(v___f_4138_, 0, v_toPure_4108_);
lean_closure_set(v___f_4138_, 1, v_inst_4109_);
lean_closure_set(v___f_4138_, 2, v_toBind_4110_);
lean_closure_set(v___f_4138_, 3, v_toMatcherInfo_4127_);
lean_closure_set(v___f_4138_, 4, v_inst_4111_);
lean_closure_set(v___f_4138_, 5, v___f_4112_);
lean_closure_set(v___f_4138_, 6, v_onMotive_4113_);
lean_closure_set(v___f_4138_, 7, v_discrs_4132_);
lean_closure_set(v___f_4138_, 8, v_inst_4114_);
lean_closure_set(v___f_4138_, 9, v_matcherName_4128_);
lean_closure_set(v___f_4138_, 10, v_onRemaining_4115_);
lean_closure_set(v___f_4138_, 11, v_remaining_4134_);
lean_closure_set(v___f_4138_, 12, v_inst_4116_);
lean_closure_set(v___f_4138_, 13, v_alts_4133_);
lean_closure_set(v___f_4138_, 14, v___f_4117_);
lean_closure_set(v___f_4138_, 15, v_onAlt_4118_);
lean_closure_set(v___f_4138_, 16, v___f_4119_);
lean_closure_set(v___f_4138_, 17, v_matcherApp_4107_);
lean_closure_set(v___f_4138_, 18, v___x_4136_);
lean_closure_set(v___f_4138_, 19, v___x_4137_);
lean_closure_set(v___f_4138_, 20, v___f_4121_);
lean_closure_set(v___f_4138_, 21, v___f_4122_);
lean_closure_set(v___f_4138_, 22, v___f_4123_);
lean_closure_set(v___f_4138_, 23, v_matcherLevels_4129_);
lean_closure_set(v___f_4138_, 24, v_motive_4131_);
lean_closure_set(v___f_4138_, 25, v_onParams_4124_);
lean_closure_set(v___f_4138_, 26, v_params_4130_);
if (v_isCasesOn_4135_ == 0)
{
lean_object* v___f_4139_; lean_object* v___f_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; 
v___f_4139_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61), 2, 1);
lean_closure_set(v___f_4139_, 0, v___f_4138_);
lean_inc_ref(v___f_4139_);
lean_inc(v_toBind_4110_);
lean_inc_ref(v_inst_4111_);
lean_inc(v_matcherName_4128_);
v___f_4140_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed), 8, 7);
lean_closure_set(v___f_4140_, 0, v_matcherName_4128_);
lean_closure_set(v___f_4140_, 1, v_inst_4111_);
lean_closure_set(v___f_4140_, 2, v_inst_4114_);
lean_closure_set(v___f_4140_, 3, v_toBind_4110_);
lean_closure_set(v___f_4140_, 4, v___f_4139_);
lean_closure_set(v___f_4140_, 5, v_toPure_4108_);
lean_closure_set(v___f_4140_, 6, v___f_4139_);
v___x_4141_ = l_Lean_Meta_getMatcherInfo_x3f___redArg(v_inst_4111_, v_inst_4125_, v_matcherName_4128_);
v___x_4142_ = lean_apply_4(v_toBind_4110_, lean_box(0), lean_box(0), v___x_4141_, v___f_4140_);
return v___x_4142_;
}
else
{
lean_object* v___f_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
lean_dec(v_matcherName_4128_);
lean_dec_ref(v_inst_4125_);
lean_dec_ref(v_inst_4114_);
lean_dec_ref(v_inst_4111_);
v___f_4143_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61), 2, 1);
lean_closure_set(v___f_4143_, 0, v___f_4138_);
v___x_4144_ = lean_unsigned_to_nat(0u);
v___x_4145_ = lean_apply_2(v_toPure_4108_, lean_box(0), v___x_4144_);
v___x_4146_ = lean_apply_4(v_toBind_4110_, lean_box(0), lean_box(0), v___x_4145_, v___f_4143_);
return v___x_4146_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed(lean_object** _args){
lean_object* v_matcherApp_4147_ = _args[0];
lean_object* v_toPure_4148_ = _args[1];
lean_object* v_inst_4149_ = _args[2];
lean_object* v_toBind_4150_ = _args[3];
lean_object* v_inst_4151_ = _args[4];
lean_object* v___f_4152_ = _args[5];
lean_object* v_onMotive_4153_ = _args[6];
lean_object* v_inst_4154_ = _args[7];
lean_object* v_onRemaining_4155_ = _args[8];
lean_object* v_inst_4156_ = _args[9];
lean_object* v___f_4157_ = _args[10];
lean_object* v_onAlt_4158_ = _args[11];
lean_object* v___f_4159_ = _args[12];
lean_object* v_useSplitter_4160_ = _args[13];
lean_object* v___f_4161_ = _args[14];
lean_object* v___f_4162_ = _args[15];
lean_object* v___f_4163_ = _args[16];
lean_object* v_onParams_4164_ = _args[17];
lean_object* v_inst_4165_ = _args[18];
lean_object* v_____do__lift_4166_ = _args[19];
_start:
{
uint8_t v_useSplitter_boxed_4167_; lean_object* v_res_4168_; 
v_useSplitter_boxed_4167_ = lean_unbox(v_useSplitter_4160_);
v_res_4168_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__64(v_matcherApp_4147_, v_toPure_4148_, v_inst_4149_, v_toBind_4150_, v_inst_4151_, v___f_4152_, v_onMotive_4153_, v_inst_4154_, v_onRemaining_4155_, v_inst_4156_, v___f_4157_, v_onAlt_4158_, v___f_4159_, v_useSplitter_boxed_4167_, v___f_4161_, v___f_4162_, v___f_4163_, v_onParams_4164_, v_inst_4165_, v_____do__lift_4166_);
return v_res_4168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg(lean_object* v_inst_4169_, lean_object* v_inst_4170_, lean_object* v_inst_4171_, lean_object* v_inst_4172_, lean_object* v_inst_4173_, lean_object* v_matcherApp_4174_, uint8_t v_useSplitter_4175_, uint8_t v_addEqualities_4176_, lean_object* v_onParams_4177_, lean_object* v_onMotive_4178_, lean_object* v_onAlt_4179_, lean_object* v_onRemaining_4180_){
_start:
{
lean_object* v_toApplicative_4181_; lean_object* v_toBind_4182_; lean_object* v_getEnv_4183_; lean_object* v_toPure_4184_; lean_object* v___f_4185_; lean_object* v___f_4186_; lean_object* v___f_4187_; lean_object* v___f_4188_; lean_object* v___f_4189_; lean_object* v___f_4190_; lean_object* v___x_4191_; lean_object* v___f_4192_; lean_object* v___x_4193_; lean_object* v___f_4194_; lean_object* v___x_4195_; 
v_toApplicative_4181_ = lean_ctor_get(v_inst_4171_, 0);
v_toBind_4182_ = lean_ctor_get(v_inst_4171_, 1);
lean_inc_n(v_toBind_4182_, 4);
v_getEnv_4183_ = lean_ctor_get(v_inst_4173_, 0);
lean_inc(v_getEnv_4183_);
v_toPure_4184_ = lean_ctor_get(v_toApplicative_4181_, 1);
lean_inc_n(v_toPure_4184_, 5);
lean_inc_ref(v_inst_4172_);
lean_inc_ref_n(v_inst_4171_, 2);
v___f_4185_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4185_, 0, v_inst_4171_);
lean_closure_set(v___f_4185_, 1, v_inst_4172_);
lean_inc_n(v_inst_4169_, 3);
v___f_4186_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4186_, 0, v_inst_4169_);
v___f_4187_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4187_, 0, v_inst_4171_);
lean_closure_set(v___f_4187_, 1, v___f_4186_);
v___f_4188_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__3), 2, 1);
lean_closure_set(v___f_4188_, 0, v_toPure_4184_);
v___f_4189_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__4), 2, 1);
lean_closure_set(v___f_4189_, 0, v_toPure_4184_);
v___f_4190_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7), 6, 3);
lean_closure_set(v___f_4190_, 0, v_toPure_4184_);
lean_closure_set(v___f_4190_, 1, v_inst_4169_);
lean_closure_set(v___f_4190_, 2, v_toBind_4182_);
v___x_4191_ = lean_box(v_addEqualities_4176_);
v___f_4192_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__12___boxed), 7, 4);
lean_closure_set(v___f_4192_, 0, v_toPure_4184_);
lean_closure_set(v___f_4192_, 1, v___x_4191_);
lean_closure_set(v___f_4192_, 2, v_inst_4169_);
lean_closure_set(v___f_4192_, 3, v_toBind_4182_);
v___x_4193_ = lean_box(v_useSplitter_4175_);
v___f_4194_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed), 20, 19);
lean_closure_set(v___f_4194_, 0, v_matcherApp_4174_);
lean_closure_set(v___f_4194_, 1, v_toPure_4184_);
lean_closure_set(v___f_4194_, 2, v_inst_4169_);
lean_closure_set(v___f_4194_, 3, v_toBind_4182_);
lean_closure_set(v___f_4194_, 4, v_inst_4171_);
lean_closure_set(v___f_4194_, 5, v___f_4192_);
lean_closure_set(v___f_4194_, 6, v_onMotive_4178_);
lean_closure_set(v___f_4194_, 7, v_inst_4172_);
lean_closure_set(v___f_4194_, 8, v_onRemaining_4180_);
lean_closure_set(v___f_4194_, 9, v_inst_4170_);
lean_closure_set(v___f_4194_, 10, v___f_4188_);
lean_closure_set(v___f_4194_, 11, v_onAlt_4179_);
lean_closure_set(v___f_4194_, 12, v___f_4187_);
lean_closure_set(v___f_4194_, 13, v___x_4193_);
lean_closure_set(v___f_4194_, 14, v___f_4189_);
lean_closure_set(v___f_4194_, 15, v___f_4185_);
lean_closure_set(v___f_4194_, 16, v___f_4190_);
lean_closure_set(v___f_4194_, 17, v_onParams_4177_);
lean_closure_set(v___f_4194_, 18, v_inst_4173_);
v___x_4195_ = lean_apply_4(v_toBind_4182_, lean_box(0), lean_box(0), v_getEnv_4183_, v___f_4194_);
return v___x_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___boxed(lean_object* v_inst_4196_, lean_object* v_inst_4197_, lean_object* v_inst_4198_, lean_object* v_inst_4199_, lean_object* v_inst_4200_, lean_object* v_matcherApp_4201_, lean_object* v_useSplitter_4202_, lean_object* v_addEqualities_4203_, lean_object* v_onParams_4204_, lean_object* v_onMotive_4205_, lean_object* v_onAlt_4206_, lean_object* v_onRemaining_4207_){
_start:
{
uint8_t v_useSplitter_boxed_4208_; uint8_t v_addEqualities_boxed_4209_; lean_object* v_res_4210_; 
v_useSplitter_boxed_4208_ = lean_unbox(v_useSplitter_4202_);
v_addEqualities_boxed_4209_ = lean_unbox(v_addEqualities_4203_);
v_res_4210_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_4196_, v_inst_4197_, v_inst_4198_, v_inst_4199_, v_inst_4200_, v_matcherApp_4201_, v_useSplitter_boxed_4208_, v_addEqualities_boxed_4209_, v_onParams_4204_, v_onMotive_4205_, v_onAlt_4206_, v_onRemaining_4207_);
return v_res_4210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform(lean_object* v_n_4211_, lean_object* v_inst_4212_, lean_object* v_inst_4213_, lean_object* v_inst_4214_, lean_object* v_inst_4215_, lean_object* v_inst_4216_, lean_object* v_inst_4217_, lean_object* v_inst_4218_, lean_object* v_inst_4219_, lean_object* v_matcherApp_4220_, uint8_t v_useSplitter_4221_, uint8_t v_addEqualities_4222_, lean_object* v_onParams_4223_, lean_object* v_onMotive_4224_, lean_object* v_onAlt_4225_, lean_object* v_onRemaining_4226_){
_start:
{
lean_object* v___x_4227_; 
v___x_4227_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_4212_, v_inst_4213_, v_inst_4214_, v_inst_4215_, v_inst_4216_, v_matcherApp_4220_, v_useSplitter_4221_, v_addEqualities_4222_, v_onParams_4223_, v_onMotive_4224_, v_onAlt_4225_, v_onRemaining_4226_);
return v___x_4227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___boxed(lean_object* v_n_4228_, lean_object* v_inst_4229_, lean_object* v_inst_4230_, lean_object* v_inst_4231_, lean_object* v_inst_4232_, lean_object* v_inst_4233_, lean_object* v_inst_4234_, lean_object* v_inst_4235_, lean_object* v_inst_4236_, lean_object* v_matcherApp_4237_, lean_object* v_useSplitter_4238_, lean_object* v_addEqualities_4239_, lean_object* v_onParams_4240_, lean_object* v_onMotive_4241_, lean_object* v_onAlt_4242_, lean_object* v_onRemaining_4243_){
_start:
{
uint8_t v_useSplitter_boxed_4244_; uint8_t v_addEqualities_boxed_4245_; lean_object* v_res_4246_; 
v_useSplitter_boxed_4244_ = lean_unbox(v_useSplitter_4238_);
v_addEqualities_boxed_4245_ = lean_unbox(v_addEqualities_4239_);
v_res_4246_ = l_Lean_Meta_MatcherApp_transform(v_n_4228_, v_inst_4229_, v_inst_4230_, v_inst_4231_, v_inst_4232_, v_inst_4233_, v_inst_4234_, v_inst_4235_, v_inst_4236_, v_matcherApp_4237_, v_useSplitter_boxed_4244_, v_addEqualities_boxed_4245_, v_onParams_4240_, v_onMotive_4241_, v_onAlt_4242_, v_onRemaining_4243_);
lean_dec(v_inst_4236_);
lean_dec(v_inst_4235_);
lean_dec_ref(v_inst_4234_);
return v_res_4246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0(lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_){
_start:
{
lean_object* v___x_4253_; 
v___x_4253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4253_, 0, v___y_4247_);
return v___x_4253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0___boxed(lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v_res_4260_; 
v_res_4260_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__0(v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4255_);
return v_res_4260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1(lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v___x_4267_; 
v___x_4267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4267_, 0, v___y_4261_);
return v___x_4267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1___boxed(lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
lean_object* v_res_4274_; 
v_res_4274_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__1(v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
lean_dec(v___y_4270_);
lean_dec_ref(v___y_4269_);
return v_res_4274_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(lean_object* v_opts_4275_, lean_object* v_opt_4276_){
_start:
{
lean_object* v_name_4277_; lean_object* v_defValue_4278_; lean_object* v_map_4279_; lean_object* v___x_4280_; 
v_name_4277_ = lean_ctor_get(v_opt_4276_, 0);
v_defValue_4278_ = lean_ctor_get(v_opt_4276_, 1);
v_map_4279_ = lean_ctor_get(v_opts_4275_, 0);
v___x_4280_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4279_, v_name_4277_);
if (lean_obj_tag(v___x_4280_) == 0)
{
uint8_t v___x_4281_; 
v___x_4281_ = lean_unbox(v_defValue_4278_);
return v___x_4281_;
}
else
{
lean_object* v_val_4282_; 
v_val_4282_ = lean_ctor_get(v___x_4280_, 0);
lean_inc(v_val_4282_);
lean_dec_ref(v___x_4280_);
if (lean_obj_tag(v_val_4282_) == 1)
{
uint8_t v_v_4283_; 
v_v_4283_ = lean_ctor_get_uint8(v_val_4282_, 0);
lean_dec_ref(v_val_4282_);
return v_v_4283_;
}
else
{
uint8_t v___x_4284_; 
lean_dec(v_val_4282_);
v___x_4284_ = lean_unbox(v_defValue_4278_);
return v___x_4284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11___boxed(lean_object* v_opts_4285_, lean_object* v_opt_4286_){
_start:
{
uint8_t v_res_4287_; lean_object* v_r_4288_; 
v_res_4287_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(v_opts_4285_, v_opt_4286_);
lean_dec_ref(v_opt_4286_);
lean_dec_ref(v_opts_4285_);
v_r_4288_ = lean_box(v_res_4287_);
return v_r_4288_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(uint8_t v___y_4297_, uint8_t v_suppressElabErrors_4298_, lean_object* v_x_4299_){
_start:
{
if (lean_obj_tag(v_x_4299_) == 1)
{
lean_object* v_pre_4300_; 
v_pre_4300_ = lean_ctor_get(v_x_4299_, 0);
switch(lean_obj_tag(v_pre_4300_))
{
case 1:
{
lean_object* v_pre_4301_; 
v_pre_4301_ = lean_ctor_get(v_pre_4300_, 0);
switch(lean_obj_tag(v_pre_4301_))
{
case 0:
{
lean_object* v_str_4302_; lean_object* v_str_4303_; lean_object* v___x_4304_; uint8_t v___x_4305_; 
v_str_4302_ = lean_ctor_get(v_x_4299_, 1);
v_str_4303_ = lean_ctor_get(v_pre_4300_, 1);
v___x_4304_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_4305_ = lean_string_dec_eq(v_str_4303_, v___x_4304_);
if (v___x_4305_ == 0)
{
lean_object* v___x_4306_; uint8_t v___x_4307_; 
v___x_4306_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_4307_ = lean_string_dec_eq(v_str_4303_, v___x_4306_);
if (v___x_4307_ == 0)
{
return v___y_4297_;
}
else
{
lean_object* v___x_4308_; uint8_t v___x_4309_; 
v___x_4308_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_4309_ = lean_string_dec_eq(v_str_4302_, v___x_4308_);
if (v___x_4309_ == 0)
{
return v___y_4297_;
}
else
{
return v_suppressElabErrors_4298_;
}
}
}
else
{
lean_object* v___x_4310_; uint8_t v___x_4311_; 
v___x_4310_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_4311_ = lean_string_dec_eq(v_str_4302_, v___x_4310_);
if (v___x_4311_ == 0)
{
return v___y_4297_;
}
else
{
return v_suppressElabErrors_4298_;
}
}
}
case 1:
{
lean_object* v_pre_4312_; 
v_pre_4312_ = lean_ctor_get(v_pre_4301_, 0);
if (lean_obj_tag(v_pre_4312_) == 0)
{
lean_object* v_str_4313_; lean_object* v_str_4314_; lean_object* v_str_4315_; lean_object* v___x_4316_; uint8_t v___x_4317_; 
v_str_4313_ = lean_ctor_get(v_x_4299_, 1);
v_str_4314_ = lean_ctor_get(v_pre_4300_, 1);
v_str_4315_ = lean_ctor_get(v_pre_4301_, 1);
v___x_4316_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_4317_ = lean_string_dec_eq(v_str_4315_, v___x_4316_);
if (v___x_4317_ == 0)
{
return v___y_4297_;
}
else
{
lean_object* v___x_4318_; uint8_t v___x_4319_; 
v___x_4318_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_4319_ = lean_string_dec_eq(v_str_4314_, v___x_4318_);
if (v___x_4319_ == 0)
{
return v___y_4297_;
}
else
{
lean_object* v___x_4320_; uint8_t v___x_4321_; 
v___x_4320_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_4321_ = lean_string_dec_eq(v_str_4313_, v___x_4320_);
if (v___x_4321_ == 0)
{
return v___y_4297_;
}
else
{
return v_suppressElabErrors_4298_;
}
}
}
}
else
{
return v___y_4297_;
}
}
default: 
{
return v___y_4297_;
}
}
}
case 0:
{
lean_object* v_str_4322_; lean_object* v___x_4323_; uint8_t v___x_4324_; 
v_str_4322_ = lean_ctor_get(v_x_4299_, 1);
v___x_4323_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_4324_ = lean_string_dec_eq(v_str_4322_, v___x_4323_);
if (v___x_4324_ == 0)
{
return v___y_4297_;
}
else
{
return v_suppressElabErrors_4298_;
}
}
default: 
{
return v___y_4297_;
}
}
}
else
{
return v___y_4297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___y_4325_, lean_object* v_suppressElabErrors_4326_, lean_object* v_x_4327_){
_start:
{
uint8_t v___y_32039__boxed_4328_; uint8_t v_suppressElabErrors_boxed_4329_; uint8_t v_res_4330_; lean_object* v_r_4331_; 
v___y_32039__boxed_4328_ = lean_unbox(v___y_4325_);
v_suppressElabErrors_boxed_4329_ = lean_unbox(v_suppressElabErrors_4326_);
v_res_4330_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(v___y_32039__boxed_4328_, v_suppressElabErrors_boxed_4329_, v_x_4327_);
lean_dec(v_x_4327_);
v_r_4331_ = lean_box(v_res_4330_);
return v_r_4331_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(lean_object* v_ref_4333_, lean_object* v_msgData_4334_, uint8_t v_severity_4335_, uint8_t v_isSilent_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_){
_start:
{
uint8_t v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; uint8_t v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4380_; uint8_t v___y_4381_; uint8_t v___y_4382_; lean_object* v___y_4383_; uint8_t v___y_4384_; lean_object* v___y_4385_; lean_object* v___y_4386_; lean_object* v___y_4387_; lean_object* v___y_4405_; uint8_t v___y_4406_; lean_object* v___y_4407_; uint8_t v___y_4408_; lean_object* v___y_4409_; uint8_t v___y_4410_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v___y_4416_; uint8_t v___y_4417_; uint8_t v___y_4418_; lean_object* v___y_4419_; lean_object* v___y_4420_; lean_object* v___y_4421_; uint8_t v___y_4422_; uint8_t v___x_4427_; uint8_t v___y_4429_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4432_; lean_object* v___y_4433_; uint8_t v___y_4434_; uint8_t v___y_4435_; uint8_t v___y_4437_; uint8_t v___x_4452_; 
v___x_4427_ = 2;
v___x_4452_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4335_, v___x_4427_);
if (v___x_4452_ == 0)
{
v___y_4437_ = v___x_4452_;
goto v___jp_4436_;
}
else
{
uint8_t v___x_4453_; 
lean_inc_ref(v_msgData_4334_);
v___x_4453_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4334_);
v___y_4437_ = v___x_4453_;
goto v___jp_4436_;
}
v___jp_4342_:
{
lean_object* v___x_4352_; lean_object* v_currNamespace_4353_; lean_object* v_openDecls_4354_; lean_object* v_env_4355_; lean_object* v_nextMacroScope_4356_; lean_object* v_ngen_4357_; lean_object* v_auxDeclNGen_4358_; lean_object* v_traceState_4359_; lean_object* v_cache_4360_; lean_object* v_messages_4361_; lean_object* v_infoState_4362_; lean_object* v_snapshotTasks_4363_; lean_object* v_newDecls_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4378_; 
v___x_4352_ = lean_st_ref_take(v___y_4351_);
v_currNamespace_4353_ = lean_ctor_get(v___y_4350_, 6);
v_openDecls_4354_ = lean_ctor_get(v___y_4350_, 7);
v_env_4355_ = lean_ctor_get(v___x_4352_, 0);
v_nextMacroScope_4356_ = lean_ctor_get(v___x_4352_, 1);
v_ngen_4357_ = lean_ctor_get(v___x_4352_, 2);
v_auxDeclNGen_4358_ = lean_ctor_get(v___x_4352_, 3);
v_traceState_4359_ = lean_ctor_get(v___x_4352_, 4);
v_cache_4360_ = lean_ctor_get(v___x_4352_, 5);
v_messages_4361_ = lean_ctor_get(v___x_4352_, 6);
v_infoState_4362_ = lean_ctor_get(v___x_4352_, 7);
v_snapshotTasks_4363_ = lean_ctor_get(v___x_4352_, 8);
v_newDecls_4364_ = lean_ctor_get(v___x_4352_, 9);
v_isSharedCheck_4378_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4378_ == 0)
{
v___x_4366_ = v___x_4352_;
v_isShared_4367_ = v_isSharedCheck_4378_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_newDecls_4364_);
lean_inc(v_snapshotTasks_4363_);
lean_inc(v_infoState_4362_);
lean_inc(v_messages_4361_);
lean_inc(v_cache_4360_);
lean_inc(v_traceState_4359_);
lean_inc(v_auxDeclNGen_4358_);
lean_inc(v_ngen_4357_);
lean_inc(v_nextMacroScope_4356_);
lean_inc(v_env_4355_);
lean_dec(v___x_4352_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4378_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4373_; 
lean_inc(v_openDecls_4354_);
lean_inc(v_currNamespace_4353_);
v___x_4368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4368_, 0, v_currNamespace_4353_);
lean_ctor_set(v___x_4368_, 1, v_openDecls_4354_);
v___x_4369_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4369_, 0, v___x_4368_);
lean_ctor_set(v___x_4369_, 1, v___y_4344_);
lean_inc_ref(v___y_4347_);
lean_inc_ref(v___y_4349_);
v___x_4370_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4370_, 0, v___y_4349_);
lean_ctor_set(v___x_4370_, 1, v___y_4346_);
lean_ctor_set(v___x_4370_, 2, v___y_4345_);
lean_ctor_set(v___x_4370_, 3, v___y_4347_);
lean_ctor_set(v___x_4370_, 4, v___x_4369_);
lean_ctor_set_uint8(v___x_4370_, sizeof(void*)*5, v___y_4343_);
lean_ctor_set_uint8(v___x_4370_, sizeof(void*)*5 + 1, v___y_4348_);
lean_ctor_set_uint8(v___x_4370_, sizeof(void*)*5 + 2, v_isSilent_4336_);
v___x_4371_ = l_Lean_MessageLog_add(v___x_4370_, v_messages_4361_);
if (v_isShared_4367_ == 0)
{
lean_ctor_set(v___x_4366_, 6, v___x_4371_);
v___x_4373_ = v___x_4366_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v_env_4355_);
lean_ctor_set(v_reuseFailAlloc_4377_, 1, v_nextMacroScope_4356_);
lean_ctor_set(v_reuseFailAlloc_4377_, 2, v_ngen_4357_);
lean_ctor_set(v_reuseFailAlloc_4377_, 3, v_auxDeclNGen_4358_);
lean_ctor_set(v_reuseFailAlloc_4377_, 4, v_traceState_4359_);
lean_ctor_set(v_reuseFailAlloc_4377_, 5, v_cache_4360_);
lean_ctor_set(v_reuseFailAlloc_4377_, 6, v___x_4371_);
lean_ctor_set(v_reuseFailAlloc_4377_, 7, v_infoState_4362_);
lean_ctor_set(v_reuseFailAlloc_4377_, 8, v_snapshotTasks_4363_);
lean_ctor_set(v_reuseFailAlloc_4377_, 9, v_newDecls_4364_);
v___x_4373_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; 
v___x_4374_ = lean_st_ref_set(v___y_4351_, v___x_4373_);
v___x_4375_ = lean_box(0);
v___x_4376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4376_, 0, v___x_4375_);
return v___x_4376_;
}
}
}
v___jp_4379_:
{
lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v_a_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4403_; 
v___x_4388_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4334_);
v___x_4389_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(v___x_4388_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
v_a_4390_ = lean_ctor_get(v___x_4389_, 0);
v_isSharedCheck_4403_ = !lean_is_exclusive(v___x_4389_);
if (v_isSharedCheck_4403_ == 0)
{
v___x_4392_ = v___x_4389_;
v_isShared_4393_ = v_isSharedCheck_4403_;
goto v_resetjp_4391_;
}
else
{
lean_inc(v_a_4390_);
lean_dec(v___x_4389_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4403_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; 
lean_inc_ref_n(v___y_4383_, 2);
v___x_4394_ = l_Lean_FileMap_toPosition(v___y_4383_, v___y_4386_);
lean_dec(v___y_4386_);
v___x_4395_ = l_Lean_FileMap_toPosition(v___y_4383_, v___y_4387_);
lean_dec(v___y_4387_);
v___x_4396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4396_, 0, v___x_4395_);
v___x_4397_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___closed__0));
if (v___y_4382_ == 0)
{
lean_del_object(v___x_4392_);
lean_dec_ref(v___y_4380_);
v___y_4343_ = v___y_4381_;
v___y_4344_ = v_a_4390_;
v___y_4345_ = v___x_4396_;
v___y_4346_ = v___x_4394_;
v___y_4347_ = v___x_4397_;
v___y_4348_ = v___y_4384_;
v___y_4349_ = v___y_4385_;
v___y_4350_ = v___y_4339_;
v___y_4351_ = v___y_4340_;
goto v___jp_4342_;
}
else
{
uint8_t v___x_4398_; 
lean_inc(v_a_4390_);
v___x_4398_ = l_Lean_MessageData_hasTag(v___y_4380_, v_a_4390_);
if (v___x_4398_ == 0)
{
lean_object* v___x_4399_; lean_object* v___x_4401_; 
lean_dec_ref(v___x_4396_);
lean_dec_ref(v___x_4394_);
lean_dec(v_a_4390_);
v___x_4399_ = lean_box(0);
if (v_isShared_4393_ == 0)
{
lean_ctor_set(v___x_4392_, 0, v___x_4399_);
v___x_4401_ = v___x_4392_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v___x_4399_);
v___x_4401_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
return v___x_4401_;
}
}
else
{
lean_del_object(v___x_4392_);
v___y_4343_ = v___y_4381_;
v___y_4344_ = v_a_4390_;
v___y_4345_ = v___x_4396_;
v___y_4346_ = v___x_4394_;
v___y_4347_ = v___x_4397_;
v___y_4348_ = v___y_4384_;
v___y_4349_ = v___y_4385_;
v___y_4350_ = v___y_4339_;
v___y_4351_ = v___y_4340_;
goto v___jp_4342_;
}
}
}
}
v___jp_4404_:
{
lean_object* v___x_4413_; 
v___x_4413_ = l_Lean_Syntax_getTailPos_x3f(v___y_4407_, v___y_4406_);
lean_dec(v___y_4407_);
if (lean_obj_tag(v___x_4413_) == 0)
{
lean_inc(v___y_4412_);
v___y_4380_ = v___y_4405_;
v___y_4381_ = v___y_4406_;
v___y_4382_ = v___y_4408_;
v___y_4383_ = v___y_4409_;
v___y_4384_ = v___y_4410_;
v___y_4385_ = v___y_4411_;
v___y_4386_ = v___y_4412_;
v___y_4387_ = v___y_4412_;
goto v___jp_4379_;
}
else
{
lean_object* v_val_4414_; 
v_val_4414_ = lean_ctor_get(v___x_4413_, 0);
lean_inc(v_val_4414_);
lean_dec_ref(v___x_4413_);
v___y_4380_ = v___y_4405_;
v___y_4381_ = v___y_4406_;
v___y_4382_ = v___y_4408_;
v___y_4383_ = v___y_4409_;
v___y_4384_ = v___y_4410_;
v___y_4385_ = v___y_4411_;
v___y_4386_ = v___y_4412_;
v___y_4387_ = v_val_4414_;
goto v___jp_4379_;
}
}
v___jp_4415_:
{
lean_object* v_ref_4423_; lean_object* v___x_4424_; 
v_ref_4423_ = l_Lean_replaceRef(v_ref_4333_, v___y_4420_);
v___x_4424_ = l_Lean_Syntax_getPos_x3f(v_ref_4423_, v___y_4417_);
if (lean_obj_tag(v___x_4424_) == 0)
{
lean_object* v___x_4425_; 
v___x_4425_ = lean_unsigned_to_nat(0u);
v___y_4405_ = v___y_4416_;
v___y_4406_ = v___y_4417_;
v___y_4407_ = v_ref_4423_;
v___y_4408_ = v___y_4418_;
v___y_4409_ = v___y_4419_;
v___y_4410_ = v___y_4422_;
v___y_4411_ = v___y_4421_;
v___y_4412_ = v___x_4425_;
goto v___jp_4404_;
}
else
{
lean_object* v_val_4426_; 
v_val_4426_ = lean_ctor_get(v___x_4424_, 0);
lean_inc(v_val_4426_);
lean_dec_ref(v___x_4424_);
v___y_4405_ = v___y_4416_;
v___y_4406_ = v___y_4417_;
v___y_4407_ = v_ref_4423_;
v___y_4408_ = v___y_4418_;
v___y_4409_ = v___y_4419_;
v___y_4410_ = v___y_4422_;
v___y_4411_ = v___y_4421_;
v___y_4412_ = v_val_4426_;
goto v___jp_4404_;
}
}
v___jp_4428_:
{
if (v___y_4435_ == 0)
{
v___y_4416_ = v___y_4433_;
v___y_4417_ = v___y_4434_;
v___y_4418_ = v___y_4429_;
v___y_4419_ = v___y_4431_;
v___y_4420_ = v___y_4430_;
v___y_4421_ = v___y_4432_;
v___y_4422_ = v_severity_4335_;
goto v___jp_4415_;
}
else
{
v___y_4416_ = v___y_4433_;
v___y_4417_ = v___y_4434_;
v___y_4418_ = v___y_4429_;
v___y_4419_ = v___y_4431_;
v___y_4420_ = v___y_4430_;
v___y_4421_ = v___y_4432_;
v___y_4422_ = v___x_4427_;
goto v___jp_4415_;
}
}
v___jp_4436_:
{
if (v___y_4437_ == 0)
{
lean_object* v_fileName_4438_; lean_object* v_fileMap_4439_; lean_object* v_options_4440_; lean_object* v_ref_4441_; uint8_t v_suppressElabErrors_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___f_4445_; uint8_t v___x_4446_; uint8_t v___x_4447_; 
v_fileName_4438_ = lean_ctor_get(v___y_4339_, 0);
v_fileMap_4439_ = lean_ctor_get(v___y_4339_, 1);
v_options_4440_ = lean_ctor_get(v___y_4339_, 2);
v_ref_4441_ = lean_ctor_get(v___y_4339_, 5);
v_suppressElabErrors_4442_ = lean_ctor_get_uint8(v___y_4339_, sizeof(void*)*14 + 1);
v___x_4443_ = lean_box(v___y_4437_);
v___x_4444_ = lean_box(v_suppressElabErrors_4442_);
v___f_4445_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4445_, 0, v___x_4443_);
lean_closure_set(v___f_4445_, 1, v___x_4444_);
v___x_4446_ = 1;
v___x_4447_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4335_, v___x_4446_);
if (v___x_4447_ == 0)
{
v___y_4429_ = v_suppressElabErrors_4442_;
v___y_4430_ = v_ref_4441_;
v___y_4431_ = v_fileMap_4439_;
v___y_4432_ = v_fileName_4438_;
v___y_4433_ = v___f_4445_;
v___y_4434_ = v___y_4437_;
v___y_4435_ = v___x_4447_;
goto v___jp_4428_;
}
else
{
lean_object* v___x_4448_; uint8_t v___x_4449_; 
v___x_4448_ = l_Lean_warningAsError;
v___x_4449_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(v_options_4440_, v___x_4448_);
v___y_4429_ = v_suppressElabErrors_4442_;
v___y_4430_ = v_ref_4441_;
v___y_4431_ = v_fileMap_4439_;
v___y_4432_ = v_fileName_4438_;
v___y_4433_ = v___f_4445_;
v___y_4434_ = v___y_4437_;
v___y_4435_ = v___x_4449_;
goto v___jp_4428_;
}
}
else
{
lean_object* v___x_4450_; lean_object* v___x_4451_; 
lean_dec_ref(v_msgData_4334_);
v___x_4450_ = lean_box(0);
v___x_4451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4451_, 0, v___x_4450_);
return v___x_4451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_4454_, lean_object* v_msgData_4455_, lean_object* v_severity_4456_, lean_object* v_isSilent_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_){
_start:
{
uint8_t v_severity_boxed_4463_; uint8_t v_isSilent_boxed_4464_; lean_object* v_res_4465_; 
v_severity_boxed_4463_ = lean_unbox(v_severity_4456_);
v_isSilent_boxed_4464_ = lean_unbox(v_isSilent_4457_);
v_res_4465_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(v_ref_4454_, v_msgData_4455_, v_severity_boxed_4463_, v_isSilent_boxed_4464_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
lean_dec(v___y_4461_);
lean_dec_ref(v___y_4460_);
lean_dec(v___y_4459_);
lean_dec_ref(v___y_4458_);
lean_dec(v_ref_4454_);
return v_res_4465_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(lean_object* v_msgData_4466_, uint8_t v_severity_4467_, uint8_t v_isSilent_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_){
_start:
{
lean_object* v_ref_4474_; lean_object* v___x_4475_; 
v_ref_4474_ = lean_ctor_get(v___y_4471_, 5);
v___x_4475_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(v_ref_4474_, v_msgData_4466_, v_severity_4467_, v_isSilent_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_);
return v___x_4475_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0___boxed(lean_object* v_msgData_4476_, lean_object* v_severity_4477_, lean_object* v_isSilent_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_){
_start:
{
uint8_t v_severity_boxed_4484_; uint8_t v_isSilent_boxed_4485_; lean_object* v_res_4486_; 
v_severity_boxed_4484_ = lean_unbox(v_severity_4477_);
v_isSilent_boxed_4485_ = lean_unbox(v_isSilent_4478_);
v_res_4486_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(v_msgData_4476_, v_severity_boxed_4484_, v_isSilent_boxed_4485_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
return v_res_4486_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(lean_object* v_msgData_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
uint8_t v___x_4493_; uint8_t v___x_4494_; lean_object* v___x_4495_; 
v___x_4493_ = 0;
v___x_4494_ = 0;
v___x_4495_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(v_msgData_4487_, v___x_4493_, v___x_4494_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
return v___x_4495_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0___boxed(lean_object* v_msgData_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_){
_start:
{
lean_object* v_res_4502_; 
v_res_4502_ = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(v_msgData_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
return v_res_4502_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1(void){
_start:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; 
v___x_4504_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0));
v___x_4505_ = l_Lean_stringToMessageData(v___x_4504_);
return v___x_4505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2(uint8_t v___x_4506_, lean_object* v___altIdx_4507_, lean_object* v_expAltType_4508_, lean_object* v___altFVars_4509_, lean_object* v_alt_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_){
_start:
{
lean_object* v___x_4516_; 
lean_inc(v___y_4514_);
lean_inc_ref(v___y_4513_);
lean_inc(v___y_4512_);
lean_inc_ref(v___y_4511_);
lean_inc_ref(v_alt_4510_);
v___x_4516_ = lean_infer_type(v_alt_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_);
if (lean_obj_tag(v___x_4516_) == 0)
{
lean_object* v_a_4517_; lean_object* v___x_4518_; 
v_a_4517_ = lean_ctor_get(v___x_4516_, 0);
lean_inc(v_a_4517_);
lean_dec_ref(v___x_4516_);
v___x_4518_ = l_Lean_Meta_mkEq(v_expAltType_4508_, v_a_4517_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_);
if (lean_obj_tag(v___x_4518_) == 0)
{
lean_object* v_a_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; 
v_a_4519_ = lean_ctor_get(v___x_4518_, 0);
lean_inc(v_a_4519_);
lean_dec_ref(v___x_4518_);
v___x_4520_ = lean_box(0);
v___x_4521_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4519_, v___x_4520_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_);
if (lean_obj_tag(v___x_4521_) == 0)
{
lean_object* v_a_4522_; lean_object* v___y_4524_; lean_object* v___x_4534_; lean_object* v___x_4535_; 
v_a_4522_ = lean_ctor_get(v___x_4521_, 0);
lean_inc(v_a_4522_);
lean_dec_ref(v___x_4521_);
v___x_4534_ = l_Lean_Expr_mvarId_x21(v_a_4522_);
v___x_4535_ = l_Lean_Meta_Split_simpMatchTarget(v___x_4534_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_);
if (lean_obj_tag(v___x_4535_) == 0)
{
lean_object* v_a_4536_; lean_object* v___x_4537_; 
v_a_4536_ = lean_ctor_get(v___x_4535_, 0);
lean_inc_n(v_a_4536_, 2);
lean_dec_ref(v___x_4535_);
v___x_4537_ = l_Lean_MVarId_refl(v_a_4536_, v___x_4506_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_);
if (lean_obj_tag(v___x_4537_) == 0)
{
lean_dec(v_a_4536_);
v___y_4524_ = v___x_4537_;
goto v___jp_4523_;
}
else
{
lean_object* v_a_4538_; uint8_t v___y_4540_; uint8_t v___x_4553_; 
v_a_4538_ = lean_ctor_get(v___x_4537_, 0);
lean_inc(v_a_4538_);
v___x_4553_ = l_Lean_Exception_isInterrupt(v_a_4538_);
if (v___x_4553_ == 0)
{
uint8_t v___x_4554_; 
v___x_4554_ = l_Lean_Exception_isRuntime(v_a_4538_);
v___y_4540_ = v___x_4554_;
goto v___jp_4539_;
}
else
{
lean_dec(v_a_4538_);
v___y_4540_ = v___x_4553_;
goto v___jp_4539_;
}
v___jp_4539_:
{
if (v___y_4540_ == 0)
{
lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4551_; 
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4551_ == 0)
{
lean_object* v_unused_4552_; 
v_unused_4552_ = lean_ctor_get(v___x_4537_, 0);
lean_dec(v_unused_4552_);
v___x_4542_ = v___x_4537_;
v_isShared_4543_ = v_isSharedCheck_4551_;
goto v_resetjp_4541_;
}
else
{
lean_dec(v___x_4537_);
v___x_4542_ = lean_box(0);
v_isShared_4543_ = v_isSharedCheck_4551_;
goto v_resetjp_4541_;
}
v_resetjp_4541_:
{
lean_object* v___x_4544_; lean_object* v___x_4546_; 
v___x_4544_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1, &l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1);
lean_inc(v_a_4536_);
if (v_isShared_4543_ == 0)
{
lean_ctor_set(v___x_4542_, 0, v_a_4536_);
v___x_4546_ = v___x_4542_;
goto v_reusejp_4545_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_a_4536_);
v___x_4546_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4545_;
}
v_reusejp_4545_:
{
lean_object* v___x_4547_; lean_object* v___x_4548_; 
v___x_4547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4547_, 0, v___x_4544_);
lean_ctor_set(v___x_4547_, 1, v___x_4546_);
v___x_4548_ = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(v___x_4547_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_);
if (lean_obj_tag(v___x_4548_) == 0)
{
lean_object* v___x_4549_; 
lean_dec_ref(v___x_4548_);
v___x_4549_ = l_Lean_MVarId_admit(v_a_4536_, v___x_4506_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_);
v___y_4524_ = v___x_4549_;
goto v___jp_4523_;
}
else
{
lean_dec(v_a_4536_);
v___y_4524_ = v___x_4548_;
goto v___jp_4523_;
}
}
}
}
else
{
lean_dec(v_a_4536_);
v___y_4524_ = v___x_4537_;
goto v___jp_4523_;
}
}
}
}
else
{
lean_object* v_a_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4562_; 
lean_dec(v_a_4522_);
lean_dec_ref(v_alt_4510_);
v_a_4555_ = lean_ctor_get(v___x_4535_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4535_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4557_ = v___x_4535_;
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_a_4555_);
lean_dec(v___x_4535_);
v___x_4557_ = lean_box(0);
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
v_resetjp_4556_:
{
lean_object* v___x_4560_; 
if (v_isShared_4558_ == 0)
{
v___x_4560_ = v___x_4557_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_a_4555_);
v___x_4560_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
return v___x_4560_;
}
}
}
v___jp_4523_:
{
if (lean_obj_tag(v___y_4524_) == 0)
{
lean_object* v___x_4525_; 
lean_dec_ref(v___y_4524_);
v___x_4525_ = l_Lean_Meta_mkEqMPR(v_a_4522_, v_alt_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_);
return v___x_4525_;
}
else
{
lean_object* v_a_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4533_; 
lean_dec(v_a_4522_);
lean_dec_ref(v_alt_4510_);
v_a_4526_ = lean_ctor_get(v___y_4524_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v___y_4524_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4528_ = v___y_4524_;
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_a_4526_);
lean_dec(v___y_4524_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4533_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v___x_4531_; 
if (v_isShared_4529_ == 0)
{
v___x_4531_ = v___x_4528_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_a_4526_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
return v___x_4531_;
}
}
}
}
}
else
{
lean_dec_ref(v_alt_4510_);
return v___x_4521_;
}
}
else
{
lean_dec_ref(v_alt_4510_);
return v___x_4518_;
}
}
else
{
lean_dec_ref(v_alt_4510_);
lean_dec_ref(v_expAltType_4508_);
return v___x_4516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___boxed(lean_object* v___x_4563_, lean_object* v___altIdx_4564_, lean_object* v_expAltType_4565_, lean_object* v___altFVars_4566_, lean_object* v_alt_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_){
_start:
{
uint8_t v___x_32362__boxed_4573_; lean_object* v_res_4574_; 
v___x_32362__boxed_4573_ = lean_unbox(v___x_4563_);
v_res_4574_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__2(v___x_32362__boxed_4573_, v___altIdx_4564_, v_expAltType_4565_, v___altFVars_4566_, v_alt_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_);
lean_dec(v___y_4571_);
lean_dec_ref(v___y_4570_);
lean_dec(v___y_4569_);
lean_dec_ref(v___y_4568_);
lean_dec_ref(v___altFVars_4566_);
lean_dec(v___altIdx_4564_);
return v_res_4574_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(lean_object* v___x_4575_, lean_object* v_e_4576_){
_start:
{
uint8_t v___x_4577_; lean_object* v_d_4579_; lean_object* v_b_4580_; 
v___x_4577_ = l_Lean_Expr_hasFVar(v_e_4576_);
if (v___x_4577_ == 0)
{
return v___x_4577_;
}
else
{
switch(lean_obj_tag(v_e_4576_))
{
case 7:
{
lean_object* v_binderType_4583_; lean_object* v_body_4584_; 
v_binderType_4583_ = lean_ctor_get(v_e_4576_, 1);
v_body_4584_ = lean_ctor_get(v_e_4576_, 2);
v_d_4579_ = v_binderType_4583_;
v_b_4580_ = v_body_4584_;
goto v___jp_4578_;
}
case 6:
{
lean_object* v_binderType_4585_; lean_object* v_body_4586_; 
v_binderType_4585_ = lean_ctor_get(v_e_4576_, 1);
v_body_4586_ = lean_ctor_get(v_e_4576_, 2);
v_d_4579_ = v_binderType_4585_;
v_b_4580_ = v_body_4586_;
goto v___jp_4578_;
}
case 10:
{
lean_object* v_expr_4587_; 
v_expr_4587_ = lean_ctor_get(v_e_4576_, 1);
v_e_4576_ = v_expr_4587_;
goto _start;
}
case 8:
{
lean_object* v_type_4589_; lean_object* v_value_4590_; lean_object* v_body_4591_; uint8_t v___x_4592_; 
v_type_4589_ = lean_ctor_get(v_e_4576_, 1);
v_value_4590_ = lean_ctor_get(v_e_4576_, 2);
v_body_4591_ = lean_ctor_get(v_e_4576_, 3);
v___x_4592_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4575_, v_type_4589_);
if (v___x_4592_ == 0)
{
uint8_t v___x_4593_; 
v___x_4593_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4575_, v_value_4590_);
if (v___x_4593_ == 0)
{
v_e_4576_ = v_body_4591_;
goto _start;
}
else
{
return v___x_4577_;
}
}
else
{
return v___x_4577_;
}
}
case 5:
{
lean_object* v_fn_4595_; lean_object* v_arg_4596_; uint8_t v___x_4597_; 
v_fn_4595_ = lean_ctor_get(v_e_4576_, 0);
v_arg_4596_ = lean_ctor_get(v_e_4576_, 1);
v___x_4597_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4575_, v_fn_4595_);
if (v___x_4597_ == 0)
{
v_e_4576_ = v_arg_4596_;
goto _start;
}
else
{
return v___x_4577_;
}
}
case 11:
{
lean_object* v_struct_4599_; 
v_struct_4599_ = lean_ctor_get(v_e_4576_, 2);
v_e_4576_ = v_struct_4599_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4601_; lean_object* v___x_4602_; uint8_t v___x_4603_; 
v_fvarId_4601_ = lean_ctor_get(v_e_4576_, 0);
v___x_4602_ = l_Lean_Expr_fvarId_x21(v___x_4575_);
v___x_4603_ = l_Lean_instBEqFVarId_beq(v_fvarId_4601_, v___x_4602_);
lean_dec(v___x_4602_);
return v___x_4603_;
}
default: 
{
uint8_t v___x_4604_; 
v___x_4604_ = 0;
return v___x_4604_;
}
}
}
v___jp_4578_:
{
uint8_t v___x_4581_; 
v___x_4581_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4575_, v_d_4579_);
if (v___x_4581_ == 0)
{
v_e_4576_ = v_b_4580_;
goto _start;
}
else
{
return v___x_4577_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1___boxed(lean_object* v___x_4605_, lean_object* v_e_4606_){
_start:
{
uint8_t v_res_4607_; lean_object* v_r_4608_; 
v_res_4607_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4605_, v_e_4606_);
lean_dec_ref(v_e_4606_);
lean_dec_ref(v___x_4605_);
v_r_4608_ = lean_box(v_res_4607_);
return v_r_4608_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4610_; lean_object* v___x_4611_; 
v___x_4610_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__0));
v___x_4611_ = l_Lean_stringToMessageData(v___x_4610_);
return v___x_4611_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4613_; lean_object* v___x_4614_; 
v___x_4613_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__2));
v___x_4614_ = l_Lean_stringToMessageData(v___x_4613_);
return v___x_4614_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_4616_; lean_object* v___x_4617_; 
v___x_4616_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__4));
v___x_4617_ = l_Lean_stringToMessageData(v___x_4616_);
return v___x_4617_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(lean_object* v_a_4618_, lean_object* v_termAlt_4619_, lean_object* v_a_4620_, lean_object* v_b_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_){
_start:
{
lean_object* v_array_4627_; lean_object* v_start_4628_; lean_object* v_stop_4629_; lean_object* v___x_4631_; uint8_t v_isShared_4632_; uint8_t v_isSharedCheck_4657_; 
v_array_4627_ = lean_ctor_get(v_a_4620_, 0);
v_start_4628_ = lean_ctor_get(v_a_4620_, 1);
v_stop_4629_ = lean_ctor_get(v_a_4620_, 2);
v_isSharedCheck_4657_ = !lean_is_exclusive(v_a_4620_);
if (v_isSharedCheck_4657_ == 0)
{
v___x_4631_ = v_a_4620_;
v_isShared_4632_ = v_isSharedCheck_4657_;
goto v_resetjp_4630_;
}
else
{
lean_inc(v_stop_4629_);
lean_inc(v_start_4628_);
lean_inc(v_array_4627_);
lean_dec(v_a_4620_);
v___x_4631_ = lean_box(0);
v_isShared_4632_ = v_isSharedCheck_4657_;
goto v_resetjp_4630_;
}
v_resetjp_4630_:
{
uint8_t v___x_4633_; 
v___x_4633_ = lean_nat_dec_lt(v_start_4628_, v_stop_4629_);
if (v___x_4633_ == 0)
{
lean_object* v___x_4634_; 
lean_del_object(v___x_4631_);
lean_dec(v_stop_4629_);
lean_dec(v_start_4628_);
lean_dec_ref(v_array_4627_);
lean_dec_ref(v_termAlt_4619_);
lean_dec_ref(v_a_4618_);
v___x_4634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4634_, 0, v_b_4621_);
return v___x_4634_;
}
else
{
lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4639_; 
v___x_4635_ = lean_box(0);
v___x_4636_ = lean_unsigned_to_nat(1u);
v___x_4637_ = lean_nat_add(v_start_4628_, v___x_4636_);
lean_inc_ref(v_array_4627_);
if (v_isShared_4632_ == 0)
{
lean_ctor_set(v___x_4631_, 1, v___x_4637_);
v___x_4639_ = v___x_4631_;
goto v_reusejp_4638_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_array_4627_);
lean_ctor_set(v_reuseFailAlloc_4656_, 1, v___x_4637_);
lean_ctor_set(v_reuseFailAlloc_4656_, 2, v_stop_4629_);
v___x_4639_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4638_;
}
v_reusejp_4638_:
{
lean_object* v___x_4640_; uint8_t v___x_4641_; 
v___x_4640_ = lean_array_fget(v_array_4627_, v_start_4628_);
lean_dec(v_start_4628_);
lean_dec_ref(v_array_4627_);
v___x_4641_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4640_, v_a_4618_);
if (v___x_4641_ == 0)
{
lean_dec(v___x_4640_);
v_a_4620_ = v___x_4639_;
v_b_4621_ = v___x_4635_;
goto _start;
}
else
{
lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; 
v___x_4643_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1);
lean_inc_ref(v_a_4618_);
v___x_4644_ = l_Lean_MessageData_ofExpr(v_a_4618_);
v___x_4645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4645_, 0, v___x_4643_);
lean_ctor_set(v___x_4645_, 1, v___x_4644_);
v___x_4646_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3);
v___x_4647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4647_, 0, v___x_4645_);
lean_ctor_set(v___x_4647_, 1, v___x_4646_);
lean_inc_ref(v_termAlt_4619_);
v___x_4648_ = l_Lean_MessageData_ofExpr(v_termAlt_4619_);
v___x_4649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4649_, 0, v___x_4647_);
lean_ctor_set(v___x_4649_, 1, v___x_4648_);
v___x_4650_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5);
v___x_4651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4651_, 0, v___x_4649_);
lean_ctor_set(v___x_4651_, 1, v___x_4650_);
v___x_4652_ = l_Lean_MessageData_ofExpr(v___x_4640_);
v___x_4653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4653_, 0, v___x_4651_);
lean_ctor_set(v___x_4653_, 1, v___x_4652_);
v___x_4654_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_4653_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_);
if (lean_obj_tag(v___x_4654_) == 0)
{
lean_dec_ref(v___x_4654_);
v_a_4620_ = v___x_4639_;
v_b_4621_ = v___x_4635_;
goto _start;
}
else
{
lean_dec_ref(v___x_4639_);
lean_dec_ref(v_termAlt_4619_);
lean_dec_ref(v_a_4618_);
return v___x_4654_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___boxed(lean_object* v_a_4658_, lean_object* v_termAlt_4659_, lean_object* v_a_4660_, lean_object* v_b_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_){
_start:
{
lean_object* v_res_4667_; 
v_res_4667_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_4658_, v_termAlt_4659_, v_a_4660_, v_b_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
return v_res_4667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(lean_object* v_nExtra_4668_, lean_object* v_v_4669_, uint8_t v___x_4670_, uint8_t v___x_4671_, uint8_t v___x_4672_, lean_object* v_xs_4673_, lean_object* v_termAltBody_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_){
_start:
{
lean_object* v___x_4680_; 
lean_inc(v___y_4678_);
lean_inc_ref(v___y_4677_);
lean_inc(v___y_4676_);
lean_inc_ref(v___y_4675_);
v___x_4680_ = lean_infer_type(v_termAltBody_4674_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_);
if (lean_obj_tag(v___x_4680_) == 0)
{
lean_object* v_a_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; 
v_a_4681_ = lean_ctor_get(v___x_4680_, 0);
lean_inc_n(v_a_4681_, 2);
lean_dec_ref(v___x_4680_);
v___x_4682_ = lean_array_get_size(v_xs_4673_);
v___x_4683_ = lean_nat_sub(v___x_4682_, v_nExtra_4668_);
v___x_4684_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_4683_);
lean_inc_ref(v_xs_4673_);
v___x_4685_ = l_Array_toSubarray___redArg(v_xs_4673_, v___x_4684_, v___x_4683_);
v___x_4686_ = l_Array_toSubarray___redArg(v_xs_4673_, v___x_4683_, v___x_4682_);
v___x_4687_ = lean_box(0);
v___x_4688_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_4681_, v_v_4669_, v___x_4686_, v___x_4687_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_);
if (lean_obj_tag(v___x_4688_) == 0)
{
lean_object* v___x_4689_; lean_object* v___x_4690_; 
lean_dec_ref(v___x_4688_);
v___x_4689_ = l_Subarray_copy___redArg(v___x_4685_);
v___x_4690_ = l_Lean_Meta_mkLambdaFVars(v___x_4689_, v_a_4681_, v___x_4670_, v___x_4671_, v___x_4670_, v___x_4671_, v___x_4672_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_);
lean_dec_ref(v___x_4689_);
return v___x_4690_;
}
else
{
lean_object* v_a_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4698_; 
lean_dec_ref(v___x_4685_);
lean_dec(v_a_4681_);
v_a_4691_ = lean_ctor_get(v___x_4688_, 0);
v_isSharedCheck_4698_ = !lean_is_exclusive(v___x_4688_);
if (v_isSharedCheck_4698_ == 0)
{
v___x_4693_ = v___x_4688_;
v_isShared_4694_ = v_isSharedCheck_4698_;
goto v_resetjp_4692_;
}
else
{
lean_inc(v_a_4691_);
lean_dec(v___x_4688_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4698_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
lean_object* v___x_4696_; 
if (v_isShared_4694_ == 0)
{
v___x_4696_ = v___x_4693_;
goto v_reusejp_4695_;
}
else
{
lean_object* v_reuseFailAlloc_4697_; 
v_reuseFailAlloc_4697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4697_, 0, v_a_4691_);
v___x_4696_ = v_reuseFailAlloc_4697_;
goto v_reusejp_4695_;
}
v_reusejp_4695_:
{
return v___x_4696_;
}
}
}
}
else
{
lean_dec_ref(v_xs_4673_);
lean_dec(v_v_4669_);
return v___x_4680_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed(lean_object* v_nExtra_4699_, lean_object* v_v_4700_, lean_object* v___x_4701_, lean_object* v___x_4702_, lean_object* v___x_4703_, lean_object* v_xs_4704_, lean_object* v_termAltBody_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_){
_start:
{
uint8_t v___x_32651__boxed_4711_; uint8_t v___x_32652__boxed_4712_; uint8_t v___x_32653__boxed_4713_; lean_object* v_res_4714_; 
v___x_32651__boxed_4711_ = lean_unbox(v___x_4701_);
v___x_32652__boxed_4712_ = lean_unbox(v___x_4702_);
v___x_32653__boxed_4713_ = lean_unbox(v___x_4703_);
v_res_4714_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(v_nExtra_4699_, v_v_4700_, v___x_32651__boxed_4711_, v___x_32652__boxed_4712_, v___x_32653__boxed_4713_, v_xs_4704_, v_termAltBody_4705_, v___y_4706_, v___y_4707_, v___y_4708_, v___y_4709_);
lean_dec(v___y_4709_);
lean_dec_ref(v___y_4708_);
lean_dec(v___y_4707_);
lean_dec_ref(v___y_4706_);
lean_dec(v_nExtra_4699_);
return v_res_4714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(lean_object* v_nExtra_4715_, size_t v_sz_4716_, size_t v_i_4717_, lean_object* v_bs_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_){
_start:
{
uint8_t v___x_4724_; 
v___x_4724_ = lean_usize_dec_lt(v_i_4717_, v_sz_4716_);
if (v___x_4724_ == 0)
{
lean_object* v___x_4725_; 
lean_dec(v_nExtra_4715_);
v___x_4725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4725_, 0, v_bs_4718_);
return v___x_4725_;
}
else
{
uint8_t v___x_4726_; uint8_t v___x_4727_; lean_object* v_v_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___f_4732_; lean_object* v___x_4733_; 
v___x_4726_ = 0;
v___x_4727_ = 1;
v_v_4728_ = lean_array_uget_borrowed(v_bs_4718_, v_i_4717_);
v___x_4729_ = lean_box(v___x_4726_);
v___x_4730_ = lean_box(v___x_4724_);
v___x_4731_ = lean_box(v___x_4727_);
lean_inc_n(v_v_4728_, 2);
lean_inc(v_nExtra_4715_);
v___f_4732_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4732_, 0, v_nExtra_4715_);
lean_closure_set(v___f_4732_, 1, v_v_4728_);
lean_closure_set(v___f_4732_, 2, v___x_4729_);
lean_closure_set(v___f_4732_, 3, v___x_4730_);
lean_closure_set(v___f_4732_, 4, v___x_4731_);
v___x_4733_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_v_4728_, v___f_4732_, v___x_4726_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_);
if (lean_obj_tag(v___x_4733_) == 0)
{
lean_object* v_a_4734_; lean_object* v___x_4735_; lean_object* v_bs_x27_4736_; size_t v___x_4737_; size_t v___x_4738_; lean_object* v___x_4739_; 
v_a_4734_ = lean_ctor_get(v___x_4733_, 0);
lean_inc(v_a_4734_);
lean_dec_ref(v___x_4733_);
v___x_4735_ = lean_unsigned_to_nat(0u);
v_bs_x27_4736_ = lean_array_uset(v_bs_4718_, v_i_4717_, v___x_4735_);
v___x_4737_ = ((size_t)1ULL);
v___x_4738_ = lean_usize_add(v_i_4717_, v___x_4737_);
v___x_4739_ = lean_array_uset(v_bs_x27_4736_, v_i_4717_, v_a_4734_);
v_i_4717_ = v___x_4738_;
v_bs_4718_ = v___x_4739_;
goto _start;
}
else
{
lean_object* v_a_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4748_; 
lean_dec_ref(v_bs_4718_);
lean_dec(v_nExtra_4715_);
v_a_4741_ = lean_ctor_get(v___x_4733_, 0);
v_isSharedCheck_4748_ = !lean_is_exclusive(v___x_4733_);
if (v_isSharedCheck_4748_ == 0)
{
v___x_4743_ = v___x_4733_;
v_isShared_4744_ = v_isSharedCheck_4748_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_a_4741_);
lean_dec(v___x_4733_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4748_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v___x_4746_; 
if (v_isShared_4744_ == 0)
{
v___x_4746_ = v___x_4743_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v_a_4741_);
v___x_4746_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
return v___x_4746_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___boxed(lean_object* v_nExtra_4749_, lean_object* v_sz_4750_, lean_object* v_i_4751_, lean_object* v_bs_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_){
_start:
{
size_t v_sz_boxed_4758_; size_t v_i_boxed_4759_; lean_object* v_res_4760_; 
v_sz_boxed_4758_ = lean_unbox_usize(v_sz_4750_);
lean_dec(v_sz_4750_);
v_i_boxed_4759_ = lean_unbox_usize(v_i_4751_);
lean_dec(v_i_4751_);
v_res_4760_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(v_nExtra_4749_, v_sz_boxed_4758_, v_i_boxed_4759_, v_bs_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_);
lean_dec(v___y_4756_);
lean_dec_ref(v___y_4755_);
lean_dec(v___y_4754_);
lean_dec_ref(v___y_4753_);
return v_res_4760_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0(void){
_start:
{
lean_object* v___x_4761_; lean_object* v___x_4762_; 
v___x_4761_ = lean_box(0);
v___x_4762_ = l_Lean_Expr_sort___override(v___x_4761_);
return v___x_4762_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1(void){
_start:
{
lean_object* v___x_4763_; lean_object* v___x_4764_; 
v___x_4763_ = lean_box(0);
v___x_4764_ = l_Lean_Level_succ___override(v___x_4763_);
return v___x_4764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3(lean_object* v_nExtra_4765_, uint8_t v___x_4766_, uint8_t v___x_4767_, lean_object* v_alts_4768_, lean_object* v_toMatcherInfo_4769_, lean_object* v_matcherName_4770_, lean_object* v_params_4771_, lean_object* v_matcherLevels_4772_, lean_object* v_motiveArgs_4773_, lean_object* v_body_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_){
_start:
{
lean_object* v___x_4780_; 
lean_inc(v_nExtra_4765_);
v___x_4780_ = l_Lean_Meta_arrowDomainsN(v_nExtra_4765_, v_body_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_);
if (lean_obj_tag(v___x_4780_) == 0)
{
lean_object* v_a_4781_; lean_object* v___x_4782_; uint8_t v___x_4783_; lean_object* v___x_4784_; 
v_a_4781_ = lean_ctor_get(v___x_4780_, 0);
lean_inc(v_a_4781_);
lean_dec_ref(v___x_4780_);
v___x_4782_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0, &l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0);
v___x_4783_ = 1;
v___x_4784_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_4773_, v___x_4782_, v___x_4766_, v___x_4767_, v___x_4766_, v___x_4767_, v___x_4783_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_);
if (lean_obj_tag(v___x_4784_) == 0)
{
lean_object* v_a_4785_; size_t v_sz_4786_; size_t v___x_4787_; lean_object* v___x_4788_; 
v_a_4785_ = lean_ctor_get(v___x_4784_, 0);
lean_inc(v_a_4785_);
lean_dec_ref(v___x_4784_);
v_sz_4786_ = lean_array_size(v_alts_4768_);
v___x_4787_ = ((size_t)0ULL);
v___x_4788_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(v_nExtra_4765_, v_sz_4786_, v___x_4787_, v_alts_4768_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_);
if (lean_obj_tag(v___x_4788_) == 0)
{
lean_object* v_a_4789_; lean_object* v_matcherLevels_4791_; lean_object* v___y_4792_; lean_object* v___y_4793_; lean_object* v_uElimPos_x3f_4798_; 
v_a_4789_ = lean_ctor_get(v___x_4788_, 0);
lean_inc(v_a_4789_);
lean_dec_ref(v___x_4788_);
v_uElimPos_x3f_4798_ = lean_ctor_get(v_toMatcherInfo_4769_, 3);
if (lean_obj_tag(v_uElimPos_x3f_4798_) == 0)
{
v_matcherLevels_4791_ = v_matcherLevels_4772_;
v___y_4792_ = v___y_4777_;
v___y_4793_ = v___y_4778_;
goto v___jp_4790_;
}
else
{
lean_object* v_val_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; 
v_val_4799_ = lean_ctor_get(v_uElimPos_x3f_4798_, 0);
v___x_4800_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1, &l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1);
v___x_4801_ = lean_array_set(v_matcherLevels_4772_, v_val_4799_, v___x_4800_);
v_matcherLevels_4791_ = v___x_4801_;
v___y_4792_ = v___y_4777_;
v___y_4793_ = v___y_4778_;
goto v___jp_4790_;
}
v___jp_4790_:
{
lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; 
v___x_4794_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_4795_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4795_, 0, v_toMatcherInfo_4769_);
lean_ctor_set(v___x_4795_, 1, v_matcherName_4770_);
lean_ctor_set(v___x_4795_, 2, v_matcherLevels_4791_);
lean_ctor_set(v___x_4795_, 3, v_params_4771_);
lean_ctor_set(v___x_4795_, 4, v_a_4785_);
lean_ctor_set(v___x_4795_, 5, v_motiveArgs_4773_);
lean_ctor_set(v___x_4795_, 6, v_a_4789_);
lean_ctor_set(v___x_4795_, 7, v___x_4794_);
v___x_4796_ = l_Lean_Meta_MatcherApp_toExpr(v___x_4795_);
v___x_4797_ = l_Lean_mkArrowN(v_a_4781_, v___x_4796_, v___y_4792_, v___y_4793_);
lean_dec(v_a_4781_);
return v___x_4797_;
}
}
else
{
lean_object* v_a_4802_; lean_object* v___x_4804_; uint8_t v_isShared_4805_; uint8_t v_isSharedCheck_4809_; 
lean_dec(v_a_4785_);
lean_dec(v_a_4781_);
lean_dec_ref(v_motiveArgs_4773_);
lean_dec_ref(v_matcherLevels_4772_);
lean_dec_ref(v_params_4771_);
lean_dec(v_matcherName_4770_);
lean_dec_ref(v_toMatcherInfo_4769_);
v_a_4802_ = lean_ctor_get(v___x_4788_, 0);
v_isSharedCheck_4809_ = !lean_is_exclusive(v___x_4788_);
if (v_isSharedCheck_4809_ == 0)
{
v___x_4804_ = v___x_4788_;
v_isShared_4805_ = v_isSharedCheck_4809_;
goto v_resetjp_4803_;
}
else
{
lean_inc(v_a_4802_);
lean_dec(v___x_4788_);
v___x_4804_ = lean_box(0);
v_isShared_4805_ = v_isSharedCheck_4809_;
goto v_resetjp_4803_;
}
v_resetjp_4803_:
{
lean_object* v___x_4807_; 
if (v_isShared_4805_ == 0)
{
v___x_4807_ = v___x_4804_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v_a_4802_);
v___x_4807_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
return v___x_4807_;
}
}
}
}
else
{
lean_dec(v_a_4781_);
lean_dec_ref(v_motiveArgs_4773_);
lean_dec_ref(v_matcherLevels_4772_);
lean_dec_ref(v_params_4771_);
lean_dec(v_matcherName_4770_);
lean_dec_ref(v_toMatcherInfo_4769_);
lean_dec_ref(v_alts_4768_);
lean_dec(v_nExtra_4765_);
return v___x_4784_;
}
}
else
{
lean_object* v_a_4810_; lean_object* v___x_4812_; uint8_t v_isShared_4813_; uint8_t v_isSharedCheck_4817_; 
lean_dec_ref(v_motiveArgs_4773_);
lean_dec_ref(v_matcherLevels_4772_);
lean_dec_ref(v_params_4771_);
lean_dec(v_matcherName_4770_);
lean_dec_ref(v_toMatcherInfo_4769_);
lean_dec_ref(v_alts_4768_);
lean_dec(v_nExtra_4765_);
v_a_4810_ = lean_ctor_get(v___x_4780_, 0);
v_isSharedCheck_4817_ = !lean_is_exclusive(v___x_4780_);
if (v_isSharedCheck_4817_ == 0)
{
v___x_4812_ = v___x_4780_;
v_isShared_4813_ = v_isSharedCheck_4817_;
goto v_resetjp_4811_;
}
else
{
lean_inc(v_a_4810_);
lean_dec(v___x_4780_);
v___x_4812_ = lean_box(0);
v_isShared_4813_ = v_isSharedCheck_4817_;
goto v_resetjp_4811_;
}
v_resetjp_4811_:
{
lean_object* v___x_4815_; 
if (v_isShared_4813_ == 0)
{
v___x_4815_ = v___x_4812_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4816_; 
v_reuseFailAlloc_4816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4816_, 0, v_a_4810_);
v___x_4815_ = v_reuseFailAlloc_4816_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
return v___x_4815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed(lean_object* v_nExtra_4818_, lean_object* v___x_4819_, lean_object* v___x_4820_, lean_object* v_alts_4821_, lean_object* v_toMatcherInfo_4822_, lean_object* v_matcherName_4823_, lean_object* v_params_4824_, lean_object* v_matcherLevels_4825_, lean_object* v_motiveArgs_4826_, lean_object* v_body_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_){
_start:
{
uint8_t v___x_32786__boxed_4833_; uint8_t v___x_32787__boxed_4834_; lean_object* v_res_4835_; 
v___x_32786__boxed_4833_ = lean_unbox(v___x_4819_);
v___x_32787__boxed_4834_ = lean_unbox(v___x_4820_);
v_res_4835_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__3(v_nExtra_4818_, v___x_32786__boxed_4833_, v___x_32787__boxed_4834_, v_alts_4821_, v_toMatcherInfo_4822_, v_matcherName_4823_, v_params_4824_, v_matcherLevels_4825_, v_motiveArgs_4826_, v_body_4827_, v___y_4828_, v___y_4829_, v___y_4830_, v___y_4831_);
lean_dec(v___y_4831_);
lean_dec_ref(v___y_4830_);
lean_dec(v___y_4829_);
lean_dec_ref(v___y_4828_);
return v_res_4835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(lean_object* v_k_4836_, lean_object* v_ys_4837_, lean_object* v_args_4838_, lean_object* v___mask_4839_, lean_object* v___bodyType_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_){
_start:
{
lean_object* v___x_4846_; 
lean_inc(v___y_4844_);
lean_inc_ref(v___y_4843_);
lean_inc(v___y_4842_);
lean_inc_ref(v___y_4841_);
v___x_4846_ = lean_apply_7(v_k_4836_, v_ys_4837_, v_args_4838_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_, lean_box(0));
return v___x_4846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed(lean_object* v_k_4847_, lean_object* v_ys_4848_, lean_object* v_args_4849_, lean_object* v___mask_4850_, lean_object* v___bodyType_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_){
_start:
{
lean_object* v_res_4857_; 
v_res_4857_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(v_k_4847_, v_ys_4848_, v_args_4849_, v___mask_4850_, v___bodyType_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_);
lean_dec(v___y_4855_);
lean_dec_ref(v___y_4854_);
lean_dec(v___y_4853_);
lean_dec_ref(v___y_4852_);
lean_dec_ref(v___bodyType_4851_);
lean_dec_ref(v___mask_4850_);
return v_res_4857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(lean_object* v_origAltType_4858_, lean_object* v_altInfo_4859_, lean_object* v_k_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_){
_start:
{
lean_object* v___f_4866_; lean_object* v___x_4867_; 
v___f_4866_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_4866_, 0, v_k_4860_);
v___x_4867_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_origAltType_4858_, v_altInfo_4859_, v___f_4866_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_);
if (lean_obj_tag(v___x_4867_) == 0)
{
lean_object* v_a_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4875_; 
v_a_4868_ = lean_ctor_get(v___x_4867_, 0);
v_isSharedCheck_4875_ = !lean_is_exclusive(v___x_4867_);
if (v_isSharedCheck_4875_ == 0)
{
v___x_4870_ = v___x_4867_;
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_a_4868_);
lean_dec(v___x_4867_);
v___x_4870_ = lean_box(0);
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
v_resetjp_4869_:
{
lean_object* v___x_4873_; 
if (v_isShared_4871_ == 0)
{
v___x_4873_ = v___x_4870_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v_a_4868_);
v___x_4873_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
return v___x_4873_;
}
}
}
else
{
lean_object* v_a_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4883_; 
v_a_4876_ = lean_ctor_get(v___x_4867_, 0);
v_isSharedCheck_4883_ = !lean_is_exclusive(v___x_4867_);
if (v_isSharedCheck_4883_ == 0)
{
v___x_4878_ = v___x_4867_;
v_isShared_4879_ = v_isSharedCheck_4883_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_a_4876_);
lean_dec(v___x_4867_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_4883_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
lean_object* v___x_4881_; 
if (v_isShared_4879_ == 0)
{
v___x_4881_ = v___x_4878_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4882_; 
v_reuseFailAlloc_4882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4882_, 0, v_a_4876_);
v___x_4881_ = v_reuseFailAlloc_4882_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
return v___x_4881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___boxed(lean_object* v_origAltType_4884_, lean_object* v_altInfo_4885_, lean_object* v_k_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_){
_start:
{
lean_object* v_res_4892_; 
v_res_4892_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v_origAltType_4884_, v_altInfo_4885_, v_k_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_);
lean_dec(v___y_4890_);
lean_dec_ref(v___y_4889_);
lean_dec(v___y_4888_);
lean_dec_ref(v___y_4887_);
return v_res_4892_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(lean_object* v___x_4893_, lean_object* v___x_4894_, lean_object* v___f_4895_, lean_object* v_fst_4896_, lean_object* v___x_4897_, lean_object* v___x_4898_, lean_object* v___x_4899_, lean_object* v___x_4900_, lean_object* v___x_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_){
_start:
{
lean_object* v___x_4907_; 
v___x_4907_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v___x_4893_, v___x_4894_, v___f_4895_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_);
if (lean_obj_tag(v___x_4907_) == 0)
{
lean_object* v_a_4908_; lean_object* v___x_4910_; uint8_t v_isShared_4911_; uint8_t v_isSharedCheck_4922_; 
v_a_4908_ = lean_ctor_get(v___x_4907_, 0);
v_isSharedCheck_4922_ = !lean_is_exclusive(v___x_4907_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4910_ = v___x_4907_;
v_isShared_4911_ = v_isSharedCheck_4922_;
goto v_resetjp_4909_;
}
else
{
lean_inc(v_a_4908_);
lean_dec(v___x_4907_);
v___x_4910_ = lean_box(0);
v_isShared_4911_ = v_isSharedCheck_4922_;
goto v_resetjp_4909_;
}
v_resetjp_4909_:
{
lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4920_; 
v___x_4912_ = lean_array_push(v_fst_4896_, v_a_4908_);
v___x_4913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4913_, 0, v___x_4897_);
lean_ctor_set(v___x_4913_, 1, v___x_4898_);
v___x_4914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4914_, 0, v___x_4899_);
lean_ctor_set(v___x_4914_, 1, v___x_4913_);
v___x_4915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4915_, 0, v___x_4900_);
lean_ctor_set(v___x_4915_, 1, v___x_4914_);
v___x_4916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4916_, 0, v___x_4901_);
lean_ctor_set(v___x_4916_, 1, v___x_4915_);
v___x_4917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4917_, 0, v___x_4912_);
lean_ctor_set(v___x_4917_, 1, v___x_4916_);
v___x_4918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4918_, 0, v___x_4917_);
if (v_isShared_4911_ == 0)
{
lean_ctor_set(v___x_4910_, 0, v___x_4918_);
v___x_4920_ = v___x_4910_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v___x_4918_);
v___x_4920_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
return v___x_4920_;
}
}
}
else
{
lean_object* v_a_4923_; lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_4930_; 
lean_dec_ref(v___x_4901_);
lean_dec_ref(v___x_4900_);
lean_dec_ref(v___x_4899_);
lean_dec_ref(v___x_4898_);
lean_dec_ref(v___x_4897_);
lean_dec(v_fst_4896_);
v_a_4923_ = lean_ctor_get(v___x_4907_, 0);
v_isSharedCheck_4930_ = !lean_is_exclusive(v___x_4907_);
if (v_isSharedCheck_4930_ == 0)
{
v___x_4925_ = v___x_4907_;
v_isShared_4926_ = v_isSharedCheck_4930_;
goto v_resetjp_4924_;
}
else
{
lean_inc(v_a_4923_);
lean_dec(v___x_4907_);
v___x_4925_ = lean_box(0);
v_isShared_4926_ = v_isSharedCheck_4930_;
goto v_resetjp_4924_;
}
v_resetjp_4924_:
{
lean_object* v___x_4928_; 
if (v_isShared_4926_ == 0)
{
v___x_4928_ = v___x_4925_;
goto v_reusejp_4927_;
}
else
{
lean_object* v_reuseFailAlloc_4929_; 
v_reuseFailAlloc_4929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4929_, 0, v_a_4923_);
v___x_4928_ = v_reuseFailAlloc_4929_;
goto v_reusejp_4927_;
}
v_reusejp_4927_:
{
return v___x_4928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed(lean_object* v___x_4931_, lean_object* v___x_4932_, lean_object* v___f_4933_, lean_object* v_fst_4934_, lean_object* v___x_4935_, lean_object* v___x_4936_, lean_object* v___x_4937_, lean_object* v___x_4938_, lean_object* v___x_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_){
_start:
{
lean_object* v_res_4945_; 
v_res_4945_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(v___x_4931_, v___x_4932_, v___f_4933_, v_fst_4934_, v___x_4935_, v___x_4936_, v___x_4937_, v___x_4938_, v___x_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_);
lean_dec(v___y_4943_);
lean_dec_ref(v___y_4942_);
lean_dec(v___y_4941_);
lean_dec_ref(v___y_4940_);
return v_res_4945_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0(void){
_start:
{
lean_object* v___x_4946_; 
v___x_4946_ = l_instMonadEIO(lean_box(0));
return v___x_4946_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(lean_object* v_msg_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_){
_start:
{
lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v_toApplicative_4959_; lean_object* v___x_4961_; uint8_t v_isShared_4962_; uint8_t v_isSharedCheck_5020_; 
v___x_4957_ = lean_obj_once(&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0, &l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0_once, _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0);
v___x_4958_ = l_StateRefT_x27_instMonad___redArg(v___x_4957_);
v_toApplicative_4959_ = lean_ctor_get(v___x_4958_, 0);
v_isSharedCheck_5020_ = !lean_is_exclusive(v___x_4958_);
if (v_isSharedCheck_5020_ == 0)
{
lean_object* v_unused_5021_; 
v_unused_5021_ = lean_ctor_get(v___x_4958_, 1);
lean_dec(v_unused_5021_);
v___x_4961_ = v___x_4958_;
v_isShared_4962_ = v_isSharedCheck_5020_;
goto v_resetjp_4960_;
}
else
{
lean_inc(v_toApplicative_4959_);
lean_dec(v___x_4958_);
v___x_4961_ = lean_box(0);
v_isShared_4962_ = v_isSharedCheck_5020_;
goto v_resetjp_4960_;
}
v_resetjp_4960_:
{
lean_object* v_toFunctor_4963_; lean_object* v_toSeq_4964_; lean_object* v_toSeqLeft_4965_; lean_object* v_toSeqRight_4966_; lean_object* v___x_4968_; uint8_t v_isShared_4969_; uint8_t v_isSharedCheck_5018_; 
v_toFunctor_4963_ = lean_ctor_get(v_toApplicative_4959_, 0);
v_toSeq_4964_ = lean_ctor_get(v_toApplicative_4959_, 2);
v_toSeqLeft_4965_ = lean_ctor_get(v_toApplicative_4959_, 3);
v_toSeqRight_4966_ = lean_ctor_get(v_toApplicative_4959_, 4);
v_isSharedCheck_5018_ = !lean_is_exclusive(v_toApplicative_4959_);
if (v_isSharedCheck_5018_ == 0)
{
lean_object* v_unused_5019_; 
v_unused_5019_ = lean_ctor_get(v_toApplicative_4959_, 1);
lean_dec(v_unused_5019_);
v___x_4968_ = v_toApplicative_4959_;
v_isShared_4969_ = v_isSharedCheck_5018_;
goto v_resetjp_4967_;
}
else
{
lean_inc(v_toSeqRight_4966_);
lean_inc(v_toSeqLeft_4965_);
lean_inc(v_toSeq_4964_);
lean_inc(v_toFunctor_4963_);
lean_dec(v_toApplicative_4959_);
v___x_4968_ = lean_box(0);
v_isShared_4969_ = v_isSharedCheck_5018_;
goto v_resetjp_4967_;
}
v_resetjp_4967_:
{
lean_object* v___f_4970_; lean_object* v___f_4971_; lean_object* v___f_4972_; lean_object* v___f_4973_; lean_object* v___x_4974_; lean_object* v___f_4975_; lean_object* v___f_4976_; lean_object* v___f_4977_; lean_object* v___x_4979_; 
v___f_4970_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__1));
v___f_4971_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__2));
lean_inc_ref(v_toFunctor_4963_);
v___f_4972_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4972_, 0, v_toFunctor_4963_);
v___f_4973_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4973_, 0, v_toFunctor_4963_);
v___x_4974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4974_, 0, v___f_4972_);
lean_ctor_set(v___x_4974_, 1, v___f_4973_);
v___f_4975_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4975_, 0, v_toSeqRight_4966_);
v___f_4976_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4976_, 0, v_toSeqLeft_4965_);
v___f_4977_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4977_, 0, v_toSeq_4964_);
if (v_isShared_4969_ == 0)
{
lean_ctor_set(v___x_4968_, 4, v___f_4975_);
lean_ctor_set(v___x_4968_, 3, v___f_4976_);
lean_ctor_set(v___x_4968_, 2, v___f_4977_);
lean_ctor_set(v___x_4968_, 1, v___f_4970_);
lean_ctor_set(v___x_4968_, 0, v___x_4974_);
v___x_4979_ = v___x_4968_;
goto v_reusejp_4978_;
}
else
{
lean_object* v_reuseFailAlloc_5017_; 
v_reuseFailAlloc_5017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5017_, 0, v___x_4974_);
lean_ctor_set(v_reuseFailAlloc_5017_, 1, v___f_4970_);
lean_ctor_set(v_reuseFailAlloc_5017_, 2, v___f_4977_);
lean_ctor_set(v_reuseFailAlloc_5017_, 3, v___f_4976_);
lean_ctor_set(v_reuseFailAlloc_5017_, 4, v___f_4975_);
v___x_4979_ = v_reuseFailAlloc_5017_;
goto v_reusejp_4978_;
}
v_reusejp_4978_:
{
lean_object* v___x_4981_; 
if (v_isShared_4962_ == 0)
{
lean_ctor_set(v___x_4961_, 1, v___f_4971_);
lean_ctor_set(v___x_4961_, 0, v___x_4979_);
v___x_4981_ = v___x_4961_;
goto v_reusejp_4980_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v___x_4979_);
lean_ctor_set(v_reuseFailAlloc_5016_, 1, v___f_4971_);
v___x_4981_ = v_reuseFailAlloc_5016_;
goto v_reusejp_4980_;
}
v_reusejp_4980_:
{
lean_object* v___x_4982_; lean_object* v_toApplicative_4983_; lean_object* v___x_4985_; uint8_t v_isShared_4986_; uint8_t v_isSharedCheck_5014_; 
v___x_4982_ = l_StateRefT_x27_instMonad___redArg(v___x_4981_);
v_toApplicative_4983_ = lean_ctor_get(v___x_4982_, 0);
v_isSharedCheck_5014_ = !lean_is_exclusive(v___x_4982_);
if (v_isSharedCheck_5014_ == 0)
{
lean_object* v_unused_5015_; 
v_unused_5015_ = lean_ctor_get(v___x_4982_, 1);
lean_dec(v_unused_5015_);
v___x_4985_ = v___x_4982_;
v_isShared_4986_ = v_isSharedCheck_5014_;
goto v_resetjp_4984_;
}
else
{
lean_inc(v_toApplicative_4983_);
lean_dec(v___x_4982_);
v___x_4985_ = lean_box(0);
v_isShared_4986_ = v_isSharedCheck_5014_;
goto v_resetjp_4984_;
}
v_resetjp_4984_:
{
lean_object* v_toFunctor_4987_; lean_object* v_toSeq_4988_; lean_object* v_toSeqLeft_4989_; lean_object* v_toSeqRight_4990_; lean_object* v___x_4992_; uint8_t v_isShared_4993_; uint8_t v_isSharedCheck_5012_; 
v_toFunctor_4987_ = lean_ctor_get(v_toApplicative_4983_, 0);
v_toSeq_4988_ = lean_ctor_get(v_toApplicative_4983_, 2);
v_toSeqLeft_4989_ = lean_ctor_get(v_toApplicative_4983_, 3);
v_toSeqRight_4990_ = lean_ctor_get(v_toApplicative_4983_, 4);
v_isSharedCheck_5012_ = !lean_is_exclusive(v_toApplicative_4983_);
if (v_isSharedCheck_5012_ == 0)
{
lean_object* v_unused_5013_; 
v_unused_5013_ = lean_ctor_get(v_toApplicative_4983_, 1);
lean_dec(v_unused_5013_);
v___x_4992_ = v_toApplicative_4983_;
v_isShared_4993_ = v_isSharedCheck_5012_;
goto v_resetjp_4991_;
}
else
{
lean_inc(v_toSeqRight_4990_);
lean_inc(v_toSeqLeft_4989_);
lean_inc(v_toSeq_4988_);
lean_inc(v_toFunctor_4987_);
lean_dec(v_toApplicative_4983_);
v___x_4992_ = lean_box(0);
v_isShared_4993_ = v_isSharedCheck_5012_;
goto v_resetjp_4991_;
}
v_resetjp_4991_:
{
lean_object* v___f_4994_; lean_object* v___f_4995_; lean_object* v___f_4996_; lean_object* v___f_4997_; lean_object* v___x_4998_; lean_object* v___f_4999_; lean_object* v___f_5000_; lean_object* v___f_5001_; lean_object* v___x_5003_; 
v___f_4994_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3));
v___f_4995_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4));
lean_inc_ref(v_toFunctor_4987_);
v___f_4996_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4996_, 0, v_toFunctor_4987_);
v___f_4997_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4997_, 0, v_toFunctor_4987_);
v___x_4998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4998_, 0, v___f_4996_);
lean_ctor_set(v___x_4998_, 1, v___f_4997_);
v___f_4999_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4999_, 0, v_toSeqRight_4990_);
v___f_5000_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5000_, 0, v_toSeqLeft_4989_);
v___f_5001_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5001_, 0, v_toSeq_4988_);
if (v_isShared_4993_ == 0)
{
lean_ctor_set(v___x_4992_, 4, v___f_4999_);
lean_ctor_set(v___x_4992_, 3, v___f_5000_);
lean_ctor_set(v___x_4992_, 2, v___f_5001_);
lean_ctor_set(v___x_4992_, 1, v___f_4994_);
lean_ctor_set(v___x_4992_, 0, v___x_4998_);
v___x_5003_ = v___x_4992_;
goto v_reusejp_5002_;
}
else
{
lean_object* v_reuseFailAlloc_5011_; 
v_reuseFailAlloc_5011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5011_, 0, v___x_4998_);
lean_ctor_set(v_reuseFailAlloc_5011_, 1, v___f_4994_);
lean_ctor_set(v_reuseFailAlloc_5011_, 2, v___f_5001_);
lean_ctor_set(v_reuseFailAlloc_5011_, 3, v___f_5000_);
lean_ctor_set(v_reuseFailAlloc_5011_, 4, v___f_4999_);
v___x_5003_ = v_reuseFailAlloc_5011_;
goto v_reusejp_5002_;
}
v_reusejp_5002_:
{
lean_object* v___x_5005_; 
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 1, v___f_4995_);
lean_ctor_set(v___x_4985_, 0, v___x_5003_);
v___x_5005_ = v___x_4985_;
goto v_reusejp_5004_;
}
else
{
lean_object* v_reuseFailAlloc_5010_; 
v_reuseFailAlloc_5010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5010_, 0, v___x_5003_);
lean_ctor_set(v_reuseFailAlloc_5010_, 1, v___f_4995_);
v___x_5005_ = v_reuseFailAlloc_5010_;
goto v_reusejp_5004_;
}
v_reusejp_5004_:
{
lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_27517__overap_5008_; lean_object* v___x_5009_; 
v___x_5006_ = l_Lean_instInhabitedExpr;
v___x_5007_ = l_instInhabitedOfMonad___redArg(v___x_5005_, v___x_5006_);
v___x_27517__overap_5008_ = lean_panic_fn_borrowed(v___x_5007_, v_msg_4951_);
lean_dec(v___x_5007_);
lean_inc(v___y_4955_);
lean_inc_ref(v___y_4954_);
lean_inc(v___y_4953_);
lean_inc_ref(v___y_4952_);
v___x_5009_ = lean_apply_5(v___x_27517__overap_5008_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_, lean_box(0));
return v___x_5009_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___boxed(lean_object* v_msg_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_){
_start:
{
lean_object* v_res_5028_; 
v_res_5028_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(v_msg_5022_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_);
lean_dec(v___y_5026_);
lean_dec_ref(v___y_5025_);
lean_dec(v___y_5024_);
lean_dec_ref(v___y_5023_);
return v_res_5028_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(lean_object* v_args_5029_, lean_object* v_ys_5030_, lean_object* v_ys2_5031_, lean_object* v_ys3_5032_, lean_object* v_onAlt_5033_, lean_object* v_a_5034_, uint8_t v___x_5035_, uint8_t v_useSplitter_5036_, lean_object* v___x_5037_, lean_object* v_ys4_5038_, lean_object* v_altType_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_){
_start:
{
lean_object* v___y_5046_; lean_object* v___x_5056_; lean_object* v___x_5057_; 
lean_inc_ref(v_args_5029_);
v___x_5056_ = l_Array_append___redArg(v_args_5029_, v_ys3_5032_);
v___x_5057_ = l_Lean_Meta_instantiateLambda(v___x_5037_, v___x_5056_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_);
lean_dec_ref(v___x_5056_);
if (lean_obj_tag(v___x_5057_) == 0)
{
v___y_5046_ = v___x_5057_;
goto v___jp_5045_;
}
else
{
lean_object* v_a_5058_; uint8_t v___y_5060_; uint8_t v___x_5063_; 
v_a_5058_ = lean_ctor_get(v___x_5057_, 0);
lean_inc(v_a_5058_);
v___x_5063_ = l_Lean_Exception_isInterrupt(v_a_5058_);
if (v___x_5063_ == 0)
{
uint8_t v___x_5064_; 
v___x_5064_ = l_Lean_Exception_isRuntime(v_a_5058_);
v___y_5060_ = v___x_5064_;
goto v___jp_5059_;
}
else
{
lean_dec(v_a_5058_);
v___y_5060_ = v___x_5063_;
goto v___jp_5059_;
}
v___jp_5059_:
{
if (v___y_5060_ == 0)
{
lean_object* v___x_5061_; lean_object* v___x_5062_; 
lean_dec_ref(v___x_5057_);
v___x_5061_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2);
v___x_5062_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_5061_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_);
v___y_5046_ = v___x_5062_;
goto v___jp_5045_;
}
else
{
v___y_5046_ = v___x_5057_;
goto v___jp_5045_;
}
}
}
v___jp_5045_:
{
if (lean_obj_tag(v___y_5046_) == 0)
{
lean_object* v_a_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; 
v_a_5047_ = lean_ctor_get(v___y_5046_, 0);
lean_inc(v_a_5047_);
lean_dec_ref(v___y_5046_);
lean_inc_ref(v_ys4_5038_);
lean_inc_ref(v_ys3_5032_);
lean_inc_ref(v_ys2_5031_);
lean_inc_ref(v_ys_5030_);
v___x_5048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5048_, 0, v_args_5029_);
lean_ctor_set(v___x_5048_, 1, v_ys_5030_);
lean_ctor_set(v___x_5048_, 2, v_ys2_5031_);
lean_ctor_set(v___x_5048_, 3, v_ys3_5032_);
lean_ctor_set(v___x_5048_, 4, v_ys4_5038_);
lean_inc(v___y_5043_);
lean_inc_ref(v___y_5042_);
lean_inc(v___y_5041_);
lean_inc_ref(v___y_5040_);
v___x_5049_ = lean_apply_9(v_onAlt_5033_, v_a_5034_, v_altType_5039_, v___x_5048_, v_a_5047_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_, lean_box(0));
if (lean_obj_tag(v___x_5049_) == 0)
{
lean_object* v_a_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; uint8_t v___x_5054_; lean_object* v___x_5055_; 
v_a_5050_ = lean_ctor_get(v___x_5049_, 0);
lean_inc(v_a_5050_);
lean_dec_ref(v___x_5049_);
v___x_5051_ = l_Array_append___redArg(v_ys_5030_, v_ys2_5031_);
lean_dec_ref(v_ys2_5031_);
v___x_5052_ = l_Array_append___redArg(v___x_5051_, v_ys3_5032_);
lean_dec_ref(v_ys3_5032_);
v___x_5053_ = l_Array_append___redArg(v___x_5052_, v_ys4_5038_);
lean_dec_ref(v_ys4_5038_);
v___x_5054_ = 1;
v___x_5055_ = l_Lean_Meta_mkLambdaFVars(v___x_5053_, v_a_5050_, v___x_5035_, v_useSplitter_5036_, v___x_5035_, v_useSplitter_5036_, v___x_5054_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_);
lean_dec_ref(v___x_5053_);
return v___x_5055_;
}
else
{
lean_dec_ref(v_ys4_5038_);
lean_dec_ref(v_ys3_5032_);
lean_dec_ref(v_ys2_5031_);
lean_dec_ref(v_ys_5030_);
return v___x_5049_;
}
}
else
{
lean_dec_ref(v_altType_5039_);
lean_dec_ref(v_ys4_5038_);
lean_dec(v_a_5034_);
lean_dec_ref(v_onAlt_5033_);
lean_dec_ref(v_ys3_5032_);
lean_dec_ref(v_ys2_5031_);
lean_dec_ref(v_ys_5030_);
lean_dec_ref(v_args_5029_);
return v___y_5046_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed(lean_object* v_args_5065_, lean_object* v_ys_5066_, lean_object* v_ys2_5067_, lean_object* v_ys3_5068_, lean_object* v_onAlt_5069_, lean_object* v_a_5070_, lean_object* v___x_5071_, lean_object* v_useSplitter_5072_, lean_object* v___x_5073_, lean_object* v_ys4_5074_, lean_object* v_altType_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_){
_start:
{
uint8_t v___x_33178__boxed_5081_; uint8_t v_useSplitter_boxed_5082_; lean_object* v_res_5083_; 
v___x_33178__boxed_5081_ = lean_unbox(v___x_5071_);
v_useSplitter_boxed_5082_ = lean_unbox(v_useSplitter_5072_);
v_res_5083_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(v_args_5065_, v_ys_5066_, v_ys2_5067_, v_ys3_5068_, v_onAlt_5069_, v_a_5070_, v___x_33178__boxed_5081_, v_useSplitter_boxed_5082_, v___x_5073_, v_ys4_5074_, v_altType_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_);
lean_dec(v___y_5079_);
lean_dec_ref(v___y_5078_);
lean_dec(v___y_5077_);
lean_dec_ref(v___y_5076_);
return v_res_5083_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(lean_object* v_args_5084_, lean_object* v_ys_5085_, lean_object* v_ys2_5086_, lean_object* v_onAlt_5087_, lean_object* v_a_5088_, uint8_t v___x_5089_, uint8_t v_useSplitter_5090_, lean_object* v___x_5091_, lean_object* v_extraEqualities_5092_, lean_object* v_ys3_5093_, lean_object* v_altType_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_){
_start:
{
lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___f_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; 
v___x_5100_ = lean_box(v___x_5089_);
v___x_5101_ = lean_box(v_useSplitter_5090_);
v___f_5102_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed), 16, 9);
lean_closure_set(v___f_5102_, 0, v_args_5084_);
lean_closure_set(v___f_5102_, 1, v_ys_5085_);
lean_closure_set(v___f_5102_, 2, v_ys2_5086_);
lean_closure_set(v___f_5102_, 3, v_ys3_5093_);
lean_closure_set(v___f_5102_, 4, v_onAlt_5087_);
lean_closure_set(v___f_5102_, 5, v_a_5088_);
lean_closure_set(v___f_5102_, 6, v___x_5100_);
lean_closure_set(v___f_5102_, 7, v___x_5101_);
lean_closure_set(v___f_5102_, 8, v___x_5091_);
v___x_5103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5103_, 0, v_extraEqualities_5092_);
v___x_5104_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_5094_, v___x_5103_, v___f_5102_, v___x_5089_, v___x_5089_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_);
return v___x_5104_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed(lean_object* v_args_5105_, lean_object* v_ys_5106_, lean_object* v_ys2_5107_, lean_object* v_onAlt_5108_, lean_object* v_a_5109_, lean_object* v___x_5110_, lean_object* v_useSplitter_5111_, lean_object* v___x_5112_, lean_object* v_extraEqualities_5113_, lean_object* v_ys3_5114_, lean_object* v_altType_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_){
_start:
{
uint8_t v___x_33243__boxed_5121_; uint8_t v_useSplitter_boxed_5122_; lean_object* v_res_5123_; 
v___x_33243__boxed_5121_ = lean_unbox(v___x_5110_);
v_useSplitter_boxed_5122_ = lean_unbox(v_useSplitter_5111_);
v_res_5123_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(v_args_5105_, v_ys_5106_, v_ys2_5107_, v_onAlt_5108_, v_a_5109_, v___x_33243__boxed_5121_, v_useSplitter_boxed_5122_, v___x_5112_, v_extraEqualities_5113_, v_ys3_5114_, v_altType_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_);
lean_dec(v___y_5119_);
lean_dec_ref(v___y_5118_);
lean_dec(v___y_5117_);
lean_dec_ref(v___y_5116_);
return v_res_5123_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(lean_object* v_args_5124_, lean_object* v_ys_5125_, lean_object* v_onAlt_5126_, lean_object* v_a_5127_, uint8_t v___x_5128_, uint8_t v_useSplitter_5129_, lean_object* v___x_5130_, lean_object* v_extraEqualities_5131_, lean_object* v_numDiscrEqs_5132_, lean_object* v_ys2_5133_, lean_object* v_altType_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_){
_start:
{
lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___f_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; 
v___x_5140_ = lean_box(v___x_5128_);
v___x_5141_ = lean_box(v_useSplitter_5129_);
v___f_5142_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_5142_, 0, v_args_5124_);
lean_closure_set(v___f_5142_, 1, v_ys_5125_);
lean_closure_set(v___f_5142_, 2, v_ys2_5133_);
lean_closure_set(v___f_5142_, 3, v_onAlt_5126_);
lean_closure_set(v___f_5142_, 4, v_a_5127_);
lean_closure_set(v___f_5142_, 5, v___x_5140_);
lean_closure_set(v___f_5142_, 6, v___x_5141_);
lean_closure_set(v___f_5142_, 7, v___x_5130_);
lean_closure_set(v___f_5142_, 8, v_extraEqualities_5131_);
v___x_5143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5143_, 0, v_numDiscrEqs_5132_);
v___x_5144_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_5134_, v___x_5143_, v___f_5142_, v___x_5128_, v___x_5128_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_);
return v___x_5144_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed(lean_object* v_args_5145_, lean_object* v_ys_5146_, lean_object* v_onAlt_5147_, lean_object* v_a_5148_, lean_object* v___x_5149_, lean_object* v_useSplitter_5150_, lean_object* v___x_5151_, lean_object* v_extraEqualities_5152_, lean_object* v_numDiscrEqs_5153_, lean_object* v_ys2_5154_, lean_object* v_altType_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_){
_start:
{
uint8_t v___x_33274__boxed_5161_; uint8_t v_useSplitter_boxed_5162_; lean_object* v_res_5163_; 
v___x_33274__boxed_5161_ = lean_unbox(v___x_5149_);
v_useSplitter_boxed_5162_ = lean_unbox(v_useSplitter_5150_);
v_res_5163_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(v_args_5145_, v_ys_5146_, v_onAlt_5147_, v_a_5148_, v___x_33274__boxed_5161_, v_useSplitter_boxed_5162_, v___x_5151_, v_extraEqualities_5152_, v_numDiscrEqs_5153_, v_ys2_5154_, v_altType_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_);
lean_dec(v___y_5159_);
lean_dec_ref(v___y_5158_);
lean_dec(v___y_5157_);
lean_dec_ref(v___y_5156_);
return v_res_5163_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(lean_object* v___x_5164_, lean_object* v___x_5165_, lean_object* v_onAlt_5166_, lean_object* v_a_5167_, uint8_t v___x_5168_, uint8_t v_useSplitter_5169_, lean_object* v___x_5170_, lean_object* v_extraEqualities_5171_, lean_object* v_numDiscrEqs_5172_, uint8_t v_hasUnitThunk_5173_, lean_object* v___x_5174_, lean_object* v_ys_5175_, lean_object* v_args_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_){
_start:
{
lean_object* v_numFields_5182_; lean_object* v_numOverlaps_5183_; uint8_t v_hasUnitThunk_5184_; lean_object* v___x_5185_; uint8_t v___x_5186_; 
v_numFields_5182_ = lean_ctor_get(v___x_5164_, 0);
v_numOverlaps_5183_ = lean_ctor_get(v___x_5164_, 1);
v_hasUnitThunk_5184_ = lean_ctor_get_uint8(v___x_5164_, sizeof(void*)*2);
v___x_5185_ = lean_array_get_size(v_ys_5175_);
v___x_5186_ = lean_nat_dec_eq(v___x_5185_, v_numFields_5182_);
if (v___x_5186_ == 0)
{
lean_object* v___x_5187_; lean_object* v___x_5188_; 
lean_dec_ref(v_args_5176_);
lean_dec_ref(v_ys_5175_);
lean_dec(v_numDiscrEqs_5172_);
lean_dec(v_extraEqualities_5171_);
lean_dec_ref(v___x_5170_);
lean_dec(v_a_5167_);
lean_dec_ref(v_onAlt_5166_);
lean_dec_ref(v___x_5165_);
v___x_5187_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3);
v___x_5188_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(v___x_5187_, v___y_5177_, v___y_5178_, v___y_5179_, v___y_5180_);
return v___x_5188_;
}
else
{
lean_object* v___x_5189_; 
v___x_5189_ = l_Lean_Meta_instantiateForall(v___x_5165_, v_ys_5175_, v___y_5177_, v___y_5178_, v___y_5179_, v___y_5180_);
if (lean_obj_tag(v___x_5189_) == 0)
{
lean_object* v_a_5190_; lean_object* v___x_5192_; uint8_t v_isShared_5193_; uint8_t v_isSharedCheck_5219_; 
v_a_5190_ = lean_ctor_get(v___x_5189_, 0);
v_isSharedCheck_5219_ = !lean_is_exclusive(v___x_5189_);
if (v_isSharedCheck_5219_ == 0)
{
v___x_5192_ = v___x_5189_;
v_isShared_5193_ = v_isSharedCheck_5219_;
goto v_resetjp_5191_;
}
else
{
lean_inc(v_a_5190_);
lean_dec(v___x_5189_);
v___x_5192_ = lean_box(0);
v_isShared_5193_ = v_isSharedCheck_5219_;
goto v_resetjp_5191_;
}
v_resetjp_5191_:
{
lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___f_5196_; lean_object* v_altType_5198_; lean_object* v___y_5199_; lean_object* v___y_5200_; lean_object* v___y_5201_; lean_object* v___y_5202_; 
v___x_5194_ = lean_box(v___x_5168_);
v___x_5195_ = lean_box(v_useSplitter_5169_);
v___f_5196_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed), 16, 9);
lean_closure_set(v___f_5196_, 0, v_args_5176_);
lean_closure_set(v___f_5196_, 1, v_ys_5175_);
lean_closure_set(v___f_5196_, 2, v_onAlt_5166_);
lean_closure_set(v___f_5196_, 3, v_a_5167_);
lean_closure_set(v___f_5196_, 4, v___x_5194_);
lean_closure_set(v___f_5196_, 5, v___x_5195_);
lean_closure_set(v___f_5196_, 6, v___x_5170_);
lean_closure_set(v___f_5196_, 7, v_extraEqualities_5171_);
lean_closure_set(v___f_5196_, 8, v_numDiscrEqs_5172_);
if (v_hasUnitThunk_5173_ == 0)
{
v_altType_5198_ = v_a_5190_;
v___y_5199_ = v___y_5177_;
v___y_5200_ = v___y_5178_;
v___y_5201_ = v___y_5179_;
v___y_5202_ = v___y_5180_;
goto v___jp_5197_;
}
else
{
lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; 
v___x_5214_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2);
v___x_5215_ = lean_mk_empty_array_with_capacity(v___x_5174_);
v___x_5216_ = lean_array_push(v___x_5215_, v___x_5214_);
v___x_5217_ = l_Lean_Meta_instantiateForall(v_a_5190_, v___x_5216_, v___y_5177_, v___y_5178_, v___y_5179_, v___y_5180_);
lean_dec_ref(v___x_5216_);
if (lean_obj_tag(v___x_5217_) == 0)
{
lean_object* v_a_5218_; 
v_a_5218_ = lean_ctor_get(v___x_5217_, 0);
lean_inc(v_a_5218_);
lean_dec_ref(v___x_5217_);
v_altType_5198_ = v_a_5218_;
v___y_5199_ = v___y_5177_;
v___y_5200_ = v___y_5178_;
v___y_5201_ = v___y_5179_;
v___y_5202_ = v___y_5180_;
goto v___jp_5197_;
}
else
{
lean_dec_ref(v___f_5196_);
lean_del_object(v___x_5192_);
return v___x_5217_;
}
}
v___jp_5197_:
{
lean_object* v___x_5204_; 
lean_inc(v_numOverlaps_5183_);
if (v_isShared_5193_ == 0)
{
lean_ctor_set_tag(v___x_5192_, 1);
lean_ctor_set(v___x_5192_, 0, v_numOverlaps_5183_);
v___x_5204_ = v___x_5192_;
goto v_reusejp_5203_;
}
else
{
lean_object* v_reuseFailAlloc_5213_; 
v_reuseFailAlloc_5213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5213_, 0, v_numOverlaps_5183_);
v___x_5204_ = v_reuseFailAlloc_5213_;
goto v_reusejp_5203_;
}
v_reusejp_5203_:
{
lean_object* v___x_5205_; 
v___x_5205_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_5198_, v___x_5204_, v___f_5196_, v___x_5168_, v___x_5168_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_);
if (lean_obj_tag(v___x_5205_) == 0)
{
if (v_hasUnitThunk_5184_ == 0)
{
return v___x_5205_;
}
else
{
lean_object* v_a_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; 
v_a_5206_ = lean_ctor_get(v___x_5205_, 0);
lean_inc(v_a_5206_);
lean_dec_ref(v___x_5205_);
v___x_5207_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__2));
v___x_5208_ = lean_unsigned_to_nat(2u);
v___x_5209_ = lean_mk_empty_array_with_capacity(v___x_5208_);
lean_dec_ref(v___x_5209_);
v___x_5210_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6);
v___x_5211_ = lean_array_push(v___x_5210_, v_a_5206_);
v___x_5212_ = l_Lean_Meta_mkAppM(v___x_5207_, v___x_5211_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_);
return v___x_5212_;
}
}
else
{
return v___x_5205_;
}
}
}
}
}
else
{
lean_dec_ref(v_args_5176_);
lean_dec_ref(v_ys_5175_);
lean_dec(v_numDiscrEqs_5172_);
lean_dec(v_extraEqualities_5171_);
lean_dec_ref(v___x_5170_);
lean_dec(v_a_5167_);
lean_dec_ref(v_onAlt_5166_);
return v___x_5189_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_5220_ = _args[0];
lean_object* v___x_5221_ = _args[1];
lean_object* v_onAlt_5222_ = _args[2];
lean_object* v_a_5223_ = _args[3];
lean_object* v___x_5224_ = _args[4];
lean_object* v_useSplitter_5225_ = _args[5];
lean_object* v___x_5226_ = _args[6];
lean_object* v_extraEqualities_5227_ = _args[7];
lean_object* v_numDiscrEqs_5228_ = _args[8];
lean_object* v_hasUnitThunk_5229_ = _args[9];
lean_object* v___x_5230_ = _args[10];
lean_object* v_ys_5231_ = _args[11];
lean_object* v_args_5232_ = _args[12];
lean_object* v___y_5233_ = _args[13];
lean_object* v___y_5234_ = _args[14];
lean_object* v___y_5235_ = _args[15];
lean_object* v___y_5236_ = _args[16];
lean_object* v___y_5237_ = _args[17];
_start:
{
uint8_t v___x_33339__boxed_5238_; uint8_t v_useSplitter_boxed_5239_; uint8_t v_hasUnitThunk_boxed_5240_; lean_object* v_res_5241_; 
v___x_33339__boxed_5238_ = lean_unbox(v___x_5224_);
v_useSplitter_boxed_5239_ = lean_unbox(v_useSplitter_5225_);
v_hasUnitThunk_boxed_5240_ = lean_unbox(v_hasUnitThunk_5229_);
v_res_5241_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(v___x_5220_, v___x_5221_, v_onAlt_5222_, v_a_5223_, v___x_33339__boxed_5238_, v_useSplitter_boxed_5239_, v___x_5226_, v_extraEqualities_5227_, v_numDiscrEqs_5228_, v_hasUnitThunk_boxed_5240_, v___x_5230_, v_ys_5231_, v_args_5232_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_);
lean_dec(v___y_5236_);
lean_dec_ref(v___y_5235_);
lean_dec(v___y_5234_);
lean_dec_ref(v___y_5233_);
lean_dec(v___x_5230_);
lean_dec_ref(v___x_5220_);
return v_res_5241_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(lean_object* v___x_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_){
_start:
{
lean_object* v___x_5248_; 
v___x_5248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5248_, 0, v___x_5242_);
return v___x_5248_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed(lean_object* v___x_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_){
_start:
{
lean_object* v_res_5255_; 
v_res_5255_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(v___x_5249_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_);
lean_dec(v___y_5253_);
lean_dec_ref(v___y_5252_);
lean_dec(v___y_5251_);
lean_dec_ref(v___y_5250_);
return v_res_5255_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(lean_object* v_msg_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_){
_start:
{
lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v_toApplicative_5264_; lean_object* v___x_5266_; uint8_t v_isShared_5267_; uint8_t v_isSharedCheck_5325_; 
v___x_5262_ = lean_obj_once(&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0, &l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0_once, _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0);
v___x_5263_ = l_StateRefT_x27_instMonad___redArg(v___x_5262_);
v_toApplicative_5264_ = lean_ctor_get(v___x_5263_, 0);
v_isSharedCheck_5325_ = !lean_is_exclusive(v___x_5263_);
if (v_isSharedCheck_5325_ == 0)
{
lean_object* v_unused_5326_; 
v_unused_5326_ = lean_ctor_get(v___x_5263_, 1);
lean_dec(v_unused_5326_);
v___x_5266_ = v___x_5263_;
v_isShared_5267_ = v_isSharedCheck_5325_;
goto v_resetjp_5265_;
}
else
{
lean_inc(v_toApplicative_5264_);
lean_dec(v___x_5263_);
v___x_5266_ = lean_box(0);
v_isShared_5267_ = v_isSharedCheck_5325_;
goto v_resetjp_5265_;
}
v_resetjp_5265_:
{
lean_object* v_toFunctor_5268_; lean_object* v_toSeq_5269_; lean_object* v_toSeqLeft_5270_; lean_object* v_toSeqRight_5271_; lean_object* v___x_5273_; uint8_t v_isShared_5274_; uint8_t v_isSharedCheck_5323_; 
v_toFunctor_5268_ = lean_ctor_get(v_toApplicative_5264_, 0);
v_toSeq_5269_ = lean_ctor_get(v_toApplicative_5264_, 2);
v_toSeqLeft_5270_ = lean_ctor_get(v_toApplicative_5264_, 3);
v_toSeqRight_5271_ = lean_ctor_get(v_toApplicative_5264_, 4);
v_isSharedCheck_5323_ = !lean_is_exclusive(v_toApplicative_5264_);
if (v_isSharedCheck_5323_ == 0)
{
lean_object* v_unused_5324_; 
v_unused_5324_ = lean_ctor_get(v_toApplicative_5264_, 1);
lean_dec(v_unused_5324_);
v___x_5273_ = v_toApplicative_5264_;
v_isShared_5274_ = v_isSharedCheck_5323_;
goto v_resetjp_5272_;
}
else
{
lean_inc(v_toSeqRight_5271_);
lean_inc(v_toSeqLeft_5270_);
lean_inc(v_toSeq_5269_);
lean_inc(v_toFunctor_5268_);
lean_dec(v_toApplicative_5264_);
v___x_5273_ = lean_box(0);
v_isShared_5274_ = v_isSharedCheck_5323_;
goto v_resetjp_5272_;
}
v_resetjp_5272_:
{
lean_object* v___f_5275_; lean_object* v___f_5276_; lean_object* v___f_5277_; lean_object* v___f_5278_; lean_object* v___x_5279_; lean_object* v___f_5280_; lean_object* v___f_5281_; lean_object* v___f_5282_; lean_object* v___x_5284_; 
v___f_5275_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__1));
v___f_5276_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__2));
lean_inc_ref(v_toFunctor_5268_);
v___f_5277_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5277_, 0, v_toFunctor_5268_);
v___f_5278_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5278_, 0, v_toFunctor_5268_);
v___x_5279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5279_, 0, v___f_5277_);
lean_ctor_set(v___x_5279_, 1, v___f_5278_);
v___f_5280_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5280_, 0, v_toSeqRight_5271_);
v___f_5281_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5281_, 0, v_toSeqLeft_5270_);
v___f_5282_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5282_, 0, v_toSeq_5269_);
if (v_isShared_5274_ == 0)
{
lean_ctor_set(v___x_5273_, 4, v___f_5280_);
lean_ctor_set(v___x_5273_, 3, v___f_5281_);
lean_ctor_set(v___x_5273_, 2, v___f_5282_);
lean_ctor_set(v___x_5273_, 1, v___f_5275_);
lean_ctor_set(v___x_5273_, 0, v___x_5279_);
v___x_5284_ = v___x_5273_;
goto v_reusejp_5283_;
}
else
{
lean_object* v_reuseFailAlloc_5322_; 
v_reuseFailAlloc_5322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5322_, 0, v___x_5279_);
lean_ctor_set(v_reuseFailAlloc_5322_, 1, v___f_5275_);
lean_ctor_set(v_reuseFailAlloc_5322_, 2, v___f_5282_);
lean_ctor_set(v_reuseFailAlloc_5322_, 3, v___f_5281_);
lean_ctor_set(v_reuseFailAlloc_5322_, 4, v___f_5280_);
v___x_5284_ = v_reuseFailAlloc_5322_;
goto v_reusejp_5283_;
}
v_reusejp_5283_:
{
lean_object* v___x_5286_; 
if (v_isShared_5267_ == 0)
{
lean_ctor_set(v___x_5266_, 1, v___f_5276_);
lean_ctor_set(v___x_5266_, 0, v___x_5284_);
v___x_5286_ = v___x_5266_;
goto v_reusejp_5285_;
}
else
{
lean_object* v_reuseFailAlloc_5321_; 
v_reuseFailAlloc_5321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5321_, 0, v___x_5284_);
lean_ctor_set(v_reuseFailAlloc_5321_, 1, v___f_5276_);
v___x_5286_ = v_reuseFailAlloc_5321_;
goto v_reusejp_5285_;
}
v_reusejp_5285_:
{
lean_object* v___x_5287_; lean_object* v_toApplicative_5288_; lean_object* v___x_5290_; uint8_t v_isShared_5291_; uint8_t v_isSharedCheck_5319_; 
v___x_5287_ = l_StateRefT_x27_instMonad___redArg(v___x_5286_);
v_toApplicative_5288_ = lean_ctor_get(v___x_5287_, 0);
v_isSharedCheck_5319_ = !lean_is_exclusive(v___x_5287_);
if (v_isSharedCheck_5319_ == 0)
{
lean_object* v_unused_5320_; 
v_unused_5320_ = lean_ctor_get(v___x_5287_, 1);
lean_dec(v_unused_5320_);
v___x_5290_ = v___x_5287_;
v_isShared_5291_ = v_isSharedCheck_5319_;
goto v_resetjp_5289_;
}
else
{
lean_inc(v_toApplicative_5288_);
lean_dec(v___x_5287_);
v___x_5290_ = lean_box(0);
v_isShared_5291_ = v_isSharedCheck_5319_;
goto v_resetjp_5289_;
}
v_resetjp_5289_:
{
lean_object* v_toFunctor_5292_; lean_object* v_toSeq_5293_; lean_object* v_toSeqLeft_5294_; lean_object* v_toSeqRight_5295_; lean_object* v___x_5297_; uint8_t v_isShared_5298_; uint8_t v_isSharedCheck_5317_; 
v_toFunctor_5292_ = lean_ctor_get(v_toApplicative_5288_, 0);
v_toSeq_5293_ = lean_ctor_get(v_toApplicative_5288_, 2);
v_toSeqLeft_5294_ = lean_ctor_get(v_toApplicative_5288_, 3);
v_toSeqRight_5295_ = lean_ctor_get(v_toApplicative_5288_, 4);
v_isSharedCheck_5317_ = !lean_is_exclusive(v_toApplicative_5288_);
if (v_isSharedCheck_5317_ == 0)
{
lean_object* v_unused_5318_; 
v_unused_5318_ = lean_ctor_get(v_toApplicative_5288_, 1);
lean_dec(v_unused_5318_);
v___x_5297_ = v_toApplicative_5288_;
v_isShared_5298_ = v_isSharedCheck_5317_;
goto v_resetjp_5296_;
}
else
{
lean_inc(v_toSeqRight_5295_);
lean_inc(v_toSeqLeft_5294_);
lean_inc(v_toSeq_5293_);
lean_inc(v_toFunctor_5292_);
lean_dec(v_toApplicative_5288_);
v___x_5297_ = lean_box(0);
v_isShared_5298_ = v_isSharedCheck_5317_;
goto v_resetjp_5296_;
}
v_resetjp_5296_:
{
lean_object* v___f_5299_; lean_object* v___f_5300_; lean_object* v___f_5301_; lean_object* v___f_5302_; lean_object* v___x_5303_; lean_object* v___f_5304_; lean_object* v___f_5305_; lean_object* v___f_5306_; lean_object* v___x_5308_; 
v___f_5299_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3));
v___f_5300_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4));
lean_inc_ref(v_toFunctor_5292_);
v___f_5301_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5301_, 0, v_toFunctor_5292_);
v___f_5302_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5302_, 0, v_toFunctor_5292_);
v___x_5303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5303_, 0, v___f_5301_);
lean_ctor_set(v___x_5303_, 1, v___f_5302_);
v___f_5304_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5304_, 0, v_toSeqRight_5295_);
v___f_5305_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5305_, 0, v_toSeqLeft_5294_);
v___f_5306_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5306_, 0, v_toSeq_5293_);
if (v_isShared_5298_ == 0)
{
lean_ctor_set(v___x_5297_, 4, v___f_5304_);
lean_ctor_set(v___x_5297_, 3, v___f_5305_);
lean_ctor_set(v___x_5297_, 2, v___f_5306_);
lean_ctor_set(v___x_5297_, 1, v___f_5299_);
lean_ctor_set(v___x_5297_, 0, v___x_5303_);
v___x_5308_ = v___x_5297_;
goto v_reusejp_5307_;
}
else
{
lean_object* v_reuseFailAlloc_5316_; 
v_reuseFailAlloc_5316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5316_, 0, v___x_5303_);
lean_ctor_set(v_reuseFailAlloc_5316_, 1, v___f_5299_);
lean_ctor_set(v_reuseFailAlloc_5316_, 2, v___f_5306_);
lean_ctor_set(v_reuseFailAlloc_5316_, 3, v___f_5305_);
lean_ctor_set(v_reuseFailAlloc_5316_, 4, v___f_5304_);
v___x_5308_ = v_reuseFailAlloc_5316_;
goto v_reusejp_5307_;
}
v_reusejp_5307_:
{
lean_object* v___x_5310_; 
if (v_isShared_5291_ == 0)
{
lean_ctor_set(v___x_5290_, 1, v___f_5300_);
lean_ctor_set(v___x_5290_, 0, v___x_5308_);
v___x_5310_ = v___x_5290_;
goto v_reusejp_5309_;
}
else
{
lean_object* v_reuseFailAlloc_5315_; 
v_reuseFailAlloc_5315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5315_, 0, v___x_5308_);
lean_ctor_set(v_reuseFailAlloc_5315_, 1, v___f_5300_);
v___x_5310_ = v_reuseFailAlloc_5315_;
goto v_reusejp_5309_;
}
v_reusejp_5309_:
{
lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_27505__overap_5313_; lean_object* v___x_5314_; 
v___x_5311_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7);
v___x_5312_ = l_instInhabitedOfMonad___redArg(v___x_5310_, v___x_5311_);
v___x_27505__overap_5313_ = lean_panic_fn_borrowed(v___x_5312_, v_msg_5256_);
lean_dec(v___x_5312_);
lean_inc(v___y_5260_);
lean_inc_ref(v___y_5259_);
lean_inc(v___y_5258_);
lean_inc_ref(v___y_5257_);
v___x_5314_ = lean_apply_5(v___x_27505__overap_5313_, v___y_5257_, v___y_5258_, v___y_5259_, v___y_5260_, lean_box(0));
return v___x_5314_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed(lean_object* v_msg_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_){
_start:
{
lean_object* v_res_5333_; 
v_res_5333_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(v_msg_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_);
lean_dec(v___y_5331_);
lean_dec_ref(v___y_5330_);
lean_dec(v___y_5329_);
lean_dec_ref(v___y_5328_);
return v_res_5333_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(lean_object* v_upperBound_5334_, lean_object* v_onAlt_5335_, uint8_t v_useSplitter_5336_, lean_object* v_extraEqualities_5337_, lean_object* v_numDiscrEqs_5338_, lean_object* v_a_5339_, lean_object* v_b_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_){
_start:
{
lean_object* v___y_5347_; uint8_t v___x_5370_; 
v___x_5370_ = lean_nat_dec_lt(v_a_5339_, v_upperBound_5334_);
if (v___x_5370_ == 0)
{
lean_object* v___x_5371_; 
lean_dec(v_a_5339_);
lean_dec(v_numDiscrEqs_5338_);
lean_dec(v_extraEqualities_5337_);
lean_dec_ref(v_onAlt_5335_);
v___x_5371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5371_, 0, v_b_5340_);
return v___x_5371_;
}
else
{
lean_object* v_snd_5372_; lean_object* v_snd_5373_; lean_object* v_snd_5374_; lean_object* v_snd_5375_; lean_object* v_snd_5376_; lean_object* v_fst_5377_; lean_object* v___x_5379_; uint8_t v_isShared_5380_; uint8_t v_isSharedCheck_5583_; 
v_snd_5372_ = lean_ctor_get(v_b_5340_, 1);
lean_inc(v_snd_5372_);
v_snd_5373_ = lean_ctor_get(v_snd_5372_, 1);
lean_inc(v_snd_5373_);
v_snd_5374_ = lean_ctor_get(v_snd_5373_, 1);
lean_inc(v_snd_5374_);
v_snd_5375_ = lean_ctor_get(v_snd_5374_, 1);
lean_inc(v_snd_5375_);
v_snd_5376_ = lean_ctor_get(v_snd_5375_, 1);
lean_inc(v_snd_5376_);
v_fst_5377_ = lean_ctor_get(v_b_5340_, 0);
v_isSharedCheck_5583_ = !lean_is_exclusive(v_b_5340_);
if (v_isSharedCheck_5583_ == 0)
{
lean_object* v_unused_5584_; 
v_unused_5584_ = lean_ctor_get(v_b_5340_, 1);
lean_dec(v_unused_5584_);
v___x_5379_ = v_b_5340_;
v_isShared_5380_ = v_isSharedCheck_5583_;
goto v_resetjp_5378_;
}
else
{
lean_inc(v_fst_5377_);
lean_dec(v_b_5340_);
v___x_5379_ = lean_box(0);
v_isShared_5380_ = v_isSharedCheck_5583_;
goto v_resetjp_5378_;
}
v_resetjp_5378_:
{
lean_object* v_fst_5381_; lean_object* v___x_5383_; uint8_t v_isShared_5384_; uint8_t v_isSharedCheck_5581_; 
v_fst_5381_ = lean_ctor_get(v_snd_5372_, 0);
v_isSharedCheck_5581_ = !lean_is_exclusive(v_snd_5372_);
if (v_isSharedCheck_5581_ == 0)
{
lean_object* v_unused_5582_; 
v_unused_5582_ = lean_ctor_get(v_snd_5372_, 1);
lean_dec(v_unused_5582_);
v___x_5383_ = v_snd_5372_;
v_isShared_5384_ = v_isSharedCheck_5581_;
goto v_resetjp_5382_;
}
else
{
lean_inc(v_fst_5381_);
lean_dec(v_snd_5372_);
v___x_5383_ = lean_box(0);
v_isShared_5384_ = v_isSharedCheck_5581_;
goto v_resetjp_5382_;
}
v_resetjp_5382_:
{
lean_object* v_fst_5385_; lean_object* v___x_5387_; uint8_t v_isShared_5388_; uint8_t v_isSharedCheck_5579_; 
v_fst_5385_ = lean_ctor_get(v_snd_5373_, 0);
v_isSharedCheck_5579_ = !lean_is_exclusive(v_snd_5373_);
if (v_isSharedCheck_5579_ == 0)
{
lean_object* v_unused_5580_; 
v_unused_5580_ = lean_ctor_get(v_snd_5373_, 1);
lean_dec(v_unused_5580_);
v___x_5387_ = v_snd_5373_;
v_isShared_5388_ = v_isSharedCheck_5579_;
goto v_resetjp_5386_;
}
else
{
lean_inc(v_fst_5385_);
lean_dec(v_snd_5373_);
v___x_5387_ = lean_box(0);
v_isShared_5388_ = v_isSharedCheck_5579_;
goto v_resetjp_5386_;
}
v_resetjp_5386_:
{
lean_object* v_fst_5389_; lean_object* v___x_5391_; uint8_t v_isShared_5392_; uint8_t v_isSharedCheck_5577_; 
v_fst_5389_ = lean_ctor_get(v_snd_5374_, 0);
v_isSharedCheck_5577_ = !lean_is_exclusive(v_snd_5374_);
if (v_isSharedCheck_5577_ == 0)
{
lean_object* v_unused_5578_; 
v_unused_5578_ = lean_ctor_get(v_snd_5374_, 1);
lean_dec(v_unused_5578_);
v___x_5391_ = v_snd_5374_;
v_isShared_5392_ = v_isSharedCheck_5577_;
goto v_resetjp_5390_;
}
else
{
lean_inc(v_fst_5389_);
lean_dec(v_snd_5374_);
v___x_5391_ = lean_box(0);
v_isShared_5392_ = v_isSharedCheck_5577_;
goto v_resetjp_5390_;
}
v_resetjp_5390_:
{
lean_object* v_fst_5393_; lean_object* v___x_5395_; uint8_t v_isShared_5396_; uint8_t v_isSharedCheck_5575_; 
v_fst_5393_ = lean_ctor_get(v_snd_5375_, 0);
v_isSharedCheck_5575_ = !lean_is_exclusive(v_snd_5375_);
if (v_isSharedCheck_5575_ == 0)
{
lean_object* v_unused_5576_; 
v_unused_5576_ = lean_ctor_get(v_snd_5375_, 1);
lean_dec(v_unused_5576_);
v___x_5395_ = v_snd_5375_;
v_isShared_5396_ = v_isSharedCheck_5575_;
goto v_resetjp_5394_;
}
else
{
lean_inc(v_fst_5393_);
lean_dec(v_snd_5375_);
v___x_5395_ = lean_box(0);
v_isShared_5396_ = v_isSharedCheck_5575_;
goto v_resetjp_5394_;
}
v_resetjp_5394_:
{
lean_object* v_array_5397_; lean_object* v_start_5398_; lean_object* v_stop_5399_; uint8_t v___x_5400_; 
v_array_5397_ = lean_ctor_get(v_snd_5376_, 0);
v_start_5398_ = lean_ctor_get(v_snd_5376_, 1);
v_stop_5399_ = lean_ctor_get(v_snd_5376_, 2);
v___x_5400_ = lean_nat_dec_lt(v_start_5398_, v_stop_5399_);
if (v___x_5400_ == 0)
{
lean_object* v___x_5402_; 
if (v_isShared_5396_ == 0)
{
v___x_5402_ = v___x_5395_;
goto v_reusejp_5401_;
}
else
{
lean_object* v_reuseFailAlloc_5417_; 
v_reuseFailAlloc_5417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5417_, 0, v_fst_5393_);
lean_ctor_set(v_reuseFailAlloc_5417_, 1, v_snd_5376_);
v___x_5402_ = v_reuseFailAlloc_5417_;
goto v_reusejp_5401_;
}
v_reusejp_5401_:
{
lean_object* v___x_5404_; 
if (v_isShared_5392_ == 0)
{
lean_ctor_set(v___x_5391_, 1, v___x_5402_);
v___x_5404_ = v___x_5391_;
goto v_reusejp_5403_;
}
else
{
lean_object* v_reuseFailAlloc_5416_; 
v_reuseFailAlloc_5416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5416_, 0, v_fst_5389_);
lean_ctor_set(v_reuseFailAlloc_5416_, 1, v___x_5402_);
v___x_5404_ = v_reuseFailAlloc_5416_;
goto v_reusejp_5403_;
}
v_reusejp_5403_:
{
lean_object* v___x_5406_; 
if (v_isShared_5388_ == 0)
{
lean_ctor_set(v___x_5387_, 1, v___x_5404_);
v___x_5406_ = v___x_5387_;
goto v_reusejp_5405_;
}
else
{
lean_object* v_reuseFailAlloc_5415_; 
v_reuseFailAlloc_5415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5415_, 0, v_fst_5385_);
lean_ctor_set(v_reuseFailAlloc_5415_, 1, v___x_5404_);
v___x_5406_ = v_reuseFailAlloc_5415_;
goto v_reusejp_5405_;
}
v_reusejp_5405_:
{
lean_object* v___x_5408_; 
if (v_isShared_5384_ == 0)
{
lean_ctor_set(v___x_5383_, 1, v___x_5406_);
v___x_5408_ = v___x_5383_;
goto v_reusejp_5407_;
}
else
{
lean_object* v_reuseFailAlloc_5414_; 
v_reuseFailAlloc_5414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5414_, 0, v_fst_5381_);
lean_ctor_set(v_reuseFailAlloc_5414_, 1, v___x_5406_);
v___x_5408_ = v_reuseFailAlloc_5414_;
goto v_reusejp_5407_;
}
v_reusejp_5407_:
{
lean_object* v___x_5410_; 
if (v_isShared_5380_ == 0)
{
lean_ctor_set(v___x_5379_, 1, v___x_5408_);
v___x_5410_ = v___x_5379_;
goto v_reusejp_5409_;
}
else
{
lean_object* v_reuseFailAlloc_5413_; 
v_reuseFailAlloc_5413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5413_, 0, v_fst_5377_);
lean_ctor_set(v_reuseFailAlloc_5413_, 1, v___x_5408_);
v___x_5410_ = v_reuseFailAlloc_5413_;
goto v_reusejp_5409_;
}
v_reusejp_5409_:
{
lean_object* v___x_5411_; lean_object* v___f_5412_; 
v___x_5411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5411_, 0, v___x_5410_);
v___f_5412_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5412_, 0, v___x_5411_);
v___y_5347_ = v___f_5412_;
goto v___jp_5346_;
}
}
}
}
}
}
else
{
lean_object* v___x_5419_; uint8_t v_isShared_5420_; uint8_t v_isSharedCheck_5571_; 
lean_inc(v_stop_5399_);
lean_inc(v_start_5398_);
lean_inc_ref(v_array_5397_);
v_isSharedCheck_5571_ = !lean_is_exclusive(v_snd_5376_);
if (v_isSharedCheck_5571_ == 0)
{
lean_object* v_unused_5572_; lean_object* v_unused_5573_; lean_object* v_unused_5574_; 
v_unused_5572_ = lean_ctor_get(v_snd_5376_, 2);
lean_dec(v_unused_5572_);
v_unused_5573_ = lean_ctor_get(v_snd_5376_, 1);
lean_dec(v_unused_5573_);
v_unused_5574_ = lean_ctor_get(v_snd_5376_, 0);
lean_dec(v_unused_5574_);
v___x_5419_ = v_snd_5376_;
v_isShared_5420_ = v_isSharedCheck_5571_;
goto v_resetjp_5418_;
}
else
{
lean_dec(v_snd_5376_);
v___x_5419_ = lean_box(0);
v_isShared_5420_ = v_isSharedCheck_5571_;
goto v_resetjp_5418_;
}
v_resetjp_5418_:
{
lean_object* v_array_5421_; lean_object* v_start_5422_; lean_object* v_stop_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5428_; 
v_array_5421_ = lean_ctor_get(v_fst_5393_, 0);
v_start_5422_ = lean_ctor_get(v_fst_5393_, 1);
v_stop_5423_ = lean_ctor_get(v_fst_5393_, 2);
v___x_5424_ = lean_array_fget(v_array_5397_, v_start_5398_);
v___x_5425_ = lean_unsigned_to_nat(1u);
v___x_5426_ = lean_nat_add(v_start_5398_, v___x_5425_);
lean_dec(v_start_5398_);
if (v_isShared_5420_ == 0)
{
lean_ctor_set(v___x_5419_, 1, v___x_5426_);
v___x_5428_ = v___x_5419_;
goto v_reusejp_5427_;
}
else
{
lean_object* v_reuseFailAlloc_5570_; 
v_reuseFailAlloc_5570_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5570_, 0, v_array_5397_);
lean_ctor_set(v_reuseFailAlloc_5570_, 1, v___x_5426_);
lean_ctor_set(v_reuseFailAlloc_5570_, 2, v_stop_5399_);
v___x_5428_ = v_reuseFailAlloc_5570_;
goto v_reusejp_5427_;
}
v_reusejp_5427_:
{
uint8_t v___x_5429_; 
v___x_5429_ = lean_nat_dec_lt(v_start_5422_, v_stop_5423_);
if (v___x_5429_ == 0)
{
lean_object* v___x_5431_; 
lean_dec(v___x_5424_);
if (v_isShared_5396_ == 0)
{
lean_ctor_set(v___x_5395_, 1, v___x_5428_);
v___x_5431_ = v___x_5395_;
goto v_reusejp_5430_;
}
else
{
lean_object* v_reuseFailAlloc_5446_; 
v_reuseFailAlloc_5446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5446_, 0, v_fst_5393_);
lean_ctor_set(v_reuseFailAlloc_5446_, 1, v___x_5428_);
v___x_5431_ = v_reuseFailAlloc_5446_;
goto v_reusejp_5430_;
}
v_reusejp_5430_:
{
lean_object* v___x_5433_; 
if (v_isShared_5392_ == 0)
{
lean_ctor_set(v___x_5391_, 1, v___x_5431_);
v___x_5433_ = v___x_5391_;
goto v_reusejp_5432_;
}
else
{
lean_object* v_reuseFailAlloc_5445_; 
v_reuseFailAlloc_5445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5445_, 0, v_fst_5389_);
lean_ctor_set(v_reuseFailAlloc_5445_, 1, v___x_5431_);
v___x_5433_ = v_reuseFailAlloc_5445_;
goto v_reusejp_5432_;
}
v_reusejp_5432_:
{
lean_object* v___x_5435_; 
if (v_isShared_5388_ == 0)
{
lean_ctor_set(v___x_5387_, 1, v___x_5433_);
v___x_5435_ = v___x_5387_;
goto v_reusejp_5434_;
}
else
{
lean_object* v_reuseFailAlloc_5444_; 
v_reuseFailAlloc_5444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5444_, 0, v_fst_5385_);
lean_ctor_set(v_reuseFailAlloc_5444_, 1, v___x_5433_);
v___x_5435_ = v_reuseFailAlloc_5444_;
goto v_reusejp_5434_;
}
v_reusejp_5434_:
{
lean_object* v___x_5437_; 
if (v_isShared_5384_ == 0)
{
lean_ctor_set(v___x_5383_, 1, v___x_5435_);
v___x_5437_ = v___x_5383_;
goto v_reusejp_5436_;
}
else
{
lean_object* v_reuseFailAlloc_5443_; 
v_reuseFailAlloc_5443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5443_, 0, v_fst_5381_);
lean_ctor_set(v_reuseFailAlloc_5443_, 1, v___x_5435_);
v___x_5437_ = v_reuseFailAlloc_5443_;
goto v_reusejp_5436_;
}
v_reusejp_5436_:
{
lean_object* v___x_5439_; 
if (v_isShared_5380_ == 0)
{
lean_ctor_set(v___x_5379_, 1, v___x_5437_);
v___x_5439_ = v___x_5379_;
goto v_reusejp_5438_;
}
else
{
lean_object* v_reuseFailAlloc_5442_; 
v_reuseFailAlloc_5442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5442_, 0, v_fst_5377_);
lean_ctor_set(v_reuseFailAlloc_5442_, 1, v___x_5437_);
v___x_5439_ = v_reuseFailAlloc_5442_;
goto v_reusejp_5438_;
}
v_reusejp_5438_:
{
lean_object* v___x_5440_; lean_object* v___f_5441_; 
v___x_5440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5440_, 0, v___x_5439_);
v___f_5441_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5441_, 0, v___x_5440_);
v___y_5347_ = v___f_5441_;
goto v___jp_5346_;
}
}
}
}
}
}
else
{
lean_object* v___x_5448_; uint8_t v_isShared_5449_; uint8_t v_isSharedCheck_5566_; 
lean_inc(v_stop_5423_);
lean_inc(v_start_5422_);
lean_inc_ref(v_array_5421_);
v_isSharedCheck_5566_ = !lean_is_exclusive(v_fst_5393_);
if (v_isSharedCheck_5566_ == 0)
{
lean_object* v_unused_5567_; lean_object* v_unused_5568_; lean_object* v_unused_5569_; 
v_unused_5567_ = lean_ctor_get(v_fst_5393_, 2);
lean_dec(v_unused_5567_);
v_unused_5568_ = lean_ctor_get(v_fst_5393_, 1);
lean_dec(v_unused_5568_);
v_unused_5569_ = lean_ctor_get(v_fst_5393_, 0);
lean_dec(v_unused_5569_);
v___x_5448_ = v_fst_5393_;
v_isShared_5449_ = v_isSharedCheck_5566_;
goto v_resetjp_5447_;
}
else
{
lean_dec(v_fst_5393_);
v___x_5448_ = lean_box(0);
v_isShared_5449_ = v_isSharedCheck_5566_;
goto v_resetjp_5447_;
}
v_resetjp_5447_:
{
lean_object* v_array_5450_; lean_object* v_start_5451_; lean_object* v_stop_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5456_; 
v_array_5450_ = lean_ctor_get(v_fst_5389_, 0);
v_start_5451_ = lean_ctor_get(v_fst_5389_, 1);
v_stop_5452_ = lean_ctor_get(v_fst_5389_, 2);
v___x_5453_ = lean_array_fget(v_array_5421_, v_start_5422_);
v___x_5454_ = lean_nat_add(v_start_5422_, v___x_5425_);
lean_dec(v_start_5422_);
if (v_isShared_5449_ == 0)
{
lean_ctor_set(v___x_5448_, 1, v___x_5454_);
v___x_5456_ = v___x_5448_;
goto v_reusejp_5455_;
}
else
{
lean_object* v_reuseFailAlloc_5565_; 
v_reuseFailAlloc_5565_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5565_, 0, v_array_5421_);
lean_ctor_set(v_reuseFailAlloc_5565_, 1, v___x_5454_);
lean_ctor_set(v_reuseFailAlloc_5565_, 2, v_stop_5423_);
v___x_5456_ = v_reuseFailAlloc_5565_;
goto v_reusejp_5455_;
}
v_reusejp_5455_:
{
uint8_t v___x_5457_; 
v___x_5457_ = lean_nat_dec_lt(v_start_5451_, v_stop_5452_);
if (v___x_5457_ == 0)
{
lean_object* v___x_5459_; 
lean_dec(v___x_5453_);
lean_dec(v___x_5424_);
if (v_isShared_5396_ == 0)
{
lean_ctor_set(v___x_5395_, 1, v___x_5428_);
lean_ctor_set(v___x_5395_, 0, v___x_5456_);
v___x_5459_ = v___x_5395_;
goto v_reusejp_5458_;
}
else
{
lean_object* v_reuseFailAlloc_5474_; 
v_reuseFailAlloc_5474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5474_, 0, v___x_5456_);
lean_ctor_set(v_reuseFailAlloc_5474_, 1, v___x_5428_);
v___x_5459_ = v_reuseFailAlloc_5474_;
goto v_reusejp_5458_;
}
v_reusejp_5458_:
{
lean_object* v___x_5461_; 
if (v_isShared_5392_ == 0)
{
lean_ctor_set(v___x_5391_, 1, v___x_5459_);
v___x_5461_ = v___x_5391_;
goto v_reusejp_5460_;
}
else
{
lean_object* v_reuseFailAlloc_5473_; 
v_reuseFailAlloc_5473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5473_, 0, v_fst_5389_);
lean_ctor_set(v_reuseFailAlloc_5473_, 1, v___x_5459_);
v___x_5461_ = v_reuseFailAlloc_5473_;
goto v_reusejp_5460_;
}
v_reusejp_5460_:
{
lean_object* v___x_5463_; 
if (v_isShared_5388_ == 0)
{
lean_ctor_set(v___x_5387_, 1, v___x_5461_);
v___x_5463_ = v___x_5387_;
goto v_reusejp_5462_;
}
else
{
lean_object* v_reuseFailAlloc_5472_; 
v_reuseFailAlloc_5472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5472_, 0, v_fst_5385_);
lean_ctor_set(v_reuseFailAlloc_5472_, 1, v___x_5461_);
v___x_5463_ = v_reuseFailAlloc_5472_;
goto v_reusejp_5462_;
}
v_reusejp_5462_:
{
lean_object* v___x_5465_; 
if (v_isShared_5384_ == 0)
{
lean_ctor_set(v___x_5383_, 1, v___x_5463_);
v___x_5465_ = v___x_5383_;
goto v_reusejp_5464_;
}
else
{
lean_object* v_reuseFailAlloc_5471_; 
v_reuseFailAlloc_5471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5471_, 0, v_fst_5381_);
lean_ctor_set(v_reuseFailAlloc_5471_, 1, v___x_5463_);
v___x_5465_ = v_reuseFailAlloc_5471_;
goto v_reusejp_5464_;
}
v_reusejp_5464_:
{
lean_object* v___x_5467_; 
if (v_isShared_5380_ == 0)
{
lean_ctor_set(v___x_5379_, 1, v___x_5465_);
v___x_5467_ = v___x_5379_;
goto v_reusejp_5466_;
}
else
{
lean_object* v_reuseFailAlloc_5470_; 
v_reuseFailAlloc_5470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5470_, 0, v_fst_5377_);
lean_ctor_set(v_reuseFailAlloc_5470_, 1, v___x_5465_);
v___x_5467_ = v_reuseFailAlloc_5470_;
goto v_reusejp_5466_;
}
v_reusejp_5466_:
{
lean_object* v___x_5468_; lean_object* v___f_5469_; 
v___x_5468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5468_, 0, v___x_5467_);
v___f_5469_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5469_, 0, v___x_5468_);
v___y_5347_ = v___f_5469_;
goto v___jp_5346_;
}
}
}
}
}
}
else
{
lean_object* v___x_5476_; uint8_t v_isShared_5477_; uint8_t v_isSharedCheck_5561_; 
lean_inc(v_stop_5452_);
lean_inc(v_start_5451_);
lean_inc_ref(v_array_5450_);
v_isSharedCheck_5561_ = !lean_is_exclusive(v_fst_5389_);
if (v_isSharedCheck_5561_ == 0)
{
lean_object* v_unused_5562_; lean_object* v_unused_5563_; lean_object* v_unused_5564_; 
v_unused_5562_ = lean_ctor_get(v_fst_5389_, 2);
lean_dec(v_unused_5562_);
v_unused_5563_ = lean_ctor_get(v_fst_5389_, 1);
lean_dec(v_unused_5563_);
v_unused_5564_ = lean_ctor_get(v_fst_5389_, 0);
lean_dec(v_unused_5564_);
v___x_5476_ = v_fst_5389_;
v_isShared_5477_ = v_isSharedCheck_5561_;
goto v_resetjp_5475_;
}
else
{
lean_dec(v_fst_5389_);
v___x_5476_ = lean_box(0);
v_isShared_5477_ = v_isSharedCheck_5561_;
goto v_resetjp_5475_;
}
v_resetjp_5475_:
{
lean_object* v_array_5478_; lean_object* v_start_5479_; lean_object* v_stop_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5484_; 
v_array_5478_ = lean_ctor_get(v_fst_5385_, 0);
v_start_5479_ = lean_ctor_get(v_fst_5385_, 1);
v_stop_5480_ = lean_ctor_get(v_fst_5385_, 2);
v___x_5481_ = lean_array_fget(v_array_5450_, v_start_5451_);
v___x_5482_ = lean_nat_add(v_start_5451_, v___x_5425_);
lean_dec(v_start_5451_);
if (v_isShared_5477_ == 0)
{
lean_ctor_set(v___x_5476_, 1, v___x_5482_);
v___x_5484_ = v___x_5476_;
goto v_reusejp_5483_;
}
else
{
lean_object* v_reuseFailAlloc_5560_; 
v_reuseFailAlloc_5560_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5560_, 0, v_array_5450_);
lean_ctor_set(v_reuseFailAlloc_5560_, 1, v___x_5482_);
lean_ctor_set(v_reuseFailAlloc_5560_, 2, v_stop_5452_);
v___x_5484_ = v_reuseFailAlloc_5560_;
goto v_reusejp_5483_;
}
v_reusejp_5483_:
{
uint8_t v___x_5485_; 
v___x_5485_ = lean_nat_dec_lt(v_start_5479_, v_stop_5480_);
if (v___x_5485_ == 0)
{
lean_object* v___x_5487_; 
lean_dec(v___x_5481_);
lean_dec(v___x_5453_);
lean_dec(v___x_5424_);
if (v_isShared_5396_ == 0)
{
lean_ctor_set(v___x_5395_, 1, v___x_5428_);
lean_ctor_set(v___x_5395_, 0, v___x_5456_);
v___x_5487_ = v___x_5395_;
goto v_reusejp_5486_;
}
else
{
lean_object* v_reuseFailAlloc_5502_; 
v_reuseFailAlloc_5502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5502_, 0, v___x_5456_);
lean_ctor_set(v_reuseFailAlloc_5502_, 1, v___x_5428_);
v___x_5487_ = v_reuseFailAlloc_5502_;
goto v_reusejp_5486_;
}
v_reusejp_5486_:
{
lean_object* v___x_5489_; 
if (v_isShared_5392_ == 0)
{
lean_ctor_set(v___x_5391_, 1, v___x_5487_);
lean_ctor_set(v___x_5391_, 0, v___x_5484_);
v___x_5489_ = v___x_5391_;
goto v_reusejp_5488_;
}
else
{
lean_object* v_reuseFailAlloc_5501_; 
v_reuseFailAlloc_5501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5501_, 0, v___x_5484_);
lean_ctor_set(v_reuseFailAlloc_5501_, 1, v___x_5487_);
v___x_5489_ = v_reuseFailAlloc_5501_;
goto v_reusejp_5488_;
}
v_reusejp_5488_:
{
lean_object* v___x_5491_; 
if (v_isShared_5388_ == 0)
{
lean_ctor_set(v___x_5387_, 1, v___x_5489_);
v___x_5491_ = v___x_5387_;
goto v_reusejp_5490_;
}
else
{
lean_object* v_reuseFailAlloc_5500_; 
v_reuseFailAlloc_5500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5500_, 0, v_fst_5385_);
lean_ctor_set(v_reuseFailAlloc_5500_, 1, v___x_5489_);
v___x_5491_ = v_reuseFailAlloc_5500_;
goto v_reusejp_5490_;
}
v_reusejp_5490_:
{
lean_object* v___x_5493_; 
if (v_isShared_5384_ == 0)
{
lean_ctor_set(v___x_5383_, 1, v___x_5491_);
v___x_5493_ = v___x_5383_;
goto v_reusejp_5492_;
}
else
{
lean_object* v_reuseFailAlloc_5499_; 
v_reuseFailAlloc_5499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5499_, 0, v_fst_5381_);
lean_ctor_set(v_reuseFailAlloc_5499_, 1, v___x_5491_);
v___x_5493_ = v_reuseFailAlloc_5499_;
goto v_reusejp_5492_;
}
v_reusejp_5492_:
{
lean_object* v___x_5495_; 
if (v_isShared_5380_ == 0)
{
lean_ctor_set(v___x_5379_, 1, v___x_5493_);
v___x_5495_ = v___x_5379_;
goto v_reusejp_5494_;
}
else
{
lean_object* v_reuseFailAlloc_5498_; 
v_reuseFailAlloc_5498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5498_, 0, v_fst_5377_);
lean_ctor_set(v_reuseFailAlloc_5498_, 1, v___x_5493_);
v___x_5495_ = v_reuseFailAlloc_5498_;
goto v_reusejp_5494_;
}
v_reusejp_5494_:
{
lean_object* v___x_5496_; lean_object* v___f_5497_; 
v___x_5496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5496_, 0, v___x_5495_);
v___f_5497_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5497_, 0, v___x_5496_);
v___y_5347_ = v___f_5497_;
goto v___jp_5346_;
}
}
}
}
}
}
else
{
lean_object* v___x_5504_; uint8_t v_isShared_5505_; uint8_t v_isSharedCheck_5556_; 
lean_inc(v_stop_5480_);
lean_inc(v_start_5479_);
lean_inc_ref(v_array_5478_);
v_isSharedCheck_5556_ = !lean_is_exclusive(v_fst_5385_);
if (v_isSharedCheck_5556_ == 0)
{
lean_object* v_unused_5557_; lean_object* v_unused_5558_; lean_object* v_unused_5559_; 
v_unused_5557_ = lean_ctor_get(v_fst_5385_, 2);
lean_dec(v_unused_5557_);
v_unused_5558_ = lean_ctor_get(v_fst_5385_, 1);
lean_dec(v_unused_5558_);
v_unused_5559_ = lean_ctor_get(v_fst_5385_, 0);
lean_dec(v_unused_5559_);
v___x_5504_ = v_fst_5385_;
v_isShared_5505_ = v_isSharedCheck_5556_;
goto v_resetjp_5503_;
}
else
{
lean_dec(v_fst_5385_);
v___x_5504_ = lean_box(0);
v_isShared_5505_ = v_isSharedCheck_5556_;
goto v_resetjp_5503_;
}
v_resetjp_5503_:
{
lean_object* v_array_5506_; lean_object* v_start_5507_; lean_object* v_stop_5508_; lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5512_; 
v_array_5506_ = lean_ctor_get(v_fst_5381_, 0);
v_start_5507_ = lean_ctor_get(v_fst_5381_, 1);
v_stop_5508_ = lean_ctor_get(v_fst_5381_, 2);
v___x_5509_ = lean_array_fget(v_array_5478_, v_start_5479_);
v___x_5510_ = lean_nat_add(v_start_5479_, v___x_5425_);
lean_dec(v_start_5479_);
if (v_isShared_5505_ == 0)
{
lean_ctor_set(v___x_5504_, 1, v___x_5510_);
v___x_5512_ = v___x_5504_;
goto v_reusejp_5511_;
}
else
{
lean_object* v_reuseFailAlloc_5555_; 
v_reuseFailAlloc_5555_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5555_, 0, v_array_5478_);
lean_ctor_set(v_reuseFailAlloc_5555_, 1, v___x_5510_);
lean_ctor_set(v_reuseFailAlloc_5555_, 2, v_stop_5480_);
v___x_5512_ = v_reuseFailAlloc_5555_;
goto v_reusejp_5511_;
}
v_reusejp_5511_:
{
uint8_t v___x_5513_; 
v___x_5513_ = lean_nat_dec_lt(v_start_5507_, v_stop_5508_);
if (v___x_5513_ == 0)
{
lean_object* v___x_5515_; 
lean_dec(v___x_5509_);
lean_dec(v___x_5481_);
lean_dec(v___x_5453_);
lean_dec(v___x_5424_);
if (v_isShared_5396_ == 0)
{
lean_ctor_set(v___x_5395_, 1, v___x_5428_);
lean_ctor_set(v___x_5395_, 0, v___x_5456_);
v___x_5515_ = v___x_5395_;
goto v_reusejp_5514_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v___x_5456_);
lean_ctor_set(v_reuseFailAlloc_5530_, 1, v___x_5428_);
v___x_5515_ = v_reuseFailAlloc_5530_;
goto v_reusejp_5514_;
}
v_reusejp_5514_:
{
lean_object* v___x_5517_; 
if (v_isShared_5392_ == 0)
{
lean_ctor_set(v___x_5391_, 1, v___x_5515_);
lean_ctor_set(v___x_5391_, 0, v___x_5484_);
v___x_5517_ = v___x_5391_;
goto v_reusejp_5516_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v___x_5484_);
lean_ctor_set(v_reuseFailAlloc_5529_, 1, v___x_5515_);
v___x_5517_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5516_;
}
v_reusejp_5516_:
{
lean_object* v___x_5519_; 
if (v_isShared_5388_ == 0)
{
lean_ctor_set(v___x_5387_, 1, v___x_5517_);
lean_ctor_set(v___x_5387_, 0, v___x_5512_);
v___x_5519_ = v___x_5387_;
goto v_reusejp_5518_;
}
else
{
lean_object* v_reuseFailAlloc_5528_; 
v_reuseFailAlloc_5528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5528_, 0, v___x_5512_);
lean_ctor_set(v_reuseFailAlloc_5528_, 1, v___x_5517_);
v___x_5519_ = v_reuseFailAlloc_5528_;
goto v_reusejp_5518_;
}
v_reusejp_5518_:
{
lean_object* v___x_5521_; 
if (v_isShared_5384_ == 0)
{
lean_ctor_set(v___x_5383_, 1, v___x_5519_);
v___x_5521_ = v___x_5383_;
goto v_reusejp_5520_;
}
else
{
lean_object* v_reuseFailAlloc_5527_; 
v_reuseFailAlloc_5527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5527_, 0, v_fst_5381_);
lean_ctor_set(v_reuseFailAlloc_5527_, 1, v___x_5519_);
v___x_5521_ = v_reuseFailAlloc_5527_;
goto v_reusejp_5520_;
}
v_reusejp_5520_:
{
lean_object* v___x_5523_; 
if (v_isShared_5380_ == 0)
{
lean_ctor_set(v___x_5379_, 1, v___x_5521_);
v___x_5523_ = v___x_5379_;
goto v_reusejp_5522_;
}
else
{
lean_object* v_reuseFailAlloc_5526_; 
v_reuseFailAlloc_5526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5526_, 0, v_fst_5377_);
lean_ctor_set(v_reuseFailAlloc_5526_, 1, v___x_5521_);
v___x_5523_ = v_reuseFailAlloc_5526_;
goto v_reusejp_5522_;
}
v_reusejp_5522_:
{
lean_object* v___x_5524_; lean_object* v___f_5525_; 
v___x_5524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5524_, 0, v___x_5523_);
v___f_5525_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5525_, 0, v___x_5524_);
v___y_5347_ = v___f_5525_;
goto v___jp_5346_;
}
}
}
}
}
}
else
{
lean_object* v___x_5532_; uint8_t v_isShared_5533_; uint8_t v_isSharedCheck_5551_; 
lean_inc(v_stop_5508_);
lean_inc(v_start_5507_);
lean_inc_ref(v_array_5506_);
lean_del_object(v___x_5395_);
lean_del_object(v___x_5391_);
lean_del_object(v___x_5387_);
lean_del_object(v___x_5383_);
lean_del_object(v___x_5379_);
v_isSharedCheck_5551_ = !lean_is_exclusive(v_fst_5381_);
if (v_isSharedCheck_5551_ == 0)
{
lean_object* v_unused_5552_; lean_object* v_unused_5553_; lean_object* v_unused_5554_; 
v_unused_5552_ = lean_ctor_get(v_fst_5381_, 2);
lean_dec(v_unused_5552_);
v_unused_5553_ = lean_ctor_get(v_fst_5381_, 1);
lean_dec(v_unused_5553_);
v_unused_5554_ = lean_ctor_get(v_fst_5381_, 0);
lean_dec(v_unused_5554_);
v___x_5532_ = v_fst_5381_;
v_isShared_5533_ = v_isSharedCheck_5551_;
goto v_resetjp_5531_;
}
else
{
lean_dec(v_fst_5381_);
v___x_5532_ = lean_box(0);
v_isShared_5533_ = v_isSharedCheck_5551_;
goto v_resetjp_5531_;
}
v_resetjp_5531_:
{
lean_object* v_numOverlaps_5534_; uint8_t v_hasUnitThunk_5535_; lean_object* v___x_5536_; uint8_t v___x_5537_; 
v_numOverlaps_5534_ = lean_ctor_get(v___x_5509_, 1);
v_hasUnitThunk_5535_ = lean_ctor_get_uint8(v___x_5509_, sizeof(void*)*2);
v___x_5536_ = lean_unsigned_to_nat(0u);
v___x_5537_ = lean_nat_dec_eq(v_numOverlaps_5534_, v___x_5536_);
if (v___x_5537_ == 0)
{
lean_object* v___x_5538_; lean_object* v___x_5539_; 
lean_del_object(v___x_5532_);
lean_dec_ref(v___x_5512_);
lean_dec(v___x_5509_);
lean_dec(v_stop_5508_);
lean_dec(v_start_5507_);
lean_dec_ref(v_array_5506_);
lean_dec_ref(v___x_5484_);
lean_dec(v___x_5481_);
lean_dec_ref(v___x_5456_);
lean_dec(v___x_5453_);
lean_dec_ref(v___x_5428_);
lean_dec(v___x_5424_);
lean_dec(v_fst_5377_);
v___x_5538_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9);
v___x_5539_ = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed), 6, 1);
lean_closure_set(v___x_5539_, 0, v___x_5538_);
v___y_5347_ = v___x_5539_;
goto v___jp_5346_;
}
else
{
uint8_t v___x_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___f_5545_; lean_object* v___x_5546_; lean_object* v___x_5548_; 
v___x_5540_ = 0;
v___x_5541_ = lean_array_fget_borrowed(v_array_5506_, v_start_5507_);
v___x_5542_ = lean_box(v___x_5540_);
v___x_5543_ = lean_box(v_useSplitter_5336_);
v___x_5544_ = lean_box(v_hasUnitThunk_5535_);
lean_inc(v_numDiscrEqs_5338_);
lean_inc(v_extraEqualities_5337_);
lean_inc(v___x_5541_);
lean_inc(v_a_5339_);
lean_inc_ref(v_onAlt_5335_);
v___f_5545_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed), 18, 11);
lean_closure_set(v___f_5545_, 0, v___x_5481_);
lean_closure_set(v___f_5545_, 1, v___x_5424_);
lean_closure_set(v___f_5545_, 2, v_onAlt_5335_);
lean_closure_set(v___f_5545_, 3, v_a_5339_);
lean_closure_set(v___f_5545_, 4, v___x_5542_);
lean_closure_set(v___f_5545_, 5, v___x_5543_);
lean_closure_set(v___f_5545_, 6, v___x_5541_);
lean_closure_set(v___f_5545_, 7, v_extraEqualities_5337_);
lean_closure_set(v___f_5545_, 8, v_numDiscrEqs_5338_);
lean_closure_set(v___f_5545_, 9, v___x_5544_);
lean_closure_set(v___f_5545_, 10, v___x_5425_);
v___x_5546_ = lean_nat_add(v_start_5507_, v___x_5425_);
lean_dec(v_start_5507_);
if (v_isShared_5533_ == 0)
{
lean_ctor_set(v___x_5532_, 1, v___x_5546_);
v___x_5548_ = v___x_5532_;
goto v_reusejp_5547_;
}
else
{
lean_object* v_reuseFailAlloc_5550_; 
v_reuseFailAlloc_5550_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5550_, 0, v_array_5506_);
lean_ctor_set(v_reuseFailAlloc_5550_, 1, v___x_5546_);
lean_ctor_set(v_reuseFailAlloc_5550_, 2, v_stop_5508_);
v___x_5548_ = v_reuseFailAlloc_5550_;
goto v_reusejp_5547_;
}
v_reusejp_5547_:
{
lean_object* v___f_5549_; 
v___f_5549_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed), 14, 9);
lean_closure_set(v___f_5549_, 0, v___x_5453_);
lean_closure_set(v___f_5549_, 1, v___x_5509_);
lean_closure_set(v___f_5549_, 2, v___f_5545_);
lean_closure_set(v___f_5549_, 3, v_fst_5377_);
lean_closure_set(v___f_5549_, 4, v___x_5456_);
lean_closure_set(v___f_5549_, 5, v___x_5428_);
lean_closure_set(v___f_5549_, 6, v___x_5484_);
lean_closure_set(v___f_5549_, 7, v___x_5512_);
lean_closure_set(v___f_5549_, 8, v___x_5548_);
v___y_5347_ = v___f_5549_;
goto v___jp_5346_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_5346_:
{
lean_object* v___x_5348_; 
lean_inc(v___y_5344_);
lean_inc_ref(v___y_5343_);
lean_inc(v___y_5342_);
lean_inc_ref(v___y_5341_);
v___x_5348_ = lean_apply_5(v___y_5347_, v___y_5341_, v___y_5342_, v___y_5343_, v___y_5344_, lean_box(0));
if (lean_obj_tag(v___x_5348_) == 0)
{
lean_object* v_a_5349_; lean_object* v___x_5351_; uint8_t v_isShared_5352_; uint8_t v_isSharedCheck_5361_; 
v_a_5349_ = lean_ctor_get(v___x_5348_, 0);
v_isSharedCheck_5361_ = !lean_is_exclusive(v___x_5348_);
if (v_isSharedCheck_5361_ == 0)
{
v___x_5351_ = v___x_5348_;
v_isShared_5352_ = v_isSharedCheck_5361_;
goto v_resetjp_5350_;
}
else
{
lean_inc(v_a_5349_);
lean_dec(v___x_5348_);
v___x_5351_ = lean_box(0);
v_isShared_5352_ = v_isSharedCheck_5361_;
goto v_resetjp_5350_;
}
v_resetjp_5350_:
{
if (lean_obj_tag(v_a_5349_) == 0)
{
lean_object* v_a_5353_; lean_object* v___x_5355_; 
lean_dec(v_a_5339_);
lean_dec(v_numDiscrEqs_5338_);
lean_dec(v_extraEqualities_5337_);
lean_dec_ref(v_onAlt_5335_);
v_a_5353_ = lean_ctor_get(v_a_5349_, 0);
lean_inc(v_a_5353_);
lean_dec_ref(v_a_5349_);
if (v_isShared_5352_ == 0)
{
lean_ctor_set(v___x_5351_, 0, v_a_5353_);
v___x_5355_ = v___x_5351_;
goto v_reusejp_5354_;
}
else
{
lean_object* v_reuseFailAlloc_5356_; 
v_reuseFailAlloc_5356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5356_, 0, v_a_5353_);
v___x_5355_ = v_reuseFailAlloc_5356_;
goto v_reusejp_5354_;
}
v_reusejp_5354_:
{
return v___x_5355_;
}
}
else
{
lean_object* v_a_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; 
lean_del_object(v___x_5351_);
v_a_5357_ = lean_ctor_get(v_a_5349_, 0);
lean_inc(v_a_5357_);
lean_dec_ref(v_a_5349_);
v___x_5358_ = lean_unsigned_to_nat(1u);
v___x_5359_ = lean_nat_add(v_a_5339_, v___x_5358_);
lean_dec(v_a_5339_);
v_a_5339_ = v___x_5359_;
v_b_5340_ = v_a_5357_;
goto _start;
}
}
}
else
{
lean_object* v_a_5362_; lean_object* v___x_5364_; uint8_t v_isShared_5365_; uint8_t v_isSharedCheck_5369_; 
lean_dec(v_a_5339_);
lean_dec(v_numDiscrEqs_5338_);
lean_dec(v_extraEqualities_5337_);
lean_dec_ref(v_onAlt_5335_);
v_a_5362_ = lean_ctor_get(v___x_5348_, 0);
v_isSharedCheck_5369_ = !lean_is_exclusive(v___x_5348_);
if (v_isSharedCheck_5369_ == 0)
{
v___x_5364_ = v___x_5348_;
v_isShared_5365_ = v_isSharedCheck_5369_;
goto v_resetjp_5363_;
}
else
{
lean_inc(v_a_5362_);
lean_dec(v___x_5348_);
v___x_5364_ = lean_box(0);
v_isShared_5365_ = v_isSharedCheck_5369_;
goto v_resetjp_5363_;
}
v_resetjp_5363_:
{
lean_object* v___x_5367_; 
if (v_isShared_5365_ == 0)
{
v___x_5367_ = v___x_5364_;
goto v_reusejp_5366_;
}
else
{
lean_object* v_reuseFailAlloc_5368_; 
v_reuseFailAlloc_5368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5368_, 0, v_a_5362_);
v___x_5367_ = v_reuseFailAlloc_5368_;
goto v_reusejp_5366_;
}
v_reusejp_5366_:
{
return v___x_5367_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___boxed(lean_object* v_upperBound_5585_, lean_object* v_onAlt_5586_, lean_object* v_useSplitter_5587_, lean_object* v_extraEqualities_5588_, lean_object* v_numDiscrEqs_5589_, lean_object* v_a_5590_, lean_object* v_b_5591_, lean_object* v___y_5592_, lean_object* v___y_5593_, lean_object* v___y_5594_, lean_object* v___y_5595_, lean_object* v___y_5596_){
_start:
{
uint8_t v_useSplitter_boxed_5597_; lean_object* v_res_5598_; 
v_useSplitter_boxed_5597_ = lean_unbox(v_useSplitter_5587_);
v_res_5598_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v_upperBound_5585_, v_onAlt_5586_, v_useSplitter_boxed_5597_, v_extraEqualities_5588_, v_numDiscrEqs_5589_, v_a_5590_, v_b_5591_, v___y_5592_, v___y_5593_, v___y_5594_, v___y_5595_);
lean_dec(v___y_5595_);
lean_dec_ref(v___y_5594_);
lean_dec(v___y_5593_);
lean_dec_ref(v___y_5592_);
lean_dec(v_upperBound_5585_);
return v_res_5598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(uint8_t v_addEqualities_5599_, lean_object* v_as_5600_, size_t v_sz_5601_, size_t v_i_5602_, lean_object* v_b_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_, lean_object* v___y_5606_, lean_object* v___y_5607_){
_start:
{
lean_object* v_a_5610_; uint8_t v___x_5614_; 
v___x_5614_ = lean_usize_dec_lt(v_i_5602_, v_sz_5601_);
if (v___x_5614_ == 0)
{
lean_object* v___x_5615_; 
v___x_5615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5615_, 0, v_b_5603_);
return v___x_5615_;
}
else
{
lean_object* v_snd_5616_; lean_object* v_snd_5617_; lean_object* v_snd_5618_; lean_object* v_snd_5619_; lean_object* v_fst_5620_; lean_object* v___x_5622_; uint8_t v_isShared_5623_; uint8_t v_isSharedCheck_5766_; 
v_snd_5616_ = lean_ctor_get(v_b_5603_, 1);
lean_inc(v_snd_5616_);
v_snd_5617_ = lean_ctor_get(v_snd_5616_, 1);
lean_inc(v_snd_5617_);
v_snd_5618_ = lean_ctor_get(v_snd_5617_, 1);
lean_inc(v_snd_5618_);
v_snd_5619_ = lean_ctor_get(v_snd_5618_, 1);
lean_inc(v_snd_5619_);
v_fst_5620_ = lean_ctor_get(v_b_5603_, 0);
v_isSharedCheck_5766_ = !lean_is_exclusive(v_b_5603_);
if (v_isSharedCheck_5766_ == 0)
{
lean_object* v_unused_5767_; 
v_unused_5767_ = lean_ctor_get(v_b_5603_, 1);
lean_dec(v_unused_5767_);
v___x_5622_ = v_b_5603_;
v_isShared_5623_ = v_isSharedCheck_5766_;
goto v_resetjp_5621_;
}
else
{
lean_inc(v_fst_5620_);
lean_dec(v_b_5603_);
v___x_5622_ = lean_box(0);
v_isShared_5623_ = v_isSharedCheck_5766_;
goto v_resetjp_5621_;
}
v_resetjp_5621_:
{
lean_object* v_fst_5624_; lean_object* v___x_5626_; uint8_t v_isShared_5627_; uint8_t v_isSharedCheck_5764_; 
v_fst_5624_ = lean_ctor_get(v_snd_5616_, 0);
v_isSharedCheck_5764_ = !lean_is_exclusive(v_snd_5616_);
if (v_isSharedCheck_5764_ == 0)
{
lean_object* v_unused_5765_; 
v_unused_5765_ = lean_ctor_get(v_snd_5616_, 1);
lean_dec(v_unused_5765_);
v___x_5626_ = v_snd_5616_;
v_isShared_5627_ = v_isSharedCheck_5764_;
goto v_resetjp_5625_;
}
else
{
lean_inc(v_fst_5624_);
lean_dec(v_snd_5616_);
v___x_5626_ = lean_box(0);
v_isShared_5627_ = v_isSharedCheck_5764_;
goto v_resetjp_5625_;
}
v_resetjp_5625_:
{
lean_object* v_fst_5628_; lean_object* v___x_5630_; uint8_t v_isShared_5631_; uint8_t v_isSharedCheck_5762_; 
v_fst_5628_ = lean_ctor_get(v_snd_5617_, 0);
v_isSharedCheck_5762_ = !lean_is_exclusive(v_snd_5617_);
if (v_isSharedCheck_5762_ == 0)
{
lean_object* v_unused_5763_; 
v_unused_5763_ = lean_ctor_get(v_snd_5617_, 1);
lean_dec(v_unused_5763_);
v___x_5630_ = v_snd_5617_;
v_isShared_5631_ = v_isSharedCheck_5762_;
goto v_resetjp_5629_;
}
else
{
lean_inc(v_fst_5628_);
lean_dec(v_snd_5617_);
v___x_5630_ = lean_box(0);
v_isShared_5631_ = v_isSharedCheck_5762_;
goto v_resetjp_5629_;
}
v_resetjp_5629_:
{
lean_object* v_fst_5632_; lean_object* v___x_5634_; uint8_t v_isShared_5635_; uint8_t v_isSharedCheck_5760_; 
v_fst_5632_ = lean_ctor_get(v_snd_5618_, 0);
v_isSharedCheck_5760_ = !lean_is_exclusive(v_snd_5618_);
if (v_isSharedCheck_5760_ == 0)
{
lean_object* v_unused_5761_; 
v_unused_5761_ = lean_ctor_get(v_snd_5618_, 1);
lean_dec(v_unused_5761_);
v___x_5634_ = v_snd_5618_;
v_isShared_5635_ = v_isSharedCheck_5760_;
goto v_resetjp_5633_;
}
else
{
lean_inc(v_fst_5632_);
lean_dec(v_snd_5618_);
v___x_5634_ = lean_box(0);
v_isShared_5635_ = v_isSharedCheck_5760_;
goto v_resetjp_5633_;
}
v_resetjp_5633_:
{
lean_object* v_array_5636_; lean_object* v_start_5637_; lean_object* v_stop_5638_; uint8_t v___x_5639_; 
v_array_5636_ = lean_ctor_get(v_snd_5619_, 0);
v_start_5637_ = lean_ctor_get(v_snd_5619_, 1);
v_stop_5638_ = lean_ctor_get(v_snd_5619_, 2);
v___x_5639_ = lean_nat_dec_lt(v_start_5637_, v_stop_5638_);
if (v___x_5639_ == 0)
{
lean_object* v___x_5641_; 
if (v_isShared_5635_ == 0)
{
v___x_5641_ = v___x_5634_;
goto v_reusejp_5640_;
}
else
{
lean_object* v_reuseFailAlloc_5652_; 
v_reuseFailAlloc_5652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5652_, 0, v_fst_5632_);
lean_ctor_set(v_reuseFailAlloc_5652_, 1, v_snd_5619_);
v___x_5641_ = v_reuseFailAlloc_5652_;
goto v_reusejp_5640_;
}
v_reusejp_5640_:
{
lean_object* v___x_5643_; 
if (v_isShared_5631_ == 0)
{
lean_ctor_set(v___x_5630_, 1, v___x_5641_);
v___x_5643_ = v___x_5630_;
goto v_reusejp_5642_;
}
else
{
lean_object* v_reuseFailAlloc_5651_; 
v_reuseFailAlloc_5651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5651_, 0, v_fst_5628_);
lean_ctor_set(v_reuseFailAlloc_5651_, 1, v___x_5641_);
v___x_5643_ = v_reuseFailAlloc_5651_;
goto v_reusejp_5642_;
}
v_reusejp_5642_:
{
lean_object* v___x_5645_; 
if (v_isShared_5627_ == 0)
{
lean_ctor_set(v___x_5626_, 1, v___x_5643_);
v___x_5645_ = v___x_5626_;
goto v_reusejp_5644_;
}
else
{
lean_object* v_reuseFailAlloc_5650_; 
v_reuseFailAlloc_5650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5650_, 0, v_fst_5624_);
lean_ctor_set(v_reuseFailAlloc_5650_, 1, v___x_5643_);
v___x_5645_ = v_reuseFailAlloc_5650_;
goto v_reusejp_5644_;
}
v_reusejp_5644_:
{
lean_object* v___x_5647_; 
if (v_isShared_5623_ == 0)
{
lean_ctor_set(v___x_5622_, 1, v___x_5645_);
v___x_5647_ = v___x_5622_;
goto v_reusejp_5646_;
}
else
{
lean_object* v_reuseFailAlloc_5649_; 
v_reuseFailAlloc_5649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5649_, 0, v_fst_5620_);
lean_ctor_set(v_reuseFailAlloc_5649_, 1, v___x_5645_);
v___x_5647_ = v_reuseFailAlloc_5649_;
goto v_reusejp_5646_;
}
v_reusejp_5646_:
{
lean_object* v___x_5648_; 
v___x_5648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5648_, 0, v___x_5647_);
return v___x_5648_;
}
}
}
}
}
else
{
lean_object* v___x_5654_; uint8_t v_isShared_5655_; uint8_t v_isSharedCheck_5756_; 
lean_inc(v_stop_5638_);
lean_inc(v_start_5637_);
lean_inc_ref(v_array_5636_);
v_isSharedCheck_5756_ = !lean_is_exclusive(v_snd_5619_);
if (v_isSharedCheck_5756_ == 0)
{
lean_object* v_unused_5757_; lean_object* v_unused_5758_; lean_object* v_unused_5759_; 
v_unused_5757_ = lean_ctor_get(v_snd_5619_, 2);
lean_dec(v_unused_5757_);
v_unused_5758_ = lean_ctor_get(v_snd_5619_, 1);
lean_dec(v_unused_5758_);
v_unused_5759_ = lean_ctor_get(v_snd_5619_, 0);
lean_dec(v_unused_5759_);
v___x_5654_ = v_snd_5619_;
v_isShared_5655_ = v_isSharedCheck_5756_;
goto v_resetjp_5653_;
}
else
{
lean_dec(v_snd_5619_);
v___x_5654_ = lean_box(0);
v_isShared_5655_ = v_isSharedCheck_5756_;
goto v_resetjp_5653_;
}
v_resetjp_5653_:
{
lean_object* v_array_5656_; lean_object* v_start_5657_; lean_object* v_stop_5658_; lean_object* v___x_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5663_; 
v_array_5656_ = lean_ctor_get(v_fst_5632_, 0);
v_start_5657_ = lean_ctor_get(v_fst_5632_, 1);
v_stop_5658_ = lean_ctor_get(v_fst_5632_, 2);
v___x_5659_ = lean_array_fget(v_array_5636_, v_start_5637_);
v___x_5660_ = lean_unsigned_to_nat(1u);
v___x_5661_ = lean_nat_add(v_start_5637_, v___x_5660_);
lean_dec(v_start_5637_);
if (v_isShared_5655_ == 0)
{
lean_ctor_set(v___x_5654_, 1, v___x_5661_);
v___x_5663_ = v___x_5654_;
goto v_reusejp_5662_;
}
else
{
lean_object* v_reuseFailAlloc_5755_; 
v_reuseFailAlloc_5755_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5755_, 0, v_array_5636_);
lean_ctor_set(v_reuseFailAlloc_5755_, 1, v___x_5661_);
lean_ctor_set(v_reuseFailAlloc_5755_, 2, v_stop_5638_);
v___x_5663_ = v_reuseFailAlloc_5755_;
goto v_reusejp_5662_;
}
v_reusejp_5662_:
{
uint8_t v___x_5664_; 
v___x_5664_ = lean_nat_dec_lt(v_start_5657_, v_stop_5658_);
if (v___x_5664_ == 0)
{
lean_object* v___x_5666_; 
lean_dec(v___x_5659_);
if (v_isShared_5635_ == 0)
{
lean_ctor_set(v___x_5634_, 1, v___x_5663_);
v___x_5666_ = v___x_5634_;
goto v_reusejp_5665_;
}
else
{
lean_object* v_reuseFailAlloc_5677_; 
v_reuseFailAlloc_5677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5677_, 0, v_fst_5632_);
lean_ctor_set(v_reuseFailAlloc_5677_, 1, v___x_5663_);
v___x_5666_ = v_reuseFailAlloc_5677_;
goto v_reusejp_5665_;
}
v_reusejp_5665_:
{
lean_object* v___x_5668_; 
if (v_isShared_5631_ == 0)
{
lean_ctor_set(v___x_5630_, 1, v___x_5666_);
v___x_5668_ = v___x_5630_;
goto v_reusejp_5667_;
}
else
{
lean_object* v_reuseFailAlloc_5676_; 
v_reuseFailAlloc_5676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5676_, 0, v_fst_5628_);
lean_ctor_set(v_reuseFailAlloc_5676_, 1, v___x_5666_);
v___x_5668_ = v_reuseFailAlloc_5676_;
goto v_reusejp_5667_;
}
v_reusejp_5667_:
{
lean_object* v___x_5670_; 
if (v_isShared_5627_ == 0)
{
lean_ctor_set(v___x_5626_, 1, v___x_5668_);
v___x_5670_ = v___x_5626_;
goto v_reusejp_5669_;
}
else
{
lean_object* v_reuseFailAlloc_5675_; 
v_reuseFailAlloc_5675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5675_, 0, v_fst_5624_);
lean_ctor_set(v_reuseFailAlloc_5675_, 1, v___x_5668_);
v___x_5670_ = v_reuseFailAlloc_5675_;
goto v_reusejp_5669_;
}
v_reusejp_5669_:
{
lean_object* v___x_5672_; 
if (v_isShared_5623_ == 0)
{
lean_ctor_set(v___x_5622_, 1, v___x_5670_);
v___x_5672_ = v___x_5622_;
goto v_reusejp_5671_;
}
else
{
lean_object* v_reuseFailAlloc_5674_; 
v_reuseFailAlloc_5674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5674_, 0, v_fst_5620_);
lean_ctor_set(v_reuseFailAlloc_5674_, 1, v___x_5670_);
v___x_5672_ = v_reuseFailAlloc_5674_;
goto v_reusejp_5671_;
}
v_reusejp_5671_:
{
lean_object* v___x_5673_; 
v___x_5673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5673_, 0, v___x_5672_);
return v___x_5673_;
}
}
}
}
}
else
{
lean_object* v___x_5679_; uint8_t v_isShared_5680_; uint8_t v_isSharedCheck_5751_; 
lean_inc(v_stop_5658_);
lean_inc(v_start_5657_);
lean_inc_ref(v_array_5656_);
v_isSharedCheck_5751_ = !lean_is_exclusive(v_fst_5632_);
if (v_isSharedCheck_5751_ == 0)
{
lean_object* v_unused_5752_; lean_object* v_unused_5753_; lean_object* v_unused_5754_; 
v_unused_5752_ = lean_ctor_get(v_fst_5632_, 2);
lean_dec(v_unused_5752_);
v_unused_5753_ = lean_ctor_get(v_fst_5632_, 1);
lean_dec(v_unused_5753_);
v_unused_5754_ = lean_ctor_get(v_fst_5632_, 0);
lean_dec(v_unused_5754_);
v___x_5679_ = v_fst_5632_;
v_isShared_5680_ = v_isSharedCheck_5751_;
goto v_resetjp_5678_;
}
else
{
lean_dec(v_fst_5632_);
v___x_5679_ = lean_box(0);
v_isShared_5680_ = v_isSharedCheck_5751_;
goto v_resetjp_5678_;
}
v_resetjp_5678_:
{
lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5684_; 
v___x_5681_ = lean_array_fget(v_array_5656_, v_start_5657_);
v___x_5682_ = lean_nat_add(v_start_5657_, v___x_5660_);
lean_dec(v_start_5657_);
if (v_isShared_5680_ == 0)
{
lean_ctor_set(v___x_5679_, 1, v___x_5682_);
v___x_5684_ = v___x_5679_;
goto v_reusejp_5683_;
}
else
{
lean_object* v_reuseFailAlloc_5750_; 
v_reuseFailAlloc_5750_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5750_, 0, v_array_5656_);
lean_ctor_set(v_reuseFailAlloc_5750_, 1, v___x_5682_);
lean_ctor_set(v_reuseFailAlloc_5750_, 2, v_stop_5658_);
v___x_5684_ = v_reuseFailAlloc_5750_;
goto v_reusejp_5683_;
}
v_reusejp_5683_:
{
if (v_addEqualities_5599_ == 0)
{
lean_dec(v___x_5681_);
goto v___jp_5685_;
}
else
{
if (lean_obj_tag(v___x_5659_) == 0)
{
lean_object* v_a_5701_; lean_object* v___x_5702_; 
lean_del_object(v___x_5634_);
lean_del_object(v___x_5630_);
lean_del_object(v___x_5626_);
lean_del_object(v___x_5622_);
v_a_5701_ = lean_array_uget_borrowed(v_as_5600_, v_i_5602_);
lean_inc(v_a_5701_);
v___x_5702_ = l_Lean_Meta_isProof(v_a_5701_, v___y_5604_, v___y_5605_, v___y_5606_, v___y_5607_);
if (lean_obj_tag(v___x_5702_) == 0)
{
lean_object* v_a_5703_; uint8_t v___x_5704_; 
v_a_5703_ = lean_ctor_get(v___x_5702_, 0);
lean_inc(v_a_5703_);
lean_dec_ref(v___x_5702_);
v___x_5704_ = lean_unbox(v_a_5703_);
lean_dec(v_a_5703_);
if (v___x_5704_ == 0)
{
lean_object* v___x_5705_; 
lean_inc(v_a_5701_);
v___x_5705_ = l_Lean_Meta_mkEqHEq(v___x_5681_, v_a_5701_, v___y_5604_, v___y_5605_, v___y_5606_, v___y_5607_);
if (lean_obj_tag(v___x_5705_) == 0)
{
lean_object* v_a_5706_; lean_object* v___x_5707_; 
v_a_5706_ = lean_ctor_get(v___x_5705_, 0);
lean_inc_n(v_a_5706_, 2);
lean_dec_ref(v___x_5705_);
v___x_5707_ = l_Lean_mkArrow(v_a_5706_, v_fst_5620_, v___y_5606_, v___y_5607_);
if (lean_obj_tag(v___x_5707_) == 0)
{
lean_object* v_a_5708_; uint8_t v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; 
v_a_5708_ = lean_ctor_get(v___x_5707_, 0);
lean_inc(v_a_5708_);
lean_dec_ref(v___x_5707_);
v___x_5709_ = l_Lean_Expr_isHEq(v_a_5706_);
lean_dec(v_a_5706_);
v___x_5710_ = lean_box(v___x_5709_);
v___x_5711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5711_, 0, v___x_5710_);
v___x_5712_ = lean_array_push(v_fst_5624_, v___x_5711_);
v___x_5713_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9___closed__0));
v___x_5714_ = lean_array_push(v_fst_5628_, v___x_5713_);
v___x_5715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5715_, 0, v___x_5684_);
lean_ctor_set(v___x_5715_, 1, v___x_5663_);
v___x_5716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5716_, 0, v___x_5714_);
lean_ctor_set(v___x_5716_, 1, v___x_5715_);
v___x_5717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5717_, 0, v___x_5712_);
lean_ctor_set(v___x_5717_, 1, v___x_5716_);
v___x_5718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5718_, 0, v_a_5708_);
lean_ctor_set(v___x_5718_, 1, v___x_5717_);
v_a_5610_ = v___x_5718_;
goto v___jp_5609_;
}
else
{
lean_object* v_a_5719_; lean_object* v___x_5721_; uint8_t v_isShared_5722_; uint8_t v_isSharedCheck_5726_; 
lean_dec(v_a_5706_);
lean_dec_ref(v___x_5684_);
lean_dec_ref(v___x_5663_);
lean_dec(v_fst_5628_);
lean_dec(v_fst_5624_);
v_a_5719_ = lean_ctor_get(v___x_5707_, 0);
v_isSharedCheck_5726_ = !lean_is_exclusive(v___x_5707_);
if (v_isSharedCheck_5726_ == 0)
{
v___x_5721_ = v___x_5707_;
v_isShared_5722_ = v_isSharedCheck_5726_;
goto v_resetjp_5720_;
}
else
{
lean_inc(v_a_5719_);
lean_dec(v___x_5707_);
v___x_5721_ = lean_box(0);
v_isShared_5722_ = v_isSharedCheck_5726_;
goto v_resetjp_5720_;
}
v_resetjp_5720_:
{
lean_object* v___x_5724_; 
if (v_isShared_5722_ == 0)
{
v___x_5724_ = v___x_5721_;
goto v_reusejp_5723_;
}
else
{
lean_object* v_reuseFailAlloc_5725_; 
v_reuseFailAlloc_5725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5725_, 0, v_a_5719_);
v___x_5724_ = v_reuseFailAlloc_5725_;
goto v_reusejp_5723_;
}
v_reusejp_5723_:
{
return v___x_5724_;
}
}
}
}
else
{
lean_object* v_a_5727_; lean_object* v___x_5729_; uint8_t v_isShared_5730_; uint8_t v_isSharedCheck_5734_; 
lean_dec_ref(v___x_5684_);
lean_dec_ref(v___x_5663_);
lean_dec(v_fst_5628_);
lean_dec(v_fst_5624_);
lean_dec(v_fst_5620_);
v_a_5727_ = lean_ctor_get(v___x_5705_, 0);
v_isSharedCheck_5734_ = !lean_is_exclusive(v___x_5705_);
if (v_isSharedCheck_5734_ == 0)
{
v___x_5729_ = v___x_5705_;
v_isShared_5730_ = v_isSharedCheck_5734_;
goto v_resetjp_5728_;
}
else
{
lean_inc(v_a_5727_);
lean_dec(v___x_5705_);
v___x_5729_ = lean_box(0);
v_isShared_5730_ = v_isSharedCheck_5734_;
goto v_resetjp_5728_;
}
v_resetjp_5728_:
{
lean_object* v___x_5732_; 
if (v_isShared_5730_ == 0)
{
v___x_5732_ = v___x_5729_;
goto v_reusejp_5731_;
}
else
{
lean_object* v_reuseFailAlloc_5733_; 
v_reuseFailAlloc_5733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5733_, 0, v_a_5727_);
v___x_5732_ = v_reuseFailAlloc_5733_;
goto v_reusejp_5731_;
}
v_reusejp_5731_:
{
return v___x_5732_;
}
}
}
}
else
{
lean_object* v___x_5735_; lean_object* v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; 
lean_dec(v___x_5681_);
v___x_5735_ = lean_box(0);
v___x_5736_ = lean_array_push(v_fst_5624_, v___x_5735_);
v___x_5737_ = lean_array_push(v_fst_5628_, v___x_5659_);
v___x_5738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5738_, 0, v___x_5684_);
lean_ctor_set(v___x_5738_, 1, v___x_5663_);
v___x_5739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5739_, 0, v___x_5737_);
lean_ctor_set(v___x_5739_, 1, v___x_5738_);
v___x_5740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5740_, 0, v___x_5736_);
lean_ctor_set(v___x_5740_, 1, v___x_5739_);
v___x_5741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5741_, 0, v_fst_5620_);
lean_ctor_set(v___x_5741_, 1, v___x_5740_);
v_a_5610_ = v___x_5741_;
goto v___jp_5609_;
}
}
else
{
lean_object* v_a_5742_; lean_object* v___x_5744_; uint8_t v_isShared_5745_; uint8_t v_isSharedCheck_5749_; 
lean_dec_ref(v___x_5684_);
lean_dec(v___x_5681_);
lean_dec_ref(v___x_5663_);
lean_dec(v_fst_5628_);
lean_dec(v_fst_5624_);
lean_dec(v_fst_5620_);
v_a_5742_ = lean_ctor_get(v___x_5702_, 0);
v_isSharedCheck_5749_ = !lean_is_exclusive(v___x_5702_);
if (v_isSharedCheck_5749_ == 0)
{
v___x_5744_ = v___x_5702_;
v_isShared_5745_ = v_isSharedCheck_5749_;
goto v_resetjp_5743_;
}
else
{
lean_inc(v_a_5742_);
lean_dec(v___x_5702_);
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
lean_dec(v___x_5681_);
goto v___jp_5685_;
}
}
v___jp_5685_:
{
lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5690_; 
v___x_5686_ = lean_box(0);
v___x_5687_ = lean_array_push(v_fst_5624_, v___x_5686_);
v___x_5688_ = lean_array_push(v_fst_5628_, v___x_5659_);
if (v_isShared_5635_ == 0)
{
lean_ctor_set(v___x_5634_, 1, v___x_5663_);
lean_ctor_set(v___x_5634_, 0, v___x_5684_);
v___x_5690_ = v___x_5634_;
goto v_reusejp_5689_;
}
else
{
lean_object* v_reuseFailAlloc_5700_; 
v_reuseFailAlloc_5700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5700_, 0, v___x_5684_);
lean_ctor_set(v_reuseFailAlloc_5700_, 1, v___x_5663_);
v___x_5690_ = v_reuseFailAlloc_5700_;
goto v_reusejp_5689_;
}
v_reusejp_5689_:
{
lean_object* v___x_5692_; 
if (v_isShared_5631_ == 0)
{
lean_ctor_set(v___x_5630_, 1, v___x_5690_);
lean_ctor_set(v___x_5630_, 0, v___x_5688_);
v___x_5692_ = v___x_5630_;
goto v_reusejp_5691_;
}
else
{
lean_object* v_reuseFailAlloc_5699_; 
v_reuseFailAlloc_5699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5699_, 0, v___x_5688_);
lean_ctor_set(v_reuseFailAlloc_5699_, 1, v___x_5690_);
v___x_5692_ = v_reuseFailAlloc_5699_;
goto v_reusejp_5691_;
}
v_reusejp_5691_:
{
lean_object* v___x_5694_; 
if (v_isShared_5627_ == 0)
{
lean_ctor_set(v___x_5626_, 1, v___x_5692_);
lean_ctor_set(v___x_5626_, 0, v___x_5687_);
v___x_5694_ = v___x_5626_;
goto v_reusejp_5693_;
}
else
{
lean_object* v_reuseFailAlloc_5698_; 
v_reuseFailAlloc_5698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5698_, 0, v___x_5687_);
lean_ctor_set(v_reuseFailAlloc_5698_, 1, v___x_5692_);
v___x_5694_ = v_reuseFailAlloc_5698_;
goto v_reusejp_5693_;
}
v_reusejp_5693_:
{
lean_object* v___x_5696_; 
if (v_isShared_5623_ == 0)
{
lean_ctor_set(v___x_5622_, 1, v___x_5694_);
v___x_5696_ = v___x_5622_;
goto v_reusejp_5695_;
}
else
{
lean_object* v_reuseFailAlloc_5697_; 
v_reuseFailAlloc_5697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5697_, 0, v_fst_5620_);
lean_ctor_set(v_reuseFailAlloc_5697_, 1, v___x_5694_);
v___x_5696_ = v_reuseFailAlloc_5697_;
goto v_reusejp_5695_;
}
v_reusejp_5695_:
{
v_a_5610_ = v___x_5696_;
goto v___jp_5609_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_5609_:
{
size_t v___x_5611_; size_t v___x_5612_; 
v___x_5611_ = ((size_t)1ULL);
v___x_5612_ = lean_usize_add(v_i_5602_, v___x_5611_);
v_i_5602_ = v___x_5612_;
v_b_5603_ = v_a_5610_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7___boxed(lean_object* v_addEqualities_5768_, lean_object* v_as_5769_, lean_object* v_sz_5770_, lean_object* v_i_5771_, lean_object* v_b_5772_, lean_object* v___y_5773_, lean_object* v___y_5774_, lean_object* v___y_5775_, lean_object* v___y_5776_, lean_object* v___y_5777_){
_start:
{
uint8_t v_addEqualities_boxed_5778_; size_t v_sz_boxed_5779_; size_t v_i_boxed_5780_; lean_object* v_res_5781_; 
v_addEqualities_boxed_5778_ = lean_unbox(v_addEqualities_5768_);
v_sz_boxed_5779_ = lean_unbox_usize(v_sz_5770_);
lean_dec(v_sz_5770_);
v_i_boxed_5780_ = lean_unbox_usize(v_i_5771_);
lean_dec(v_i_5771_);
v_res_5781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(v_addEqualities_boxed_5778_, v_as_5769_, v_sz_boxed_5779_, v_i_boxed_5780_, v_b_5772_, v___y_5773_, v___y_5774_, v___y_5775_, v___y_5776_);
lean_dec(v___y_5776_);
lean_dec_ref(v___y_5775_);
lean_dec(v___y_5774_);
lean_dec_ref(v___y_5773_);
lean_dec_ref(v_as_5769_);
return v_res_5781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(lean_object* v_onMotive_5782_, lean_object* v_toMatcherInfo_5783_, lean_object* v_a_5784_, uint8_t v_addEqualities_5785_, size_t v___x_5786_, lean_object* v_discrs_5787_, lean_object* v_motiveArgs_5788_, lean_object* v_motiveBody_5789_, lean_object* v___y_5790_, lean_object* v___y_5791_, lean_object* v___y_5792_, lean_object* v___y_5793_){
_start:
{
lean_object* v___x_5887_; lean_object* v___x_5888_; uint8_t v___x_5889_; 
v___x_5887_ = lean_array_get_size(v_motiveArgs_5788_);
v___x_5888_ = lean_array_get_size(v_discrs_5787_);
v___x_5889_ = lean_nat_dec_eq(v___x_5887_, v___x_5888_);
if (v___x_5889_ == 0)
{
lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v_a_5898_; lean_object* v___x_5900_; uint8_t v_isShared_5901_; uint8_t v_isSharedCheck_5905_; 
lean_dec_ref(v_motiveBody_5789_);
lean_dec_ref(v_motiveArgs_5788_);
lean_dec_ref(v_a_5784_);
lean_dec_ref(v_toMatcherInfo_5783_);
lean_dec_ref(v_onMotive_5782_);
v___x_5890_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_5891_ = l_Nat_reprFast(v___x_5888_);
v___x_5892_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5892_, 0, v___x_5891_);
v___x_5893_ = l_Lean_MessageData_ofFormat(v___x_5892_);
v___x_5894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5894_, 0, v___x_5890_);
lean_ctor_set(v___x_5894_, 1, v___x_5893_);
v___x_5895_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_5896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5896_, 0, v___x_5894_);
lean_ctor_set(v___x_5896_, 1, v___x_5895_);
v___x_5897_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_5896_, v___y_5790_, v___y_5791_, v___y_5792_, v___y_5793_);
v_a_5898_ = lean_ctor_get(v___x_5897_, 0);
v_isSharedCheck_5905_ = !lean_is_exclusive(v___x_5897_);
if (v_isSharedCheck_5905_ == 0)
{
v___x_5900_ = v___x_5897_;
v_isShared_5901_ = v_isSharedCheck_5905_;
goto v_resetjp_5899_;
}
else
{
lean_inc(v_a_5898_);
lean_dec(v___x_5897_);
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
else
{
goto v___jp_5795_;
}
v___jp_5795_:
{
lean_object* v___x_5796_; 
lean_inc(v___y_5793_);
lean_inc_ref(v___y_5792_);
lean_inc(v___y_5791_);
lean_inc_ref(v___y_5790_);
lean_inc_ref(v_motiveArgs_5788_);
v___x_5796_ = lean_apply_7(v_onMotive_5782_, v_motiveArgs_5788_, v_motiveBody_5789_, v___y_5790_, v___y_5791_, v___y_5792_, v___y_5793_, lean_box(0));
if (lean_obj_tag(v___x_5796_) == 0)
{
lean_object* v_a_5797_; lean_object* v_discrInfos_5798_; lean_object* v___x_5799_; lean_object* v_addHEqualities_5800_; lean_object* v___x_5801_; lean_object* v___x_5802_; lean_object* v___x_5803_; lean_object* v___x_5804_; lean_object* v___x_5805_; lean_object* v___x_5806_; lean_object* v___x_5807_; lean_object* v___x_5808_; size_t v_sz_5809_; lean_object* v___x_5810_; 
v_a_5797_ = lean_ctor_get(v___x_5796_, 0);
lean_inc(v_a_5797_);
lean_dec_ref(v___x_5796_);
v_discrInfos_5798_ = lean_ctor_get(v_toMatcherInfo_5783_, 4);
lean_inc_ref(v_discrInfos_5798_);
lean_dec_ref(v_toMatcherInfo_5783_);
v___x_5799_ = lean_unsigned_to_nat(0u);
v_addHEqualities_5800_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___closed__0));
v___x_5801_ = lean_array_get_size(v_a_5784_);
v___x_5802_ = l_Array_toSubarray___redArg(v_a_5784_, v___x_5799_, v___x_5801_);
v___x_5803_ = lean_array_get_size(v_discrInfos_5798_);
v___x_5804_ = l_Array_toSubarray___redArg(v_discrInfos_5798_, v___x_5799_, v___x_5803_);
v___x_5805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5805_, 0, v___x_5802_);
lean_ctor_set(v___x_5805_, 1, v___x_5804_);
v___x_5806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5806_, 0, v_addHEqualities_5800_);
lean_ctor_set(v___x_5806_, 1, v___x_5805_);
v___x_5807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5807_, 0, v_addHEqualities_5800_);
lean_ctor_set(v___x_5807_, 1, v___x_5806_);
v___x_5808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5808_, 0, v_a_5797_);
lean_ctor_set(v___x_5808_, 1, v___x_5807_);
v_sz_5809_ = lean_array_size(v_motiveArgs_5788_);
v___x_5810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(v_addEqualities_5785_, v_motiveArgs_5788_, v_sz_5809_, v___x_5786_, v___x_5808_, v___y_5790_, v___y_5791_, v___y_5792_, v___y_5793_);
if (lean_obj_tag(v___x_5810_) == 0)
{
lean_object* v_a_5811_; lean_object* v_snd_5812_; lean_object* v_snd_5813_; lean_object* v_fst_5814_; lean_object* v___x_5816_; uint8_t v_isShared_5817_; uint8_t v_isSharedCheck_5869_; 
v_a_5811_ = lean_ctor_get(v___x_5810_, 0);
lean_inc(v_a_5811_);
lean_dec_ref(v___x_5810_);
v_snd_5812_ = lean_ctor_get(v_a_5811_, 1);
lean_inc(v_snd_5812_);
v_snd_5813_ = lean_ctor_get(v_snd_5812_, 1);
lean_inc(v_snd_5813_);
v_fst_5814_ = lean_ctor_get(v_a_5811_, 0);
v_isSharedCheck_5869_ = !lean_is_exclusive(v_a_5811_);
if (v_isSharedCheck_5869_ == 0)
{
lean_object* v_unused_5870_; 
v_unused_5870_ = lean_ctor_get(v_a_5811_, 1);
lean_dec(v_unused_5870_);
v___x_5816_ = v_a_5811_;
v_isShared_5817_ = v_isSharedCheck_5869_;
goto v_resetjp_5815_;
}
else
{
lean_inc(v_fst_5814_);
lean_dec(v_a_5811_);
v___x_5816_ = lean_box(0);
v_isShared_5817_ = v_isSharedCheck_5869_;
goto v_resetjp_5815_;
}
v_resetjp_5815_:
{
lean_object* v_fst_5818_; lean_object* v___x_5820_; uint8_t v_isShared_5821_; uint8_t v_isSharedCheck_5867_; 
v_fst_5818_ = lean_ctor_get(v_snd_5812_, 0);
v_isSharedCheck_5867_ = !lean_is_exclusive(v_snd_5812_);
if (v_isSharedCheck_5867_ == 0)
{
lean_object* v_unused_5868_; 
v_unused_5868_ = lean_ctor_get(v_snd_5812_, 1);
lean_dec(v_unused_5868_);
v___x_5820_ = v_snd_5812_;
v_isShared_5821_ = v_isSharedCheck_5867_;
goto v_resetjp_5819_;
}
else
{
lean_inc(v_fst_5818_);
lean_dec(v_snd_5812_);
v___x_5820_ = lean_box(0);
v_isShared_5821_ = v_isSharedCheck_5867_;
goto v_resetjp_5819_;
}
v_resetjp_5819_:
{
lean_object* v_fst_5822_; lean_object* v___x_5824_; uint8_t v_isShared_5825_; uint8_t v_isSharedCheck_5865_; 
v_fst_5822_ = lean_ctor_get(v_snd_5813_, 0);
v_isSharedCheck_5865_ = !lean_is_exclusive(v_snd_5813_);
if (v_isSharedCheck_5865_ == 0)
{
lean_object* v_unused_5866_; 
v_unused_5866_ = lean_ctor_get(v_snd_5813_, 1);
lean_dec(v_unused_5866_);
v___x_5824_ = v_snd_5813_;
v_isShared_5825_ = v_isSharedCheck_5865_;
goto v_resetjp_5823_;
}
else
{
lean_inc(v_fst_5822_);
lean_dec(v_snd_5813_);
v___x_5824_ = lean_box(0);
v_isShared_5825_ = v_isSharedCheck_5865_;
goto v_resetjp_5823_;
}
v_resetjp_5823_:
{
uint8_t v___x_5826_; uint8_t v___x_5827_; uint8_t v___x_5828_; lean_object* v___x_5829_; 
v___x_5826_ = 0;
v___x_5827_ = 1;
v___x_5828_ = 1;
lean_inc(v_fst_5814_);
v___x_5829_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_5788_, v_fst_5814_, v___x_5826_, v___x_5827_, v___x_5826_, v___x_5827_, v___x_5828_, v___y_5790_, v___y_5791_, v___y_5792_, v___y_5793_);
lean_dec_ref(v_motiveArgs_5788_);
if (lean_obj_tag(v___x_5829_) == 0)
{
lean_object* v_a_5830_; lean_object* v___x_5831_; 
v_a_5830_ = lean_ctor_get(v___x_5829_, 0);
lean_inc(v_a_5830_);
lean_dec_ref(v___x_5829_);
v___x_5831_ = l_Lean_Meta_getLevel(v_fst_5814_, v___y_5790_, v___y_5791_, v___y_5792_, v___y_5793_);
if (lean_obj_tag(v___x_5831_) == 0)
{
lean_object* v_a_5832_; lean_object* v___x_5834_; uint8_t v_isShared_5835_; uint8_t v_isSharedCheck_5848_; 
v_a_5832_ = lean_ctor_get(v___x_5831_, 0);
v_isSharedCheck_5848_ = !lean_is_exclusive(v___x_5831_);
if (v_isSharedCheck_5848_ == 0)
{
v___x_5834_ = v___x_5831_;
v_isShared_5835_ = v_isSharedCheck_5848_;
goto v_resetjp_5833_;
}
else
{
lean_inc(v_a_5832_);
lean_dec(v___x_5831_);
v___x_5834_ = lean_box(0);
v_isShared_5835_ = v_isSharedCheck_5848_;
goto v_resetjp_5833_;
}
v_resetjp_5833_:
{
lean_object* v___x_5837_; 
if (v_isShared_5825_ == 0)
{
lean_ctor_set(v___x_5824_, 1, v_fst_5822_);
lean_ctor_set(v___x_5824_, 0, v_fst_5818_);
v___x_5837_ = v___x_5824_;
goto v_reusejp_5836_;
}
else
{
lean_object* v_reuseFailAlloc_5847_; 
v_reuseFailAlloc_5847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5847_, 0, v_fst_5818_);
lean_ctor_set(v_reuseFailAlloc_5847_, 1, v_fst_5822_);
v___x_5837_ = v_reuseFailAlloc_5847_;
goto v_reusejp_5836_;
}
v_reusejp_5836_:
{
lean_object* v___x_5839_; 
if (v_isShared_5821_ == 0)
{
lean_ctor_set(v___x_5820_, 1, v___x_5837_);
lean_ctor_set(v___x_5820_, 0, v_a_5832_);
v___x_5839_ = v___x_5820_;
goto v_reusejp_5838_;
}
else
{
lean_object* v_reuseFailAlloc_5846_; 
v_reuseFailAlloc_5846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5846_, 0, v_a_5832_);
lean_ctor_set(v_reuseFailAlloc_5846_, 1, v___x_5837_);
v___x_5839_ = v_reuseFailAlloc_5846_;
goto v_reusejp_5838_;
}
v_reusejp_5838_:
{
lean_object* v___x_5841_; 
if (v_isShared_5817_ == 0)
{
lean_ctor_set(v___x_5816_, 1, v___x_5839_);
lean_ctor_set(v___x_5816_, 0, v_a_5830_);
v___x_5841_ = v___x_5816_;
goto v_reusejp_5840_;
}
else
{
lean_object* v_reuseFailAlloc_5845_; 
v_reuseFailAlloc_5845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5845_, 0, v_a_5830_);
lean_ctor_set(v_reuseFailAlloc_5845_, 1, v___x_5839_);
v___x_5841_ = v_reuseFailAlloc_5845_;
goto v_reusejp_5840_;
}
v_reusejp_5840_:
{
lean_object* v___x_5843_; 
if (v_isShared_5835_ == 0)
{
lean_ctor_set(v___x_5834_, 0, v___x_5841_);
v___x_5843_ = v___x_5834_;
goto v_reusejp_5842_;
}
else
{
lean_object* v_reuseFailAlloc_5844_; 
v_reuseFailAlloc_5844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5844_, 0, v___x_5841_);
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
}
}
else
{
lean_object* v_a_5849_; lean_object* v___x_5851_; uint8_t v_isShared_5852_; uint8_t v_isSharedCheck_5856_; 
lean_dec(v_a_5830_);
lean_del_object(v___x_5824_);
lean_dec(v_fst_5822_);
lean_del_object(v___x_5820_);
lean_dec(v_fst_5818_);
lean_del_object(v___x_5816_);
v_a_5849_ = lean_ctor_get(v___x_5831_, 0);
v_isSharedCheck_5856_ = !lean_is_exclusive(v___x_5831_);
if (v_isSharedCheck_5856_ == 0)
{
v___x_5851_ = v___x_5831_;
v_isShared_5852_ = v_isSharedCheck_5856_;
goto v_resetjp_5850_;
}
else
{
lean_inc(v_a_5849_);
lean_dec(v___x_5831_);
v___x_5851_ = lean_box(0);
v_isShared_5852_ = v_isSharedCheck_5856_;
goto v_resetjp_5850_;
}
v_resetjp_5850_:
{
lean_object* v___x_5854_; 
if (v_isShared_5852_ == 0)
{
v___x_5854_ = v___x_5851_;
goto v_reusejp_5853_;
}
else
{
lean_object* v_reuseFailAlloc_5855_; 
v_reuseFailAlloc_5855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5855_, 0, v_a_5849_);
v___x_5854_ = v_reuseFailAlloc_5855_;
goto v_reusejp_5853_;
}
v_reusejp_5853_:
{
return v___x_5854_;
}
}
}
}
else
{
lean_object* v_a_5857_; lean_object* v___x_5859_; uint8_t v_isShared_5860_; uint8_t v_isSharedCheck_5864_; 
lean_del_object(v___x_5824_);
lean_dec(v_fst_5822_);
lean_del_object(v___x_5820_);
lean_dec(v_fst_5818_);
lean_del_object(v___x_5816_);
lean_dec(v_fst_5814_);
v_a_5857_ = lean_ctor_get(v___x_5829_, 0);
v_isSharedCheck_5864_ = !lean_is_exclusive(v___x_5829_);
if (v_isSharedCheck_5864_ == 0)
{
v___x_5859_ = v___x_5829_;
v_isShared_5860_ = v_isSharedCheck_5864_;
goto v_resetjp_5858_;
}
else
{
lean_inc(v_a_5857_);
lean_dec(v___x_5829_);
v___x_5859_ = lean_box(0);
v_isShared_5860_ = v_isSharedCheck_5864_;
goto v_resetjp_5858_;
}
v_resetjp_5858_:
{
lean_object* v___x_5862_; 
if (v_isShared_5860_ == 0)
{
v___x_5862_ = v___x_5859_;
goto v_reusejp_5861_;
}
else
{
lean_object* v_reuseFailAlloc_5863_; 
v_reuseFailAlloc_5863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5863_, 0, v_a_5857_);
v___x_5862_ = v_reuseFailAlloc_5863_;
goto v_reusejp_5861_;
}
v_reusejp_5861_:
{
return v___x_5862_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5871_; lean_object* v___x_5873_; uint8_t v_isShared_5874_; uint8_t v_isSharedCheck_5878_; 
lean_dec_ref(v_motiveArgs_5788_);
v_a_5871_ = lean_ctor_get(v___x_5810_, 0);
v_isSharedCheck_5878_ = !lean_is_exclusive(v___x_5810_);
if (v_isSharedCheck_5878_ == 0)
{
v___x_5873_ = v___x_5810_;
v_isShared_5874_ = v_isSharedCheck_5878_;
goto v_resetjp_5872_;
}
else
{
lean_inc(v_a_5871_);
lean_dec(v___x_5810_);
v___x_5873_ = lean_box(0);
v_isShared_5874_ = v_isSharedCheck_5878_;
goto v_resetjp_5872_;
}
v_resetjp_5872_:
{
lean_object* v___x_5876_; 
if (v_isShared_5874_ == 0)
{
v___x_5876_ = v___x_5873_;
goto v_reusejp_5875_;
}
else
{
lean_object* v_reuseFailAlloc_5877_; 
v_reuseFailAlloc_5877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5877_, 0, v_a_5871_);
v___x_5876_ = v_reuseFailAlloc_5877_;
goto v_reusejp_5875_;
}
v_reusejp_5875_:
{
return v___x_5876_;
}
}
}
}
else
{
lean_object* v_a_5879_; lean_object* v___x_5881_; uint8_t v_isShared_5882_; uint8_t v_isSharedCheck_5886_; 
lean_dec_ref(v_motiveArgs_5788_);
lean_dec_ref(v_a_5784_);
lean_dec_ref(v_toMatcherInfo_5783_);
v_a_5879_ = lean_ctor_get(v___x_5796_, 0);
v_isSharedCheck_5886_ = !lean_is_exclusive(v___x_5796_);
if (v_isSharedCheck_5886_ == 0)
{
v___x_5881_ = v___x_5796_;
v_isShared_5882_ = v_isSharedCheck_5886_;
goto v_resetjp_5880_;
}
else
{
lean_inc(v_a_5879_);
lean_dec(v___x_5796_);
v___x_5881_ = lean_box(0);
v_isShared_5882_ = v_isSharedCheck_5886_;
goto v_resetjp_5880_;
}
v_resetjp_5880_:
{
lean_object* v___x_5884_; 
if (v_isShared_5882_ == 0)
{
v___x_5884_ = v___x_5881_;
goto v_reusejp_5883_;
}
else
{
lean_object* v_reuseFailAlloc_5885_; 
v_reuseFailAlloc_5885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5885_, 0, v_a_5879_);
v___x_5884_ = v_reuseFailAlloc_5885_;
goto v_reusejp_5883_;
}
v_reusejp_5883_:
{
return v___x_5884_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed(lean_object* v_onMotive_5906_, lean_object* v_toMatcherInfo_5907_, lean_object* v_a_5908_, lean_object* v_addEqualities_5909_, lean_object* v___x_5910_, lean_object* v_discrs_5911_, lean_object* v_motiveArgs_5912_, lean_object* v_motiveBody_5913_, lean_object* v___y_5914_, lean_object* v___y_5915_, lean_object* v___y_5916_, lean_object* v___y_5917_, lean_object* v___y_5918_){
_start:
{
uint8_t v_addEqualities_boxed_5919_; size_t v___x_34398__boxed_5920_; lean_object* v_res_5921_; 
v_addEqualities_boxed_5919_ = lean_unbox(v_addEqualities_5909_);
v___x_34398__boxed_5920_ = lean_unbox_usize(v___x_5910_);
lean_dec(v___x_5910_);
v_res_5921_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(v_onMotive_5906_, v_toMatcherInfo_5907_, v_a_5908_, v_addEqualities_boxed_5919_, v___x_34398__boxed_5920_, v_discrs_5911_, v_motiveArgs_5912_, v_motiveBody_5913_, v___y_5914_, v___y_5915_, v___y_5916_, v___y_5917_);
lean_dec(v___y_5917_);
lean_dec_ref(v___y_5916_);
lean_dec(v___y_5915_);
lean_dec_ref(v___y_5914_);
lean_dec_ref(v_discrs_5911_);
return v_res_5921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(lean_object* v_as_5922_, size_t v_sz_5923_, size_t v_i_5924_, lean_object* v_b_5925_, lean_object* v___y_5926_, lean_object* v___y_5927_, lean_object* v___y_5928_, lean_object* v___y_5929_){
_start:
{
lean_object* v_a_5932_; uint8_t v___x_5936_; 
v___x_5936_ = lean_usize_dec_lt(v_i_5924_, v_sz_5923_);
if (v___x_5936_ == 0)
{
lean_object* v___x_5937_; 
v___x_5937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5937_, 0, v_b_5925_);
return v___x_5937_;
}
else
{
lean_object* v_snd_5938_; lean_object* v_snd_5939_; lean_object* v_fst_5940_; lean_object* v___x_5942_; uint8_t v_isShared_5943_; uint8_t v_isSharedCheck_6000_; 
v_snd_5938_ = lean_ctor_get(v_b_5925_, 1);
lean_inc(v_snd_5938_);
v_snd_5939_ = lean_ctor_get(v_snd_5938_, 1);
lean_inc(v_snd_5939_);
v_fst_5940_ = lean_ctor_get(v_b_5925_, 0);
v_isSharedCheck_6000_ = !lean_is_exclusive(v_b_5925_);
if (v_isSharedCheck_6000_ == 0)
{
lean_object* v_unused_6001_; 
v_unused_6001_ = lean_ctor_get(v_b_5925_, 1);
lean_dec(v_unused_6001_);
v___x_5942_ = v_b_5925_;
v_isShared_5943_ = v_isSharedCheck_6000_;
goto v_resetjp_5941_;
}
else
{
lean_inc(v_fst_5940_);
lean_dec(v_b_5925_);
v___x_5942_ = lean_box(0);
v_isShared_5943_ = v_isSharedCheck_6000_;
goto v_resetjp_5941_;
}
v_resetjp_5941_:
{
lean_object* v_fst_5944_; lean_object* v___x_5946_; uint8_t v_isShared_5947_; uint8_t v_isSharedCheck_5998_; 
v_fst_5944_ = lean_ctor_get(v_snd_5938_, 0);
v_isSharedCheck_5998_ = !lean_is_exclusive(v_snd_5938_);
if (v_isSharedCheck_5998_ == 0)
{
lean_object* v_unused_5999_; 
v_unused_5999_ = lean_ctor_get(v_snd_5938_, 1);
lean_dec(v_unused_5999_);
v___x_5946_ = v_snd_5938_;
v_isShared_5947_ = v_isSharedCheck_5998_;
goto v_resetjp_5945_;
}
else
{
lean_inc(v_fst_5944_);
lean_dec(v_snd_5938_);
v___x_5946_ = lean_box(0);
v_isShared_5947_ = v_isSharedCheck_5998_;
goto v_resetjp_5945_;
}
v_resetjp_5945_:
{
lean_object* v_array_5948_; lean_object* v_start_5949_; lean_object* v_stop_5950_; uint8_t v___x_5951_; 
v_array_5948_ = lean_ctor_get(v_snd_5939_, 0);
v_start_5949_ = lean_ctor_get(v_snd_5939_, 1);
v_stop_5950_ = lean_ctor_get(v_snd_5939_, 2);
v___x_5951_ = lean_nat_dec_lt(v_start_5949_, v_stop_5950_);
if (v___x_5951_ == 0)
{
lean_object* v___x_5953_; 
if (v_isShared_5947_ == 0)
{
v___x_5953_ = v___x_5946_;
goto v_reusejp_5952_;
}
else
{
lean_object* v_reuseFailAlloc_5958_; 
v_reuseFailAlloc_5958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5958_, 0, v_fst_5944_);
lean_ctor_set(v_reuseFailAlloc_5958_, 1, v_snd_5939_);
v___x_5953_ = v_reuseFailAlloc_5958_;
goto v_reusejp_5952_;
}
v_reusejp_5952_:
{
lean_object* v___x_5955_; 
if (v_isShared_5943_ == 0)
{
lean_ctor_set(v___x_5942_, 1, v___x_5953_);
v___x_5955_ = v___x_5942_;
goto v_reusejp_5954_;
}
else
{
lean_object* v_reuseFailAlloc_5957_; 
v_reuseFailAlloc_5957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5957_, 0, v_fst_5940_);
lean_ctor_set(v_reuseFailAlloc_5957_, 1, v___x_5953_);
v___x_5955_ = v_reuseFailAlloc_5957_;
goto v_reusejp_5954_;
}
v_reusejp_5954_:
{
lean_object* v___x_5956_; 
v___x_5956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5956_, 0, v___x_5955_);
return v___x_5956_;
}
}
}
else
{
lean_object* v___x_5960_; uint8_t v_isShared_5961_; uint8_t v_isSharedCheck_5994_; 
lean_inc(v_stop_5950_);
lean_inc(v_start_5949_);
lean_inc_ref(v_array_5948_);
v_isSharedCheck_5994_ = !lean_is_exclusive(v_snd_5939_);
if (v_isSharedCheck_5994_ == 0)
{
lean_object* v_unused_5995_; lean_object* v_unused_5996_; lean_object* v_unused_5997_; 
v_unused_5995_ = lean_ctor_get(v_snd_5939_, 2);
lean_dec(v_unused_5995_);
v_unused_5996_ = lean_ctor_get(v_snd_5939_, 1);
lean_dec(v_unused_5996_);
v_unused_5997_ = lean_ctor_get(v_snd_5939_, 0);
lean_dec(v_unused_5997_);
v___x_5960_ = v_snd_5939_;
v_isShared_5961_ = v_isSharedCheck_5994_;
goto v_resetjp_5959_;
}
else
{
lean_dec(v_snd_5939_);
v___x_5960_ = lean_box(0);
v_isShared_5961_ = v_isSharedCheck_5994_;
goto v_resetjp_5959_;
}
v_resetjp_5959_:
{
lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5966_; 
v___x_5962_ = lean_array_fget(v_array_5948_, v_start_5949_);
v___x_5963_ = lean_unsigned_to_nat(1u);
v___x_5964_ = lean_nat_add(v_start_5949_, v___x_5963_);
lean_dec(v_start_5949_);
if (v_isShared_5961_ == 0)
{
lean_ctor_set(v___x_5960_, 1, v___x_5964_);
v___x_5966_ = v___x_5960_;
goto v_reusejp_5965_;
}
else
{
lean_object* v_reuseFailAlloc_5993_; 
v_reuseFailAlloc_5993_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5993_, 0, v_array_5948_);
lean_ctor_set(v_reuseFailAlloc_5993_, 1, v___x_5964_);
lean_ctor_set(v_reuseFailAlloc_5993_, 2, v_stop_5950_);
v___x_5966_ = v_reuseFailAlloc_5993_;
goto v_reusejp_5965_;
}
v_reusejp_5965_:
{
lean_object* v___y_5968_; 
if (lean_obj_tag(v___x_5962_) == 0)
{
lean_object* v___x_5986_; lean_object* v___x_5987_; 
lean_del_object(v___x_5946_);
lean_del_object(v___x_5942_);
v___x_5986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5986_, 0, v_fst_5944_);
lean_ctor_set(v___x_5986_, 1, v___x_5966_);
v___x_5987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5987_, 0, v_fst_5940_);
lean_ctor_set(v___x_5987_, 1, v___x_5986_);
v_a_5932_ = v___x_5987_;
goto v___jp_5931_;
}
else
{
lean_object* v_val_5988_; lean_object* v_a_5989_; uint8_t v___x_5990_; 
v_val_5988_ = lean_ctor_get(v___x_5962_, 0);
lean_inc(v_val_5988_);
lean_dec_ref(v___x_5962_);
v_a_5989_ = lean_array_uget_borrowed(v_as_5922_, v_i_5924_);
v___x_5990_ = lean_unbox(v_val_5988_);
lean_dec(v_val_5988_);
if (v___x_5990_ == 0)
{
lean_object* v___x_5991_; 
lean_inc(v_a_5989_);
v___x_5991_ = l_Lean_Meta_mkEqRefl(v_a_5989_, v___y_5926_, v___y_5927_, v___y_5928_, v___y_5929_);
v___y_5968_ = v___x_5991_;
goto v___jp_5967_;
}
else
{
lean_object* v___x_5992_; 
lean_inc(v_a_5989_);
v___x_5992_ = l_Lean_Meta_mkHEqRefl(v_a_5989_, v___y_5926_, v___y_5927_, v___y_5928_, v___y_5929_);
v___y_5968_ = v___x_5992_;
goto v___jp_5967_;
}
}
v___jp_5967_:
{
if (lean_obj_tag(v___y_5968_) == 0)
{
lean_object* v_a_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___x_5973_; 
v_a_5969_ = lean_ctor_get(v___y_5968_, 0);
lean_inc(v_a_5969_);
lean_dec_ref(v___y_5968_);
v___x_5970_ = lean_array_push(v_fst_5940_, v_a_5969_);
v___x_5971_ = lean_nat_add(v_fst_5944_, v___x_5963_);
lean_dec(v_fst_5944_);
if (v_isShared_5947_ == 0)
{
lean_ctor_set(v___x_5946_, 1, v___x_5966_);
lean_ctor_set(v___x_5946_, 0, v___x_5971_);
v___x_5973_ = v___x_5946_;
goto v_reusejp_5972_;
}
else
{
lean_object* v_reuseFailAlloc_5977_; 
v_reuseFailAlloc_5977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5977_, 0, v___x_5971_);
lean_ctor_set(v_reuseFailAlloc_5977_, 1, v___x_5966_);
v___x_5973_ = v_reuseFailAlloc_5977_;
goto v_reusejp_5972_;
}
v_reusejp_5972_:
{
lean_object* v___x_5975_; 
if (v_isShared_5943_ == 0)
{
lean_ctor_set(v___x_5942_, 1, v___x_5973_);
lean_ctor_set(v___x_5942_, 0, v___x_5970_);
v___x_5975_ = v___x_5942_;
goto v_reusejp_5974_;
}
else
{
lean_object* v_reuseFailAlloc_5976_; 
v_reuseFailAlloc_5976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5976_, 0, v___x_5970_);
lean_ctor_set(v_reuseFailAlloc_5976_, 1, v___x_5973_);
v___x_5975_ = v_reuseFailAlloc_5976_;
goto v_reusejp_5974_;
}
v_reusejp_5974_:
{
v_a_5932_ = v___x_5975_;
goto v___jp_5931_;
}
}
}
else
{
lean_object* v_a_5978_; lean_object* v___x_5980_; uint8_t v_isShared_5981_; uint8_t v_isSharedCheck_5985_; 
lean_dec_ref(v___x_5966_);
lean_del_object(v___x_5946_);
lean_dec(v_fst_5944_);
lean_del_object(v___x_5942_);
lean_dec(v_fst_5940_);
v_a_5978_ = lean_ctor_get(v___y_5968_, 0);
v_isSharedCheck_5985_ = !lean_is_exclusive(v___y_5968_);
if (v_isSharedCheck_5985_ == 0)
{
v___x_5980_ = v___y_5968_;
v_isShared_5981_ = v_isSharedCheck_5985_;
goto v_resetjp_5979_;
}
else
{
lean_inc(v_a_5978_);
lean_dec(v___y_5968_);
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
}
}
}
}
}
}
v___jp_5931_:
{
size_t v___x_5933_; size_t v___x_5934_; 
v___x_5933_ = ((size_t)1ULL);
v___x_5934_ = lean_usize_add(v_i_5924_, v___x_5933_);
v_i_5924_ = v___x_5934_;
v_b_5925_ = v_a_5932_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8___boxed(lean_object* v_as_6002_, lean_object* v_sz_6003_, lean_object* v_i_6004_, lean_object* v_b_6005_, lean_object* v___y_6006_, lean_object* v___y_6007_, lean_object* v___y_6008_, lean_object* v___y_6009_, lean_object* v___y_6010_){
_start:
{
size_t v_sz_boxed_6011_; size_t v_i_boxed_6012_; lean_object* v_res_6013_; 
v_sz_boxed_6011_ = lean_unbox_usize(v_sz_6003_);
lean_dec(v_sz_6003_);
v_i_boxed_6012_ = lean_unbox_usize(v_i_6004_);
lean_dec(v_i_6004_);
v_res_6013_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(v_as_6002_, v_sz_boxed_6011_, v_i_boxed_6012_, v_b_6005_, v___y_6006_, v___y_6007_, v___y_6008_, v___y_6009_);
lean_dec(v___y_6009_);
lean_dec_ref(v___y_6008_);
lean_dec(v___y_6007_);
lean_dec_ref(v___y_6006_);
lean_dec_ref(v_as_6002_);
return v_res_6013_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(lean_object* v___x_6014_, lean_object* v___y_6015_, lean_object* v___y_6016_, lean_object* v___y_6017_, lean_object* v___y_6018_){
_start:
{
lean_object* v___x_6020_; 
v___x_6020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6020_, 0, v___x_6014_);
return v___x_6020_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed(lean_object* v___x_6021_, lean_object* v___y_6022_, lean_object* v___y_6023_, lean_object* v___y_6024_, lean_object* v___y_6025_, lean_object* v___y_6026_){
_start:
{
lean_object* v_res_6027_; 
v_res_6027_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(v___x_6021_, v___y_6022_, v___y_6023_, v___y_6024_, v___y_6025_);
lean_dec(v___y_6025_);
lean_dec_ref(v___y_6024_);
lean_dec(v___y_6023_);
lean_dec_ref(v___y_6022_);
return v_res_6027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(size_t v_sz_6028_, size_t v_i_6029_, lean_object* v_bs_6030_, lean_object* v___y_6031_, lean_object* v___y_6032_, lean_object* v___y_6033_){
_start:
{
uint8_t v___x_6035_; 
v___x_6035_ = lean_usize_dec_lt(v_i_6029_, v_sz_6028_);
if (v___x_6035_ == 0)
{
lean_object* v___x_6036_; 
v___x_6036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6036_, 0, v_bs_6030_);
return v___x_6036_;
}
else
{
lean_object* v_v_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; 
v_v_6037_ = lean_array_uget_borrowed(v_bs_6030_, v_i_6029_);
v___x_6038_ = l_Lean_Expr_fvarId_x21(v_v_6037_);
v___x_6039_ = l_Lean_FVarId_getUserName___redArg(v___x_6038_, v___y_6031_, v___y_6032_, v___y_6033_);
if (lean_obj_tag(v___x_6039_) == 0)
{
lean_object* v_a_6040_; lean_object* v___x_6041_; lean_object* v_bs_x27_6042_; size_t v___x_6043_; size_t v___x_6044_; lean_object* v___x_6045_; 
v_a_6040_ = lean_ctor_get(v___x_6039_, 0);
lean_inc(v_a_6040_);
lean_dec_ref(v___x_6039_);
v___x_6041_ = lean_unsigned_to_nat(0u);
v_bs_x27_6042_ = lean_array_uset(v_bs_6030_, v_i_6029_, v___x_6041_);
v___x_6043_ = ((size_t)1ULL);
v___x_6044_ = lean_usize_add(v_i_6029_, v___x_6043_);
v___x_6045_ = lean_array_uset(v_bs_x27_6042_, v_i_6029_, v_a_6040_);
v_i_6029_ = v___x_6044_;
v_bs_6030_ = v___x_6045_;
goto _start;
}
else
{
lean_object* v_a_6047_; lean_object* v___x_6049_; uint8_t v_isShared_6050_; uint8_t v_isSharedCheck_6054_; 
lean_dec_ref(v_bs_6030_);
v_a_6047_ = lean_ctor_get(v___x_6039_, 0);
v_isSharedCheck_6054_ = !lean_is_exclusive(v___x_6039_);
if (v_isSharedCheck_6054_ == 0)
{
v___x_6049_ = v___x_6039_;
v_isShared_6050_ = v_isSharedCheck_6054_;
goto v_resetjp_6048_;
}
else
{
lean_inc(v_a_6047_);
lean_dec(v___x_6039_);
v___x_6049_ = lean_box(0);
v_isShared_6050_ = v_isSharedCheck_6054_;
goto v_resetjp_6048_;
}
v_resetjp_6048_:
{
lean_object* v___x_6052_; 
if (v_isShared_6050_ == 0)
{
v___x_6052_ = v___x_6049_;
goto v_reusejp_6051_;
}
else
{
lean_object* v_reuseFailAlloc_6053_; 
v_reuseFailAlloc_6053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6053_, 0, v_a_6047_);
v___x_6052_ = v_reuseFailAlloc_6053_;
goto v_reusejp_6051_;
}
v_reusejp_6051_:
{
return v___x_6052_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg___boxed(lean_object* v_sz_6055_, lean_object* v_i_6056_, lean_object* v_bs_6057_, lean_object* v___y_6058_, lean_object* v___y_6059_, lean_object* v___y_6060_, lean_object* v___y_6061_){
_start:
{
size_t v_sz_boxed_6062_; size_t v_i_boxed_6063_; lean_object* v_res_6064_; 
v_sz_boxed_6062_ = lean_unbox_usize(v_sz_6055_);
lean_dec(v_sz_6055_);
v_i_boxed_6063_ = lean_unbox_usize(v_i_6056_);
lean_dec(v_i_6056_);
v_res_6064_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_boxed_6062_, v_i_boxed_6063_, v_bs_6057_, v___y_6058_, v___y_6059_, v___y_6060_);
lean_dec(v___y_6060_);
lean_dec_ref(v___y_6059_);
lean_dec_ref(v___y_6058_);
return v_res_6064_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(lean_object* v_xs_6065_, lean_object* v_x_6066_, lean_object* v___y_6067_, lean_object* v___y_6068_, lean_object* v___y_6069_, lean_object* v___y_6070_){
_start:
{
size_t v_sz_6072_; size_t v___x_6073_; lean_object* v___x_6074_; 
v_sz_6072_ = lean_array_size(v_xs_6065_);
v___x_6073_ = ((size_t)0ULL);
v___x_6074_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_6072_, v___x_6073_, v_xs_6065_, v___y_6067_, v___y_6069_, v___y_6070_);
return v___x_6074_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3___boxed(lean_object* v_xs_6075_, lean_object* v_x_6076_, lean_object* v___y_6077_, lean_object* v___y_6078_, lean_object* v___y_6079_, lean_object* v___y_6080_, lean_object* v___y_6081_){
_start:
{
lean_object* v_res_6082_; 
v_res_6082_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(v_xs_6075_, v_x_6076_, v___y_6077_, v___y_6078_, v___y_6079_, v___y_6080_);
lean_dec(v___y_6080_);
lean_dec_ref(v___y_6079_);
lean_dec(v___y_6078_);
lean_dec_ref(v___y_6077_);
lean_dec_ref(v_x_6076_);
return v_res_6082_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(lean_object* v___x_6083_, lean_object* v___x_6084_, lean_object* v___f_6085_, uint8_t v___x_6086_, lean_object* v_fst_6087_, lean_object* v___x_6088_, lean_object* v___x_6089_, lean_object* v___x_6090_, lean_object* v___y_6091_, lean_object* v___y_6092_, lean_object* v___y_6093_, lean_object* v___y_6094_){
_start:
{
lean_object* v___x_6096_; 
v___x_6096_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v___x_6083_, v___x_6084_, v___f_6085_, v___x_6086_, v___x_6086_, v___y_6091_, v___y_6092_, v___y_6093_, v___y_6094_);
if (lean_obj_tag(v___x_6096_) == 0)
{
lean_object* v_a_6097_; lean_object* v___x_6099_; uint8_t v_isShared_6100_; uint8_t v_isSharedCheck_6109_; 
v_a_6097_ = lean_ctor_get(v___x_6096_, 0);
v_isSharedCheck_6109_ = !lean_is_exclusive(v___x_6096_);
if (v_isSharedCheck_6109_ == 0)
{
v___x_6099_ = v___x_6096_;
v_isShared_6100_ = v_isSharedCheck_6109_;
goto v_resetjp_6098_;
}
else
{
lean_inc(v_a_6097_);
lean_dec(v___x_6096_);
v___x_6099_ = lean_box(0);
v_isShared_6100_ = v_isSharedCheck_6109_;
goto v_resetjp_6098_;
}
v_resetjp_6098_:
{
lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6107_; 
v___x_6101_ = lean_array_push(v_fst_6087_, v_a_6097_);
v___x_6102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6102_, 0, v___x_6088_);
lean_ctor_set(v___x_6102_, 1, v___x_6089_);
v___x_6103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6103_, 0, v___x_6090_);
lean_ctor_set(v___x_6103_, 1, v___x_6102_);
v___x_6104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6104_, 0, v___x_6101_);
lean_ctor_set(v___x_6104_, 1, v___x_6103_);
v___x_6105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6105_, 0, v___x_6104_);
if (v_isShared_6100_ == 0)
{
lean_ctor_set(v___x_6099_, 0, v___x_6105_);
v___x_6107_ = v___x_6099_;
goto v_reusejp_6106_;
}
else
{
lean_object* v_reuseFailAlloc_6108_; 
v_reuseFailAlloc_6108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6108_, 0, v___x_6105_);
v___x_6107_ = v_reuseFailAlloc_6108_;
goto v_reusejp_6106_;
}
v_reusejp_6106_:
{
return v___x_6107_;
}
}
}
else
{
lean_object* v_a_6110_; lean_object* v___x_6112_; uint8_t v_isShared_6113_; uint8_t v_isSharedCheck_6117_; 
lean_dec_ref(v___x_6090_);
lean_dec_ref(v___x_6089_);
lean_dec_ref(v___x_6088_);
lean_dec(v_fst_6087_);
v_a_6110_ = lean_ctor_get(v___x_6096_, 0);
v_isSharedCheck_6117_ = !lean_is_exclusive(v___x_6096_);
if (v_isSharedCheck_6117_ == 0)
{
v___x_6112_ = v___x_6096_;
v_isShared_6113_ = v_isSharedCheck_6117_;
goto v_resetjp_6111_;
}
else
{
lean_inc(v_a_6110_);
lean_dec(v___x_6096_);
v___x_6112_ = lean_box(0);
v_isShared_6113_ = v_isSharedCheck_6117_;
goto v_resetjp_6111_;
}
v_resetjp_6111_:
{
lean_object* v___x_6115_; 
if (v_isShared_6113_ == 0)
{
v___x_6115_ = v___x_6112_;
goto v_reusejp_6114_;
}
else
{
lean_object* v_reuseFailAlloc_6116_; 
v_reuseFailAlloc_6116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6116_, 0, v_a_6110_);
v___x_6115_ = v_reuseFailAlloc_6116_;
goto v_reusejp_6114_;
}
v_reusejp_6114_:
{
return v___x_6115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed(lean_object* v___x_6118_, lean_object* v___x_6119_, lean_object* v___f_6120_, lean_object* v___x_6121_, lean_object* v_fst_6122_, lean_object* v___x_6123_, lean_object* v___x_6124_, lean_object* v___x_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_, lean_object* v___y_6129_, lean_object* v___y_6130_){
_start:
{
uint8_t v___x_34861__boxed_6131_; lean_object* v_res_6132_; 
v___x_34861__boxed_6131_ = lean_unbox(v___x_6121_);
v_res_6132_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(v___x_6118_, v___x_6119_, v___f_6120_, v___x_34861__boxed_6131_, v_fst_6122_, v___x_6123_, v___x_6124_, v___x_6125_, v___y_6126_, v___y_6127_, v___y_6128_, v___y_6129_);
lean_dec(v___y_6129_);
lean_dec_ref(v___y_6128_);
lean_dec(v___y_6127_);
lean_dec_ref(v___y_6126_);
return v_res_6132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(lean_object* v_fvars_6133_, lean_object* v_names_6134_, lean_object* v_k_6135_, lean_object* v___y_6136_, lean_object* v___y_6137_, lean_object* v___y_6138_, lean_object* v___y_6139_){
_start:
{
lean_object* v___x_6141_; 
v___x_6141_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_6133_, v_names_6134_, v_k_6135_, v___y_6136_, v___y_6137_, v___y_6138_, v___y_6139_);
if (lean_obj_tag(v___x_6141_) == 0)
{
lean_object* v_a_6142_; lean_object* v___x_6144_; uint8_t v_isShared_6145_; uint8_t v_isSharedCheck_6149_; 
v_a_6142_ = lean_ctor_get(v___x_6141_, 0);
v_isSharedCheck_6149_ = !lean_is_exclusive(v___x_6141_);
if (v_isSharedCheck_6149_ == 0)
{
v___x_6144_ = v___x_6141_;
v_isShared_6145_ = v_isSharedCheck_6149_;
goto v_resetjp_6143_;
}
else
{
lean_inc(v_a_6142_);
lean_dec(v___x_6141_);
v___x_6144_ = lean_box(0);
v_isShared_6145_ = v_isSharedCheck_6149_;
goto v_resetjp_6143_;
}
v_resetjp_6143_:
{
lean_object* v___x_6147_; 
if (v_isShared_6145_ == 0)
{
v___x_6147_ = v___x_6144_;
goto v_reusejp_6146_;
}
else
{
lean_object* v_reuseFailAlloc_6148_; 
v_reuseFailAlloc_6148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6148_, 0, v_a_6142_);
v___x_6147_ = v_reuseFailAlloc_6148_;
goto v_reusejp_6146_;
}
v_reusejp_6146_:
{
return v___x_6147_;
}
}
}
else
{
lean_object* v_a_6150_; lean_object* v___x_6152_; uint8_t v_isShared_6153_; uint8_t v_isSharedCheck_6157_; 
v_a_6150_ = lean_ctor_get(v___x_6141_, 0);
v_isSharedCheck_6157_ = !lean_is_exclusive(v___x_6141_);
if (v_isSharedCheck_6157_ == 0)
{
v___x_6152_ = v___x_6141_;
v_isShared_6153_ = v_isSharedCheck_6157_;
goto v_resetjp_6151_;
}
else
{
lean_inc(v_a_6150_);
lean_dec(v___x_6141_);
v___x_6152_ = lean_box(0);
v_isShared_6153_ = v_isSharedCheck_6157_;
goto v_resetjp_6151_;
}
v_resetjp_6151_:
{
lean_object* v___x_6155_; 
if (v_isShared_6153_ == 0)
{
v___x_6155_ = v___x_6152_;
goto v_reusejp_6154_;
}
else
{
lean_object* v_reuseFailAlloc_6156_; 
v_reuseFailAlloc_6156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6156_, 0, v_a_6150_);
v___x_6155_ = v_reuseFailAlloc_6156_;
goto v_reusejp_6154_;
}
v_reusejp_6154_:
{
return v___x_6155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg___boxed(lean_object* v_fvars_6158_, lean_object* v_names_6159_, lean_object* v_k_6160_, lean_object* v___y_6161_, lean_object* v___y_6162_, lean_object* v___y_6163_, lean_object* v___y_6164_, lean_object* v___y_6165_){
_start:
{
lean_object* v_res_6166_; 
v_res_6166_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_fvars_6158_, v_names_6159_, v_k_6160_, v___y_6161_, v___y_6162_, v___y_6163_, v___y_6164_);
lean_dec(v___y_6164_);
lean_dec_ref(v___y_6163_);
lean_dec(v___y_6162_);
lean_dec_ref(v___y_6161_);
lean_dec_ref(v_names_6159_);
lean_dec_ref(v_fvars_6158_);
return v_res_6166_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(lean_object* v___x_6167_, lean_object* v_xs_6168_, lean_object* v_remaining_x27_6169_, lean_object* v_ys4_6170_, lean_object* v_onAlt_6171_, lean_object* v_a_6172_, lean_object* v_altType_6173_, uint8_t v___x_6174_, uint8_t v___x_6175_, lean_object* v___y_6176_, lean_object* v___y_6177_, lean_object* v___y_6178_, lean_object* v___y_6179_){
_start:
{
lean_object* v___x_6181_; 
v___x_6181_ = l_Lean_Meta_instantiateLambda(v___x_6167_, v_xs_6168_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_);
if (lean_obj_tag(v___x_6181_) == 0)
{
lean_object* v_a_6182_; lean_object* v___x_6183_; lean_object* v___x_6184_; 
v_a_6182_ = lean_ctor_get(v___x_6181_, 0);
lean_inc(v_a_6182_);
lean_dec_ref(v___x_6181_);
lean_inc_ref(v_ys4_6170_);
lean_inc_ref(v_remaining_x27_6169_);
lean_inc_ref_n(v_xs_6168_, 2);
v___x_6183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6183_, 0, v_xs_6168_);
lean_ctor_set(v___x_6183_, 1, v_xs_6168_);
lean_ctor_set(v___x_6183_, 2, v_remaining_x27_6169_);
lean_ctor_set(v___x_6183_, 3, v_remaining_x27_6169_);
lean_ctor_set(v___x_6183_, 4, v_ys4_6170_);
lean_inc(v___y_6179_);
lean_inc_ref(v___y_6178_);
lean_inc(v___y_6177_);
lean_inc_ref(v___y_6176_);
v___x_6184_ = lean_apply_9(v_onAlt_6171_, v_a_6172_, v_altType_6173_, v___x_6183_, v_a_6182_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_, lean_box(0));
if (lean_obj_tag(v___x_6184_) == 0)
{
lean_object* v_a_6185_; lean_object* v___x_6186_; uint8_t v___x_6187_; lean_object* v___x_6188_; 
v_a_6185_ = lean_ctor_get(v___x_6184_, 0);
lean_inc(v_a_6185_);
lean_dec_ref(v___x_6184_);
v___x_6186_ = l_Array_append___redArg(v_xs_6168_, v_ys4_6170_);
lean_dec_ref(v_ys4_6170_);
v___x_6187_ = 1;
v___x_6188_ = l_Lean_Meta_mkLambdaFVars(v___x_6186_, v_a_6185_, v___x_6174_, v___x_6175_, v___x_6174_, v___x_6175_, v___x_6187_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_);
lean_dec(v___y_6179_);
lean_dec_ref(v___y_6178_);
lean_dec(v___y_6177_);
lean_dec_ref(v___y_6176_);
lean_dec_ref(v___x_6186_);
return v___x_6188_;
}
else
{
lean_dec(v___y_6179_);
lean_dec_ref(v___y_6178_);
lean_dec(v___y_6177_);
lean_dec_ref(v___y_6176_);
lean_dec_ref(v_ys4_6170_);
lean_dec_ref(v_xs_6168_);
return v___x_6184_;
}
}
else
{
lean_dec(v___y_6179_);
lean_dec_ref(v___y_6178_);
lean_dec(v___y_6177_);
lean_dec_ref(v___y_6176_);
lean_dec_ref(v_altType_6173_);
lean_dec(v_a_6172_);
lean_dec_ref(v_onAlt_6171_);
lean_dec_ref(v_ys4_6170_);
lean_dec_ref(v_remaining_x27_6169_);
lean_dec_ref(v_xs_6168_);
return v___x_6181_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed(lean_object* v___x_6189_, lean_object* v_xs_6190_, lean_object* v_remaining_x27_6191_, lean_object* v_ys4_6192_, lean_object* v_onAlt_6193_, lean_object* v_a_6194_, lean_object* v_altType_6195_, lean_object* v___x_6196_, lean_object* v___x_6197_, lean_object* v___y_6198_, lean_object* v___y_6199_, lean_object* v___y_6200_, lean_object* v___y_6201_, lean_object* v___y_6202_){
_start:
{
uint8_t v___x_34988__boxed_6203_; uint8_t v___x_34989__boxed_6204_; lean_object* v_res_6205_; 
v___x_34988__boxed_6203_ = lean_unbox(v___x_6196_);
v___x_34989__boxed_6204_ = lean_unbox(v___x_6197_);
v_res_6205_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(v___x_6189_, v_xs_6190_, v_remaining_x27_6191_, v_ys4_6192_, v_onAlt_6193_, v_a_6194_, v_altType_6195_, v___x_34988__boxed_6203_, v___x_34989__boxed_6204_, v___y_6198_, v___y_6199_, v___y_6200_, v___y_6201_);
return v_res_6205_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(lean_object* v___x_6206_, lean_object* v___f_6207_, uint8_t v___x_6208_, lean_object* v_xs_6209_, lean_object* v_remaining_x27_6210_, lean_object* v_onAlt_6211_, lean_object* v_a_6212_, uint8_t v___x_6213_, lean_object* v_ys4_6214_, lean_object* v_altType_6215_, lean_object* v___y_6216_, lean_object* v___y_6217_, lean_object* v___y_6218_, lean_object* v___y_6219_){
_start:
{
lean_object* v___x_6221_; 
lean_inc_ref(v___x_6206_);
v___x_6221_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v___x_6206_, v___f_6207_, v___x_6208_, v___y_6216_, v___y_6217_, v___y_6218_, v___y_6219_);
if (lean_obj_tag(v___x_6221_) == 0)
{
lean_object* v_a_6222_; lean_object* v___x_6223_; lean_object* v___x_6224_; lean_object* v___f_6225_; lean_object* v___x_6226_; 
v_a_6222_ = lean_ctor_get(v___x_6221_, 0);
lean_inc(v_a_6222_);
lean_dec_ref(v___x_6221_);
v___x_6223_ = lean_box(v___x_6208_);
v___x_6224_ = lean_box(v___x_6213_);
lean_inc_ref(v_xs_6209_);
v___f_6225_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_6225_, 0, v___x_6206_);
lean_closure_set(v___f_6225_, 1, v_xs_6209_);
lean_closure_set(v___f_6225_, 2, v_remaining_x27_6210_);
lean_closure_set(v___f_6225_, 3, v_ys4_6214_);
lean_closure_set(v___f_6225_, 4, v_onAlt_6211_);
lean_closure_set(v___f_6225_, 5, v_a_6212_);
lean_closure_set(v___f_6225_, 6, v_altType_6215_);
lean_closure_set(v___f_6225_, 7, v___x_6223_);
lean_closure_set(v___f_6225_, 8, v___x_6224_);
v___x_6226_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_xs_6209_, v_a_6222_, v___f_6225_, v___y_6216_, v___y_6217_, v___y_6218_, v___y_6219_);
lean_dec(v_a_6222_);
lean_dec_ref(v_xs_6209_);
return v___x_6226_;
}
else
{
lean_object* v_a_6227_; lean_object* v___x_6229_; uint8_t v_isShared_6230_; uint8_t v_isSharedCheck_6234_; 
lean_dec_ref(v_altType_6215_);
lean_dec_ref(v_ys4_6214_);
lean_dec(v_a_6212_);
lean_dec_ref(v_onAlt_6211_);
lean_dec_ref(v_remaining_x27_6210_);
lean_dec_ref(v_xs_6209_);
lean_dec_ref(v___x_6206_);
v_a_6227_ = lean_ctor_get(v___x_6221_, 0);
v_isSharedCheck_6234_ = !lean_is_exclusive(v___x_6221_);
if (v_isSharedCheck_6234_ == 0)
{
v___x_6229_ = v___x_6221_;
v_isShared_6230_ = v_isSharedCheck_6234_;
goto v_resetjp_6228_;
}
else
{
lean_inc(v_a_6227_);
lean_dec(v___x_6221_);
v___x_6229_ = lean_box(0);
v_isShared_6230_ = v_isSharedCheck_6234_;
goto v_resetjp_6228_;
}
v_resetjp_6228_:
{
lean_object* v___x_6232_; 
if (v_isShared_6230_ == 0)
{
v___x_6232_ = v___x_6229_;
goto v_reusejp_6231_;
}
else
{
lean_object* v_reuseFailAlloc_6233_; 
v_reuseFailAlloc_6233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6233_, 0, v_a_6227_);
v___x_6232_ = v_reuseFailAlloc_6233_;
goto v_reusejp_6231_;
}
v_reusejp_6231_:
{
return v___x_6232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed(lean_object* v___x_6235_, lean_object* v___f_6236_, lean_object* v___x_6237_, lean_object* v_xs_6238_, lean_object* v_remaining_x27_6239_, lean_object* v_onAlt_6240_, lean_object* v_a_6241_, lean_object* v___x_6242_, lean_object* v_ys4_6243_, lean_object* v_altType_6244_, lean_object* v___y_6245_, lean_object* v___y_6246_, lean_object* v___y_6247_, lean_object* v___y_6248_, lean_object* v___y_6249_){
_start:
{
uint8_t v___x_35031__boxed_6250_; uint8_t v___x_35032__boxed_6251_; lean_object* v_res_6252_; 
v___x_35031__boxed_6250_ = lean_unbox(v___x_6237_);
v___x_35032__boxed_6251_ = lean_unbox(v___x_6242_);
v_res_6252_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(v___x_6235_, v___f_6236_, v___x_35031__boxed_6250_, v_xs_6238_, v_remaining_x27_6239_, v_onAlt_6240_, v_a_6241_, v___x_35032__boxed_6251_, v_ys4_6243_, v_altType_6244_, v___y_6245_, v___y_6246_, v___y_6247_, v___y_6248_);
lean_dec(v___y_6248_);
lean_dec_ref(v___y_6247_);
lean_dec(v___y_6246_);
lean_dec_ref(v___y_6245_);
return v_res_6252_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(lean_object* v___x_6253_, lean_object* v___f_6254_, uint8_t v___x_6255_, lean_object* v_remaining_x27_6256_, lean_object* v_onAlt_6257_, lean_object* v_a_6258_, uint8_t v___x_6259_, lean_object* v_extraEqualities_6260_, lean_object* v_xs_6261_, lean_object* v_altType_6262_, lean_object* v___y_6263_, lean_object* v___y_6264_, lean_object* v___y_6265_, lean_object* v___y_6266_){
_start:
{
lean_object* v___x_6268_; lean_object* v___x_6269_; lean_object* v___f_6270_; lean_object* v___x_6271_; lean_object* v___x_6272_; 
v___x_6268_ = lean_box(v___x_6255_);
v___x_6269_ = lean_box(v___x_6259_);
v___f_6270_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed), 15, 8);
lean_closure_set(v___f_6270_, 0, v___x_6253_);
lean_closure_set(v___f_6270_, 1, v___f_6254_);
lean_closure_set(v___f_6270_, 2, v___x_6268_);
lean_closure_set(v___f_6270_, 3, v_xs_6261_);
lean_closure_set(v___f_6270_, 4, v_remaining_x27_6256_);
lean_closure_set(v___f_6270_, 5, v_onAlt_6257_);
lean_closure_set(v___f_6270_, 6, v_a_6258_);
lean_closure_set(v___f_6270_, 7, v___x_6269_);
v___x_6271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6271_, 0, v_extraEqualities_6260_);
v___x_6272_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_6262_, v___x_6271_, v___f_6270_, v___x_6255_, v___x_6255_, v___y_6263_, v___y_6264_, v___y_6265_, v___y_6266_);
return v___x_6272_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed(lean_object* v___x_6273_, lean_object* v___f_6274_, lean_object* v___x_6275_, lean_object* v_remaining_x27_6276_, lean_object* v_onAlt_6277_, lean_object* v_a_6278_, lean_object* v___x_6279_, lean_object* v_extraEqualities_6280_, lean_object* v_xs_6281_, lean_object* v_altType_6282_, lean_object* v___y_6283_, lean_object* v___y_6284_, lean_object* v___y_6285_, lean_object* v___y_6286_, lean_object* v___y_6287_){
_start:
{
uint8_t v___x_35086__boxed_6288_; uint8_t v___x_35087__boxed_6289_; lean_object* v_res_6290_; 
v___x_35086__boxed_6288_ = lean_unbox(v___x_6275_);
v___x_35087__boxed_6289_ = lean_unbox(v___x_6279_);
v_res_6290_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(v___x_6273_, v___f_6274_, v___x_35086__boxed_6288_, v_remaining_x27_6276_, v_onAlt_6277_, v_a_6278_, v___x_35087__boxed_6289_, v_extraEqualities_6280_, v_xs_6281_, v_altType_6282_, v___y_6283_, v___y_6284_, v___y_6285_, v___y_6286_);
lean_dec(v___y_6286_);
lean_dec_ref(v___y_6285_);
lean_dec(v___y_6284_);
lean_dec_ref(v___y_6283_);
return v_res_6290_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(lean_object* v_upperBound_6292_, lean_object* v_onAlt_6293_, lean_object* v_extraEqualities_6294_, lean_object* v_a_6295_, lean_object* v_b_6296_, lean_object* v___y_6297_, lean_object* v___y_6298_, lean_object* v___y_6299_, lean_object* v___y_6300_){
_start:
{
lean_object* v___y_6303_; uint8_t v___x_6326_; 
v___x_6326_ = lean_nat_dec_lt(v_a_6295_, v_upperBound_6292_);
if (v___x_6326_ == 0)
{
lean_object* v___x_6327_; 
lean_dec(v_a_6295_);
lean_dec(v_extraEqualities_6294_);
lean_dec_ref(v_onAlt_6293_);
v___x_6327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6327_, 0, v_b_6296_);
return v___x_6327_;
}
else
{
lean_object* v_snd_6328_; lean_object* v_snd_6329_; lean_object* v_snd_6330_; lean_object* v_fst_6331_; lean_object* v___x_6333_; uint8_t v_isShared_6334_; uint8_t v_isSharedCheck_6438_; 
v_snd_6328_ = lean_ctor_get(v_b_6296_, 1);
lean_inc(v_snd_6328_);
v_snd_6329_ = lean_ctor_get(v_snd_6328_, 1);
lean_inc(v_snd_6329_);
v_snd_6330_ = lean_ctor_get(v_snd_6329_, 1);
lean_inc(v_snd_6330_);
v_fst_6331_ = lean_ctor_get(v_b_6296_, 0);
v_isSharedCheck_6438_ = !lean_is_exclusive(v_b_6296_);
if (v_isSharedCheck_6438_ == 0)
{
lean_object* v_unused_6439_; 
v_unused_6439_ = lean_ctor_get(v_b_6296_, 1);
lean_dec(v_unused_6439_);
v___x_6333_ = v_b_6296_;
v_isShared_6334_ = v_isSharedCheck_6438_;
goto v_resetjp_6332_;
}
else
{
lean_inc(v_fst_6331_);
lean_dec(v_b_6296_);
v___x_6333_ = lean_box(0);
v_isShared_6334_ = v_isSharedCheck_6438_;
goto v_resetjp_6332_;
}
v_resetjp_6332_:
{
lean_object* v_fst_6335_; lean_object* v___x_6337_; uint8_t v_isShared_6338_; uint8_t v_isSharedCheck_6436_; 
v_fst_6335_ = lean_ctor_get(v_snd_6328_, 0);
v_isSharedCheck_6436_ = !lean_is_exclusive(v_snd_6328_);
if (v_isSharedCheck_6436_ == 0)
{
lean_object* v_unused_6437_; 
v_unused_6437_ = lean_ctor_get(v_snd_6328_, 1);
lean_dec(v_unused_6437_);
v___x_6337_ = v_snd_6328_;
v_isShared_6338_ = v_isSharedCheck_6436_;
goto v_resetjp_6336_;
}
else
{
lean_inc(v_fst_6335_);
lean_dec(v_snd_6328_);
v___x_6337_ = lean_box(0);
v_isShared_6338_ = v_isSharedCheck_6436_;
goto v_resetjp_6336_;
}
v_resetjp_6336_:
{
lean_object* v_fst_6339_; lean_object* v___x_6341_; uint8_t v_isShared_6342_; uint8_t v_isSharedCheck_6434_; 
v_fst_6339_ = lean_ctor_get(v_snd_6329_, 0);
v_isSharedCheck_6434_ = !lean_is_exclusive(v_snd_6329_);
if (v_isSharedCheck_6434_ == 0)
{
lean_object* v_unused_6435_; 
v_unused_6435_ = lean_ctor_get(v_snd_6329_, 1);
lean_dec(v_unused_6435_);
v___x_6341_ = v_snd_6329_;
v_isShared_6342_ = v_isSharedCheck_6434_;
goto v_resetjp_6340_;
}
else
{
lean_inc(v_fst_6339_);
lean_dec(v_snd_6329_);
v___x_6341_ = lean_box(0);
v_isShared_6342_ = v_isSharedCheck_6434_;
goto v_resetjp_6340_;
}
v_resetjp_6340_:
{
lean_object* v_array_6343_; lean_object* v_start_6344_; lean_object* v_stop_6345_; uint8_t v___x_6346_; 
v_array_6343_ = lean_ctor_get(v_snd_6330_, 0);
v_start_6344_ = lean_ctor_get(v_snd_6330_, 1);
v_stop_6345_ = lean_ctor_get(v_snd_6330_, 2);
v___x_6346_ = lean_nat_dec_lt(v_start_6344_, v_stop_6345_);
if (v___x_6346_ == 0)
{
lean_object* v___x_6348_; 
if (v_isShared_6342_ == 0)
{
v___x_6348_ = v___x_6341_;
goto v_reusejp_6347_;
}
else
{
lean_object* v_reuseFailAlloc_6357_; 
v_reuseFailAlloc_6357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6357_, 0, v_fst_6339_);
lean_ctor_set(v_reuseFailAlloc_6357_, 1, v_snd_6330_);
v___x_6348_ = v_reuseFailAlloc_6357_;
goto v_reusejp_6347_;
}
v_reusejp_6347_:
{
lean_object* v___x_6350_; 
if (v_isShared_6338_ == 0)
{
lean_ctor_set(v___x_6337_, 1, v___x_6348_);
v___x_6350_ = v___x_6337_;
goto v_reusejp_6349_;
}
else
{
lean_object* v_reuseFailAlloc_6356_; 
v_reuseFailAlloc_6356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6356_, 0, v_fst_6335_);
lean_ctor_set(v_reuseFailAlloc_6356_, 1, v___x_6348_);
v___x_6350_ = v_reuseFailAlloc_6356_;
goto v_reusejp_6349_;
}
v_reusejp_6349_:
{
lean_object* v___x_6352_; 
if (v_isShared_6334_ == 0)
{
lean_ctor_set(v___x_6333_, 1, v___x_6350_);
v___x_6352_ = v___x_6333_;
goto v_reusejp_6351_;
}
else
{
lean_object* v_reuseFailAlloc_6355_; 
v_reuseFailAlloc_6355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6355_, 0, v_fst_6331_);
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
v___y_6303_ = v___f_6354_;
goto v___jp_6302_;
}
}
}
}
else
{
lean_object* v___x_6359_; uint8_t v_isShared_6360_; uint8_t v_isSharedCheck_6430_; 
lean_inc(v_stop_6345_);
lean_inc(v_start_6344_);
lean_inc_ref(v_array_6343_);
v_isSharedCheck_6430_ = !lean_is_exclusive(v_snd_6330_);
if (v_isSharedCheck_6430_ == 0)
{
lean_object* v_unused_6431_; lean_object* v_unused_6432_; lean_object* v_unused_6433_; 
v_unused_6431_ = lean_ctor_get(v_snd_6330_, 2);
lean_dec(v_unused_6431_);
v_unused_6432_ = lean_ctor_get(v_snd_6330_, 1);
lean_dec(v_unused_6432_);
v_unused_6433_ = lean_ctor_get(v_snd_6330_, 0);
lean_dec(v_unused_6433_);
v___x_6359_ = v_snd_6330_;
v_isShared_6360_ = v_isSharedCheck_6430_;
goto v_resetjp_6358_;
}
else
{
lean_dec(v_snd_6330_);
v___x_6359_ = lean_box(0);
v_isShared_6360_ = v_isSharedCheck_6430_;
goto v_resetjp_6358_;
}
v_resetjp_6358_:
{
lean_object* v_array_6361_; lean_object* v_start_6362_; lean_object* v_stop_6363_; lean_object* v___x_6364_; lean_object* v___x_6365_; lean_object* v___x_6366_; lean_object* v___x_6368_; 
v_array_6361_ = lean_ctor_get(v_fst_6339_, 0);
v_start_6362_ = lean_ctor_get(v_fst_6339_, 1);
v_stop_6363_ = lean_ctor_get(v_fst_6339_, 2);
v___x_6364_ = lean_array_fget(v_array_6343_, v_start_6344_);
v___x_6365_ = lean_unsigned_to_nat(1u);
v___x_6366_ = lean_nat_add(v_start_6344_, v___x_6365_);
lean_dec(v_start_6344_);
if (v_isShared_6360_ == 0)
{
lean_ctor_set(v___x_6359_, 1, v___x_6366_);
v___x_6368_ = v___x_6359_;
goto v_reusejp_6367_;
}
else
{
lean_object* v_reuseFailAlloc_6429_; 
v_reuseFailAlloc_6429_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6429_, 0, v_array_6343_);
lean_ctor_set(v_reuseFailAlloc_6429_, 1, v___x_6366_);
lean_ctor_set(v_reuseFailAlloc_6429_, 2, v_stop_6345_);
v___x_6368_ = v_reuseFailAlloc_6429_;
goto v_reusejp_6367_;
}
v_reusejp_6367_:
{
uint8_t v___x_6369_; 
v___x_6369_ = lean_nat_dec_lt(v_start_6362_, v_stop_6363_);
if (v___x_6369_ == 0)
{
lean_object* v___x_6371_; 
lean_dec(v___x_6364_);
if (v_isShared_6342_ == 0)
{
lean_ctor_set(v___x_6341_, 1, v___x_6368_);
v___x_6371_ = v___x_6341_;
goto v_reusejp_6370_;
}
else
{
lean_object* v_reuseFailAlloc_6380_; 
v_reuseFailAlloc_6380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6380_, 0, v_fst_6339_);
lean_ctor_set(v_reuseFailAlloc_6380_, 1, v___x_6368_);
v___x_6371_ = v_reuseFailAlloc_6380_;
goto v_reusejp_6370_;
}
v_reusejp_6370_:
{
lean_object* v___x_6373_; 
if (v_isShared_6338_ == 0)
{
lean_ctor_set(v___x_6337_, 1, v___x_6371_);
v___x_6373_ = v___x_6337_;
goto v_reusejp_6372_;
}
else
{
lean_object* v_reuseFailAlloc_6379_; 
v_reuseFailAlloc_6379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6379_, 0, v_fst_6335_);
lean_ctor_set(v_reuseFailAlloc_6379_, 1, v___x_6371_);
v___x_6373_ = v_reuseFailAlloc_6379_;
goto v_reusejp_6372_;
}
v_reusejp_6372_:
{
lean_object* v___x_6375_; 
if (v_isShared_6334_ == 0)
{
lean_ctor_set(v___x_6333_, 1, v___x_6373_);
v___x_6375_ = v___x_6333_;
goto v_reusejp_6374_;
}
else
{
lean_object* v_reuseFailAlloc_6378_; 
v_reuseFailAlloc_6378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6378_, 0, v_fst_6331_);
lean_ctor_set(v_reuseFailAlloc_6378_, 1, v___x_6373_);
v___x_6375_ = v_reuseFailAlloc_6378_;
goto v_reusejp_6374_;
}
v_reusejp_6374_:
{
lean_object* v___x_6376_; lean_object* v___f_6377_; 
v___x_6376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6376_, 0, v___x_6375_);
v___f_6377_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6377_, 0, v___x_6376_);
v___y_6303_ = v___f_6377_;
goto v___jp_6302_;
}
}
}
}
else
{
lean_object* v___x_6382_; uint8_t v_isShared_6383_; uint8_t v_isSharedCheck_6425_; 
lean_inc(v_stop_6363_);
lean_inc(v_start_6362_);
lean_inc_ref(v_array_6361_);
v_isSharedCheck_6425_ = !lean_is_exclusive(v_fst_6339_);
if (v_isSharedCheck_6425_ == 0)
{
lean_object* v_unused_6426_; lean_object* v_unused_6427_; lean_object* v_unused_6428_; 
v_unused_6426_ = lean_ctor_get(v_fst_6339_, 2);
lean_dec(v_unused_6426_);
v_unused_6427_ = lean_ctor_get(v_fst_6339_, 1);
lean_dec(v_unused_6427_);
v_unused_6428_ = lean_ctor_get(v_fst_6339_, 0);
lean_dec(v_unused_6428_);
v___x_6382_ = v_fst_6339_;
v_isShared_6383_ = v_isSharedCheck_6425_;
goto v_resetjp_6381_;
}
else
{
lean_dec(v_fst_6339_);
v___x_6382_ = lean_box(0);
v_isShared_6383_ = v_isSharedCheck_6425_;
goto v_resetjp_6381_;
}
v_resetjp_6381_:
{
lean_object* v_array_6384_; lean_object* v_start_6385_; lean_object* v_stop_6386_; lean_object* v___x_6387_; lean_object* v___x_6388_; lean_object* v___x_6390_; 
v_array_6384_ = lean_ctor_get(v_fst_6335_, 0);
v_start_6385_ = lean_ctor_get(v_fst_6335_, 1);
v_stop_6386_ = lean_ctor_get(v_fst_6335_, 2);
v___x_6387_ = lean_array_fget(v_array_6361_, v_start_6362_);
v___x_6388_ = lean_nat_add(v_start_6362_, v___x_6365_);
lean_dec(v_start_6362_);
if (v_isShared_6383_ == 0)
{
lean_ctor_set(v___x_6382_, 1, v___x_6388_);
v___x_6390_ = v___x_6382_;
goto v_reusejp_6389_;
}
else
{
lean_object* v_reuseFailAlloc_6424_; 
v_reuseFailAlloc_6424_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6424_, 0, v_array_6361_);
lean_ctor_set(v_reuseFailAlloc_6424_, 1, v___x_6388_);
lean_ctor_set(v_reuseFailAlloc_6424_, 2, v_stop_6363_);
v___x_6390_ = v_reuseFailAlloc_6424_;
goto v_reusejp_6389_;
}
v_reusejp_6389_:
{
uint8_t v___x_6391_; 
v___x_6391_ = lean_nat_dec_lt(v_start_6385_, v_stop_6386_);
if (v___x_6391_ == 0)
{
lean_object* v___x_6393_; 
lean_dec(v___x_6387_);
lean_dec(v___x_6364_);
if (v_isShared_6342_ == 0)
{
lean_ctor_set(v___x_6341_, 1, v___x_6368_);
lean_ctor_set(v___x_6341_, 0, v___x_6390_);
v___x_6393_ = v___x_6341_;
goto v_reusejp_6392_;
}
else
{
lean_object* v_reuseFailAlloc_6402_; 
v_reuseFailAlloc_6402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6402_, 0, v___x_6390_);
lean_ctor_set(v_reuseFailAlloc_6402_, 1, v___x_6368_);
v___x_6393_ = v_reuseFailAlloc_6402_;
goto v_reusejp_6392_;
}
v_reusejp_6392_:
{
lean_object* v___x_6395_; 
if (v_isShared_6338_ == 0)
{
lean_ctor_set(v___x_6337_, 1, v___x_6393_);
v___x_6395_ = v___x_6337_;
goto v_reusejp_6394_;
}
else
{
lean_object* v_reuseFailAlloc_6401_; 
v_reuseFailAlloc_6401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6401_, 0, v_fst_6335_);
lean_ctor_set(v_reuseFailAlloc_6401_, 1, v___x_6393_);
v___x_6395_ = v_reuseFailAlloc_6401_;
goto v_reusejp_6394_;
}
v_reusejp_6394_:
{
lean_object* v___x_6397_; 
if (v_isShared_6334_ == 0)
{
lean_ctor_set(v___x_6333_, 1, v___x_6395_);
v___x_6397_ = v___x_6333_;
goto v_reusejp_6396_;
}
else
{
lean_object* v_reuseFailAlloc_6400_; 
v_reuseFailAlloc_6400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6400_, 0, v_fst_6331_);
lean_ctor_set(v_reuseFailAlloc_6400_, 1, v___x_6395_);
v___x_6397_ = v_reuseFailAlloc_6400_;
goto v_reusejp_6396_;
}
v_reusejp_6396_:
{
lean_object* v___x_6398_; lean_object* v___f_6399_; 
v___x_6398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6398_, 0, v___x_6397_);
v___f_6399_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6399_, 0, v___x_6398_);
v___y_6303_ = v___f_6399_;
goto v___jp_6302_;
}
}
}
}
else
{
lean_object* v___x_6404_; uint8_t v_isShared_6405_; uint8_t v_isSharedCheck_6420_; 
lean_inc(v_stop_6386_);
lean_inc(v_start_6385_);
lean_inc_ref(v_array_6384_);
lean_del_object(v___x_6341_);
lean_del_object(v___x_6337_);
lean_del_object(v___x_6333_);
v_isSharedCheck_6420_ = !lean_is_exclusive(v_fst_6335_);
if (v_isSharedCheck_6420_ == 0)
{
lean_object* v_unused_6421_; lean_object* v_unused_6422_; lean_object* v_unused_6423_; 
v_unused_6421_ = lean_ctor_get(v_fst_6335_, 2);
lean_dec(v_unused_6421_);
v_unused_6422_ = lean_ctor_get(v_fst_6335_, 1);
lean_dec(v_unused_6422_);
v_unused_6423_ = lean_ctor_get(v_fst_6335_, 0);
lean_dec(v_unused_6423_);
v___x_6404_ = v_fst_6335_;
v_isShared_6405_ = v_isSharedCheck_6420_;
goto v_resetjp_6403_;
}
else
{
lean_dec(v_fst_6335_);
v___x_6404_ = lean_box(0);
v_isShared_6405_ = v_isSharedCheck_6420_;
goto v_resetjp_6403_;
}
v_resetjp_6403_:
{
lean_object* v___f_6406_; uint8_t v___x_6407_; lean_object* v_remaining_x27_6408_; lean_object* v___x_6409_; lean_object* v___x_6410_; lean_object* v___x_6411_; lean_object* v___f_6412_; lean_object* v___x_6413_; lean_object* v___x_6415_; 
v___f_6406_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___closed__0));
v___x_6407_ = 0;
v_remaining_x27_6408_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_6409_ = lean_array_fget_borrowed(v_array_6384_, v_start_6385_);
v___x_6410_ = lean_box(v___x_6407_);
v___x_6411_ = lean_box(v___x_6391_);
lean_inc(v_extraEqualities_6294_);
lean_inc(v_a_6295_);
lean_inc_ref(v_onAlt_6293_);
lean_inc(v___x_6409_);
v___f_6412_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed), 15, 8);
lean_closure_set(v___f_6412_, 0, v___x_6409_);
lean_closure_set(v___f_6412_, 1, v___f_6406_);
lean_closure_set(v___f_6412_, 2, v___x_6410_);
lean_closure_set(v___f_6412_, 3, v_remaining_x27_6408_);
lean_closure_set(v___f_6412_, 4, v_onAlt_6293_);
lean_closure_set(v___f_6412_, 5, v_a_6295_);
lean_closure_set(v___f_6412_, 6, v___x_6411_);
lean_closure_set(v___f_6412_, 7, v_extraEqualities_6294_);
v___x_6413_ = lean_nat_add(v_start_6385_, v___x_6365_);
lean_dec(v_start_6385_);
if (v_isShared_6405_ == 0)
{
lean_ctor_set(v___x_6404_, 1, v___x_6413_);
v___x_6415_ = v___x_6404_;
goto v_reusejp_6414_;
}
else
{
lean_object* v_reuseFailAlloc_6419_; 
v_reuseFailAlloc_6419_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6419_, 0, v_array_6384_);
lean_ctor_set(v_reuseFailAlloc_6419_, 1, v___x_6413_);
lean_ctor_set(v_reuseFailAlloc_6419_, 2, v_stop_6386_);
v___x_6415_ = v_reuseFailAlloc_6419_;
goto v_reusejp_6414_;
}
v_reusejp_6414_:
{
lean_object* v___x_6416_; lean_object* v___x_6417_; lean_object* v___f_6418_; 
v___x_6416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6416_, 0, v___x_6387_);
v___x_6417_ = lean_box(v___x_6407_);
v___f_6418_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed), 13, 8);
lean_closure_set(v___f_6418_, 0, v___x_6364_);
lean_closure_set(v___f_6418_, 1, v___x_6416_);
lean_closure_set(v___f_6418_, 2, v___f_6412_);
lean_closure_set(v___f_6418_, 3, v___x_6417_);
lean_closure_set(v___f_6418_, 4, v_fst_6331_);
lean_closure_set(v___f_6418_, 5, v___x_6390_);
lean_closure_set(v___f_6418_, 6, v___x_6368_);
lean_closure_set(v___f_6418_, 7, v___x_6415_);
v___y_6303_ = v___f_6418_;
goto v___jp_6302_;
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_6302_:
{
lean_object* v___x_6304_; 
lean_inc(v___y_6300_);
lean_inc_ref(v___y_6299_);
lean_inc(v___y_6298_);
lean_inc_ref(v___y_6297_);
v___x_6304_ = lean_apply_5(v___y_6303_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, lean_box(0));
if (lean_obj_tag(v___x_6304_) == 0)
{
lean_object* v_a_6305_; lean_object* v___x_6307_; uint8_t v_isShared_6308_; uint8_t v_isSharedCheck_6317_; 
v_a_6305_ = lean_ctor_get(v___x_6304_, 0);
v_isSharedCheck_6317_ = !lean_is_exclusive(v___x_6304_);
if (v_isSharedCheck_6317_ == 0)
{
v___x_6307_ = v___x_6304_;
v_isShared_6308_ = v_isSharedCheck_6317_;
goto v_resetjp_6306_;
}
else
{
lean_inc(v_a_6305_);
lean_dec(v___x_6304_);
v___x_6307_ = lean_box(0);
v_isShared_6308_ = v_isSharedCheck_6317_;
goto v_resetjp_6306_;
}
v_resetjp_6306_:
{
if (lean_obj_tag(v_a_6305_) == 0)
{
lean_object* v_a_6309_; lean_object* v___x_6311_; 
lean_dec(v_a_6295_);
lean_dec(v_extraEqualities_6294_);
lean_dec_ref(v_onAlt_6293_);
v_a_6309_ = lean_ctor_get(v_a_6305_, 0);
lean_inc(v_a_6309_);
lean_dec_ref(v_a_6305_);
if (v_isShared_6308_ == 0)
{
lean_ctor_set(v___x_6307_, 0, v_a_6309_);
v___x_6311_ = v___x_6307_;
goto v_reusejp_6310_;
}
else
{
lean_object* v_reuseFailAlloc_6312_; 
v_reuseFailAlloc_6312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6312_, 0, v_a_6309_);
v___x_6311_ = v_reuseFailAlloc_6312_;
goto v_reusejp_6310_;
}
v_reusejp_6310_:
{
return v___x_6311_;
}
}
else
{
lean_object* v_a_6313_; lean_object* v___x_6314_; lean_object* v___x_6315_; 
lean_del_object(v___x_6307_);
v_a_6313_ = lean_ctor_get(v_a_6305_, 0);
lean_inc(v_a_6313_);
lean_dec_ref(v_a_6305_);
v___x_6314_ = lean_unsigned_to_nat(1u);
v___x_6315_ = lean_nat_add(v_a_6295_, v___x_6314_);
lean_dec(v_a_6295_);
v_a_6295_ = v___x_6315_;
v_b_6296_ = v_a_6313_;
goto _start;
}
}
}
else
{
lean_object* v_a_6318_; lean_object* v___x_6320_; uint8_t v_isShared_6321_; uint8_t v_isSharedCheck_6325_; 
lean_dec(v_a_6295_);
lean_dec(v_extraEqualities_6294_);
lean_dec_ref(v_onAlt_6293_);
v_a_6318_ = lean_ctor_get(v___x_6304_, 0);
v_isSharedCheck_6325_ = !lean_is_exclusive(v___x_6304_);
if (v_isSharedCheck_6325_ == 0)
{
v___x_6320_ = v___x_6304_;
v_isShared_6321_ = v_isSharedCheck_6325_;
goto v_resetjp_6319_;
}
else
{
lean_inc(v_a_6318_);
lean_dec(v___x_6304_);
v___x_6320_ = lean_box(0);
v_isShared_6321_ = v_isSharedCheck_6325_;
goto v_resetjp_6319_;
}
v_resetjp_6319_:
{
lean_object* v___x_6323_; 
if (v_isShared_6321_ == 0)
{
v___x_6323_ = v___x_6320_;
goto v_reusejp_6322_;
}
else
{
lean_object* v_reuseFailAlloc_6324_; 
v_reuseFailAlloc_6324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6324_, 0, v_a_6318_);
v___x_6323_ = v_reuseFailAlloc_6324_;
goto v_reusejp_6322_;
}
v_reusejp_6322_:
{
return v___x_6323_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___boxed(lean_object* v_upperBound_6440_, lean_object* v_onAlt_6441_, lean_object* v_extraEqualities_6442_, lean_object* v_a_6443_, lean_object* v_b_6444_, lean_object* v___y_6445_, lean_object* v___y_6446_, lean_object* v___y_6447_, lean_object* v___y_6448_, lean_object* v___y_6449_){
_start:
{
lean_object* v_res_6450_; 
v_res_6450_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v_upperBound_6440_, v_onAlt_6441_, v_extraEqualities_6442_, v_a_6443_, v_b_6444_, v___y_6445_, v___y_6446_, v___y_6447_, v___y_6448_);
lean_dec(v___y_6448_);
lean_dec_ref(v___y_6447_);
lean_dec(v___y_6446_);
lean_dec_ref(v___y_6445_);
lean_dec(v_upperBound_6440_);
return v_res_6450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(lean_object* v_onParams_6451_, size_t v_sz_6452_, size_t v_i_6453_, lean_object* v_bs_6454_, lean_object* v___y_6455_, lean_object* v___y_6456_, lean_object* v___y_6457_, lean_object* v___y_6458_){
_start:
{
uint8_t v___x_6460_; 
v___x_6460_ = lean_usize_dec_lt(v_i_6453_, v_sz_6452_);
if (v___x_6460_ == 0)
{
lean_object* v___x_6461_; 
lean_dec_ref(v_onParams_6451_);
v___x_6461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6461_, 0, v_bs_6454_);
return v___x_6461_;
}
else
{
lean_object* v_v_6462_; lean_object* v___x_6463_; 
v_v_6462_ = lean_array_uget_borrowed(v_bs_6454_, v_i_6453_);
lean_inc_ref(v_onParams_6451_);
lean_inc(v___y_6458_);
lean_inc_ref(v___y_6457_);
lean_inc(v___y_6456_);
lean_inc_ref(v___y_6455_);
lean_inc(v_v_6462_);
v___x_6463_ = lean_apply_6(v_onParams_6451_, v_v_6462_, v___y_6455_, v___y_6456_, v___y_6457_, v___y_6458_, lean_box(0));
if (lean_obj_tag(v___x_6463_) == 0)
{
lean_object* v_a_6464_; lean_object* v___x_6465_; lean_object* v_bs_x27_6466_; size_t v___x_6467_; size_t v___x_6468_; lean_object* v___x_6469_; 
v_a_6464_ = lean_ctor_get(v___x_6463_, 0);
lean_inc(v_a_6464_);
lean_dec_ref(v___x_6463_);
v___x_6465_ = lean_unsigned_to_nat(0u);
v_bs_x27_6466_ = lean_array_uset(v_bs_6454_, v_i_6453_, v___x_6465_);
v___x_6467_ = ((size_t)1ULL);
v___x_6468_ = lean_usize_add(v_i_6453_, v___x_6467_);
v___x_6469_ = lean_array_uset(v_bs_x27_6466_, v_i_6453_, v_a_6464_);
v_i_6453_ = v___x_6468_;
v_bs_6454_ = v___x_6469_;
goto _start;
}
else
{
lean_object* v_a_6471_; lean_object* v___x_6473_; uint8_t v_isShared_6474_; uint8_t v_isSharedCheck_6478_; 
lean_dec_ref(v_bs_6454_);
lean_dec_ref(v_onParams_6451_);
v_a_6471_ = lean_ctor_get(v___x_6463_, 0);
v_isSharedCheck_6478_ = !lean_is_exclusive(v___x_6463_);
if (v_isSharedCheck_6478_ == 0)
{
v___x_6473_ = v___x_6463_;
v_isShared_6474_ = v_isSharedCheck_6478_;
goto v_resetjp_6472_;
}
else
{
lean_inc(v_a_6471_);
lean_dec(v___x_6463_);
v___x_6473_ = lean_box(0);
v_isShared_6474_ = v_isSharedCheck_6478_;
goto v_resetjp_6472_;
}
v_resetjp_6472_:
{
lean_object* v___x_6476_; 
if (v_isShared_6474_ == 0)
{
v___x_6476_ = v___x_6473_;
goto v_reusejp_6475_;
}
else
{
lean_object* v_reuseFailAlloc_6477_; 
v_reuseFailAlloc_6477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6477_, 0, v_a_6471_);
v___x_6476_ = v_reuseFailAlloc_6477_;
goto v_reusejp_6475_;
}
v_reusejp_6475_:
{
return v___x_6476_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6___boxed(lean_object* v_onParams_6479_, lean_object* v_sz_6480_, lean_object* v_i_6481_, lean_object* v_bs_6482_, lean_object* v___y_6483_, lean_object* v___y_6484_, lean_object* v___y_6485_, lean_object* v___y_6486_, lean_object* v___y_6487_){
_start:
{
size_t v_sz_boxed_6488_; size_t v_i_boxed_6489_; lean_object* v_res_6490_; 
v_sz_boxed_6488_ = lean_unbox_usize(v_sz_6480_);
lean_dec(v_sz_6480_);
v_i_boxed_6489_ = lean_unbox_usize(v_i_6481_);
lean_dec(v_i_6481_);
v_res_6490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6479_, v_sz_boxed_6488_, v_i_boxed_6489_, v_bs_6482_, v___y_6483_, v___y_6484_, v___y_6485_, v___y_6486_);
lean_dec(v___y_6486_);
lean_dec_ref(v___y_6485_);
lean_dec(v___y_6484_);
lean_dec_ref(v___y_6483_);
return v_res_6490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(lean_object* v_declName_6491_, lean_object* v___y_6492_){
_start:
{
lean_object* v___x_6494_; lean_object* v_env_6495_; lean_object* v___x_6496_; lean_object* v___x_6497_; 
v___x_6494_ = lean_st_ref_get(v___y_6492_);
v_env_6495_ = lean_ctor_get(v___x_6494_, 0);
lean_inc_ref(v_env_6495_);
lean_dec(v___x_6494_);
v___x_6496_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_6495_, v_declName_6491_);
v___x_6497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6497_, 0, v___x_6496_);
return v___x_6497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg___boxed(lean_object* v_declName_6498_, lean_object* v___y_6499_, lean_object* v___y_6500_){
_start:
{
lean_object* v_res_6501_; 
v_res_6501_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_declName_6498_, v___y_6499_);
lean_dec(v___y_6499_);
return v_res_6501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(lean_object* v_matcherApp_6504_, uint8_t v_useSplitter_6505_, uint8_t v_addEqualities_6506_, lean_object* v_onParams_6507_, lean_object* v_onMotive_6508_, lean_object* v_onAlt_6509_, lean_object* v_onRemaining_6510_, lean_object* v___y_6511_, lean_object* v___y_6512_, lean_object* v___y_6513_, lean_object* v___y_6514_){
_start:
{
lean_object* v___x_6516_; lean_object* v_env_6517_; lean_object* v_toMatcherInfo_6518_; lean_object* v_matcherName_6519_; lean_object* v_matcherLevels_6520_; lean_object* v_params_6521_; lean_object* v_motive_6522_; lean_object* v_discrs_6523_; lean_object* v_alts_6524_; lean_object* v_remaining_6525_; lean_object* v___y_6527_; lean_object* v___y_6528_; lean_object* v___y_6529_; lean_object* v___y_6530_; lean_object* v___y_6531_; lean_object* v___y_6532_; lean_object* v___y_6533_; lean_object* v___y_6534_; lean_object* v___y_6535_; lean_object* v___y_6536_; lean_object* v___y_6537_; lean_object* v___y_6538_; lean_object* v___y_6539_; uint8_t v_isCasesOn_6624_; lean_object* v___y_6626_; size_t v___y_6627_; lean_object* v___y_6628_; lean_object* v___y_6629_; lean_object* v___y_6630_; lean_object* v___y_6631_; lean_object* v___y_6632_; lean_object* v_matcherLevels_6633_; lean_object* v___y_6634_; lean_object* v___y_6635_; lean_object* v___y_6636_; lean_object* v___y_6637_; lean_object* v_numDiscrEqs_6831_; lean_object* v___y_6832_; lean_object* v___y_6833_; lean_object* v___y_6834_; lean_object* v___y_6835_; 
v___x_6516_ = lean_st_ref_get(v___y_6514_);
v_env_6517_ = lean_ctor_get(v___x_6516_, 0);
lean_inc_ref(v_env_6517_);
lean_dec(v___x_6516_);
v_toMatcherInfo_6518_ = lean_ctor_get(v_matcherApp_6504_, 0);
lean_inc_ref(v_toMatcherInfo_6518_);
v_matcherName_6519_ = lean_ctor_get(v_matcherApp_6504_, 1);
lean_inc_n(v_matcherName_6519_, 2);
v_matcherLevels_6520_ = lean_ctor_get(v_matcherApp_6504_, 2);
v_params_6521_ = lean_ctor_get(v_matcherApp_6504_, 3);
v_motive_6522_ = lean_ctor_get(v_matcherApp_6504_, 4);
v_discrs_6523_ = lean_ctor_get(v_matcherApp_6504_, 5);
v_alts_6524_ = lean_ctor_get(v_matcherApp_6504_, 6);
lean_inc_ref(v_alts_6524_);
v_remaining_6525_ = lean_ctor_get(v_matcherApp_6504_, 7);
lean_inc_ref(v_remaining_6525_);
v_isCasesOn_6624_ = l_Lean_isCasesOnRecursor(v_env_6517_, v_matcherName_6519_);
if (v_isCasesOn_6624_ == 0)
{
lean_object* v___x_6885_; lean_object* v_a_6886_; 
lean_inc(v_matcherName_6519_);
v___x_6885_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_matcherName_6519_, v___y_6514_);
v_a_6886_ = lean_ctor_get(v___x_6885_, 0);
lean_inc(v_a_6886_);
lean_dec_ref(v___x_6885_);
if (lean_obj_tag(v_a_6886_) == 0)
{
lean_object* v___x_6887_; lean_object* v___x_6888_; lean_object* v___x_6889_; lean_object* v___x_6890_; lean_object* v___x_6891_; lean_object* v___x_6892_; lean_object* v_a_6893_; lean_object* v___x_6895_; uint8_t v_isShared_6896_; uint8_t v_isSharedCheck_6900_; 
lean_dec_ref(v_remaining_6525_);
lean_dec_ref(v_alts_6524_);
lean_dec_ref(v_toMatcherInfo_6518_);
lean_dec_ref(v_onRemaining_6510_);
lean_dec_ref(v_onAlt_6509_);
lean_dec_ref(v_onMotive_6508_);
lean_dec_ref(v_onParams_6507_);
lean_dec_ref(v_matcherApp_6504_);
v___x_6887_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1);
v___x_6888_ = l_Lean_MessageData_ofName(v_matcherName_6519_);
v___x_6889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6889_, 0, v___x_6887_);
lean_ctor_set(v___x_6889_, 1, v___x_6888_);
v___x_6890_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3);
v___x_6891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6891_, 0, v___x_6889_);
lean_ctor_set(v___x_6891_, 1, v___x_6890_);
v___x_6892_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_6891_, v___y_6511_, v___y_6512_, v___y_6513_, v___y_6514_);
v_a_6893_ = lean_ctor_get(v___x_6892_, 0);
v_isSharedCheck_6900_ = !lean_is_exclusive(v___x_6892_);
if (v_isSharedCheck_6900_ == 0)
{
v___x_6895_ = v___x_6892_;
v_isShared_6896_ = v_isSharedCheck_6900_;
goto v_resetjp_6894_;
}
else
{
lean_inc(v_a_6893_);
lean_dec(v___x_6892_);
v___x_6895_ = lean_box(0);
v_isShared_6896_ = v_isSharedCheck_6900_;
goto v_resetjp_6894_;
}
v_resetjp_6894_:
{
lean_object* v___x_6898_; 
if (v_isShared_6896_ == 0)
{
v___x_6898_ = v___x_6895_;
goto v_reusejp_6897_;
}
else
{
lean_object* v_reuseFailAlloc_6899_; 
v_reuseFailAlloc_6899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6899_, 0, v_a_6893_);
v___x_6898_ = v_reuseFailAlloc_6899_;
goto v_reusejp_6897_;
}
v_reusejp_6897_:
{
return v___x_6898_;
}
}
}
else
{
lean_object* v_val_6901_; lean_object* v___x_6902_; 
v_val_6901_ = lean_ctor_get(v_a_6886_, 0);
lean_inc(v_val_6901_);
lean_dec_ref(v_a_6886_);
v___x_6902_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_6901_);
lean_dec(v_val_6901_);
v_numDiscrEqs_6831_ = v___x_6902_;
v___y_6832_ = v___y_6511_;
v___y_6833_ = v___y_6512_;
v___y_6834_ = v___y_6513_;
v___y_6835_ = v___y_6514_;
goto v___jp_6830_;
}
}
else
{
lean_object* v___x_6903_; 
v___x_6903_ = lean_unsigned_to_nat(0u);
v_numDiscrEqs_6831_ = v___x_6903_;
v___y_6832_ = v___y_6511_;
v___y_6833_ = v___y_6512_;
v___y_6834_ = v___y_6513_;
v___y_6835_ = v___y_6514_;
goto v___jp_6830_;
}
v___jp_6526_:
{
lean_object* v___x_6540_; lean_object* v___x_6541_; lean_object* v_aux_6542_; lean_object* v_aux_6543_; lean_object* v_aux_6544_; lean_object* v___x_6545_; lean_object* v___x_6546_; lean_object* v___x_6547_; lean_object* v___f_6548_; uint8_t v___x_6549_; lean_object* v___x_6550_; lean_object* v___x_6551_; lean_object* v___x_6552_; 
lean_inc_ref(v___y_6534_);
v___x_6540_ = lean_array_to_list(v___y_6534_);
lean_inc(v_matcherName_6519_);
v___x_6541_ = l_Lean_mkConst(v_matcherName_6519_, v___x_6540_);
v_aux_6542_ = l_Lean_mkAppN(v___x_6541_, v___y_6529_);
lean_inc_ref(v___y_6530_);
v_aux_6543_ = l_Lean_Expr_app___override(v_aux_6542_, v___y_6530_);
v_aux_6544_ = l_Lean_mkAppN(v_aux_6543_, v___y_6527_);
v___x_6545_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1);
lean_inc_ref_n(v_aux_6544_, 2);
v___x_6546_ = l_Lean_indentExpr(v_aux_6544_);
v___x_6547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6547_, 0, v___x_6545_);
lean_ctor_set(v___x_6547_, 1, v___x_6546_);
v___f_6548_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6548_, 0, v___x_6547_);
v___x_6549_ = 0;
v___x_6550_ = lean_box(v___x_6549_);
v___x_6551_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6551_, 0, v_aux_6544_);
lean_closure_set(v___x_6551_, 1, v___x_6550_);
v___x_6552_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6551_, v___f_6548_, v___y_6532_, v___y_6528_, v___y_6531_, v___y_6535_);
if (lean_obj_tag(v___x_6552_) == 0)
{
lean_object* v___x_6553_; lean_object* v___x_6554_; 
lean_dec_ref(v___x_6552_);
v___x_6553_ = lean_array_get_size(v_alts_6524_);
v___x_6554_ = l_Lean_Meta_inferArgumentTypesN(v___x_6553_, v_aux_6544_, v___y_6532_, v___y_6528_, v___y_6531_, v___y_6535_);
if (lean_obj_tag(v___x_6554_) == 0)
{
lean_object* v_a_6555_; lean_object* v___x_6556_; lean_object* v___x_6557_; lean_object* v___x_6558_; lean_object* v___x_6559_; lean_object* v___x_6560_; lean_object* v___x_6561_; lean_object* v___x_6562_; lean_object* v___x_6563_; lean_object* v___x_6564_; lean_object* v___x_6565_; 
v_a_6555_ = lean_ctor_get(v___x_6554_, 0);
lean_inc(v_a_6555_);
lean_dec_ref(v___x_6554_);
v___x_6556_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_6504_);
v___x_6557_ = lean_array_get_size(v___x_6556_);
v___x_6558_ = lean_array_get_size(v_a_6555_);
lean_inc_n(v___y_6533_, 3);
v___x_6559_ = l_Array_toSubarray___redArg(v_alts_6524_, v___y_6533_, v___x_6553_);
v___x_6560_ = l_Array_toSubarray___redArg(v___x_6556_, v___y_6533_, v___x_6557_);
v___x_6561_ = l_Array_toSubarray___redArg(v_a_6555_, v___y_6533_, v___x_6558_);
v___x_6562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6562_, 0, v___x_6560_);
lean_ctor_set(v___x_6562_, 1, v___x_6561_);
v___x_6563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6563_, 0, v___x_6559_);
lean_ctor_set(v___x_6563_, 1, v___x_6562_);
lean_inc_ref(v___y_6537_);
v___x_6564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6564_, 0, v___y_6537_);
lean_ctor_set(v___x_6564_, 1, v___x_6563_);
v___x_6565_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v___x_6553_, v_onAlt_6509_, v___y_6539_, v___y_6533_, v___x_6564_, v___y_6532_, v___y_6528_, v___y_6531_, v___y_6535_);
if (lean_obj_tag(v___x_6565_) == 0)
{
lean_object* v_a_6566_; lean_object* v_fst_6567_; lean_object* v___x_6568_; 
v_a_6566_ = lean_ctor_get(v___x_6565_, 0);
lean_inc(v_a_6566_);
lean_dec_ref(v___x_6565_);
v_fst_6567_ = lean_ctor_get(v_a_6566_, 0);
lean_inc(v_fst_6567_);
lean_dec(v_a_6566_);
lean_inc(v___y_6535_);
lean_inc_ref(v___y_6531_);
lean_inc(v___y_6528_);
lean_inc_ref(v___y_6532_);
v___x_6568_ = lean_apply_6(v_onRemaining_6510_, v_remaining_6525_, v___y_6532_, v___y_6528_, v___y_6531_, v___y_6535_, lean_box(0));
if (lean_obj_tag(v___x_6568_) == 0)
{
lean_object* v_a_6569_; lean_object* v___x_6571_; uint8_t v_isShared_6572_; uint8_t v_isSharedCheck_6591_; 
v_a_6569_ = lean_ctor_get(v___x_6568_, 0);
v_isSharedCheck_6591_ = !lean_is_exclusive(v___x_6568_);
if (v_isSharedCheck_6591_ == 0)
{
v___x_6571_ = v___x_6568_;
v_isShared_6572_ = v_isSharedCheck_6591_;
goto v_resetjp_6570_;
}
else
{
lean_inc(v_a_6569_);
lean_dec(v___x_6568_);
v___x_6571_ = lean_box(0);
v_isShared_6572_ = v_isSharedCheck_6591_;
goto v_resetjp_6570_;
}
v_resetjp_6570_:
{
lean_object* v_numParams_6573_; lean_object* v_numDiscrs_6574_; lean_object* v_altInfos_6575_; lean_object* v_uElimPos_x3f_6576_; lean_object* v_overlaps_6577_; lean_object* v___x_6579_; uint8_t v_isShared_6580_; uint8_t v_isSharedCheck_6589_; 
v_numParams_6573_ = lean_ctor_get(v_toMatcherInfo_6518_, 0);
v_numDiscrs_6574_ = lean_ctor_get(v_toMatcherInfo_6518_, 1);
v_altInfos_6575_ = lean_ctor_get(v_toMatcherInfo_6518_, 2);
v_uElimPos_x3f_6576_ = lean_ctor_get(v_toMatcherInfo_6518_, 3);
v_overlaps_6577_ = lean_ctor_get(v_toMatcherInfo_6518_, 5);
v_isSharedCheck_6589_ = !lean_is_exclusive(v_toMatcherInfo_6518_);
if (v_isSharedCheck_6589_ == 0)
{
lean_object* v_unused_6590_; 
v_unused_6590_ = lean_ctor_get(v_toMatcherInfo_6518_, 4);
lean_dec(v_unused_6590_);
v___x_6579_ = v_toMatcherInfo_6518_;
v_isShared_6580_ = v_isSharedCheck_6589_;
goto v_resetjp_6578_;
}
else
{
lean_inc(v_overlaps_6577_);
lean_inc(v_uElimPos_x3f_6576_);
lean_inc(v_altInfos_6575_);
lean_inc(v_numDiscrs_6574_);
lean_inc(v_numParams_6573_);
lean_dec(v_toMatcherInfo_6518_);
v___x_6579_ = lean_box(0);
v_isShared_6580_ = v_isSharedCheck_6589_;
goto v_resetjp_6578_;
}
v_resetjp_6578_:
{
lean_object* v_remaining_x27_6581_; lean_object* v___x_6583_; 
v_remaining_x27_6581_ = l_Array_append___redArg(v___y_6538_, v_a_6569_);
lean_dec(v_a_6569_);
if (v_isShared_6580_ == 0)
{
lean_ctor_set(v___x_6579_, 4, v___y_6536_);
v___x_6583_ = v___x_6579_;
goto v_reusejp_6582_;
}
else
{
lean_object* v_reuseFailAlloc_6588_; 
v_reuseFailAlloc_6588_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6588_, 0, v_numParams_6573_);
lean_ctor_set(v_reuseFailAlloc_6588_, 1, v_numDiscrs_6574_);
lean_ctor_set(v_reuseFailAlloc_6588_, 2, v_altInfos_6575_);
lean_ctor_set(v_reuseFailAlloc_6588_, 3, v_uElimPos_x3f_6576_);
lean_ctor_set(v_reuseFailAlloc_6588_, 4, v___y_6536_);
lean_ctor_set(v_reuseFailAlloc_6588_, 5, v_overlaps_6577_);
v___x_6583_ = v_reuseFailAlloc_6588_;
goto v_reusejp_6582_;
}
v_reusejp_6582_:
{
lean_object* v___x_6584_; lean_object* v___x_6586_; 
v___x_6584_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6584_, 0, v___x_6583_);
lean_ctor_set(v___x_6584_, 1, v_matcherName_6519_);
lean_ctor_set(v___x_6584_, 2, v___y_6534_);
lean_ctor_set(v___x_6584_, 3, v___y_6529_);
lean_ctor_set(v___x_6584_, 4, v___y_6530_);
lean_ctor_set(v___x_6584_, 5, v___y_6527_);
lean_ctor_set(v___x_6584_, 6, v_fst_6567_);
lean_ctor_set(v___x_6584_, 7, v_remaining_x27_6581_);
if (v_isShared_6572_ == 0)
{
lean_ctor_set(v___x_6571_, 0, v___x_6584_);
v___x_6586_ = v___x_6571_;
goto v_reusejp_6585_;
}
else
{
lean_object* v_reuseFailAlloc_6587_; 
v_reuseFailAlloc_6587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6587_, 0, v___x_6584_);
v___x_6586_ = v_reuseFailAlloc_6587_;
goto v_reusejp_6585_;
}
v_reusejp_6585_:
{
return v___x_6586_;
}
}
}
}
}
else
{
lean_object* v_a_6592_; lean_object* v___x_6594_; uint8_t v_isShared_6595_; uint8_t v_isSharedCheck_6599_; 
lean_dec(v_fst_6567_);
lean_dec(v___y_6538_);
lean_dec_ref(v___y_6536_);
lean_dec_ref(v___y_6534_);
lean_dec_ref(v___y_6530_);
lean_dec_ref(v___y_6529_);
lean_dec_ref(v___y_6527_);
lean_dec(v_matcherName_6519_);
lean_dec_ref(v_toMatcherInfo_6518_);
v_a_6592_ = lean_ctor_get(v___x_6568_, 0);
v_isSharedCheck_6599_ = !lean_is_exclusive(v___x_6568_);
if (v_isSharedCheck_6599_ == 0)
{
v___x_6594_ = v___x_6568_;
v_isShared_6595_ = v_isSharedCheck_6599_;
goto v_resetjp_6593_;
}
else
{
lean_inc(v_a_6592_);
lean_dec(v___x_6568_);
v___x_6594_ = lean_box(0);
v_isShared_6595_ = v_isSharedCheck_6599_;
goto v_resetjp_6593_;
}
v_resetjp_6593_:
{
lean_object* v___x_6597_; 
if (v_isShared_6595_ == 0)
{
v___x_6597_ = v___x_6594_;
goto v_reusejp_6596_;
}
else
{
lean_object* v_reuseFailAlloc_6598_; 
v_reuseFailAlloc_6598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6598_, 0, v_a_6592_);
v___x_6597_ = v_reuseFailAlloc_6598_;
goto v_reusejp_6596_;
}
v_reusejp_6596_:
{
return v___x_6597_;
}
}
}
}
else
{
lean_object* v_a_6600_; lean_object* v___x_6602_; uint8_t v_isShared_6603_; uint8_t v_isSharedCheck_6607_; 
lean_dec(v___y_6538_);
lean_dec_ref(v___y_6536_);
lean_dec_ref(v___y_6534_);
lean_dec_ref(v___y_6530_);
lean_dec_ref(v___y_6529_);
lean_dec_ref(v___y_6527_);
lean_dec_ref(v_remaining_6525_);
lean_dec(v_matcherName_6519_);
lean_dec_ref(v_toMatcherInfo_6518_);
lean_dec_ref(v_onRemaining_6510_);
v_a_6600_ = lean_ctor_get(v___x_6565_, 0);
v_isSharedCheck_6607_ = !lean_is_exclusive(v___x_6565_);
if (v_isSharedCheck_6607_ == 0)
{
v___x_6602_ = v___x_6565_;
v_isShared_6603_ = v_isSharedCheck_6607_;
goto v_resetjp_6601_;
}
else
{
lean_inc(v_a_6600_);
lean_dec(v___x_6565_);
v___x_6602_ = lean_box(0);
v_isShared_6603_ = v_isSharedCheck_6607_;
goto v_resetjp_6601_;
}
v_resetjp_6601_:
{
lean_object* v___x_6605_; 
if (v_isShared_6603_ == 0)
{
v___x_6605_ = v___x_6602_;
goto v_reusejp_6604_;
}
else
{
lean_object* v_reuseFailAlloc_6606_; 
v_reuseFailAlloc_6606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6606_, 0, v_a_6600_);
v___x_6605_ = v_reuseFailAlloc_6606_;
goto v_reusejp_6604_;
}
v_reusejp_6604_:
{
return v___x_6605_;
}
}
}
}
else
{
lean_object* v_a_6608_; lean_object* v___x_6610_; uint8_t v_isShared_6611_; uint8_t v_isSharedCheck_6615_; 
lean_dec(v___y_6539_);
lean_dec(v___y_6538_);
lean_dec_ref(v___y_6536_);
lean_dec_ref(v___y_6534_);
lean_dec(v___y_6533_);
lean_dec_ref(v___y_6530_);
lean_dec_ref(v___y_6529_);
lean_dec_ref(v___y_6527_);
lean_dec_ref(v_remaining_6525_);
lean_dec_ref(v_alts_6524_);
lean_dec(v_matcherName_6519_);
lean_dec_ref(v_toMatcherInfo_6518_);
lean_dec_ref(v_onRemaining_6510_);
lean_dec_ref(v_onAlt_6509_);
lean_dec_ref(v_matcherApp_6504_);
v_a_6608_ = lean_ctor_get(v___x_6554_, 0);
v_isSharedCheck_6615_ = !lean_is_exclusive(v___x_6554_);
if (v_isSharedCheck_6615_ == 0)
{
v___x_6610_ = v___x_6554_;
v_isShared_6611_ = v_isSharedCheck_6615_;
goto v_resetjp_6609_;
}
else
{
lean_inc(v_a_6608_);
lean_dec(v___x_6554_);
v___x_6610_ = lean_box(0);
v_isShared_6611_ = v_isSharedCheck_6615_;
goto v_resetjp_6609_;
}
v_resetjp_6609_:
{
lean_object* v___x_6613_; 
if (v_isShared_6611_ == 0)
{
v___x_6613_ = v___x_6610_;
goto v_reusejp_6612_;
}
else
{
lean_object* v_reuseFailAlloc_6614_; 
v_reuseFailAlloc_6614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6614_, 0, v_a_6608_);
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
else
{
lean_object* v_a_6616_; lean_object* v___x_6618_; uint8_t v_isShared_6619_; uint8_t v_isSharedCheck_6623_; 
lean_dec_ref(v_aux_6544_);
lean_dec(v___y_6539_);
lean_dec(v___y_6538_);
lean_dec_ref(v___y_6536_);
lean_dec_ref(v___y_6534_);
lean_dec(v___y_6533_);
lean_dec_ref(v___y_6530_);
lean_dec_ref(v___y_6529_);
lean_dec_ref(v___y_6527_);
lean_dec_ref(v_remaining_6525_);
lean_dec_ref(v_alts_6524_);
lean_dec(v_matcherName_6519_);
lean_dec_ref(v_toMatcherInfo_6518_);
lean_dec_ref(v_onRemaining_6510_);
lean_dec_ref(v_onAlt_6509_);
lean_dec_ref(v_matcherApp_6504_);
v_a_6616_ = lean_ctor_get(v___x_6552_, 0);
v_isSharedCheck_6623_ = !lean_is_exclusive(v___x_6552_);
if (v_isSharedCheck_6623_ == 0)
{
v___x_6618_ = v___x_6552_;
v_isShared_6619_ = v_isSharedCheck_6623_;
goto v_resetjp_6617_;
}
else
{
lean_inc(v_a_6616_);
lean_dec(v___x_6552_);
v___x_6618_ = lean_box(0);
v_isShared_6619_ = v_isSharedCheck_6623_;
goto v_resetjp_6617_;
}
v_resetjp_6617_:
{
lean_object* v___x_6621_; 
if (v_isShared_6619_ == 0)
{
v___x_6621_ = v___x_6618_;
goto v_reusejp_6620_;
}
else
{
lean_object* v_reuseFailAlloc_6622_; 
v_reuseFailAlloc_6622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6622_, 0, v_a_6616_);
v___x_6621_ = v_reuseFailAlloc_6622_;
goto v_reusejp_6620_;
}
v_reusejp_6620_:
{
return v___x_6621_;
}
}
}
}
v___jp_6625_:
{
lean_object* v___x_6638_; lean_object* v_remaining_x27_6639_; lean_object* v___x_6640_; lean_object* v___x_6641_; lean_object* v___x_6642_; lean_object* v___x_6643_; lean_object* v___x_6644_; lean_object* v___x_6645_; size_t v_sz_6646_; lean_object* v___x_6647_; 
v___x_6638_ = lean_unsigned_to_nat(0u);
v_remaining_x27_6639_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_6640_ = l_Array_reverse___redArg(v___y_6628_);
v___x_6641_ = lean_array_get_size(v___x_6640_);
v___x_6642_ = l_Array_toSubarray___redArg(v___x_6640_, v___x_6638_, v___x_6641_);
lean_inc_ref(v___y_6626_);
v___x_6643_ = l_Array_reverse___redArg(v___y_6626_);
v___x_6644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6644_, 0, v___x_6638_);
lean_ctor_set(v___x_6644_, 1, v___x_6642_);
v___x_6645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6645_, 0, v_remaining_x27_6639_);
lean_ctor_set(v___x_6645_, 1, v___x_6644_);
v_sz_6646_ = lean_array_size(v___x_6643_);
v___x_6647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(v___x_6643_, v_sz_6646_, v___y_6627_, v___x_6645_, v___y_6634_, v___y_6635_, v___y_6636_, v___y_6637_);
lean_dec_ref(v___x_6643_);
if (lean_obj_tag(v___x_6647_) == 0)
{
lean_object* v_a_6648_; lean_object* v_snd_6649_; 
v_a_6648_ = lean_ctor_get(v___x_6647_, 0);
lean_inc(v_a_6648_);
lean_dec_ref(v___x_6647_);
v_snd_6649_ = lean_ctor_get(v_a_6648_, 1);
lean_inc(v_snd_6649_);
if (v_useSplitter_6505_ == 0)
{
lean_object* v_fst_6650_; lean_object* v_fst_6651_; 
lean_dec(v___y_6632_);
v_fst_6650_ = lean_ctor_get(v_a_6648_, 0);
lean_inc(v_fst_6650_);
lean_dec(v_a_6648_);
v_fst_6651_ = lean_ctor_get(v_snd_6649_, 0);
lean_inc(v_fst_6651_);
lean_dec(v_snd_6649_);
v___y_6527_ = v___y_6626_;
v___y_6528_ = v___y_6635_;
v___y_6529_ = v___y_6630_;
v___y_6530_ = v___y_6629_;
v___y_6531_ = v___y_6636_;
v___y_6532_ = v___y_6634_;
v___y_6533_ = v___x_6638_;
v___y_6534_ = v_matcherLevels_6633_;
v___y_6535_ = v___y_6637_;
v___y_6536_ = v___y_6631_;
v___y_6537_ = v_remaining_x27_6639_;
v___y_6538_ = v_fst_6650_;
v___y_6539_ = v_fst_6651_;
goto v___jp_6526_;
}
else
{
if (v_isCasesOn_6624_ == 0)
{
lean_object* v___x_6653_; uint8_t v_isShared_6654_; uint8_t v_isSharedCheck_6811_; 
v_isSharedCheck_6811_ = !lean_is_exclusive(v_matcherApp_6504_);
if (v_isSharedCheck_6811_ == 0)
{
lean_object* v_unused_6812_; lean_object* v_unused_6813_; lean_object* v_unused_6814_; lean_object* v_unused_6815_; lean_object* v_unused_6816_; lean_object* v_unused_6817_; lean_object* v_unused_6818_; lean_object* v_unused_6819_; 
v_unused_6812_ = lean_ctor_get(v_matcherApp_6504_, 7);
lean_dec(v_unused_6812_);
v_unused_6813_ = lean_ctor_get(v_matcherApp_6504_, 6);
lean_dec(v_unused_6813_);
v_unused_6814_ = lean_ctor_get(v_matcherApp_6504_, 5);
lean_dec(v_unused_6814_);
v_unused_6815_ = lean_ctor_get(v_matcherApp_6504_, 4);
lean_dec(v_unused_6815_);
v_unused_6816_ = lean_ctor_get(v_matcherApp_6504_, 3);
lean_dec(v_unused_6816_);
v_unused_6817_ = lean_ctor_get(v_matcherApp_6504_, 2);
lean_dec(v_unused_6817_);
v_unused_6818_ = lean_ctor_get(v_matcherApp_6504_, 1);
lean_dec(v_unused_6818_);
v_unused_6819_ = lean_ctor_get(v_matcherApp_6504_, 0);
lean_dec(v_unused_6819_);
v___x_6653_ = v_matcherApp_6504_;
v_isShared_6654_ = v_isSharedCheck_6811_;
goto v_resetjp_6652_;
}
else
{
lean_dec(v_matcherApp_6504_);
v___x_6653_ = lean_box(0);
v_isShared_6654_ = v_isSharedCheck_6811_;
goto v_resetjp_6652_;
}
v_resetjp_6652_:
{
lean_object* v_fst_6655_; lean_object* v___x_6657_; uint8_t v_isShared_6658_; uint8_t v_isSharedCheck_6809_; 
v_fst_6655_ = lean_ctor_get(v_a_6648_, 0);
v_isSharedCheck_6809_ = !lean_is_exclusive(v_a_6648_);
if (v_isSharedCheck_6809_ == 0)
{
lean_object* v_unused_6810_; 
v_unused_6810_ = lean_ctor_get(v_a_6648_, 1);
lean_dec(v_unused_6810_);
v___x_6657_ = v_a_6648_;
v_isShared_6658_ = v_isSharedCheck_6809_;
goto v_resetjp_6656_;
}
else
{
lean_inc(v_fst_6655_);
lean_dec(v_a_6648_);
v___x_6657_ = lean_box(0);
v_isShared_6658_ = v_isSharedCheck_6809_;
goto v_resetjp_6656_;
}
v_resetjp_6656_:
{
lean_object* v_fst_6659_; lean_object* v___x_6661_; uint8_t v_isShared_6662_; uint8_t v_isSharedCheck_6807_; 
v_fst_6659_ = lean_ctor_get(v_snd_6649_, 0);
v_isSharedCheck_6807_ = !lean_is_exclusive(v_snd_6649_);
if (v_isSharedCheck_6807_ == 0)
{
lean_object* v_unused_6808_; 
v_unused_6808_ = lean_ctor_get(v_snd_6649_, 1);
lean_dec(v_unused_6808_);
v___x_6661_ = v_snd_6649_;
v_isShared_6662_ = v_isSharedCheck_6807_;
goto v_resetjp_6660_;
}
else
{
lean_inc(v_fst_6659_);
lean_dec(v_snd_6649_);
v___x_6661_ = lean_box(0);
v_isShared_6662_ = v_isSharedCheck_6807_;
goto v_resetjp_6660_;
}
v_resetjp_6660_:
{
lean_object* v___x_6663_; lean_object* v___x_6664_; lean_object* v_aux1_6665_; lean_object* v_aux1_6666_; lean_object* v_aux1_6667_; lean_object* v___x_6668_; lean_object* v___x_6669_; lean_object* v___x_6670_; lean_object* v___x_6671_; lean_object* v___x_6672_; lean_object* v___f_6673_; uint8_t v___x_6674_; lean_object* v___x_6675_; lean_object* v___x_6676_; lean_object* v___x_6677_; 
lean_inc_ref(v_matcherLevels_6633_);
v___x_6663_ = lean_array_to_list(v_matcherLevels_6633_);
lean_inc(v___x_6663_);
lean_inc(v_matcherName_6519_);
v___x_6664_ = l_Lean_mkConst(v_matcherName_6519_, v___x_6663_);
v_aux1_6665_ = l_Lean_mkAppN(v___x_6664_, v___y_6630_);
lean_inc_ref(v___y_6629_);
v_aux1_6666_ = l_Lean_Expr_app___override(v_aux1_6665_, v___y_6629_);
v_aux1_6667_ = l_Lean_mkAppN(v_aux1_6666_, v___y_6626_);
v___x_6668_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3);
lean_inc_ref_n(v_aux1_6667_, 2);
v___x_6669_ = l_Lean_indentExpr(v_aux1_6667_);
v___x_6670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6670_, 0, v___x_6668_);
lean_ctor_set(v___x_6670_, 1, v___x_6669_);
v___x_6671_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5);
v___x_6672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6672_, 0, v___x_6670_);
lean_ctor_set(v___x_6672_, 1, v___x_6671_);
v___f_6673_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6673_, 0, v___x_6672_);
v___x_6674_ = 0;
v___x_6675_ = lean_box(v___x_6674_);
v___x_6676_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6676_, 0, v_aux1_6667_);
lean_closure_set(v___x_6676_, 1, v___x_6675_);
v___x_6677_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6676_, v___f_6673_, v___y_6634_, v___y_6635_, v___y_6636_, v___y_6637_);
if (lean_obj_tag(v___x_6677_) == 0)
{
lean_object* v___x_6678_; lean_object* v___x_6679_; 
lean_dec_ref(v___x_6677_);
v___x_6678_ = lean_array_get_size(v_alts_6524_);
v___x_6679_ = l_Lean_Meta_inferArgumentTypesN(v___x_6678_, v_aux1_6667_, v___y_6634_, v___y_6635_, v___y_6636_, v___y_6637_);
if (lean_obj_tag(v___x_6679_) == 0)
{
lean_object* v_a_6680_; lean_object* v___x_6681_; 
v_a_6680_ = lean_ctor_get(v___x_6679_, 0);
lean_inc(v_a_6680_);
lean_dec_ref(v___x_6679_);
lean_inc(v___y_6637_);
lean_inc_ref(v___y_6636_);
lean_inc(v___y_6635_);
lean_inc_ref(v___y_6634_);
v___x_6681_ = lean_get_match_equations_for(v_matcherName_6519_, v___y_6634_, v___y_6635_, v___y_6636_, v___y_6637_);
if (lean_obj_tag(v___x_6681_) == 0)
{
lean_object* v_a_6682_; lean_object* v_splitterName_6683_; lean_object* v_splitterMatchInfo_6684_; lean_object* v___x_6685_; lean_object* v_aux2_6686_; lean_object* v_aux2_6687_; lean_object* v_aux2_6688_; lean_object* v___x_6689_; lean_object* v___x_6690_; lean_object* v___x_6691_; lean_object* v___x_6692_; lean_object* v___f_6693_; lean_object* v___x_6694_; lean_object* v___x_6695_; lean_object* v___x_6696_; 
v_a_6682_ = lean_ctor_get(v___x_6681_, 0);
lean_inc(v_a_6682_);
lean_dec_ref(v___x_6681_);
v_splitterName_6683_ = lean_ctor_get(v_a_6682_, 1);
lean_inc_n(v_splitterName_6683_, 2);
v_splitterMatchInfo_6684_ = lean_ctor_get(v_a_6682_, 2);
lean_inc_ref(v_splitterMatchInfo_6684_);
lean_dec(v_a_6682_);
v___x_6685_ = l_Lean_mkConst(v_splitterName_6683_, v___x_6663_);
v_aux2_6686_ = l_Lean_mkAppN(v___x_6685_, v___y_6630_);
lean_inc_ref(v___y_6629_);
v_aux2_6687_ = l_Lean_Expr_app___override(v_aux2_6686_, v___y_6629_);
v_aux2_6688_ = l_Lean_mkAppN(v_aux2_6687_, v___y_6626_);
v___x_6689_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1);
lean_inc_ref_n(v_aux2_6688_, 2);
v___x_6690_ = l_Lean_indentExpr(v_aux2_6688_);
v___x_6691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6691_, 0, v___x_6689_);
lean_ctor_set(v___x_6691_, 1, v___x_6690_);
v___x_6692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6692_, 0, v___x_6691_);
lean_ctor_set(v___x_6692_, 1, v___x_6671_);
v___f_6693_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6693_, 0, v___x_6692_);
v___x_6694_ = lean_box(v___x_6674_);
v___x_6695_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6695_, 0, v_aux2_6688_);
lean_closure_set(v___x_6695_, 1, v___x_6694_);
v___x_6696_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6695_, v___f_6693_, v___y_6634_, v___y_6635_, v___y_6636_, v___y_6637_);
if (lean_obj_tag(v___x_6696_) == 0)
{
lean_object* v___x_6697_; 
lean_dec_ref(v___x_6696_);
v___x_6697_ = l_Lean_Meta_inferArgumentTypesN(v___x_6678_, v_aux2_6688_, v___y_6634_, v___y_6635_, v___y_6636_, v___y_6637_);
if (lean_obj_tag(v___x_6697_) == 0)
{
lean_object* v_a_6698_; lean_object* v_numParams_6699_; lean_object* v_numDiscrs_6700_; lean_object* v_altInfos_6701_; lean_object* v_uElimPos_x3f_6702_; lean_object* v_overlaps_6703_; lean_object* v_altInfos_6704_; lean_object* v___x_6706_; uint8_t v_isShared_6707_; uint8_t v_isSharedCheck_6761_; 
v_a_6698_ = lean_ctor_get(v___x_6697_, 0);
lean_inc(v_a_6698_);
lean_dec_ref(v___x_6697_);
v_numParams_6699_ = lean_ctor_get(v_toMatcherInfo_6518_, 0);
lean_inc(v_numParams_6699_);
v_numDiscrs_6700_ = lean_ctor_get(v_toMatcherInfo_6518_, 1);
lean_inc(v_numDiscrs_6700_);
v_altInfos_6701_ = lean_ctor_get(v_toMatcherInfo_6518_, 2);
lean_inc_ref(v_altInfos_6701_);
v_uElimPos_x3f_6702_ = lean_ctor_get(v_toMatcherInfo_6518_, 3);
lean_inc(v_uElimPos_x3f_6702_);
v_overlaps_6703_ = lean_ctor_get(v_toMatcherInfo_6518_, 5);
lean_inc_ref(v_overlaps_6703_);
lean_dec_ref(v_toMatcherInfo_6518_);
v_altInfos_6704_ = lean_ctor_get(v_splitterMatchInfo_6684_, 2);
v_isSharedCheck_6761_ = !lean_is_exclusive(v_splitterMatchInfo_6684_);
if (v_isSharedCheck_6761_ == 0)
{
lean_object* v_unused_6762_; lean_object* v_unused_6763_; lean_object* v_unused_6764_; lean_object* v_unused_6765_; lean_object* v_unused_6766_; 
v_unused_6762_ = lean_ctor_get(v_splitterMatchInfo_6684_, 5);
lean_dec(v_unused_6762_);
v_unused_6763_ = lean_ctor_get(v_splitterMatchInfo_6684_, 4);
lean_dec(v_unused_6763_);
v_unused_6764_ = lean_ctor_get(v_splitterMatchInfo_6684_, 3);
lean_dec(v_unused_6764_);
v_unused_6765_ = lean_ctor_get(v_splitterMatchInfo_6684_, 1);
lean_dec(v_unused_6765_);
v_unused_6766_ = lean_ctor_get(v_splitterMatchInfo_6684_, 0);
lean_dec(v_unused_6766_);
v___x_6706_ = v_splitterMatchInfo_6684_;
v_isShared_6707_ = v_isSharedCheck_6761_;
goto v_resetjp_6705_;
}
else
{
lean_inc(v_altInfos_6704_);
lean_dec(v_splitterMatchInfo_6684_);
v___x_6706_ = lean_box(0);
v_isShared_6707_ = v_isSharedCheck_6761_;
goto v_resetjp_6705_;
}
v_resetjp_6705_:
{
lean_object* v___x_6708_; lean_object* v___x_6709_; lean_object* v___x_6710_; lean_object* v___x_6711_; lean_object* v___x_6712_; lean_object* v___x_6713_; lean_object* v___x_6714_; lean_object* v___x_6715_; lean_object* v___x_6716_; lean_object* v___x_6718_; 
v___x_6708_ = lean_array_get_size(v_altInfos_6701_);
v___x_6709_ = lean_array_get_size(v_altInfos_6704_);
v___x_6710_ = lean_array_get_size(v_a_6680_);
v___x_6711_ = lean_array_get_size(v_a_6698_);
v___x_6712_ = l_Array_toSubarray___redArg(v_alts_6524_, v___x_6638_, v___x_6678_);
lean_inc_ref(v_altInfos_6701_);
v___x_6713_ = l_Array_toSubarray___redArg(v_altInfos_6701_, v___x_6638_, v___x_6708_);
v___x_6714_ = l_Array_toSubarray___redArg(v_altInfos_6704_, v___x_6638_, v___x_6709_);
v___x_6715_ = l_Array_toSubarray___redArg(v_a_6680_, v___x_6638_, v___x_6710_);
v___x_6716_ = l_Array_toSubarray___redArg(v_a_6698_, v___x_6638_, v___x_6711_);
if (v_isShared_6662_ == 0)
{
lean_ctor_set(v___x_6661_, 1, v___x_6716_);
lean_ctor_set(v___x_6661_, 0, v___x_6715_);
v___x_6718_ = v___x_6661_;
goto v_reusejp_6717_;
}
else
{
lean_object* v_reuseFailAlloc_6760_; 
v_reuseFailAlloc_6760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6760_, 0, v___x_6715_);
lean_ctor_set(v_reuseFailAlloc_6760_, 1, v___x_6716_);
v___x_6718_ = v_reuseFailAlloc_6760_;
goto v_reusejp_6717_;
}
v_reusejp_6717_:
{
lean_object* v___x_6720_; 
if (v_isShared_6658_ == 0)
{
lean_ctor_set(v___x_6657_, 1, v___x_6718_);
lean_ctor_set(v___x_6657_, 0, v___x_6714_);
v___x_6720_ = v___x_6657_;
goto v_reusejp_6719_;
}
else
{
lean_object* v_reuseFailAlloc_6759_; 
v_reuseFailAlloc_6759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6759_, 0, v___x_6714_);
lean_ctor_set(v_reuseFailAlloc_6759_, 1, v___x_6718_);
v___x_6720_ = v_reuseFailAlloc_6759_;
goto v_reusejp_6719_;
}
v_reusejp_6719_:
{
lean_object* v___x_6721_; lean_object* v___x_6722_; lean_object* v___x_6723_; lean_object* v___x_6724_; 
v___x_6721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6721_, 0, v___x_6713_);
lean_ctor_set(v___x_6721_, 1, v___x_6720_);
v___x_6722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6722_, 0, v___x_6712_);
lean_ctor_set(v___x_6722_, 1, v___x_6721_);
v___x_6723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6723_, 0, v_remaining_x27_6639_);
lean_ctor_set(v___x_6723_, 1, v___x_6722_);
v___x_6724_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v___x_6678_, v_onAlt_6509_, v_useSplitter_6505_, v_fst_6659_, v___y_6632_, v___x_6638_, v___x_6723_, v___y_6634_, v___y_6635_, v___y_6636_, v___y_6637_);
if (lean_obj_tag(v___x_6724_) == 0)
{
lean_object* v_a_6725_; lean_object* v_fst_6726_; lean_object* v___x_6727_; 
v_a_6725_ = lean_ctor_get(v___x_6724_, 0);
lean_inc(v_a_6725_);
lean_dec_ref(v___x_6724_);
v_fst_6726_ = lean_ctor_get(v_a_6725_, 0);
lean_inc(v_fst_6726_);
lean_dec(v_a_6725_);
lean_inc(v___y_6637_);
lean_inc_ref(v___y_6636_);
lean_inc(v___y_6635_);
lean_inc_ref(v___y_6634_);
v___x_6727_ = lean_apply_6(v_onRemaining_6510_, v_remaining_6525_, v___y_6634_, v___y_6635_, v___y_6636_, v___y_6637_, lean_box(0));
if (lean_obj_tag(v___x_6727_) == 0)
{
lean_object* v_a_6728_; lean_object* v___x_6730_; uint8_t v_isShared_6731_; uint8_t v_isSharedCheck_6742_; 
v_a_6728_ = lean_ctor_get(v___x_6727_, 0);
v_isSharedCheck_6742_ = !lean_is_exclusive(v___x_6727_);
if (v_isSharedCheck_6742_ == 0)
{
v___x_6730_ = v___x_6727_;
v_isShared_6731_ = v_isSharedCheck_6742_;
goto v_resetjp_6729_;
}
else
{
lean_inc(v_a_6728_);
lean_dec(v___x_6727_);
v___x_6730_ = lean_box(0);
v_isShared_6731_ = v_isSharedCheck_6742_;
goto v_resetjp_6729_;
}
v_resetjp_6729_:
{
lean_object* v_remaining_x27_6732_; lean_object* v___x_6734_; 
v_remaining_x27_6732_ = l_Array_append___redArg(v_fst_6655_, v_a_6728_);
lean_dec(v_a_6728_);
if (v_isShared_6707_ == 0)
{
lean_ctor_set(v___x_6706_, 5, v_overlaps_6703_);
lean_ctor_set(v___x_6706_, 4, v___y_6631_);
lean_ctor_set(v___x_6706_, 3, v_uElimPos_x3f_6702_);
lean_ctor_set(v___x_6706_, 2, v_altInfos_6701_);
lean_ctor_set(v___x_6706_, 1, v_numDiscrs_6700_);
lean_ctor_set(v___x_6706_, 0, v_numParams_6699_);
v___x_6734_ = v___x_6706_;
goto v_reusejp_6733_;
}
else
{
lean_object* v_reuseFailAlloc_6741_; 
v_reuseFailAlloc_6741_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6741_, 0, v_numParams_6699_);
lean_ctor_set(v_reuseFailAlloc_6741_, 1, v_numDiscrs_6700_);
lean_ctor_set(v_reuseFailAlloc_6741_, 2, v_altInfos_6701_);
lean_ctor_set(v_reuseFailAlloc_6741_, 3, v_uElimPos_x3f_6702_);
lean_ctor_set(v_reuseFailAlloc_6741_, 4, v___y_6631_);
lean_ctor_set(v_reuseFailAlloc_6741_, 5, v_overlaps_6703_);
v___x_6734_ = v_reuseFailAlloc_6741_;
goto v_reusejp_6733_;
}
v_reusejp_6733_:
{
lean_object* v___x_6736_; 
if (v_isShared_6654_ == 0)
{
lean_ctor_set(v___x_6653_, 7, v_remaining_x27_6732_);
lean_ctor_set(v___x_6653_, 6, v_fst_6726_);
lean_ctor_set(v___x_6653_, 5, v___y_6626_);
lean_ctor_set(v___x_6653_, 4, v___y_6629_);
lean_ctor_set(v___x_6653_, 3, v___y_6630_);
lean_ctor_set(v___x_6653_, 2, v_matcherLevels_6633_);
lean_ctor_set(v___x_6653_, 1, v_splitterName_6683_);
lean_ctor_set(v___x_6653_, 0, v___x_6734_);
v___x_6736_ = v___x_6653_;
goto v_reusejp_6735_;
}
else
{
lean_object* v_reuseFailAlloc_6740_; 
v_reuseFailAlloc_6740_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_6740_, 0, v___x_6734_);
lean_ctor_set(v_reuseFailAlloc_6740_, 1, v_splitterName_6683_);
lean_ctor_set(v_reuseFailAlloc_6740_, 2, v_matcherLevels_6633_);
lean_ctor_set(v_reuseFailAlloc_6740_, 3, v___y_6630_);
lean_ctor_set(v_reuseFailAlloc_6740_, 4, v___y_6629_);
lean_ctor_set(v_reuseFailAlloc_6740_, 5, v___y_6626_);
lean_ctor_set(v_reuseFailAlloc_6740_, 6, v_fst_6726_);
lean_ctor_set(v_reuseFailAlloc_6740_, 7, v_remaining_x27_6732_);
v___x_6736_ = v_reuseFailAlloc_6740_;
goto v_reusejp_6735_;
}
v_reusejp_6735_:
{
lean_object* v___x_6738_; 
if (v_isShared_6731_ == 0)
{
lean_ctor_set(v___x_6730_, 0, v___x_6736_);
v___x_6738_ = v___x_6730_;
goto v_reusejp_6737_;
}
else
{
lean_object* v_reuseFailAlloc_6739_; 
v_reuseFailAlloc_6739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6739_, 0, v___x_6736_);
v___x_6738_ = v_reuseFailAlloc_6739_;
goto v_reusejp_6737_;
}
v_reusejp_6737_:
{
return v___x_6738_;
}
}
}
}
}
else
{
lean_object* v_a_6743_; lean_object* v___x_6745_; uint8_t v_isShared_6746_; uint8_t v_isSharedCheck_6750_; 
lean_dec(v_fst_6726_);
lean_del_object(v___x_6706_);
lean_dec_ref(v_overlaps_6703_);
lean_dec(v_uElimPos_x3f_6702_);
lean_dec_ref(v_altInfos_6701_);
lean_dec(v_numDiscrs_6700_);
lean_dec(v_numParams_6699_);
lean_dec(v_splitterName_6683_);
lean_dec(v_fst_6655_);
lean_del_object(v___x_6653_);
lean_dec_ref(v_matcherLevels_6633_);
lean_dec_ref(v___y_6631_);
lean_dec_ref(v___y_6630_);
lean_dec_ref(v___y_6629_);
lean_dec_ref(v___y_6626_);
v_a_6743_ = lean_ctor_get(v___x_6727_, 0);
v_isSharedCheck_6750_ = !lean_is_exclusive(v___x_6727_);
if (v_isSharedCheck_6750_ == 0)
{
v___x_6745_ = v___x_6727_;
v_isShared_6746_ = v_isSharedCheck_6750_;
goto v_resetjp_6744_;
}
else
{
lean_inc(v_a_6743_);
lean_dec(v___x_6727_);
v___x_6745_ = lean_box(0);
v_isShared_6746_ = v_isSharedCheck_6750_;
goto v_resetjp_6744_;
}
v_resetjp_6744_:
{
lean_object* v___x_6748_; 
if (v_isShared_6746_ == 0)
{
v___x_6748_ = v___x_6745_;
goto v_reusejp_6747_;
}
else
{
lean_object* v_reuseFailAlloc_6749_; 
v_reuseFailAlloc_6749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6749_, 0, v_a_6743_);
v___x_6748_ = v_reuseFailAlloc_6749_;
goto v_reusejp_6747_;
}
v_reusejp_6747_:
{
return v___x_6748_;
}
}
}
}
else
{
lean_object* v_a_6751_; lean_object* v___x_6753_; uint8_t v_isShared_6754_; uint8_t v_isSharedCheck_6758_; 
lean_del_object(v___x_6706_);
lean_dec_ref(v_overlaps_6703_);
lean_dec(v_uElimPos_x3f_6702_);
lean_dec_ref(v_altInfos_6701_);
lean_dec(v_numDiscrs_6700_);
lean_dec(v_numParams_6699_);
lean_dec(v_splitterName_6683_);
lean_dec(v_fst_6655_);
lean_del_object(v___x_6653_);
lean_dec_ref(v_matcherLevels_6633_);
lean_dec_ref(v___y_6631_);
lean_dec_ref(v___y_6630_);
lean_dec_ref(v___y_6629_);
lean_dec_ref(v___y_6626_);
lean_dec_ref(v_remaining_6525_);
lean_dec_ref(v_onRemaining_6510_);
v_a_6751_ = lean_ctor_get(v___x_6724_, 0);
v_isSharedCheck_6758_ = !lean_is_exclusive(v___x_6724_);
if (v_isSharedCheck_6758_ == 0)
{
v___x_6753_ = v___x_6724_;
v_isShared_6754_ = v_isSharedCheck_6758_;
goto v_resetjp_6752_;
}
else
{
lean_inc(v_a_6751_);
lean_dec(v___x_6724_);
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
}
}
}
else
{
lean_object* v_a_6767_; lean_object* v___x_6769_; uint8_t v_isShared_6770_; uint8_t v_isSharedCheck_6774_; 
lean_dec_ref(v_splitterMatchInfo_6684_);
lean_dec(v_splitterName_6683_);
lean_dec(v_a_6680_);
lean_del_object(v___x_6661_);
lean_dec(v_fst_6659_);
lean_del_object(v___x_6657_);
lean_dec(v_fst_6655_);
lean_del_object(v___x_6653_);
lean_dec_ref(v_matcherLevels_6633_);
lean_dec(v___y_6632_);
lean_dec_ref(v___y_6631_);
lean_dec_ref(v___y_6630_);
lean_dec_ref(v___y_6629_);
lean_dec_ref(v___y_6626_);
lean_dec_ref(v_remaining_6525_);
lean_dec_ref(v_alts_6524_);
lean_dec_ref(v_toMatcherInfo_6518_);
lean_dec_ref(v_onRemaining_6510_);
lean_dec_ref(v_onAlt_6509_);
v_a_6767_ = lean_ctor_get(v___x_6697_, 0);
v_isSharedCheck_6774_ = !lean_is_exclusive(v___x_6697_);
if (v_isSharedCheck_6774_ == 0)
{
v___x_6769_ = v___x_6697_;
v_isShared_6770_ = v_isSharedCheck_6774_;
goto v_resetjp_6768_;
}
else
{
lean_inc(v_a_6767_);
lean_dec(v___x_6697_);
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
lean_dec_ref(v_aux2_6688_);
lean_dec_ref(v_splitterMatchInfo_6684_);
lean_dec(v_splitterName_6683_);
lean_dec(v_a_6680_);
lean_del_object(v___x_6661_);
lean_dec(v_fst_6659_);
lean_del_object(v___x_6657_);
lean_dec(v_fst_6655_);
lean_del_object(v___x_6653_);
lean_dec_ref(v_matcherLevels_6633_);
lean_dec(v___y_6632_);
lean_dec_ref(v___y_6631_);
lean_dec_ref(v___y_6630_);
lean_dec_ref(v___y_6629_);
lean_dec_ref(v___y_6626_);
lean_dec_ref(v_remaining_6525_);
lean_dec_ref(v_alts_6524_);
lean_dec_ref(v_toMatcherInfo_6518_);
lean_dec_ref(v_onRemaining_6510_);
lean_dec_ref(v_onAlt_6509_);
v_a_6775_ = lean_ctor_get(v___x_6696_, 0);
v_isSharedCheck_6782_ = !lean_is_exclusive(v___x_6696_);
if (v_isSharedCheck_6782_ == 0)
{
v___x_6777_ = v___x_6696_;
v_isShared_6778_ = v_isSharedCheck_6782_;
goto v_resetjp_6776_;
}
else
{
lean_inc(v_a_6775_);
lean_dec(v___x_6696_);
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
lean_dec(v_a_6680_);
lean_dec(v___x_6663_);
lean_del_object(v___x_6661_);
lean_dec(v_fst_6659_);
lean_del_object(v___x_6657_);
lean_dec(v_fst_6655_);
lean_del_object(v___x_6653_);
lean_dec_ref(v_matcherLevels_6633_);
lean_dec(v___y_6632_);
lean_dec_ref(v___y_6631_);
lean_dec_ref(v___y_6630_);
lean_dec_ref(v___y_6629_);
lean_dec_ref(v___y_6626_);
lean_dec_ref(v_remaining_6525_);
lean_dec_ref(v_alts_6524_);
lean_dec_ref(v_toMatcherInfo_6518_);
lean_dec_ref(v_onRemaining_6510_);
lean_dec_ref(v_onAlt_6509_);
v_a_6783_ = lean_ctor_get(v___x_6681_, 0);
v_isSharedCheck_6790_ = !lean_is_exclusive(v___x_6681_);
if (v_isSharedCheck_6790_ == 0)
{
v___x_6785_ = v___x_6681_;
v_isShared_6786_ = v_isSharedCheck_6790_;
goto v_resetjp_6784_;
}
else
{
lean_inc(v_a_6783_);
lean_dec(v___x_6681_);
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
else
{
lean_object* v_a_6791_; lean_object* v___x_6793_; uint8_t v_isShared_6794_; uint8_t v_isSharedCheck_6798_; 
lean_dec(v___x_6663_);
lean_del_object(v___x_6661_);
lean_dec(v_fst_6659_);
lean_del_object(v___x_6657_);
lean_dec(v_fst_6655_);
lean_del_object(v___x_6653_);
lean_dec_ref(v_matcherLevels_6633_);
lean_dec(v___y_6632_);
lean_dec_ref(v___y_6631_);
lean_dec_ref(v___y_6630_);
lean_dec_ref(v___y_6629_);
lean_dec_ref(v___y_6626_);
lean_dec_ref(v_remaining_6525_);
lean_dec_ref(v_alts_6524_);
lean_dec(v_matcherName_6519_);
lean_dec_ref(v_toMatcherInfo_6518_);
lean_dec_ref(v_onRemaining_6510_);
lean_dec_ref(v_onAlt_6509_);
v_a_6791_ = lean_ctor_get(v___x_6679_, 0);
v_isSharedCheck_6798_ = !lean_is_exclusive(v___x_6679_);
if (v_isSharedCheck_6798_ == 0)
{
v___x_6793_ = v___x_6679_;
v_isShared_6794_ = v_isSharedCheck_6798_;
goto v_resetjp_6792_;
}
else
{
lean_inc(v_a_6791_);
lean_dec(v___x_6679_);
v___x_6793_ = lean_box(0);
v_isShared_6794_ = v_isSharedCheck_6798_;
goto v_resetjp_6792_;
}
v_resetjp_6792_:
{
lean_object* v___x_6796_; 
if (v_isShared_6794_ == 0)
{
v___x_6796_ = v___x_6793_;
goto v_reusejp_6795_;
}
else
{
lean_object* v_reuseFailAlloc_6797_; 
v_reuseFailAlloc_6797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6797_, 0, v_a_6791_);
v___x_6796_ = v_reuseFailAlloc_6797_;
goto v_reusejp_6795_;
}
v_reusejp_6795_:
{
return v___x_6796_;
}
}
}
}
else
{
lean_object* v_a_6799_; lean_object* v___x_6801_; uint8_t v_isShared_6802_; uint8_t v_isSharedCheck_6806_; 
lean_dec_ref(v_aux1_6667_);
lean_dec(v___x_6663_);
lean_del_object(v___x_6661_);
lean_dec(v_fst_6659_);
lean_del_object(v___x_6657_);
lean_dec(v_fst_6655_);
lean_del_object(v___x_6653_);
lean_dec_ref(v_matcherLevels_6633_);
lean_dec(v___y_6632_);
lean_dec_ref(v___y_6631_);
lean_dec_ref(v___y_6630_);
lean_dec_ref(v___y_6629_);
lean_dec_ref(v___y_6626_);
lean_dec_ref(v_remaining_6525_);
lean_dec_ref(v_alts_6524_);
lean_dec(v_matcherName_6519_);
lean_dec_ref(v_toMatcherInfo_6518_);
lean_dec_ref(v_onRemaining_6510_);
lean_dec_ref(v_onAlt_6509_);
v_a_6799_ = lean_ctor_get(v___x_6677_, 0);
v_isSharedCheck_6806_ = !lean_is_exclusive(v___x_6677_);
if (v_isSharedCheck_6806_ == 0)
{
v___x_6801_ = v___x_6677_;
v_isShared_6802_ = v_isSharedCheck_6806_;
goto v_resetjp_6800_;
}
else
{
lean_inc(v_a_6799_);
lean_dec(v___x_6677_);
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
}
}
}
else
{
lean_object* v_fst_6820_; lean_object* v_fst_6821_; 
lean_dec(v___y_6632_);
v_fst_6820_ = lean_ctor_get(v_a_6648_, 0);
lean_inc(v_fst_6820_);
lean_dec(v_a_6648_);
v_fst_6821_ = lean_ctor_get(v_snd_6649_, 0);
lean_inc(v_fst_6821_);
lean_dec(v_snd_6649_);
v___y_6527_ = v___y_6626_;
v___y_6528_ = v___y_6635_;
v___y_6529_ = v___y_6630_;
v___y_6530_ = v___y_6629_;
v___y_6531_ = v___y_6636_;
v___y_6532_ = v___y_6634_;
v___y_6533_ = v___x_6638_;
v___y_6534_ = v_matcherLevels_6633_;
v___y_6535_ = v___y_6637_;
v___y_6536_ = v___y_6631_;
v___y_6537_ = v_remaining_x27_6639_;
v___y_6538_ = v_fst_6820_;
v___y_6539_ = v_fst_6821_;
goto v___jp_6526_;
}
}
}
else
{
lean_object* v_a_6822_; lean_object* v___x_6824_; uint8_t v_isShared_6825_; uint8_t v_isSharedCheck_6829_; 
lean_dec_ref(v_matcherLevels_6633_);
lean_dec(v___y_6632_);
lean_dec_ref(v___y_6631_);
lean_dec_ref(v___y_6630_);
lean_dec_ref(v___y_6629_);
lean_dec_ref(v___y_6626_);
lean_dec_ref(v_remaining_6525_);
lean_dec_ref(v_alts_6524_);
lean_dec(v_matcherName_6519_);
lean_dec_ref(v_toMatcherInfo_6518_);
lean_dec_ref(v_onRemaining_6510_);
lean_dec_ref(v_onAlt_6509_);
lean_dec_ref(v_matcherApp_6504_);
v_a_6822_ = lean_ctor_get(v___x_6647_, 0);
v_isSharedCheck_6829_ = !lean_is_exclusive(v___x_6647_);
if (v_isSharedCheck_6829_ == 0)
{
v___x_6824_ = v___x_6647_;
v_isShared_6825_ = v_isSharedCheck_6829_;
goto v_resetjp_6823_;
}
else
{
lean_inc(v_a_6822_);
lean_dec(v___x_6647_);
v___x_6824_ = lean_box(0);
v_isShared_6825_ = v_isSharedCheck_6829_;
goto v_resetjp_6823_;
}
v_resetjp_6823_:
{
lean_object* v___x_6827_; 
if (v_isShared_6825_ == 0)
{
v___x_6827_ = v___x_6824_;
goto v_reusejp_6826_;
}
else
{
lean_object* v_reuseFailAlloc_6828_; 
v_reuseFailAlloc_6828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6828_, 0, v_a_6822_);
v___x_6827_ = v_reuseFailAlloc_6828_;
goto v_reusejp_6826_;
}
v_reusejp_6826_:
{
return v___x_6827_;
}
}
}
}
v___jp_6830_:
{
size_t v_sz_6836_; size_t v___x_6837_; lean_object* v___x_6838_; 
v_sz_6836_ = lean_array_size(v_params_6521_);
v___x_6837_ = ((size_t)0ULL);
lean_inc_ref(v_params_6521_);
lean_inc_ref(v_onParams_6507_);
v___x_6838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6507_, v_sz_6836_, v___x_6837_, v_params_6521_, v___y_6832_, v___y_6833_, v___y_6834_, v___y_6835_);
if (lean_obj_tag(v___x_6838_) == 0)
{
lean_object* v_a_6839_; size_t v_sz_6840_; lean_object* v___x_6841_; 
v_a_6839_ = lean_ctor_get(v___x_6838_, 0);
lean_inc(v_a_6839_);
lean_dec_ref(v___x_6838_);
v_sz_6840_ = lean_array_size(v_discrs_6523_);
lean_inc_ref(v_discrs_6523_);
v___x_6841_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6507_, v_sz_6840_, v___x_6837_, v_discrs_6523_, v___y_6832_, v___y_6833_, v___y_6834_, v___y_6835_);
if (lean_obj_tag(v___x_6841_) == 0)
{
lean_object* v_a_6842_; lean_object* v___x_6843_; lean_object* v___x_6844_; lean_object* v___f_6845_; uint8_t v___x_6846_; lean_object* v___x_6847_; 
v_a_6842_ = lean_ctor_get(v___x_6841_, 0);
lean_inc_n(v_a_6842_, 2);
lean_dec_ref(v___x_6841_);
v___x_6843_ = lean_box(v_addEqualities_6506_);
v___x_6844_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed__const__1));
lean_inc_ref(v_discrs_6523_);
lean_inc_ref(v_toMatcherInfo_6518_);
v___f_6845_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed), 13, 6);
lean_closure_set(v___f_6845_, 0, v_onMotive_6508_);
lean_closure_set(v___f_6845_, 1, v_toMatcherInfo_6518_);
lean_closure_set(v___f_6845_, 2, v_a_6842_);
lean_closure_set(v___f_6845_, 3, v___x_6843_);
lean_closure_set(v___f_6845_, 4, v___x_6844_);
lean_closure_set(v___f_6845_, 5, v_discrs_6523_);
v___x_6846_ = 0;
lean_inc_ref(v_motive_6522_);
v___x_6847_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_6522_, v___f_6845_, v___x_6846_, v___y_6832_, v___y_6833_, v___y_6834_, v___y_6835_);
if (lean_obj_tag(v___x_6847_) == 0)
{
lean_object* v_a_6848_; lean_object* v_snd_6849_; lean_object* v_snd_6850_; lean_object* v_uElimPos_x3f_6851_; 
v_a_6848_ = lean_ctor_get(v___x_6847_, 0);
lean_inc(v_a_6848_);
lean_dec_ref(v___x_6847_);
v_snd_6849_ = lean_ctor_get(v_a_6848_, 1);
v_snd_6850_ = lean_ctor_get(v_snd_6849_, 1);
lean_inc(v_snd_6850_);
v_uElimPos_x3f_6851_ = lean_ctor_get(v_toMatcherInfo_6518_, 3);
if (lean_obj_tag(v_uElimPos_x3f_6851_) == 0)
{
lean_object* v_fst_6852_; lean_object* v_fst_6853_; lean_object* v_snd_6854_; 
v_fst_6852_ = lean_ctor_get(v_a_6848_, 0);
lean_inc(v_fst_6852_);
lean_dec(v_a_6848_);
v_fst_6853_ = lean_ctor_get(v_snd_6850_, 0);
lean_inc(v_fst_6853_);
v_snd_6854_ = lean_ctor_get(v_snd_6850_, 1);
lean_inc(v_snd_6854_);
lean_dec(v_snd_6850_);
lean_inc_ref(v_matcherLevels_6520_);
v___y_6626_ = v_a_6842_;
v___y_6627_ = v___x_6837_;
v___y_6628_ = v_fst_6853_;
v___y_6629_ = v_fst_6852_;
v___y_6630_ = v_a_6839_;
v___y_6631_ = v_snd_6854_;
v___y_6632_ = v_numDiscrEqs_6831_;
v_matcherLevels_6633_ = v_matcherLevels_6520_;
v___y_6634_ = v___y_6832_;
v___y_6635_ = v___y_6833_;
v___y_6636_ = v___y_6834_;
v___y_6637_ = v___y_6835_;
goto v___jp_6625_;
}
else
{
lean_object* v_fst_6855_; lean_object* v_fst_6856_; lean_object* v_fst_6857_; lean_object* v_snd_6858_; lean_object* v_val_6859_; lean_object* v___x_6860_; 
lean_inc(v_snd_6849_);
v_fst_6855_ = lean_ctor_get(v_a_6848_, 0);
lean_inc(v_fst_6855_);
lean_dec(v_a_6848_);
v_fst_6856_ = lean_ctor_get(v_snd_6849_, 0);
lean_inc(v_fst_6856_);
lean_dec(v_snd_6849_);
v_fst_6857_ = lean_ctor_get(v_snd_6850_, 0);
lean_inc(v_fst_6857_);
v_snd_6858_ = lean_ctor_get(v_snd_6850_, 1);
lean_inc(v_snd_6858_);
lean_dec(v_snd_6850_);
v_val_6859_ = lean_ctor_get(v_uElimPos_x3f_6851_, 0);
lean_inc_ref(v_matcherLevels_6520_);
v___x_6860_ = lean_array_set(v_matcherLevels_6520_, v_val_6859_, v_fst_6856_);
v___y_6626_ = v_a_6842_;
v___y_6627_ = v___x_6837_;
v___y_6628_ = v_fst_6857_;
v___y_6629_ = v_fst_6855_;
v___y_6630_ = v_a_6839_;
v___y_6631_ = v_snd_6858_;
v___y_6632_ = v_numDiscrEqs_6831_;
v_matcherLevels_6633_ = v___x_6860_;
v___y_6634_ = v___y_6832_;
v___y_6635_ = v___y_6833_;
v___y_6636_ = v___y_6834_;
v___y_6637_ = v___y_6835_;
goto v___jp_6625_;
}
}
else
{
lean_object* v_a_6861_; lean_object* v___x_6863_; uint8_t v_isShared_6864_; uint8_t v_isSharedCheck_6868_; 
lean_dec(v_a_6842_);
lean_dec(v_a_6839_);
lean_dec(v_numDiscrEqs_6831_);
lean_dec_ref(v_remaining_6525_);
lean_dec_ref(v_alts_6524_);
lean_dec(v_matcherName_6519_);
lean_dec_ref(v_toMatcherInfo_6518_);
lean_dec_ref(v_onRemaining_6510_);
lean_dec_ref(v_onAlt_6509_);
lean_dec_ref(v_matcherApp_6504_);
v_a_6861_ = lean_ctor_get(v___x_6847_, 0);
v_isSharedCheck_6868_ = !lean_is_exclusive(v___x_6847_);
if (v_isSharedCheck_6868_ == 0)
{
v___x_6863_ = v___x_6847_;
v_isShared_6864_ = v_isSharedCheck_6868_;
goto v_resetjp_6862_;
}
else
{
lean_inc(v_a_6861_);
lean_dec(v___x_6847_);
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
else
{
lean_object* v_a_6869_; lean_object* v___x_6871_; uint8_t v_isShared_6872_; uint8_t v_isSharedCheck_6876_; 
lean_dec(v_a_6839_);
lean_dec(v_numDiscrEqs_6831_);
lean_dec_ref(v_remaining_6525_);
lean_dec_ref(v_alts_6524_);
lean_dec(v_matcherName_6519_);
lean_dec_ref(v_toMatcherInfo_6518_);
lean_dec_ref(v_onRemaining_6510_);
lean_dec_ref(v_onAlt_6509_);
lean_dec_ref(v_onMotive_6508_);
lean_dec_ref(v_matcherApp_6504_);
v_a_6869_ = lean_ctor_get(v___x_6841_, 0);
v_isSharedCheck_6876_ = !lean_is_exclusive(v___x_6841_);
if (v_isSharedCheck_6876_ == 0)
{
v___x_6871_ = v___x_6841_;
v_isShared_6872_ = v_isSharedCheck_6876_;
goto v_resetjp_6870_;
}
else
{
lean_inc(v_a_6869_);
lean_dec(v___x_6841_);
v___x_6871_ = lean_box(0);
v_isShared_6872_ = v_isSharedCheck_6876_;
goto v_resetjp_6870_;
}
v_resetjp_6870_:
{
lean_object* v___x_6874_; 
if (v_isShared_6872_ == 0)
{
v___x_6874_ = v___x_6871_;
goto v_reusejp_6873_;
}
else
{
lean_object* v_reuseFailAlloc_6875_; 
v_reuseFailAlloc_6875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6875_, 0, v_a_6869_);
v___x_6874_ = v_reuseFailAlloc_6875_;
goto v_reusejp_6873_;
}
v_reusejp_6873_:
{
return v___x_6874_;
}
}
}
}
else
{
lean_object* v_a_6877_; lean_object* v___x_6879_; uint8_t v_isShared_6880_; uint8_t v_isSharedCheck_6884_; 
lean_dec(v_numDiscrEqs_6831_);
lean_dec_ref(v_remaining_6525_);
lean_dec_ref(v_alts_6524_);
lean_dec(v_matcherName_6519_);
lean_dec_ref(v_toMatcherInfo_6518_);
lean_dec_ref(v_onRemaining_6510_);
lean_dec_ref(v_onAlt_6509_);
lean_dec_ref(v_onMotive_6508_);
lean_dec_ref(v_onParams_6507_);
lean_dec_ref(v_matcherApp_6504_);
v_a_6877_ = lean_ctor_get(v___x_6838_, 0);
v_isSharedCheck_6884_ = !lean_is_exclusive(v___x_6838_);
if (v_isSharedCheck_6884_ == 0)
{
v___x_6879_ = v___x_6838_;
v_isShared_6880_ = v_isSharedCheck_6884_;
goto v_resetjp_6878_;
}
else
{
lean_inc(v_a_6877_);
lean_dec(v___x_6838_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed(lean_object* v_matcherApp_6904_, lean_object* v_useSplitter_6905_, lean_object* v_addEqualities_6906_, lean_object* v_onParams_6907_, lean_object* v_onMotive_6908_, lean_object* v_onAlt_6909_, lean_object* v_onRemaining_6910_, lean_object* v___y_6911_, lean_object* v___y_6912_, lean_object* v___y_6913_, lean_object* v___y_6914_, lean_object* v___y_6915_){
_start:
{
uint8_t v_useSplitter_boxed_6916_; uint8_t v_addEqualities_boxed_6917_; lean_object* v_res_6918_; 
v_useSplitter_boxed_6916_ = lean_unbox(v_useSplitter_6905_);
v_addEqualities_boxed_6917_ = lean_unbox(v_addEqualities_6906_);
v_res_6918_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(v_matcherApp_6904_, v_useSplitter_boxed_6916_, v_addEqualities_boxed_6917_, v_onParams_6907_, v_onMotive_6908_, v_onAlt_6909_, v_onRemaining_6910_, v___y_6911_, v___y_6912_, v___y_6913_, v___y_6914_);
lean_dec(v___y_6914_);
lean_dec_ref(v___y_6913_);
lean_dec(v___y_6912_);
lean_dec_ref(v___y_6911_);
return v_res_6918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType(lean_object* v_matcherApp_6924_, lean_object* v_a_6925_, lean_object* v_a_6926_, lean_object* v_a_6927_, lean_object* v_a_6928_){
_start:
{
lean_object* v_toMatcherInfo_6930_; lean_object* v_matcherName_6931_; lean_object* v_matcherLevels_6932_; lean_object* v_params_6933_; lean_object* v_alts_6934_; lean_object* v_remaining_6935_; lean_object* v___f_6936_; lean_object* v___f_6937_; lean_object* v_nExtra_6938_; uint8_t v___x_6939_; lean_object* v___f_6940_; uint8_t v___x_6941_; lean_object* v___x_6942_; lean_object* v___x_6943_; lean_object* v___f_6944_; lean_object* v___x_6945_; 
v_toMatcherInfo_6930_ = lean_ctor_get(v_matcherApp_6924_, 0);
v_matcherName_6931_ = lean_ctor_get(v_matcherApp_6924_, 1);
v_matcherLevels_6932_ = lean_ctor_get(v_matcherApp_6924_, 2);
v_params_6933_ = lean_ctor_get(v_matcherApp_6924_, 3);
v_alts_6934_ = lean_ctor_get(v_matcherApp_6924_, 6);
v_remaining_6935_ = lean_ctor_get(v_matcherApp_6924_, 7);
v___f_6936_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__0));
v___f_6937_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__1));
v_nExtra_6938_ = lean_array_get_size(v_remaining_6935_);
v___x_6939_ = 1;
v___f_6940_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__2));
v___x_6941_ = 0;
v___x_6942_ = lean_box(v___x_6941_);
v___x_6943_ = lean_box(v___x_6939_);
lean_inc_ref(v_matcherLevels_6932_);
lean_inc_ref(v_params_6933_);
lean_inc(v_matcherName_6931_);
lean_inc_ref(v_toMatcherInfo_6930_);
lean_inc_ref(v_alts_6934_);
v___f_6944_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed), 15, 8);
lean_closure_set(v___f_6944_, 0, v_nExtra_6938_);
lean_closure_set(v___f_6944_, 1, v___x_6942_);
lean_closure_set(v___f_6944_, 2, v___x_6943_);
lean_closure_set(v___f_6944_, 3, v_alts_6934_);
lean_closure_set(v___f_6944_, 4, v_toMatcherInfo_6930_);
lean_closure_set(v___f_6944_, 5, v_matcherName_6931_);
lean_closure_set(v___f_6944_, 6, v_params_6933_);
lean_closure_set(v___f_6944_, 7, v_matcherLevels_6932_);
v___x_6945_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(v_matcherApp_6924_, v___x_6939_, v___x_6941_, v___f_6936_, v___f_6944_, v___f_6940_, v___f_6937_, v_a_6925_, v_a_6926_, v_a_6927_, v_a_6928_);
return v___x_6945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___boxed(lean_object* v_matcherApp_6946_, lean_object* v_a_6947_, lean_object* v_a_6948_, lean_object* v_a_6949_, lean_object* v_a_6950_, lean_object* v_a_6951_){
_start:
{
lean_object* v_res_6952_; 
v_res_6952_ = l_Lean_Meta_MatcherApp_inferMatchType(v_matcherApp_6946_, v_a_6947_, v_a_6948_, v_a_6949_, v_a_6950_);
lean_dec(v_a_6950_);
lean_dec_ref(v_a_6949_);
lean_dec(v_a_6948_);
lean_dec_ref(v_a_6947_);
return v_res_6952_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(lean_object* v_a_6953_, lean_object* v_termAlt_6954_, lean_object* v_inst_6955_, lean_object* v_R_6956_, lean_object* v_a_6957_, lean_object* v_b_6958_, lean_object* v_c_6959_, lean_object* v___y_6960_, lean_object* v___y_6961_, lean_object* v___y_6962_, lean_object* v___y_6963_){
_start:
{
lean_object* v___x_6965_; 
v___x_6965_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_6953_, v_termAlt_6954_, v_a_6957_, v_b_6958_, v___y_6960_, v___y_6961_, v___y_6962_, v___y_6963_);
return v___x_6965_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___boxed(lean_object* v_a_6966_, lean_object* v_termAlt_6967_, lean_object* v_inst_6968_, lean_object* v_R_6969_, lean_object* v_a_6970_, lean_object* v_b_6971_, lean_object* v_c_6972_, lean_object* v___y_6973_, lean_object* v___y_6974_, lean_object* v___y_6975_, lean_object* v___y_6976_, lean_object* v___y_6977_){
_start:
{
lean_object* v_res_6978_; 
v_res_6978_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(v_a_6966_, v_termAlt_6967_, v_inst_6968_, v_R_6969_, v_a_6970_, v_b_6971_, v_c_6972_, v___y_6973_, v___y_6974_, v___y_6975_, v___y_6976_);
lean_dec(v___y_6976_);
lean_dec_ref(v___y_6975_);
lean_dec(v___y_6974_);
lean_dec_ref(v___y_6973_);
return v_res_6978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(lean_object* v_00_u03b1_6979_, lean_object* v_fvars_6980_, lean_object* v_names_6981_, lean_object* v_k_6982_, lean_object* v___y_6983_, lean_object* v___y_6984_, lean_object* v___y_6985_, lean_object* v___y_6986_){
_start:
{
lean_object* v___x_6988_; 
v___x_6988_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_fvars_6980_, v_names_6981_, v_k_6982_, v___y_6983_, v___y_6984_, v___y_6985_, v___y_6986_);
return v___x_6988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___boxed(lean_object* v_00_u03b1_6989_, lean_object* v_fvars_6990_, lean_object* v_names_6991_, lean_object* v_k_6992_, lean_object* v___y_6993_, lean_object* v___y_6994_, lean_object* v___y_6995_, lean_object* v___y_6996_, lean_object* v___y_6997_){
_start:
{
lean_object* v_res_6998_; 
v_res_6998_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(v_00_u03b1_6989_, v_fvars_6990_, v_names_6991_, v_k_6992_, v___y_6993_, v___y_6994_, v___y_6995_, v___y_6996_);
lean_dec(v___y_6996_);
lean_dec_ref(v___y_6995_);
lean_dec(v___y_6994_);
lean_dec_ref(v___y_6993_);
lean_dec_ref(v_names_6991_);
lean_dec_ref(v_fvars_6990_);
return v_res_6998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(lean_object* v_00_u03b1_6999_, lean_object* v_origAltType_7000_, lean_object* v_altInfo_7001_, lean_object* v_k_7002_, lean_object* v___y_7003_, lean_object* v___y_7004_, lean_object* v___y_7005_, lean_object* v___y_7006_){
_start:
{
lean_object* v___x_7008_; 
v___x_7008_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v_origAltType_7000_, v_altInfo_7001_, v_k_7002_, v___y_7003_, v___y_7004_, v___y_7005_, v___y_7006_);
return v___x_7008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___boxed(lean_object* v_00_u03b1_7009_, lean_object* v_origAltType_7010_, lean_object* v_altInfo_7011_, lean_object* v_k_7012_, lean_object* v___y_7013_, lean_object* v___y_7014_, lean_object* v___y_7015_, lean_object* v___y_7016_, lean_object* v___y_7017_){
_start:
{
lean_object* v_res_7018_; 
v_res_7018_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(v_00_u03b1_7009_, v_origAltType_7010_, v_altInfo_7011_, v_k_7012_, v___y_7013_, v___y_7014_, v___y_7015_, v___y_7016_);
lean_dec(v___y_7016_);
lean_dec_ref(v___y_7015_);
lean_dec(v___y_7014_);
lean_dec_ref(v___y_7013_);
return v_res_7018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(lean_object* v_declName_7019_, lean_object* v___y_7020_, lean_object* v___y_7021_, lean_object* v___y_7022_, lean_object* v___y_7023_){
_start:
{
lean_object* v___x_7025_; 
v___x_7025_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_declName_7019_, v___y_7023_);
return v___x_7025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___boxed(lean_object* v_declName_7026_, lean_object* v___y_7027_, lean_object* v___y_7028_, lean_object* v___y_7029_, lean_object* v___y_7030_, lean_object* v___y_7031_){
_start:
{
lean_object* v_res_7032_; 
v_res_7032_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(v_declName_7026_, v___y_7027_, v___y_7028_, v___y_7029_, v___y_7030_);
lean_dec(v___y_7030_);
lean_dec_ref(v___y_7029_);
lean_dec(v___y_7028_);
lean_dec_ref(v___y_7027_);
return v_res_7032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(size_t v_sz_7033_, size_t v_i_7034_, lean_object* v_bs_7035_, lean_object* v___y_7036_, lean_object* v___y_7037_, lean_object* v___y_7038_, lean_object* v___y_7039_){
_start:
{
lean_object* v___x_7041_; 
v___x_7041_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_7033_, v_i_7034_, v_bs_7035_, v___y_7036_, v___y_7038_, v___y_7039_);
return v___x_7041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___boxed(lean_object* v_sz_7042_, lean_object* v_i_7043_, lean_object* v_bs_7044_, lean_object* v___y_7045_, lean_object* v___y_7046_, lean_object* v___y_7047_, lean_object* v___y_7048_, lean_object* v___y_7049_){
_start:
{
size_t v_sz_boxed_7050_; size_t v_i_boxed_7051_; lean_object* v_res_7052_; 
v_sz_boxed_7050_ = lean_unbox_usize(v_sz_7042_);
lean_dec(v_sz_7042_);
v_i_boxed_7051_ = lean_unbox_usize(v_i_7043_);
lean_dec(v_i_7043_);
v_res_7052_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(v_sz_boxed_7050_, v_i_boxed_7051_, v_bs_7044_, v___y_7045_, v___y_7046_, v___y_7047_, v___y_7048_);
lean_dec(v___y_7048_);
lean_dec_ref(v___y_7047_);
lean_dec(v___y_7046_);
lean_dec_ref(v___y_7045_);
return v_res_7052_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(lean_object* v_upperBound_7053_, lean_object* v_onAlt_7054_, lean_object* v_extraEqualities_7055_, lean_object* v_inst_7056_, lean_object* v_R_7057_, lean_object* v_a_7058_, lean_object* v_b_7059_, lean_object* v_c_7060_, lean_object* v___y_7061_, lean_object* v___y_7062_, lean_object* v___y_7063_, lean_object* v___y_7064_){
_start:
{
lean_object* v___x_7066_; 
v___x_7066_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v_upperBound_7053_, v_onAlt_7054_, v_extraEqualities_7055_, v_a_7058_, v_b_7059_, v___y_7061_, v___y_7062_, v___y_7063_, v___y_7064_);
return v___x_7066_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___boxed(lean_object* v_upperBound_7067_, lean_object* v_onAlt_7068_, lean_object* v_extraEqualities_7069_, lean_object* v_inst_7070_, lean_object* v_R_7071_, lean_object* v_a_7072_, lean_object* v_b_7073_, lean_object* v_c_7074_, lean_object* v___y_7075_, lean_object* v___y_7076_, lean_object* v___y_7077_, lean_object* v___y_7078_, lean_object* v___y_7079_){
_start:
{
lean_object* v_res_7080_; 
v_res_7080_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(v_upperBound_7067_, v_onAlt_7068_, v_extraEqualities_7069_, v_inst_7070_, v_R_7071_, v_a_7072_, v_b_7073_, v_c_7074_, v___y_7075_, v___y_7076_, v___y_7077_, v___y_7078_);
lean_dec(v___y_7078_);
lean_dec_ref(v___y_7077_);
lean_dec(v___y_7076_);
lean_dec_ref(v___y_7075_);
lean_dec(v_upperBound_7067_);
return v_res_7080_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(lean_object* v_upperBound_7081_, lean_object* v_onAlt_7082_, uint8_t v_useSplitter_7083_, lean_object* v_extraEqualities_7084_, lean_object* v_numDiscrEqs_7085_, lean_object* v_inst_7086_, lean_object* v_R_7087_, lean_object* v_a_7088_, lean_object* v_b_7089_, lean_object* v_c_7090_, lean_object* v___y_7091_, lean_object* v___y_7092_, lean_object* v___y_7093_, lean_object* v___y_7094_){
_start:
{
lean_object* v___x_7096_; 
v___x_7096_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v_upperBound_7081_, v_onAlt_7082_, v_useSplitter_7083_, v_extraEqualities_7084_, v_numDiscrEqs_7085_, v_a_7088_, v_b_7089_, v___y_7091_, v___y_7092_, v___y_7093_, v___y_7094_);
return v___x_7096_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___boxed(lean_object* v_upperBound_7097_, lean_object* v_onAlt_7098_, lean_object* v_useSplitter_7099_, lean_object* v_extraEqualities_7100_, lean_object* v_numDiscrEqs_7101_, lean_object* v_inst_7102_, lean_object* v_R_7103_, lean_object* v_a_7104_, lean_object* v_b_7105_, lean_object* v_c_7106_, lean_object* v___y_7107_, lean_object* v___y_7108_, lean_object* v___y_7109_, lean_object* v___y_7110_, lean_object* v___y_7111_){
_start:
{
uint8_t v_useSplitter_boxed_7112_; lean_object* v_res_7113_; 
v_useSplitter_boxed_7112_ = lean_unbox(v_useSplitter_7099_);
v_res_7113_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(v_upperBound_7097_, v_onAlt_7098_, v_useSplitter_boxed_7112_, v_extraEqualities_7100_, v_numDiscrEqs_7101_, v_inst_7102_, v_R_7103_, v_a_7104_, v_b_7105_, v_c_7106_, v___y_7107_, v___y_7108_, v___y_7109_, v___y_7110_);
lean_dec(v___y_7110_);
lean_dec_ref(v___y_7109_);
lean_dec(v___y_7108_);
lean_dec_ref(v___y_7107_);
lean_dec(v_upperBound_7097_);
return v_res_7113_;
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
