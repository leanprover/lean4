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
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* l_Subarray_empty(lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
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
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_mkEqHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_instInhabitedExpr;
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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Meta_instantiateLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_forallBoundedTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqHEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Meta_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_MatcherApp_transform___redArg___lam__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__18___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__18___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__24(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__28(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__37(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Function"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__0_value;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "const"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__1 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__1_value;
static const lean_ctor_object l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 8, 186, 189, 152, 89, 197, 12)}};
static const lean_ctor_object l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__1_value),LEAN_SCALAR_PTR_LITERAL(231, 33, 22, 82, 100, 121, 126, 178)}};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__2 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__2_value;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__3 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__3_value;
static const lean_ctor_object l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__3_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__4 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__4_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__5;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__42(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__42___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0_value;
static const lean_ctor_object l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__3_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_ctor_object l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 186, 243, 194, 96, 12, 218, 7)}};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__45___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Meta.Match.MatcherApp.Transform"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__45___closed__0_value;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__45___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Meta.MatcherApp.transform"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45___closed__1 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__45___closed__1_value;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__45___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "assertion violation: ys.size == splitterAltInfo.numFields\n        "};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45___closed__2 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__45___closed__2_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__45___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "assertion violation: altInfo.numOverlaps = 0\n      "};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__0_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__50(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__50___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "failed to transform matcher, type error when constructing splitter motive:"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__0_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "failed to transform matcher, type error when constructing new motive:"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__0_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__1;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "failed to transform matcher, type error when constructing new pre-splitter motive:"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__2 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__2_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__3;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "\nfailed with"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__4 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__4_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__61(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__61___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__62(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__62___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matcher "};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__0_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__1;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = " has no MatchInfo found"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__2 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__2_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__65(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__65___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__66(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__66___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(lean_object* v_alt_150_, uint8_t v___x_151_, lean_object* v_xs_152_, uint8_t v_refined_153_, lean_object* v___x_154_, lean_object* v_unrefinedArgType_155_, lean_object* v_x_156_, lean_object* v_x_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
uint8_t v___x_163_; uint8_t v___x_164_; lean_object* v___x_165_; 
v___x_163_ = 0;
v___x_164_ = 1;
v___x_165_ = l_Lean_Meta_mkLambdaFVars(v_x_156_, v_alt_150_, v___x_163_, v___x_151_, v___x_163_, v___x_151_, v___x_164_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v_a_166_; uint8_t v_refined_168_; lean_object* v___y_169_; lean_object* v___y_170_; lean_object* v___y_171_; lean_object* v___y_172_; 
v_a_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_a_166_);
lean_dec_ref_known(v___x_165_, 1);
if (v_refined_153_ == 0)
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = lean_unsigned_to_nat(0u);
v___x_193_ = lean_array_get_borrowed(v___x_154_, v_x_156_, v___x_192_);
lean_inc(v___y_161_);
lean_inc_ref(v___y_160_);
lean_inc(v___y_159_);
lean_inc_ref(v___y_158_);
lean_inc(v___x_193_);
v___x_194_ = lean_infer_type(v___x_193_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_196_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_a_195_);
lean_dec_ref_known(v___x_194_, 1);
v___x_196_ = l_Lean_Meta_isExprDefEq(v_unrefinedArgType_155_, v_a_195_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; uint8_t v___x_198_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_a_197_);
lean_dec_ref_known(v___x_196_, 1);
v___x_198_ = lean_unbox(v_a_197_);
lean_dec(v_a_197_);
if (v___x_198_ == 0)
{
v_refined_168_ = v___x_151_;
v___y_169_ = v___y_158_;
v___y_170_ = v___y_159_;
v___y_171_ = v___y_160_;
v___y_172_ = v___y_161_;
goto v___jp_167_;
}
else
{
v_refined_168_ = v_refined_153_;
v___y_169_ = v___y_158_;
v___y_170_ = v___y_159_;
v___y_171_ = v___y_160_;
v___y_172_ = v___y_161_;
goto v___jp_167_;
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
lean_dec(v_a_166_);
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
lean_dec(v_a_166_);
lean_dec_ref(v_unrefinedArgType_155_);
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
lean_dec_ref(v_unrefinedArgType_155_);
v_refined_168_ = v_refined_153_;
v___y_169_ = v___y_158_;
v___y_170_ = v___y_159_;
v___y_171_ = v___y_160_;
v___y_172_ = v___y_161_;
goto v___jp_167_;
}
v___jp_167_:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_Meta_mkLambdaFVars(v_xs_152_, v_a_166_, v___x_163_, v___x_151_, v___x_163_, v___x_151_, v___x_164_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_183_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_183_ == 0)
{
v___x_176_ = v___x_173_;
v_isShared_177_ = v_isSharedCheck_183_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_173_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_183_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_178_ = lean_box(v_refined_168_);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v_a_174_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 0, v___x_179_);
v___x_181_ = v___x_176_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
else
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
v_a_184_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___x_173_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_173_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_a_184_);
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
}
else
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
lean_dec_ref(v_unrefinedArgType_155_);
v_a_215_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_222_ == 0)
{
v___x_217_ = v___x_165_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_165_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0___boxed(lean_object* v_alt_223_, lean_object* v___x_224_, lean_object* v_xs_225_, lean_object* v_refined_226_, lean_object* v___x_227_, lean_object* v_unrefinedArgType_228_, lean_object* v_x_229_, lean_object* v_x_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
uint8_t v___x_4199__boxed_236_; uint8_t v_refined_boxed_237_; lean_object* v_res_238_; 
v___x_4199__boxed_236_ = lean_unbox(v___x_224_);
v_refined_boxed_237_ = lean_unbox(v_refined_226_);
v_res_238_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(v_alt_223_, v___x_4199__boxed_236_, v_xs_225_, v_refined_boxed_237_, v___x_227_, v_unrefinedArgType_228_, v_x_229_, v_x_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec_ref(v_x_230_);
lean_dec_ref(v_x_229_);
lean_dec_ref(v___x_227_);
lean_dec_ref(v_xs_225_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(uint8_t v___x_296_, uint8_t v_refined_297_, lean_object* v___x_298_, lean_object* v_unrefinedArgType_299_, lean_object* v_binderType_300_, lean_object* v_numParams_301_, lean_object* v_xs_302_, lean_object* v_alt_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___f_311_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; lean_object* v___y_335_; uint8_t v___y_336_; lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_309_ = lean_box(v___x_296_);
v___x_310_ = lean_box(v_refined_297_);
lean_inc_ref(v_xs_302_);
v___f_311_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0___boxed), 13, 6);
lean_closure_set(v___f_311_, 0, v_alt_303_);
lean_closure_set(v___f_311_, 1, v___x_309_);
lean_closure_set(v___f_311_, 2, v_xs_302_);
lean_closure_set(v___f_311_, 3, v___x_310_);
lean_closure_set(v___f_311_, 4, v___x_298_);
lean_closure_set(v___f_311_, 5, v_unrefinedArgType_299_);
v___x_344_ = lean_array_get_size(v_xs_302_);
v___x_345_ = lean_nat_dec_eq(v___x_344_, v_numParams_301_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_346_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__4, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__4_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__4);
v___x_347_ = l_Nat_reprFast(v_numParams_301_);
v___x_348_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
v___x_349_ = l_Lean_MessageData_ofFormat(v___x_348_);
v___x_350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_346_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
v___x_351_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__6, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__6_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__6);
v___x_352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_350_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___x_353_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_352_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_dec_ref_known(v___x_353_, 1);
goto v___jp_339_;
}
else
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
lean_dec_ref(v___f_311_);
lean_dec_ref(v_xs_302_);
lean_dec_ref(v_binderType_300_);
v_a_354_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_353_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_353_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_354_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
else
{
lean_dec(v_numParams_301_);
goto v___jp_339_;
}
v___jp_312_:
{
if (lean_obj_tag(v___y_317_) == 0)
{
lean_object* v_a_318_; lean_object* v___x_319_; uint8_t v___x_320_; lean_object* v___x_321_; 
v_a_318_ = lean_ctor_get(v___y_317_, 0);
lean_inc(v_a_318_);
lean_dec_ref_known(v___y_317_, 1);
v___x_319_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__0));
v___x_320_ = 0;
v___x_321_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_a_318_, v___x_319_, v___f_311_, v___x_320_, v___x_320_, v___y_314_, v___y_315_, v___y_313_, v___y_316_);
return v___x_321_;
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
lean_dec_ref(v___f_311_);
v_a_322_ = lean_ctor_get(v___y_317_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___y_317_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___y_317_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___y_317_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
v___jp_330_:
{
if (v___y_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec_ref(v___y_332_);
v___x_337_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2);
v___x_338_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_337_, v___y_333_, v___y_334_, v___y_331_, v___y_335_);
v___y_313_ = v___y_331_;
v___y_314_ = v___y_333_;
v___y_315_ = v___y_334_;
v___y_316_ = v___y_335_;
v___y_317_ = v___x_338_;
goto v___jp_312_;
}
else
{
v___y_313_ = v___y_331_;
v___y_314_ = v___y_333_;
v___y_315_ = v___y_334_;
v___y_316_ = v___y_335_;
v___y_317_ = v___y_332_;
goto v___jp_312_;
}
}
v___jp_339_:
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_Meta_instantiateForall(v_binderType_300_, v_xs_302_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
lean_dec_ref(v_xs_302_);
if (lean_obj_tag(v___x_340_) == 0)
{
v___y_313_ = v___y_306_;
v___y_314_ = v___y_304_;
v___y_315_ = v___y_305_;
v___y_316_ = v___y_307_;
v___y_317_ = v___x_340_;
goto v___jp_312_;
}
else
{
lean_object* v_a_341_; uint8_t v___x_342_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_a_341_);
v___x_342_ = l_Lean_Exception_isInterrupt(v_a_341_);
if (v___x_342_ == 0)
{
uint8_t v___x_343_; 
v___x_343_ = l_Lean_Exception_isRuntime(v_a_341_);
v___y_331_ = v___y_306_;
v___y_332_ = v___x_340_;
v___y_333_ = v___y_304_;
v___y_334_ = v___y_305_;
v___y_335_ = v___y_307_;
v___y_336_ = v___x_343_;
goto v___jp_330_;
}
else
{
lean_dec(v_a_341_);
v___y_331_ = v___y_306_;
v___y_332_ = v___x_340_;
v___y_333_ = v___y_304_;
v___y_334_ = v___y_305_;
v___y_335_ = v___y_307_;
v___y_336_ = v___x_342_;
goto v___jp_330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed(lean_object* v___x_362_, lean_object* v_refined_363_, lean_object* v___x_364_, lean_object* v_unrefinedArgType_365_, lean_object* v_binderType_366_, lean_object* v_numParams_367_, lean_object* v_xs_368_, lean_object* v_alt_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
uint8_t v___x_4424__boxed_375_; uint8_t v_refined_boxed_376_; lean_object* v_res_377_; 
v___x_4424__boxed_375_ = lean_unbox(v___x_362_);
v_refined_boxed_376_ = lean_unbox(v_refined_363_);
v_res_377_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(v___x_4424__boxed_375_, v_refined_boxed_376_, v___x_364_, v_unrefinedArgType_365_, v_binderType_366_, v_numParams_367_, v_xs_368_, v_alt_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
return v_res_377_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__0));
v___x_380_ = l_Lean_stringToMessageData(v___x_379_);
return v___x_380_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__2));
v___x_383_ = l_Lean_stringToMessageData(v___x_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(lean_object* v_unrefinedArgType_384_, lean_object* v_typeNew_385_, lean_object* v_altNumParams_386_, lean_object* v_alts_387_, uint8_t v_refined_388_, lean_object* v_i_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = lean_array_get_size(v_alts_387_);
v___x_396_ = lean_nat_dec_lt(v_i_389_, v___x_395_);
if (v___x_396_ == 0)
{
lean_dec(v_i_389_);
lean_dec_ref(v_typeNew_385_);
lean_dec_ref(v_unrefinedArgType_384_);
if (v_refined_388_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; 
lean_dec_ref(v_alts_387_);
v___x_397_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1);
v___x_398_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_397_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
return v___x_398_;
}
else
{
lean_object* v___x_399_; 
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v_alts_387_);
return v___x_399_;
}
}
else
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Meta_whnfD(v_typeNew_385_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_401_);
lean_dec_ref_known(v___x_400_, 1);
if (lean_obj_tag(v_a_401_) == 7)
{
lean_object* v_binderType_402_; lean_object* v_body_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v_alt_406_; lean_object* v_numParams_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___f_410_; uint8_t v___x_411_; lean_object* v___x_412_; 
v_binderType_402_ = lean_ctor_get(v_a_401_, 1);
lean_inc_ref(v_binderType_402_);
v_body_403_ = lean_ctor_get(v_a_401_, 2);
lean_inc_ref(v_body_403_);
lean_dec_ref_known(v_a_401_, 3);
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = l_Lean_instInhabitedExpr;
v_alt_406_ = lean_array_fget_borrowed(v_alts_387_, v_i_389_);
v_numParams_407_ = lean_array_get_borrowed(v___x_404_, v_altNumParams_386_, v_i_389_);
v___x_408_ = lean_box(v___x_396_);
v___x_409_ = lean_box(v_refined_388_);
lean_inc_n(v_numParams_407_, 2);
lean_inc_ref(v_unrefinedArgType_384_);
v___f_410_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed), 13, 6);
lean_closure_set(v___f_410_, 0, v___x_408_);
lean_closure_set(v___f_410_, 1, v___x_409_);
lean_closure_set(v___f_410_, 2, v___x_405_);
lean_closure_set(v___f_410_, 3, v_unrefinedArgType_384_);
lean_closure_set(v___f_410_, 4, v_binderType_402_);
lean_closure_set(v___f_410_, 5, v_numParams_407_);
v___x_411_ = 0;
lean_inc(v_alt_406_);
v___x_412_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2___redArg(v_alt_406_, v_numParams_407_, v___f_410_, v___x_411_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v_fst_414_; lean_object* v_snd_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_412_, 1);
v_fst_414_ = lean_ctor_get(v_a_413_, 0);
lean_inc(v_fst_414_);
v_snd_415_ = lean_ctor_get(v_a_413_, 1);
lean_inc(v_snd_415_);
lean_dec(v_a_413_);
v___x_416_ = lean_expr_instantiate1(v_body_403_, v_fst_414_);
lean_dec_ref(v_body_403_);
v___x_417_ = lean_array_fset(v_alts_387_, v_i_389_, v_fst_414_);
v___x_418_ = lean_unsigned_to_nat(1u);
v___x_419_ = lean_nat_add(v_i_389_, v___x_418_);
lean_dec(v_i_389_);
v___x_420_ = lean_unbox(v_snd_415_);
lean_dec(v_snd_415_);
v_typeNew_385_ = v___x_416_;
v_alts_387_ = v___x_417_;
v_refined_388_ = v___x_420_;
v_i_389_ = v___x_419_;
goto _start;
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec_ref(v_body_403_);
lean_dec(v_i_389_);
lean_dec_ref(v_alts_387_);
lean_dec_ref(v_unrefinedArgType_384_);
v_a_422_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_412_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_412_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
else
{
lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec(v_a_401_);
lean_dec(v_i_389_);
lean_dec_ref(v_alts_387_);
lean_dec_ref(v_unrefinedArgType_384_);
v___x_430_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3);
v___x_431_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_430_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
return v___x_431_;
}
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
lean_dec(v_i_389_);
lean_dec_ref(v_alts_387_);
lean_dec_ref(v_unrefinedArgType_384_);
v_a_432_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v___x_400_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_400_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___boxed(lean_object* v_unrefinedArgType_440_, lean_object* v_typeNew_441_, lean_object* v_altNumParams_442_, lean_object* v_alts_443_, lean_object* v_refined_444_, lean_object* v_i_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
uint8_t v_refined_boxed_451_; lean_object* v_res_452_; 
v_refined_boxed_451_ = lean_unbox(v_refined_444_);
v_res_452_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(v_unrefinedArgType_440_, v_typeNew_441_, v_altNumParams_442_, v_alts_443_, v_refined_boxed_451_, v_i_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
lean_dec(v_a_447_);
lean_dec_ref(v_a_446_);
lean_dec_ref(v_altNumParams_442_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0(lean_object* v_00_u03b1_453_, lean_object* v_msg_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v_msg_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___boxed(lean_object* v_00_u03b1_461_, lean_object* v_msg_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0(v_00_u03b1_461_, v_msg_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(lean_object* v_e_469_, lean_object* v_k_470_, uint8_t v_cleanupAnnotations_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v___f_477_; uint8_t v___x_478_; uint8_t v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___f_477_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_477_, 0, v_k_470_);
v___x_478_ = 1;
v___x_479_ = 0;
v___x_480_ = lean_box(0);
v___x_481_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_469_, v___x_478_, v___x_479_, v___x_478_, v___x_479_, v___x_480_, v___f_477_, v_cleanupAnnotations_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_481_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_481_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
v_a_490_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_481_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_481_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg___boxed(lean_object* v_e_498_, lean_object* v_k_499_, lean_object* v_cleanupAnnotations_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_506_; lean_object* v_res_507_; 
v_cleanupAnnotations_boxed_506_ = lean_unbox(v_cleanupAnnotations_500_);
v_res_507_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_e_498_, v_k_499_, v_cleanupAnnotations_boxed_506_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1(lean_object* v_00_u03b1_508_, lean_object* v_e_509_, lean_object* v_k_510_, uint8_t v_cleanupAnnotations_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_e_509_, v_k_510_, v_cleanupAnnotations_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___boxed(lean_object* v_00_u03b1_518_, lean_object* v_e_519_, lean_object* v_k_520_, lean_object* v_cleanupAnnotations_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_527_; lean_object* v_res_528_; 
v_cleanupAnnotations_boxed_527_ = lean_unbox(v_cleanupAnnotations_521_);
v_res_528_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1(v_00_u03b1_518_, v_e_519_, v_k_520_, v_cleanupAnnotations_boxed_527_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(lean_object* v___x_529_, lean_object* v_motiveArgs_530_, lean_object* v_x_531_, lean_object* v_x_532_){
_start:
{
lean_object* v_zero_533_; uint8_t v_isZero_534_; 
v_zero_533_ = lean_unsigned_to_nat(0u);
v_isZero_534_ = lean_nat_dec_eq(v_x_531_, v_zero_533_);
if (v_isZero_534_ == 1)
{
lean_dec(v_x_531_);
return v_x_532_;
}
else
{
lean_object* v_one_535_; lean_object* v_n_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v_one_535_ = lean_unsigned_to_nat(1u);
v_n_536_ = lean_nat_sub(v_x_531_, v_one_535_);
lean_dec(v_x_531_);
v___x_537_ = lean_array_fget_borrowed(v___x_529_, v_n_536_);
v___x_538_ = l_Lean_Expr_isFVar(v___x_537_);
if (v___x_538_ == 0)
{
v_x_531_ = v_n_536_;
goto _start;
}
else
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_540_ = l_Lean_instInhabitedExpr;
v___x_541_ = lean_array_get_borrowed(v___x_540_, v_motiveArgs_530_, v_n_536_);
lean_inc(v___x_537_);
v___x_542_ = l_Lean_Expr_replaceFVar(v_x_532_, v___x_537_, v___x_541_);
lean_dec_ref(v_x_532_);
v_x_531_ = v_n_536_;
v_x_532_ = v___x_542_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0___boxed(lean_object* v___x_544_, lean_object* v_motiveArgs_545_, lean_object* v_x_546_, lean_object* v_x_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(v___x_544_, v_motiveArgs_545_, v_x_546_, v_x_547_);
lean_dec_ref(v_motiveArgs_545_);
lean_dec_ref(v___x_544_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(lean_object* v___x_549_, lean_object* v_motiveArgs_550_, lean_object* v_x_551_, lean_object* v_x_552_){
_start:
{
lean_object* v_zero_553_; uint8_t v_isZero_554_; 
v_zero_553_ = lean_unsigned_to_nat(0u);
v_isZero_554_ = lean_nat_dec_eq(v_x_551_, v_zero_553_);
if (v_isZero_554_ == 1)
{
return v_x_552_;
}
else
{
lean_object* v_one_555_; lean_object* v_n_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_one_555_ = lean_unsigned_to_nat(1u);
v_n_556_ = lean_nat_sub(v_x_551_, v_one_555_);
v___x_557_ = lean_array_fget_borrowed(v___x_549_, v_n_556_);
v___x_558_ = l_Lean_Expr_isFVar(v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; 
v___x_559_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(v___x_549_, v_motiveArgs_550_, v_n_556_, v_x_552_);
return v___x_559_;
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_560_ = l_Lean_instInhabitedExpr;
v___x_561_ = lean_array_get_borrowed(v___x_560_, v_motiveArgs_550_, v_n_556_);
lean_inc(v___x_557_);
v___x_562_ = l_Lean_Expr_replaceFVar(v_x_552_, v___x_557_, v___x_561_);
lean_dec_ref(v_x_552_);
v___x_563_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(v___x_549_, v_motiveArgs_550_, v_n_556_, v___x_562_);
return v___x_563_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0___boxed(lean_object* v___x_564_, lean_object* v_motiveArgs_565_, lean_object* v_x_566_, lean_object* v_x_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(v___x_564_, v_motiveArgs_565_, v_x_566_, v_x_567_);
lean_dec(v_x_566_);
lean_dec_ref(v_motiveArgs_565_);
lean_dec_ref(v___x_564_);
return v_res_568_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__0));
v___x_571_ = l_Lean_stringToMessageData(v___x_570_);
return v___x_571_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__2));
v___x_574_ = l_Lean_stringToMessageData(v___x_573_);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = ((lean_object*)(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4));
v___x_577_ = l_Lean_stringToMessageData(v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0(lean_object* v_matcherApp_578_, lean_object* v_e_579_, lean_object* v_discrs_580_, lean_object* v_toMatcherInfo_581_, lean_object* v_remaining_582_, lean_object* v_matcherName_583_, lean_object* v_alts_584_, lean_object* v_params_585_, lean_object* v_matcherLevels_586_, lean_object* v_motiveArgs_587_, lean_object* v_motiveBody_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; uint8_t v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v_matcherLevels_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_738_ = lean_array_get_size(v_motiveArgs_587_);
v___x_739_ = lean_array_get_size(v_discrs_580_);
v___x_740_ = lean_nat_dec_eq(v___x_738_, v___x_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec_ref(v_motiveBody_588_);
lean_dec_ref(v_matcherLevels_586_);
lean_dec_ref(v_params_585_);
lean_dec_ref(v_alts_584_);
lean_dec(v_matcherName_583_);
lean_dec_ref(v_toMatcherInfo_581_);
lean_dec_ref(v_discrs_580_);
lean_dec_ref(v_e_579_);
lean_dec_ref(v_matcherApp_578_);
v___x_741_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_742_ = l_Nat_reprFast(v___x_739_);
v___x_743_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
v___x_744_ = l_Lean_MessageData_ofFormat(v___x_743_);
v___x_745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_741_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_747_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
v_a_749_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_748_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_748_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
else
{
v___y_698_ = v___y_589_;
v___y_699_ = v___y_590_;
v___y_700_ = v___y_591_;
v___y_701_ = v___y_592_;
goto v___jp_697_;
}
v___jp_594_:
{
lean_object* v___x_610_; 
lean_inc(v___y_609_);
lean_inc_ref(v___y_608_);
lean_inc(v___y_607_);
lean_inc_ref(v___y_606_);
v___x_610_ = lean_infer_type(v___y_599_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_a_611_);
lean_dec_ref_known(v___x_610_, 1);
v___x_612_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_578_);
v___x_613_ = lean_unsigned_to_nat(0u);
v___x_614_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(v___y_597_, v_a_611_, v___x_612_, v___y_598_, v___y_604_, v___x_613_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
lean_dec_ref(v___x_612_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_627_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_627_ == 0)
{
v___x_617_ = v___x_614_;
v_isShared_618_ = v_isSharedCheck_627_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_614_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_627_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_619_ = lean_unsigned_to_nat(1u);
v___x_620_ = lean_mk_empty_array_with_capacity(v___x_619_);
v___x_621_ = lean_array_push(v___x_620_, v_e_579_);
v___x_622_ = l_Array_append___redArg(v___x_621_, v___y_595_);
v___x_623_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_623_, 0, v___y_602_);
lean_ctor_set(v___x_623_, 1, v___y_596_);
lean_ctor_set(v___x_623_, 2, v___y_601_);
lean_ctor_set(v___x_623_, 3, v___y_600_);
lean_ctor_set(v___x_623_, 4, v___y_605_);
lean_ctor_set(v___x_623_, 5, v___y_603_);
lean_ctor_set(v___x_623_, 6, v_a_615_);
lean_ctor_set(v___x_623_, 7, v___x_622_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_623_);
v___x_625_ = v___x_617_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec_ref(v___y_605_);
lean_dec_ref(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_596_);
lean_dec_ref(v_e_579_);
v_a_628_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_614_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_614_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_dec_ref(v___y_605_);
lean_dec_ref(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec_ref(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec(v___y_596_);
lean_dec_ref(v_e_579_);
lean_dec_ref(v_matcherApp_578_);
v_a_636_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_610_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_610_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
v___jp_644_:
{
uint8_t v___x_658_; uint8_t v___x_659_; uint8_t v___x_660_; lean_object* v___x_661_; 
v___x_658_ = 0;
v___x_659_ = 1;
v___x_660_ = 1;
v___x_661_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_587_, v___y_652_, v___x_658_, v___x_659_, v___x_658_, v___x_659_, v___x_660_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc_n(v_a_662_, 2);
lean_dec_ref_known(v___x_661_, 1);
lean_inc_ref(v_matcherLevels_653_);
v___x_663_ = lean_array_to_list(v_matcherLevels_653_);
lean_inc(v___y_647_);
v___x_664_ = l_Lean_mkConst(v___y_647_, v___x_663_);
v___x_665_ = l_Lean_mkAppN(v___x_664_, v___y_650_);
v___x_666_ = l_Lean_Expr_app___override(v___x_665_, v_a_662_);
v___x_667_ = l_Lean_mkAppN(v___x_666_, v___y_651_);
lean_inc_ref(v___x_667_);
v___x_668_ = l_Lean_Meta_isTypeCorrect(v___x_667_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; uint8_t v___x_670_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
v___x_670_ = lean_unbox(v_a_669_);
lean_dec(v_a_669_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
lean_dec_ref(v___x_667_);
lean_dec(v_a_662_);
lean_dec_ref(v_matcherLevels_653_);
lean_dec_ref(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec_ref(v_e_579_);
lean_dec_ref(v_matcherApp_578_);
v___x_671_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1);
v___x_672_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_671_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_672_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
else
{
v___y_595_ = v___y_645_;
v___y_596_ = v___y_647_;
v___y_597_ = v___y_646_;
v___y_598_ = v___y_648_;
v___y_599_ = v___x_667_;
v___y_600_ = v___y_650_;
v___y_601_ = v_matcherLevels_653_;
v___y_602_ = v___y_649_;
v___y_603_ = v___y_651_;
v___y_604_ = v___x_658_;
v___y_605_ = v_a_662_;
v___y_606_ = v___y_654_;
v___y_607_ = v___y_655_;
v___y_608_ = v___y_656_;
v___y_609_ = v___y_657_;
goto v___jp_594_;
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
lean_dec_ref(v___x_667_);
lean_dec(v_a_662_);
lean_dec_ref(v_matcherLevels_653_);
lean_dec_ref(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec_ref(v_e_579_);
lean_dec_ref(v_matcherApp_578_);
v_a_681_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_668_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_668_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec_ref(v_matcherLevels_653_);
lean_dec_ref(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec_ref(v_e_579_);
lean_dec_ref(v_matcherApp_578_);
v_a_689_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_661_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_661_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
v___jp_697_:
{
lean_object* v___x_702_; 
lean_inc(v___y_701_);
lean_inc_ref(v___y_700_);
lean_inc(v___y_699_);
lean_inc_ref(v___y_698_);
lean_inc_ref(v_e_579_);
v___x_702_ = lean_infer_type(v_e_579_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc_n(v_a_703_, 2);
lean_dec_ref_known(v___x_702_, 1);
v___x_704_ = lean_array_get_size(v_discrs_580_);
v___x_705_ = l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(v_discrs_580_, v_motiveArgs_587_, v___x_704_, v_a_703_);
v___x_706_ = l_Lean_mkArrow(v___x_705_, v_motiveBody_588_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_uElimPos_x3f_707_; 
v_uElimPos_x3f_707_ = lean_ctor_get(v_toMatcherInfo_581_, 3);
if (lean_obj_tag(v_uElimPos_x3f_707_) == 0)
{
lean_object* v_a_708_; 
v_a_708_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_708_);
lean_dec_ref_known(v___x_706_, 1);
v___y_645_ = v_remaining_582_;
v___y_646_ = v_a_703_;
v___y_647_ = v_matcherName_583_;
v___y_648_ = v_alts_584_;
v___y_649_ = v_toMatcherInfo_581_;
v___y_650_ = v_params_585_;
v___y_651_ = v_discrs_580_;
v___y_652_ = v_a_708_;
v_matcherLevels_653_ = v_matcherLevels_586_;
v___y_654_ = v___y_698_;
v___y_655_ = v___y_699_;
v___y_656_ = v___y_700_;
v___y_657_ = v___y_701_;
goto v___jp_644_;
}
else
{
lean_object* v_a_709_; lean_object* v_val_710_; lean_object* v___x_711_; 
v_a_709_ = lean_ctor_get(v___x_706_, 0);
lean_inc_n(v_a_709_, 2);
lean_dec_ref_known(v___x_706_, 1);
v_val_710_ = lean_ctor_get(v_uElimPos_x3f_707_, 0);
v___x_711_ = l_Lean_Meta_getLevel(v_a_709_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___x_713_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref_known(v___x_711_, 1);
v___x_713_ = lean_array_set(v_matcherLevels_586_, v_val_710_, v_a_712_);
v___y_645_ = v_remaining_582_;
v___y_646_ = v_a_703_;
v___y_647_ = v_matcherName_583_;
v___y_648_ = v_alts_584_;
v___y_649_ = v_toMatcherInfo_581_;
v___y_650_ = v_params_585_;
v___y_651_ = v_discrs_580_;
v___y_652_ = v_a_709_;
v_matcherLevels_653_ = v___x_713_;
v___y_654_ = v___y_698_;
v___y_655_ = v___y_699_;
v___y_656_ = v___y_700_;
v___y_657_ = v___y_701_;
goto v___jp_644_;
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec(v_a_709_);
lean_dec(v_a_703_);
lean_dec_ref(v_matcherLevels_586_);
lean_dec_ref(v_params_585_);
lean_dec_ref(v_alts_584_);
lean_dec(v_matcherName_583_);
lean_dec_ref(v_toMatcherInfo_581_);
lean_dec_ref(v_discrs_580_);
lean_dec_ref(v_e_579_);
lean_dec_ref(v_matcherApp_578_);
v_a_714_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_711_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_711_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec(v_a_703_);
lean_dec_ref(v_matcherLevels_586_);
lean_dec_ref(v_params_585_);
lean_dec_ref(v_alts_584_);
lean_dec(v_matcherName_583_);
lean_dec_ref(v_toMatcherInfo_581_);
lean_dec_ref(v_discrs_580_);
lean_dec_ref(v_e_579_);
lean_dec_ref(v_matcherApp_578_);
v_a_722_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_706_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_706_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
lean_dec_ref(v_motiveBody_588_);
lean_dec_ref(v_matcherLevels_586_);
lean_dec_ref(v_params_585_);
lean_dec_ref(v_alts_584_);
lean_dec(v_matcherName_583_);
lean_dec_ref(v_toMatcherInfo_581_);
lean_dec_ref(v_discrs_580_);
lean_dec_ref(v_e_579_);
lean_dec_ref(v_matcherApp_578_);
v_a_730_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_702_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_702_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___boxed(lean_object* v_matcherApp_757_, lean_object* v_e_758_, lean_object* v_discrs_759_, lean_object* v_toMatcherInfo_760_, lean_object* v_remaining_761_, lean_object* v_matcherName_762_, lean_object* v_alts_763_, lean_object* v_params_764_, lean_object* v_matcherLevels_765_, lean_object* v_motiveArgs_766_, lean_object* v_motiveBody_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_Meta_MatcherApp_addArg___lam__0(v_matcherApp_757_, v_e_758_, v_discrs_759_, v_toMatcherInfo_760_, v_remaining_761_, v_matcherName_762_, v_alts_763_, v_params_764_, v_matcherLevels_765_, v_motiveArgs_766_, v_motiveBody_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec_ref(v_motiveArgs_766_);
lean_dec_ref(v_remaining_761_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg(lean_object* v_matcherApp_774_, lean_object* v_e_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_toMatcherInfo_781_; lean_object* v_matcherName_782_; lean_object* v_matcherLevels_783_; lean_object* v_params_784_; lean_object* v_motive_785_; lean_object* v_discrs_786_; lean_object* v_alts_787_; lean_object* v_remaining_788_; lean_object* v___f_789_; uint8_t v___x_790_; lean_object* v___x_791_; 
v_toMatcherInfo_781_ = lean_ctor_get(v_matcherApp_774_, 0);
lean_inc_ref(v_toMatcherInfo_781_);
v_matcherName_782_ = lean_ctor_get(v_matcherApp_774_, 1);
lean_inc(v_matcherName_782_);
v_matcherLevels_783_ = lean_ctor_get(v_matcherApp_774_, 2);
lean_inc_ref(v_matcherLevels_783_);
v_params_784_ = lean_ctor_get(v_matcherApp_774_, 3);
lean_inc_ref(v_params_784_);
v_motive_785_ = lean_ctor_get(v_matcherApp_774_, 4);
lean_inc_ref(v_motive_785_);
v_discrs_786_ = lean_ctor_get(v_matcherApp_774_, 5);
lean_inc_ref(v_discrs_786_);
v_alts_787_ = lean_ctor_get(v_matcherApp_774_, 6);
lean_inc_ref(v_alts_787_);
v_remaining_788_ = lean_ctor_get(v_matcherApp_774_, 7);
lean_inc_ref(v_remaining_788_);
v___f_789_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_addArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_789_, 0, v_matcherApp_774_);
lean_closure_set(v___f_789_, 1, v_e_775_);
lean_closure_set(v___f_789_, 2, v_discrs_786_);
lean_closure_set(v___f_789_, 3, v_toMatcherInfo_781_);
lean_closure_set(v___f_789_, 4, v_remaining_788_);
lean_closure_set(v___f_789_, 5, v_matcherName_782_);
lean_closure_set(v___f_789_, 6, v_alts_787_);
lean_closure_set(v___f_789_, 7, v_params_784_);
lean_closure_set(v___f_789_, 8, v_matcherLevels_783_);
v___x_790_ = 0;
v___x_791_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_785_, v___f_789_, v___x_790_, v_a_776_, v_a_777_, v_a_778_, v_a_779_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___boxed(lean_object* v_matcherApp_792_, lean_object* v_e_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Lean_Meta_MatcherApp_addArg(v_matcherApp_792_, v_e_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg_x3f(lean_object* v_matcherApp_800_, lean_object* v_e_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_Meta_MatcherApp_addArg(v_matcherApp_800_, v_e_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_816_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_816_ == 0)
{
v___x_810_ = v___x_807_;
v_isShared_811_ = v_isSharedCheck_816_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_807_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_816_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_812_; lean_object* v___x_814_; 
v___x_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_812_, 0, v_a_808_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_812_);
v___x_814_ = v___x_810_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_812_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_832_; 
v_a_817_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_832_ == 0)
{
v___x_819_ = v___x_807_;
v_isShared_820_ = v_isSharedCheck_832_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_807_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_832_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
uint8_t v___y_822_; uint8_t v___x_830_; 
v___x_830_ = l_Lean_Exception_isInterrupt(v_a_817_);
if (v___x_830_ == 0)
{
uint8_t v___x_831_; 
lean_inc(v_a_817_);
v___x_831_ = l_Lean_Exception_isRuntime(v_a_817_);
v___y_822_ = v___x_831_;
goto v___jp_821_;
}
else
{
v___y_822_ = v___x_830_;
goto v___jp_821_;
}
v___jp_821_:
{
if (v___y_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___x_825_; 
lean_dec(v_a_817_);
v___x_823_ = lean_box(0);
if (v_isShared_820_ == 0)
{
lean_ctor_set_tag(v___x_819_, 0);
lean_ctor_set(v___x_819_, 0, v___x_823_);
v___x_825_ = v___x_819_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
else
{
lean_object* v___x_828_; 
if (v_isShared_820_ == 0)
{
v___x_828_ = v___x_819_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_817_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg_x3f___boxed(lean_object* v_matcherApp_833_, lean_object* v_e_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_matcherApp_833_, v_e_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_);
lean_dec(v_a_838_);
lean_dec_ref(v_a_837_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg(lean_object* v_type_841_, lean_object* v_k_842_, uint8_t v_cleanupAnnotations_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___f_849_; uint8_t v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___f_849_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg___boxed(lean_object* v_type_869_, lean_object* v_k_870_, lean_object* v_cleanupAnnotations_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_877_; lean_object* v_res_878_; 
v_cleanupAnnotations_boxed_877_ = lean_unbox(v_cleanupAnnotations_871_);
v_res_878_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg(v_type_869_, v_k_870_, v_cleanupAnnotations_boxed_877_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3(lean_object* v_00_u03b1_879_, lean_object* v_type_880_, lean_object* v_k_881_, uint8_t v_cleanupAnnotations_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg(v_type_880_, v_k_881_, v_cleanupAnnotations_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___boxed(lean_object* v_00_u03b1_889_, lean_object* v_type_890_, lean_object* v_k_891_, lean_object* v_cleanupAnnotations_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_898_; lean_object* v_res_899_; 
v_cleanupAnnotations_boxed_898_ = lean_unbox(v_cleanupAnnotations_892_);
v_res_899_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3(v_00_u03b1_889_, v_type_890_, v_k_891_, v_cleanupAnnotations_boxed_898_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__1(size_t v_sz_900_, size_t v_i_901_, lean_object* v_bs_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
uint8_t v___x_908_; 
v___x_908_ = lean_usize_dec_lt(v_i_901_, v_sz_900_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; 
v___x_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_909_, 0, v_bs_902_);
return v___x_909_;
}
else
{
lean_object* v_v_910_; lean_object* v___x_911_; 
v_v_910_ = lean_array_uget_borrowed(v_bs_902_, v_i_901_);
lean_inc(v___y_906_);
lean_inc_ref(v___y_905_);
lean_inc(v___y_904_);
lean_inc_ref(v___y_903_);
lean_inc(v_v_910_);
v___x_911_ = lean_infer_type(v_v_910_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_913_; lean_object* v_bs_x27_914_; size_t v___x_915_; size_t v___x_916_; lean_object* v___x_917_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref_known(v___x_911_, 1);
v___x_913_ = lean_unsigned_to_nat(0u);
v_bs_x27_914_ = lean_array_uset(v_bs_902_, v_i_901_, v___x_913_);
v___x_915_ = ((size_t)1ULL);
v___x_916_ = lean_usize_add(v_i_901_, v___x_915_);
v___x_917_ = lean_array_uset(v_bs_x27_914_, v_i_901_, v_a_912_);
v_i_901_ = v___x_916_;
v_bs_902_ = v___x_917_;
goto _start;
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
lean_dec_ref(v_bs_902_);
v_a_919_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_911_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_911_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___boxed(lean_object* v_sz_927_, lean_object* v_i_928_, lean_object* v_bs_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
size_t v_sz_boxed_935_; size_t v_i_boxed_936_; lean_object* v_res_937_; 
v_sz_boxed_935_ = lean_unbox_usize(v_sz_927_);
lean_dec(v_sz_927_);
v_i_boxed_936_ = lean_unbox_usize(v_i_928_);
lean_dec(v_i_928_);
v_res_937_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__1(v_sz_boxed_935_, v_i_boxed_936_, v_bs_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
return v_res_937_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__1(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = ((lean_object*)(l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__0));
v___x_940_ = l_Lean_stringToMessageData(v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0(uint8_t v___x_941_, uint8_t v___x_942_, uint8_t v___x_943_, lean_object* v_a_944_, lean_object* v_fvs_945_, lean_object* v_body_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v___x_960_; uint8_t v___x_961_; 
v___x_960_ = lean_array_get_size(v_fvs_945_);
v___x_961_ = lean_nat_dec_eq(v___x_960_, v_a_944_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
v___x_962_ = lean_obj_once(&l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__1, &l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__1);
v___x_963_ = l_Nat_reprFast(v_a_944_);
v___x_964_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
v___x_965_ = l_Lean_MessageData_ofFormat(v___x_964_);
v___x_966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_962_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_968_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
v_a_970_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
else
{
lean_dec(v_a_944_);
goto v___jp_952_;
}
v___jp_952_:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_953_ = lean_unsigned_to_nat(2u);
v___x_954_ = l_Lean_Expr_getAppNumArgs(v_body_946_);
v___x_955_ = lean_nat_sub(v___x_954_, v___x_953_);
lean_dec(v___x_954_);
v___x_956_ = lean_unsigned_to_nat(1u);
v___x_957_ = lean_nat_sub(v___x_955_, v___x_956_);
lean_dec(v___x_955_);
v___x_958_ = l_Lean_Expr_getRevArg_x21(v_body_946_, v___x_957_);
v___x_959_ = l_Lean_Meta_mkLambdaFVars(v_fvs_945_, v___x_958_, v___x_941_, v___x_942_, v___x_941_, v___x_942_, v___x_943_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
return v___x_959_;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___boxed(lean_object* v___x_978_, lean_object* v___x_979_, lean_object* v___x_980_, lean_object* v_a_981_, lean_object* v_fvs_982_, lean_object* v_body_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
uint8_t v___x_3800__boxed_989_; uint8_t v___x_3801__boxed_990_; uint8_t v___x_3802__boxed_991_; lean_object* v_res_992_; 
v___x_3800__boxed_989_ = lean_unbox(v___x_978_);
v___x_3801__boxed_990_ = lean_unbox(v___x_979_);
v___x_3802__boxed_991_ = lean_unbox(v___x_980_);
v_res_992_ = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0(v___x_3800__boxed_989_, v___x_3801__boxed_990_, v___x_3802__boxed_991_, v_a_981_, v_fvs_982_, v_body_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec_ref(v_body_983_);
lean_dec_ref(v_fvs_982_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(lean_object* v_as_993_, lean_object* v_bs_994_, lean_object* v_i_995_, lean_object* v_cs_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v___x_1002_; uint8_t v___x_1003_; 
v___x_1002_ = lean_array_get_size(v_as_993_);
v___x_1003_ = lean_nat_dec_lt(v_i_995_, v___x_1002_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; 
lean_dec(v_i_995_);
v___x_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1004_, 0, v_cs_996_);
return v___x_1004_;
}
else
{
lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1005_ = lean_array_get_size(v_bs_994_);
v___x_1006_ = lean_nat_dec_lt(v_i_995_, v___x_1005_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; 
lean_dec(v_i_995_);
v___x_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1007_, 0, v_cs_996_);
return v___x_1007_;
}
else
{
uint8_t v___x_1008_; uint8_t v___x_1009_; lean_object* v_a_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___f_1014_; lean_object* v_b_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1008_ = 0;
v___x_1009_ = 1;
v_a_1010_ = lean_array_fget_borrowed(v_as_993_, v_i_995_);
v___x_1011_ = lean_box(v___x_1008_);
v___x_1012_ = lean_box(v___x_1006_);
v___x_1013_ = lean_box(v___x_1009_);
lean_inc_n(v_a_1010_, 2);
v___f_1014_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1014_, 0, v___x_1011_);
lean_closure_set(v___f_1014_, 1, v___x_1012_);
lean_closure_set(v___f_1014_, 2, v___x_1013_);
lean_closure_set(v___f_1014_, 3, v_a_1010_);
v_b_1015_ = lean_array_fget_borrowed(v_bs_994_, v_i_995_);
v___x_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1016_, 0, v_a_1010_);
lean_inc(v_b_1015_);
v___x_1017_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_b_1015_, v___x_1016_, v___f_1014_, v___x_1008_, v___x_1008_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref_known(v___x_1017_, 1);
v___x_1019_ = lean_unsigned_to_nat(1u);
v___x_1020_ = lean_nat_add(v_i_995_, v___x_1019_);
lean_dec(v_i_995_);
v___x_1021_ = lean_array_push(v_cs_996_, v_a_1018_);
v_i_995_ = v___x_1020_;
v_cs_996_ = v___x_1021_;
goto _start;
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec_ref(v_cs_996_);
lean_dec(v_i_995_);
v_a_1023_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1017_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1017_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___boxed(lean_object* v_as_1031_, lean_object* v_bs_1032_, lean_object* v_i_1033_, lean_object* v_cs_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(v_as_1031_, v_bs_1032_, v_i_1033_, v_cs_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec_ref(v_bs_1032_);
lean_dec_ref(v_as_1031_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0(lean_object* v_matcherApp_1043_, lean_object* v_altAuxs_1044_, lean_object* v_x_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
size_t v_sz_1051_; size_t v___x_1052_; lean_object* v___x_1053_; 
v_sz_1051_ = lean_array_size(v_altAuxs_1044_);
v___x_1052_ = ((size_t)0ULL);
v___x_1053_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__1(v_sz_1051_, v___x_1052_, v_altAuxs_1044_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1054_);
lean_dec_ref_known(v___x_1053_, 1);
v___x_1055_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_1043_);
v___x_1056_ = lean_unsigned_to_nat(0u);
v___x_1057_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_1058_ = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(v___x_1055_, v_a_1054_, v___x_1056_, v___x_1057_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v_a_1054_);
lean_dec_ref(v___x_1055_);
return v___x_1058_;
}
else
{
lean_dec_ref(v_matcherApp_1043_);
return v___x_1053_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0___boxed(lean_object* v_matcherApp_1059_, lean_object* v_altAuxs_1060_, lean_object* v_x_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_Meta_MatcherApp_refineThrough___lam__0(v_matcherApp_1059_, v_altAuxs_1060_, v_x_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec_ref(v_x_1061_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(lean_object* v___x_1068_, lean_object* v_motiveArgs_1069_, lean_object* v_i_1070_, lean_object* v_a_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_zero_1077_; uint8_t v_isZero_1078_; 
v_zero_1077_ = lean_unsigned_to_nat(0u);
v_isZero_1078_ = lean_nat_dec_eq(v_i_1070_, v_zero_1077_);
if (v_isZero_1078_ == 1)
{
lean_object* v___x_1079_; 
lean_dec(v_i_1070_);
v___x_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1079_, 0, v_a_1071_);
return v___x_1079_;
}
else
{
lean_object* v_one_1080_; lean_object* v_n_1081_; lean_object* v_discr_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v_one_1080_ = lean_unsigned_to_nat(1u);
v_n_1081_ = lean_nat_sub(v_i_1070_, v_one_1080_);
lean_dec(v_i_1070_);
v_discr_1082_ = lean_array_fget_borrowed(v___x_1068_, v_n_1081_);
v___x_1083_ = lean_box(0);
lean_inc(v_discr_1082_);
v___x_1084_ = l_Lean_Meta_kabstract(v_a_1071_, v_discr_1082_, v___x_1083_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1086_; lean_object* v_motiveArg_1087_; lean_object* v___x_1088_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1084_, 1);
v___x_1086_ = l_Lean_instInhabitedExpr;
v_motiveArg_1087_ = lean_array_get_borrowed(v___x_1086_, v_motiveArgs_1069_, v_n_1081_);
v___x_1088_ = lean_expr_instantiate1(v_a_1085_, v_motiveArg_1087_);
lean_dec(v_a_1085_);
v_i_1070_ = v_n_1081_;
v_a_1071_ = v___x_1088_;
goto _start;
}
else
{
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1090_; 
v_a_1090_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1090_);
lean_dec_ref_known(v___x_1084_, 1);
v_i_1070_ = v_n_1081_;
v_a_1071_ = v_a_1090_;
goto _start;
}
else
{
lean_dec(v_n_1081_);
return v___x_1084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg___boxed(lean_object* v___x_1092_, lean_object* v_motiveArgs_1093_, lean_object* v_i_1094_, lean_object* v_a_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(v___x_1092_, v_motiveArgs_1093_, v_i_1094_, v_a_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec_ref(v_motiveArgs_1093_);
lean_dec_ref(v___x_1092_);
return v_res_1101_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__0));
v___x_1104_ = l_Lean_stringToMessageData(v___x_1103_);
return v___x_1104_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__2));
v___x_1107_ = l_Lean_stringToMessageData(v___x_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1(lean_object* v___f_1108_, lean_object* v_discrs_1109_, lean_object* v_e_1110_, lean_object* v_toMatcherInfo_1111_, lean_object* v_params_1112_, lean_object* v_matcherName_1113_, lean_object* v_matcherLevels_1114_, lean_object* v_motiveArgs_1115_, lean_object* v___motiveBody_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v___y_1123_; lean_object* v___y_1124_; uint8_t v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v_matcherLevels_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___x_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1221_ = lean_array_get_size(v_motiveArgs_1115_);
v___x_1222_ = lean_array_get_size(v_discrs_1109_);
v___x_1223_ = lean_nat_dec_eq(v___x_1221_, v___x_1222_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec_ref(v_matcherLevels_1114_);
lean_dec(v_matcherName_1113_);
lean_dec_ref(v_e_1110_);
lean_dec_ref(v___f_1108_);
v___x_1224_ = lean_obj_once(&l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3, &l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3_once, _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3);
v___x_1225_ = l_Nat_reprFast(v___x_1222_);
v___x_1226_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
v___x_1227_ = l_Lean_MessageData_ofFormat(v___x_1226_);
v___x_1228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1224_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_1230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1228_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
v___x_1231_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_1230_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1231_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1231_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
else
{
v___y_1191_ = v___y_1117_;
v___y_1192_ = v___y_1118_;
v___y_1193_ = v___y_1119_;
v___y_1194_ = v___y_1120_;
goto v___jp_1190_;
}
v___jp_1122_:
{
lean_object* v___x_1130_; 
lean_inc(v___y_1129_);
lean_inc_ref(v___y_1128_);
lean_inc(v___y_1127_);
lean_inc_ref(v___y_1126_);
v___x_1130_ = lean_infer_type(v___y_1124_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1132_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1131_);
lean_dec_ref_known(v___x_1130_, 1);
v___x_1132_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg(v_a_1131_, v___y_1123_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
return v___x_1132_;
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec_ref(v___y_1123_);
v_a_1133_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1130_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1130_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
v___jp_1141_:
{
uint8_t v___x_1151_; uint8_t v___x_1152_; uint8_t v___x_1153_; lean_object* v___x_1154_; 
v___x_1151_ = 0;
v___x_1152_ = 1;
v___x_1153_ = 1;
v___x_1154_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_1115_, v___y_1144_, v___x_1151_, v___x_1152_, v___x_1151_, v___x_1152_, v___x_1153_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_a_1155_);
lean_dec_ref_known(v___x_1154_, 1);
v___x_1156_ = lean_array_to_list(v_matcherLevels_1146_);
v___x_1157_ = l_Lean_mkConst(v___y_1143_, v___x_1156_);
v___x_1158_ = l_Lean_mkAppN(v___x_1157_, v___y_1142_);
v___x_1159_ = l_Lean_Expr_app___override(v___x_1158_, v_a_1155_);
v___x_1160_ = l_Lean_mkAppN(v___x_1159_, v___y_1145_);
lean_inc_ref(v___x_1160_);
v___x_1161_ = l_Lean_Meta_isTypeCorrect(v___x_1160_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; uint8_t v___x_1163_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1162_);
lean_dec_ref_known(v___x_1161_, 1);
v___x_1163_ = lean_unbox(v_a_1162_);
lean_dec(v_a_1162_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
lean_dec_ref(v___x_1160_);
lean_dec_ref(v___f_1108_);
v___x_1164_ = lean_obj_once(&l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1, &l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1_once, _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1);
v___x_1165_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_1164_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1165_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1165_);
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
else
{
v___y_1123_ = v___f_1108_;
v___y_1124_ = v___x_1160_;
v___y_1125_ = v___x_1151_;
v___y_1126_ = v___y_1147_;
v___y_1127_ = v___y_1148_;
v___y_1128_ = v___y_1149_;
v___y_1129_ = v___y_1150_;
goto v___jp_1122_;
}
}
else
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
lean_dec_ref(v___x_1160_);
lean_dec_ref(v___f_1108_);
v_a_1174_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_1161_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1161_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
else
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
lean_dec_ref(v_matcherLevels_1146_);
lean_dec(v___y_1143_);
lean_dec_ref(v___f_1108_);
v_a_1182_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1154_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1154_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
v___jp_1190_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = lean_array_get_size(v_discrs_1109_);
v___x_1196_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(v_discrs_1109_, v_motiveArgs_1115_, v___x_1195_, v_e_1110_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; lean_object* v___x_1198_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc_n(v_a_1197_, 2);
lean_dec_ref_known(v___x_1196_, 1);
v___x_1198_ = l_Lean_Meta_mkEq(v_a_1197_, v_a_1197_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_uElimPos_x3f_1199_; 
v_uElimPos_x3f_1199_ = lean_ctor_get(v_toMatcherInfo_1111_, 3);
if (lean_obj_tag(v_uElimPos_x3f_1199_) == 0)
{
lean_object* v_a_1200_; 
v_a_1200_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1200_);
lean_dec_ref_known(v___x_1198_, 1);
v___y_1142_ = v_params_1112_;
v___y_1143_ = v_matcherName_1113_;
v___y_1144_ = v_a_1200_;
v___y_1145_ = v_discrs_1109_;
v_matcherLevels_1146_ = v_matcherLevels_1114_;
v___y_1147_ = v___y_1191_;
v___y_1148_ = v___y_1192_;
v___y_1149_ = v___y_1193_;
v___y_1150_ = v___y_1194_;
goto v___jp_1141_;
}
else
{
lean_object* v_a_1201_; lean_object* v_val_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v_a_1201_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1201_);
lean_dec_ref_known(v___x_1198_, 1);
v_val_1202_ = lean_ctor_get(v_uElimPos_x3f_1199_, 0);
v___x_1203_ = lean_box(0);
v___x_1204_ = lean_array_set(v_matcherLevels_1114_, v_val_1202_, v___x_1203_);
v___y_1142_ = v_params_1112_;
v___y_1143_ = v_matcherName_1113_;
v___y_1144_ = v_a_1201_;
v___y_1145_ = v_discrs_1109_;
v_matcherLevels_1146_ = v___x_1204_;
v___y_1147_ = v___y_1191_;
v___y_1148_ = v___y_1192_;
v___y_1149_ = v___y_1193_;
v___y_1150_ = v___y_1194_;
goto v___jp_1141_;
}
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_dec_ref(v_matcherLevels_1114_);
lean_dec(v_matcherName_1113_);
lean_dec_ref(v___f_1108_);
v_a_1205_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1198_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1198_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_dec_ref(v_matcherLevels_1114_);
lean_dec(v_matcherName_1113_);
lean_dec_ref(v___f_1108_);
v_a_1213_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1196_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1196_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___boxed(lean_object* v___f_1240_, lean_object* v_discrs_1241_, lean_object* v_e_1242_, lean_object* v_toMatcherInfo_1243_, lean_object* v_params_1244_, lean_object* v_matcherName_1245_, lean_object* v_matcherLevels_1246_, lean_object* v_motiveArgs_1247_, lean_object* v___motiveBody_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_Meta_MatcherApp_refineThrough___lam__1(v___f_1240_, v_discrs_1241_, v_e_1242_, v_toMatcherInfo_1243_, v_params_1244_, v_matcherName_1245_, v_matcherLevels_1246_, v_motiveArgs_1247_, v___motiveBody_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec_ref(v___motiveBody_1248_);
lean_dec_ref(v_motiveArgs_1247_);
lean_dec_ref(v_params_1244_);
lean_dec_ref(v_toMatcherInfo_1243_);
lean_dec_ref(v_discrs_1241_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough(lean_object* v_matcherApp_1255_, lean_object* v_e_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v_toMatcherInfo_1262_; lean_object* v_matcherName_1263_; lean_object* v_matcherLevels_1264_; lean_object* v_params_1265_; lean_object* v_motive_1266_; lean_object* v_discrs_1267_; lean_object* v___f_1268_; lean_object* v___f_1269_; uint8_t v___x_1270_; lean_object* v___x_1271_; 
v_toMatcherInfo_1262_ = lean_ctor_get(v_matcherApp_1255_, 0);
lean_inc_ref(v_toMatcherInfo_1262_);
v_matcherName_1263_ = lean_ctor_get(v_matcherApp_1255_, 1);
lean_inc(v_matcherName_1263_);
v_matcherLevels_1264_ = lean_ctor_get(v_matcherApp_1255_, 2);
lean_inc_ref(v_matcherLevels_1264_);
v_params_1265_ = lean_ctor_get(v_matcherApp_1255_, 3);
lean_inc_ref(v_params_1265_);
v_motive_1266_ = lean_ctor_get(v_matcherApp_1255_, 4);
lean_inc_ref(v_motive_1266_);
v_discrs_1267_ = lean_ctor_get(v_matcherApp_1255_, 5);
lean_inc_ref(v_discrs_1267_);
v___f_1268_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1268_, 0, v_matcherApp_1255_);
v___f_1269_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1269_, 0, v___f_1268_);
lean_closure_set(v___f_1269_, 1, v_discrs_1267_);
lean_closure_set(v___f_1269_, 2, v_e_1256_);
lean_closure_set(v___f_1269_, 3, v_toMatcherInfo_1262_);
lean_closure_set(v___f_1269_, 4, v_params_1265_);
lean_closure_set(v___f_1269_, 5, v_matcherName_1263_);
lean_closure_set(v___f_1269_, 6, v_matcherLevels_1264_);
v___x_1270_ = 0;
v___x_1271_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_1266_, v___f_1269_, v___x_1270_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___boxed(lean_object* v_matcherApp_1272_, lean_object* v_e_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_Meta_MatcherApp_refineThrough(v_matcherApp_1272_, v_e_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0(lean_object* v___x_1280_, lean_object* v_motiveArgs_1281_, lean_object* v_n_1282_, lean_object* v_i_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(v___x_1280_, v_motiveArgs_1281_, v_i_1283_, v_a_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___boxed(lean_object* v___x_1292_, lean_object* v_motiveArgs_1293_, lean_object* v_n_1294_, lean_object* v_i_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0(v___x_1292_, v_motiveArgs_1293_, v_n_1294_, v_i_1295_, v_a_1296_, v_a_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v_n_1294_);
lean_dec_ref(v_motiveArgs_1293_);
lean_dec_ref(v___x_1292_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough_x3f(lean_object* v_matcherApp_1304_, lean_object* v_e_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Lean_Meta_MatcherApp_refineThrough(v_matcherApp_1304_, v_e_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1320_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1314_ = v___x_1311_;
v_isShared_1315_ = v_isSharedCheck_1320_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1311_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1320_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1316_; lean_object* v___x_1318_; 
v___x_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1316_, 0, v_a_1312_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v___x_1316_);
v___x_1318_ = v___x_1314_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1336_; 
v_a_1321_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1323_ = v___x_1311_;
v_isShared_1324_ = v_isSharedCheck_1336_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1311_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1336_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
uint8_t v___y_1326_; uint8_t v___x_1334_; 
v___x_1334_ = l_Lean_Exception_isInterrupt(v_a_1321_);
if (v___x_1334_ == 0)
{
uint8_t v___x_1335_; 
lean_inc(v_a_1321_);
v___x_1335_ = l_Lean_Exception_isRuntime(v_a_1321_);
v___y_1326_ = v___x_1335_;
goto v___jp_1325_;
}
else
{
v___y_1326_ = v___x_1334_;
goto v___jp_1325_;
}
v___jp_1325_:
{
if (v___y_1326_ == 0)
{
lean_object* v___x_1327_; lean_object* v___x_1329_; 
lean_dec(v_a_1321_);
v___x_1327_ = lean_box(0);
if (v_isShared_1324_ == 0)
{
lean_ctor_set_tag(v___x_1323_, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1327_);
v___x_1329_ = v___x_1323_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
else
{
lean_object* v___x_1332_; 
if (v_isShared_1324_ == 0)
{
v___x_1332_ = v___x_1323_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1321_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough_x3f___boxed(lean_object* v_matcherApp_1337_, lean_object* v_e_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_Meta_MatcherApp_refineThrough_x3f(v_matcherApp_1337_, v_e_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_);
lean_dec(v_a_1342_);
lean_dec_ref(v_a_1341_);
lean_dec(v_a_1340_);
lean_dec_ref(v_a_1339_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(lean_object* v_lctx_1345_, lean_object* v_x_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_keyedConfig_1352_; uint8_t v_trackZetaDelta_1353_; lean_object* v_zetaDeltaSet_1354_; lean_object* v_localInstances_1355_; lean_object* v_defEqCtx_x3f_1356_; lean_object* v_synthPendingDepth_1357_; lean_object* v_customCanUnfoldPredicate_x3f_1358_; uint8_t v_univApprox_1359_; uint8_t v_inTypeClassResolution_1360_; uint8_t v_cacheInferType_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v_keyedConfig_1352_ = lean_ctor_get(v___y_1347_, 0);
v_trackZetaDelta_1353_ = lean_ctor_get_uint8(v___y_1347_, sizeof(void*)*7);
v_zetaDeltaSet_1354_ = lean_ctor_get(v___y_1347_, 1);
v_localInstances_1355_ = lean_ctor_get(v___y_1347_, 3);
v_defEqCtx_x3f_1356_ = lean_ctor_get(v___y_1347_, 4);
v_synthPendingDepth_1357_ = lean_ctor_get(v___y_1347_, 5);
v_customCanUnfoldPredicate_x3f_1358_ = lean_ctor_get(v___y_1347_, 6);
v_univApprox_1359_ = lean_ctor_get_uint8(v___y_1347_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1360_ = lean_ctor_get_uint8(v___y_1347_, sizeof(void*)*7 + 2);
v_cacheInferType_1361_ = lean_ctor_get_uint8(v___y_1347_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_1358_);
lean_inc(v_synthPendingDepth_1357_);
lean_inc(v_defEqCtx_x3f_1356_);
lean_inc_ref(v_localInstances_1355_);
lean_inc(v_zetaDeltaSet_1354_);
lean_inc_ref(v_keyedConfig_1352_);
v___x_1362_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1362_, 0, v_keyedConfig_1352_);
lean_ctor_set(v___x_1362_, 1, v_zetaDeltaSet_1354_);
lean_ctor_set(v___x_1362_, 2, v_lctx_1345_);
lean_ctor_set(v___x_1362_, 3, v_localInstances_1355_);
lean_ctor_set(v___x_1362_, 4, v_defEqCtx_x3f_1356_);
lean_ctor_set(v___x_1362_, 5, v_synthPendingDepth_1357_);
lean_ctor_set(v___x_1362_, 6, v_customCanUnfoldPredicate_x3f_1358_);
lean_ctor_set_uint8(v___x_1362_, sizeof(void*)*7, v_trackZetaDelta_1353_);
lean_ctor_set_uint8(v___x_1362_, sizeof(void*)*7 + 1, v_univApprox_1359_);
lean_ctor_set_uint8(v___x_1362_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1360_);
lean_ctor_set_uint8(v___x_1362_, sizeof(void*)*7 + 3, v_cacheInferType_1361_);
lean_inc(v___y_1350_);
lean_inc_ref(v___y_1349_);
lean_inc(v___y_1348_);
v___x_1363_ = lean_apply_5(v_x_1346_, v___x_1362_, v___y_1348_, v___y_1349_, v___y_1350_, lean_box(0));
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg___boxed(lean_object* v_lctx_1364_, lean_object* v_x_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1364_, v_x_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(lean_object* v_00_u03b1_1372_, lean_object* v_lctx_1373_, lean_object* v_x_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1373_, v_x_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___boxed(lean_object* v_00_u03b1_1381_, lean_object* v_lctx_1382_, lean_object* v_x_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(v_00_u03b1_1381_, v_lctx_1382_, v_x_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(lean_object* v_as_1390_, size_t v_i_1391_, size_t v_stop_1392_, lean_object* v_b_1393_){
_start:
{
uint8_t v___x_1394_; 
v___x_1394_ = lean_usize_dec_eq(v_i_1391_, v_stop_1392_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; lean_object* v_fst_1396_; lean_object* v_snd_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; size_t v___x_1400_; size_t v___x_1401_; 
v___x_1395_ = lean_array_uget_borrowed(v_as_1390_, v_i_1391_);
v_fst_1396_ = lean_ctor_get(v___x_1395_, 0);
v_snd_1397_ = lean_ctor_get(v___x_1395_, 1);
v___x_1398_ = l_Lean_Expr_fvarId_x21(v_fst_1396_);
lean_inc(v_snd_1397_);
v___x_1399_ = l_Lean_LocalContext_setUserName(v_b_1393_, v___x_1398_, v_snd_1397_);
v___x_1400_ = ((size_t)1ULL);
v___x_1401_ = lean_usize_add(v_i_1391_, v___x_1400_);
v_i_1391_ = v___x_1401_;
v_b_1393_ = v___x_1399_;
goto _start;
}
else
{
return v_b_1393_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1___boxed(lean_object* v_as_1403_, lean_object* v_i_1404_, lean_object* v_stop_1405_, lean_object* v_b_1406_){
_start:
{
size_t v_i_boxed_1407_; size_t v_stop_boxed_1408_; lean_object* v_res_1409_; 
v_i_boxed_1407_ = lean_unbox_usize(v_i_1404_);
lean_dec(v_i_1404_);
v_stop_boxed_1408_ = lean_unbox_usize(v_stop_1405_);
lean_dec(v_stop_1405_);
v_res_1409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(v_as_1403_, v_i_boxed_1407_, v_stop_boxed_1408_, v_b_1406_);
lean_dec_ref(v_as_1403_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(lean_object* v_fvars_1410_, lean_object* v_names_1411_, lean_object* v_k_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v_lctx_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v_lctx_1418_ = lean_ctor_get(v_a_1413_, 2);
v___x_1419_ = l_Array_zip___redArg(v_fvars_1410_, v_names_1411_);
v___x_1420_ = lean_unsigned_to_nat(0u);
v___x_1421_ = lean_array_get_size(v___x_1419_);
v___x_1422_ = lean_nat_dec_lt(v___x_1420_, v___x_1421_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; 
lean_dec_ref(v___x_1419_);
lean_inc_ref(v_lctx_1418_);
v___x_1423_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1418_, v_k_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_);
return v___x_1423_;
}
else
{
uint8_t v___x_1424_; 
v___x_1424_ = lean_nat_dec_le(v___x_1421_, v___x_1421_);
if (v___x_1424_ == 0)
{
if (v___x_1422_ == 0)
{
lean_object* v___x_1425_; 
lean_dec_ref(v___x_1419_);
lean_inc_ref(v_lctx_1418_);
v___x_1425_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1418_, v_k_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_);
return v___x_1425_;
}
else
{
size_t v___x_1426_; size_t v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1426_ = ((size_t)0ULL);
v___x_1427_ = lean_usize_of_nat(v___x_1421_);
lean_inc_ref(v_lctx_1418_);
v___x_1428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(v___x_1419_, v___x_1426_, v___x_1427_, v_lctx_1418_);
lean_dec_ref(v___x_1419_);
v___x_1429_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v___x_1428_, v_k_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_);
return v___x_1429_;
}
}
else
{
size_t v___x_1430_; size_t v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1430_ = ((size_t)0ULL);
v___x_1431_ = lean_usize_of_nat(v___x_1421_);
lean_inc_ref(v_lctx_1418_);
v___x_1432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(v___x_1419_, v___x_1430_, v___x_1431_, v_lctx_1418_);
lean_dec_ref(v___x_1419_);
v___x_1433_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v___x_1432_, v_k_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_);
return v___x_1433_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg___boxed(lean_object* v_fvars_1434_, lean_object* v_names_1435_, lean_object* v_k_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_1434_, v_names_1435_, v_k_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec_ref(v_names_1435_);
lean_dec_ref(v_fvars_1434_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl(lean_object* v_00_u03b1_1443_, lean_object* v_fvars_1444_, lean_object* v_names_1445_, lean_object* v_k_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_1444_, v_names_1445_, v_k_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___boxed(lean_object* v_00_u03b1_1453_, lean_object* v_fvars_1454_, lean_object* v_names_1455_, lean_object* v_k_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl(v_00_u03b1_1453_, v_fvars_1454_, v_names_1455_, v_k_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_);
lean_dec(v_a_1460_);
lean_dec_ref(v_a_1459_);
lean_dec(v_a_1458_);
lean_dec_ref(v_a_1457_);
lean_dec_ref(v_names_1455_);
lean_dec_ref(v_fvars_1454_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0(lean_object* v_k_1463_, lean_object* v_fvars_1464_, lean_object* v_names_1465_, lean_object* v_runInBase_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = lean_apply_2(v_runInBase_1466_, lean_box(0), v_k_1463_);
v___x_1473_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_1464_, v_names_1465_, v___x_1472_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0___boxed(lean_object* v_k_1474_, lean_object* v_fvars_1475_, lean_object* v_names_1476_, lean_object* v_runInBase_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0(v_k_1474_, v_fvars_1475_, v_names_1476_, v_runInBase_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec_ref(v_names_1476_);
lean_dec_ref(v_fvars_1475_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg(lean_object* v_inst_1484_, lean_object* v_inst_1485_, lean_object* v_fvars_1486_, lean_object* v_names_1487_, lean_object* v_k_1488_){
_start:
{
lean_object* v_toBind_1489_; lean_object* v_liftWith_1490_; lean_object* v_restoreM_1491_; lean_object* v___f_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v_toBind_1489_ = lean_ctor_get(v_inst_1485_, 1);
lean_inc(v_toBind_1489_);
lean_dec_ref(v_inst_1485_);
v_liftWith_1490_ = lean_ctor_get(v_inst_1484_, 0);
lean_inc(v_liftWith_1490_);
v_restoreM_1491_ = lean_ctor_get(v_inst_1484_, 1);
lean_inc(v_restoreM_1491_);
lean_dec_ref(v_inst_1484_);
v___f_1492_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1492_, 0, v_k_1488_);
lean_closure_set(v___f_1492_, 1, v_fvars_1486_);
lean_closure_set(v___f_1492_, 2, v_names_1487_);
v___x_1493_ = lean_apply_2(v_liftWith_1490_, lean_box(0), v___f_1492_);
v___x_1494_ = lean_apply_1(v_restoreM_1491_, lean_box(0));
v___x_1495_ = lean_apply_4(v_toBind_1489_, lean_box(0), lean_box(0), v___x_1493_, v___x_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames(lean_object* v_n_1496_, lean_object* v_inst_1497_, lean_object* v_inst_1498_, lean_object* v_00_u03b1_1499_, lean_object* v_fvars_1500_, lean_object* v_names_1501_, lean_object* v_k_1502_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Lean_Meta_MatcherApp_withUserNames___redArg(v_inst_1497_, v_inst_1498_, v_fvars_1500_, v_names_1501_, v_k_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0(lean_object* v_k_1504_, lean_object* v_runInBase_1505_, lean_object* v_ys_1506_, lean_object* v_args_1507_, lean_object* v___mask_1508_, lean_object* v___bodyType_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = lean_apply_2(v_k_1504_, v_ys_1506_, v_args_1507_);
lean_inc(v___y_1513_);
lean_inc_ref(v___y_1512_);
lean_inc(v___y_1511_);
lean_inc_ref(v___y_1510_);
v___x_1516_ = lean_apply_7(v_runInBase_1505_, lean_box(0), v___x_1515_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, lean_box(0));
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0___boxed(lean_object* v_k_1517_, lean_object* v_runInBase_1518_, lean_object* v_ys_1519_, lean_object* v_args_1520_, lean_object* v___mask_1521_, lean_object* v___bodyType_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0(v_k_1517_, v_runInBase_1518_, v_ys_1519_, v_args_1520_, v___mask_1521_, v___bodyType_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec_ref(v___bodyType_1522_);
lean_dec_ref(v___mask_1521_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1(lean_object* v_k_1529_, lean_object* v_origAltType_1530_, lean_object* v_altInfo_1531_, lean_object* v_runInBase_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v___f_1538_; lean_object* v___x_1539_; 
v___f_1538_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1538_, 0, v_k_1529_);
lean_closure_set(v___f_1538_, 1, v_runInBase_1532_);
v___x_1539_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_origAltType_1530_, v_altInfo_1531_, v___f_1538_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1___boxed(lean_object* v_k_1540_, lean_object* v_origAltType_1541_, lean_object* v_altInfo_1542_, lean_object* v_runInBase_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1(v_k_1540_, v_origAltType_1541_, v_altInfo_1542_, v_runInBase_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(lean_object* v_inst_1550_, lean_object* v_inst_1551_, lean_object* v_origAltType_1552_, lean_object* v_altInfo_1553_, lean_object* v_k_1554_){
_start:
{
lean_object* v_toBind_1555_; lean_object* v_liftWith_1556_; lean_object* v_restoreM_1557_; lean_object* v___f_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v_toBind_1555_ = lean_ctor_get(v_inst_1550_, 1);
lean_inc(v_toBind_1555_);
lean_dec_ref(v_inst_1550_);
v_liftWith_1556_ = lean_ctor_get(v_inst_1551_, 0);
lean_inc(v_liftWith_1556_);
v_restoreM_1557_ = lean_ctor_get(v_inst_1551_, 1);
lean_inc(v_restoreM_1557_);
lean_dec_ref(v_inst_1551_);
v___f_1558_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1___boxed), 9, 3);
lean_closure_set(v___f_1558_, 0, v_k_1554_);
lean_closure_set(v___f_1558_, 1, v_origAltType_1552_);
lean_closure_set(v___f_1558_, 2, v_altInfo_1553_);
v___x_1559_ = lean_apply_2(v_liftWith_1556_, lean_box(0), v___f_1558_);
v___x_1560_ = lean_apply_1(v_restoreM_1557_, lean_box(0));
v___x_1561_ = lean_apply_4(v_toBind_1555_, lean_box(0), lean_box(0), v___x_1559_, v___x_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27(lean_object* v_n_1562_, lean_object* v_inst_1563_, lean_object* v_inst_1564_, lean_object* v_00_u03b1_1565_, lean_object* v_origAltType_1566_, lean_object* v_altInfo_1567_, lean_object* v_k_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(v_inst_1563_, v_inst_1564_, v_origAltType_1566_, v_altInfo_1567_, v_k_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_TransformAltFVars_altParams(lean_object* v_fvars_1570_){
_start:
{
lean_object* v_args_1571_; lean_object* v_discrEqs_1572_; lean_object* v___x_1573_; 
v_args_1571_ = lean_ctor_get(v_fvars_1570_, 0);
lean_inc_ref(v_args_1571_);
v_discrEqs_1572_ = lean_ctor_get(v_fvars_1570_, 3);
lean_inc_ref(v_discrEqs_1572_);
lean_dec_ref(v_fvars_1570_);
v___x_1573_ = l_Array_append___redArg(v_args_1571_, v_discrEqs_1572_);
lean_dec_ref(v_discrEqs_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_TransformAltFVars_all(lean_object* v_fvars_1574_){
_start:
{
lean_object* v_fields_1575_; lean_object* v_overlaps_1576_; lean_object* v_discrEqs_1577_; lean_object* v_extraEqs_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v_fields_1575_ = lean_ctor_get(v_fvars_1574_, 1);
lean_inc_ref(v_fields_1575_);
v_overlaps_1576_ = lean_ctor_get(v_fvars_1574_, 2);
lean_inc_ref(v_overlaps_1576_);
v_discrEqs_1577_ = lean_ctor_get(v_fvars_1574_, 3);
lean_inc_ref(v_discrEqs_1577_);
v_extraEqs_1578_ = lean_ctor_get(v_fvars_1574_, 4);
lean_inc_ref(v_extraEqs_1578_);
lean_dec_ref(v_fvars_1574_);
v___x_1579_ = l_Array_append___redArg(v_fields_1575_, v_overlaps_1576_);
lean_dec_ref(v_overlaps_1576_);
v___x_1580_ = l_Array_append___redArg(v___x_1579_, v_discrEqs_1577_);
lean_dec_ref(v_discrEqs_1577_);
v___x_1581_ = l_Array_append___redArg(v___x_1580_, v_extraEqs_1578_);
lean_dec_ref(v_extraEqs_1578_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0(lean_object* v_inst_1582_, lean_object* v_inst_1583_, lean_object* v_x_1584_){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2);
v___x_1586_ = l_Lean_throwError___redArg(v_inst_1582_, v_inst_1583_, v___x_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed(lean_object* v_inst_1587_, lean_object* v_inst_1588_, lean_object* v_x_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__0(v_inst_1587_, v_inst_1588_, v_x_1589_);
lean_dec_ref(v_x_1589_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1(lean_object* v_inst_1591_, lean_object* v_x_1592_){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1593_ = l_Lean_Expr_fvarId_x21(v_x_1592_);
v___x_1594_ = lean_alloc_closure((void*)(l_Lean_FVarId_getUserName___boxed), 6, 1);
lean_closure_set(v___x_1594_, 0, v___x_1593_);
v___x_1595_ = lean_apply_2(v_inst_1591_, lean_box(0), v___x_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed(lean_object* v_inst_1596_, lean_object* v_x_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__1(v_inst_1596_, v_x_1597_);
lean_dec_ref(v_x_1597_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2(lean_object* v_inst_1599_, lean_object* v___f_1600_, lean_object* v_xs_1601_, lean_object* v_x_1602_){
_start:
{
size_t v_sz_1603_; size_t v___x_1604_; lean_object* v___x_1605_; 
v_sz_1603_ = lean_array_size(v_xs_1601_);
v___x_1604_ = ((size_t)0ULL);
v___x_1605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1599_, v___f_1600_, v_sz_1603_, v___x_1604_, v_xs_1601_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed(lean_object* v_inst_1606_, lean_object* v___f_1607_, lean_object* v_xs_1608_, lean_object* v_x_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__2(v_inst_1606_, v___f_1607_, v_xs_1608_, v_x_1609_);
lean_dec_ref(v_x_1609_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__3(lean_object* v_fst_1611_, lean_object* v_fst_1612_, lean_object* v___x_1613_, lean_object* v___x_1614_, lean_object* v_toPure_1615_, lean_object* v_____do__lift_1616_){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1617_ = lean_array_push(v_fst_1611_, v_____do__lift_1616_);
v___x_1618_ = lean_nat_add(v_fst_1612_, v___x_1613_);
v___x_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
lean_ctor_set(v___x_1619_, 1, v___x_1614_);
v___x_1620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1617_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
v___x_1622_ = lean_apply_2(v_toPure_1615_, lean_box(0), v___x_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__3___boxed(lean_object* v_fst_1623_, lean_object* v_fst_1624_, lean_object* v___x_1625_, lean_object* v___x_1626_, lean_object* v_toPure_1627_, lean_object* v_____do__lift_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__3(v_fst_1623_, v_fst_1624_, v___x_1625_, v___x_1626_, v_toPure_1627_, v_____do__lift_1628_);
lean_dec(v___x_1625_);
lean_dec(v_fst_1624_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__4(uint8_t v_val_1630_, lean_object* v_a_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
if (v_val_1630_ == 0)
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_Meta_mkEqRefl(v_a_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
return v___x_1637_;
}
else
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_Meta_mkHEqRefl(v_a_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
return v___x_1638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__4___boxed(lean_object* v_val_1639_, lean_object* v_a_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
uint8_t v_val_12464__boxed_1646_; lean_object* v_res_1647_; 
v_val_12464__boxed_1646_ = lean_unbox(v_val_1639_);
v_res_1647_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__4(v_val_12464__boxed_1646_, v_a_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__5(lean_object* v_toPure_1648_, lean_object* v_inst_1649_, lean_object* v_toBind_1650_, lean_object* v_a_1651_, lean_object* v_x_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_snd_1654_; lean_object* v_snd_1655_; lean_object* v_fst_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1704_; 
v_snd_1654_ = lean_ctor_get(v___y_1653_, 1);
lean_inc(v_snd_1654_);
v_snd_1655_ = lean_ctor_get(v_snd_1654_, 1);
lean_inc(v_snd_1655_);
v_fst_1656_ = lean_ctor_get(v___y_1653_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___y_1653_);
if (v_isSharedCheck_1704_ == 0)
{
lean_object* v_unused_1705_; 
v_unused_1705_ = lean_ctor_get(v___y_1653_, 1);
lean_dec(v_unused_1705_);
v___x_1658_ = v___y_1653_;
v_isShared_1659_ = v_isSharedCheck_1704_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_fst_1656_);
lean_dec(v___y_1653_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1704_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v_fst_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1702_; 
v_fst_1660_ = lean_ctor_get(v_snd_1654_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v_snd_1654_);
if (v_isSharedCheck_1702_ == 0)
{
lean_object* v_unused_1703_; 
v_unused_1703_ = lean_ctor_get(v_snd_1654_, 1);
lean_dec(v_unused_1703_);
v___x_1662_ = v_snd_1654_;
v_isShared_1663_ = v_isSharedCheck_1702_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_fst_1660_);
lean_dec(v_snd_1654_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1702_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v_array_1664_; lean_object* v_start_1665_; lean_object* v_stop_1666_; uint8_t v___x_1667_; 
v_array_1664_ = lean_ctor_get(v_snd_1655_, 0);
v_start_1665_ = lean_ctor_get(v_snd_1655_, 1);
v_stop_1666_ = lean_ctor_get(v_snd_1655_, 2);
v___x_1667_ = lean_nat_dec_lt(v_start_1665_, v_stop_1666_);
if (v___x_1667_ == 0)
{
lean_object* v___x_1669_; 
lean_dec_ref(v_a_1651_);
lean_dec(v_toBind_1650_);
lean_dec(v_inst_1649_);
if (v_isShared_1663_ == 0)
{
v___x_1669_ = v___x_1662_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_fst_1660_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_snd_1655_);
v___x_1669_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1671_; 
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 1, v___x_1669_);
v___x_1671_ = v___x_1658_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_fst_1656_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
v___x_1673_ = lean_apply_2(v_toPure_1648_, lean_box(0), v___x_1672_);
return v___x_1673_;
}
}
}
else
{
lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1698_; 
lean_inc(v_stop_1666_);
lean_inc(v_start_1665_);
lean_inc_ref(v_array_1664_);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_snd_1655_);
if (v_isSharedCheck_1698_ == 0)
{
lean_object* v_unused_1699_; lean_object* v_unused_1700_; lean_object* v_unused_1701_; 
v_unused_1699_ = lean_ctor_get(v_snd_1655_, 2);
lean_dec(v_unused_1699_);
v_unused_1700_ = lean_ctor_get(v_snd_1655_, 1);
lean_dec(v_unused_1700_);
v_unused_1701_ = lean_ctor_get(v_snd_1655_, 0);
lean_dec(v_unused_1701_);
v___x_1677_ = v_snd_1655_;
v_isShared_1678_ = v_isSharedCheck_1698_;
goto v_resetjp_1676_;
}
else
{
lean_dec(v_snd_1655_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1698_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1679_ = lean_array_fget(v_array_1664_, v_start_1665_);
v___x_1680_ = lean_unsigned_to_nat(1u);
v___x_1681_ = lean_nat_add(v_start_1665_, v___x_1680_);
lean_dec(v_start_1665_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 1, v___x_1681_);
v___x_1683_ = v___x_1677_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_array_1664_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v___x_1681_);
lean_ctor_set(v_reuseFailAlloc_1697_, 2, v_stop_1666_);
v___x_1683_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v___x_1685_; 
lean_dec_ref(v_a_1651_);
lean_dec(v_toBind_1650_);
lean_dec(v_inst_1649_);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 1, v___x_1683_);
v___x_1685_ = v___x_1662_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_fst_1660_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
lean_object* v___x_1687_; 
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 1, v___x_1685_);
v___x_1687_ = v___x_1658_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_fst_1656_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
v___x_1689_ = lean_apply_2(v_toPure_1648_, lean_box(0), v___x_1688_);
return v___x_1689_;
}
}
}
else
{
lean_object* v_val_1692_; lean_object* v___f_1693_; lean_object* v___f_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
lean_del_object(v___x_1662_);
lean_del_object(v___x_1658_);
v_val_1692_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_val_1692_);
lean_dec_ref_known(v___x_1679_, 1);
v___f_1693_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_1693_, 0, v_fst_1656_);
lean_closure_set(v___f_1693_, 1, v_fst_1660_);
lean_closure_set(v___f_1693_, 2, v___x_1680_);
lean_closure_set(v___f_1693_, 3, v___x_1683_);
lean_closure_set(v___f_1693_, 4, v_toPure_1648_);
v___f_1694_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__4___boxed), 7, 2);
lean_closure_set(v___f_1694_, 0, v_val_1692_);
lean_closure_set(v___f_1694_, 1, v_a_1651_);
v___x_1695_ = lean_apply_2(v_inst_1649_, lean_box(0), v___f_1694_);
v___x_1696_ = lean_apply_4(v_toBind_1650_, lean_box(0), lean_box(0), v___x_1695_, v___f_1693_);
return v___x_1696_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6(lean_object* v_val_1706_, lean_object* v_fst_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Lean_mkArrow(v_val_1706_, v_fst_1707_, v___y_1710_, v___y_1711_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed(lean_object* v_val_1714_, lean_object* v_fst_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__6(v_val_1714_, v_fst_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7(lean_object* v_val_1724_, lean_object* v_fst_1725_, lean_object* v_fst_1726_, lean_object* v___x_1727_, lean_object* v___x_1728_, lean_object* v_toPure_1729_, lean_object* v_motiveBody_x27_1730_){
_start:
{
uint8_t v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1731_ = l_Lean_Expr_isHEq(v_val_1724_);
v___x_1732_ = lean_box(v___x_1731_);
v___x_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
v___x_1734_ = lean_array_push(v_fst_1725_, v___x_1733_);
v___x_1735_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7___closed__0));
v___x_1736_ = lean_array_push(v_fst_1726_, v___x_1735_);
v___x_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1727_);
lean_ctor_set(v___x_1737_, 1, v___x_1728_);
v___x_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1736_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
v___x_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1734_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
v___x_1740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1740_, 0, v_motiveBody_x27_1730_);
lean_ctor_set(v___x_1740_, 1, v___x_1739_);
v___x_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
v___x_1742_ = lean_apply_2(v_toPure_1729_, lean_box(0), v___x_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7___boxed(lean_object* v_val_1743_, lean_object* v_fst_1744_, lean_object* v_fst_1745_, lean_object* v___x_1746_, lean_object* v___x_1747_, lean_object* v_toPure_1748_, lean_object* v_motiveBody_x27_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__7(v_val_1743_, v_fst_1744_, v_fst_1745_, v___x_1746_, v___x_1747_, v_toPure_1748_, v_motiveBody_x27_1749_);
lean_dec_ref(v_val_1743_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8(lean_object* v_fst_1751_, lean_object* v_fst_1752_, lean_object* v_fst_1753_, lean_object* v___x_1754_, lean_object* v___x_1755_, lean_object* v_toPure_1756_, lean_object* v_inst_1757_, lean_object* v_toBind_1758_, lean_object* v___x_1759_, lean_object* v_heq_x3f_1760_){
_start:
{
if (lean_obj_tag(v_heq_x3f_1760_) == 1)
{
lean_object* v_val_1761_; lean_object* v___f_1762_; lean_object* v___f_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_dec(v___x_1759_);
v_val_1761_ = lean_ctor_get(v_heq_x3f_1760_, 0);
lean_inc_n(v_val_1761_, 2);
lean_dec_ref_known(v_heq_x3f_1760_, 1);
v___f_1762_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed), 7, 2);
lean_closure_set(v___f_1762_, 0, v_val_1761_);
lean_closure_set(v___f_1762_, 1, v_fst_1751_);
v___f_1763_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7___boxed), 7, 6);
lean_closure_set(v___f_1763_, 0, v_val_1761_);
lean_closure_set(v___f_1763_, 1, v_fst_1752_);
lean_closure_set(v___f_1763_, 2, v_fst_1753_);
lean_closure_set(v___f_1763_, 3, v___x_1754_);
lean_closure_set(v___f_1763_, 4, v___x_1755_);
lean_closure_set(v___f_1763_, 5, v_toPure_1756_);
v___x_1764_ = lean_apply_2(v_inst_1757_, lean_box(0), v___f_1762_);
v___x_1765_ = lean_apply_4(v_toBind_1758_, lean_box(0), lean_box(0), v___x_1764_, v___f_1763_);
return v___x_1765_;
}
else
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
lean_dec(v_heq_x3f_1760_);
lean_dec(v_toBind_1758_);
lean_dec(v_inst_1757_);
v___x_1766_ = lean_box(0);
v___x_1767_ = lean_array_push(v_fst_1752_, v___x_1766_);
v___x_1768_ = lean_array_push(v_fst_1753_, v___x_1759_);
v___x_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1754_);
lean_ctor_set(v___x_1769_, 1, v___x_1755_);
v___x_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1768_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
v___x_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1767_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
v___x_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1772_, 0, v_fst_1751_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
v___x_1774_ = lean_apply_2(v_toPure_1756_, lean_box(0), v___x_1773_);
return v___x_1774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9(lean_object* v___f_1775_, lean_object* v_heq_x3f_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = lean_apply_1(v___f_1775_, v_heq_x3f_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12(lean_object* v_heq_1778_, lean_object* v_toPure_1779_, lean_object* v_toBind_1780_, lean_object* v___f_1781_, lean_object* v___f_1782_, uint8_t v_addProofEqualities_1783_, uint8_t v_____do__lift_1784_){
_start:
{
if (v_____do__lift_1784_ == 0)
{
lean_dec(v___f_1782_);
goto v___jp_1785_;
}
else
{
if (v_addProofEqualities_1783_ == 0)
{
lean_dec(v___f_1781_);
lean_dec_ref(v_heq_1778_);
goto v___jp_1789_;
}
else
{
uint8_t v___x_1793_; 
v___x_1793_ = l_Lean_Expr_isHEq(v_heq_1778_);
if (v___x_1793_ == 0)
{
lean_dec(v___f_1782_);
goto v___jp_1785_;
}
else
{
lean_dec(v___f_1781_);
lean_dec_ref(v_heq_1778_);
goto v___jp_1789_;
}
}
}
v___jp_1785_:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1786_, 0, v_heq_1778_);
v___x_1787_ = lean_apply_2(v_toPure_1779_, lean_box(0), v___x_1786_);
v___x_1788_ = lean_apply_4(v_toBind_1780_, lean_box(0), lean_box(0), v___x_1787_, v___f_1781_);
return v___x_1788_;
}
v___jp_1789_:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1790_ = lean_box(0);
v___x_1791_ = lean_apply_2(v_toPure_1779_, lean_box(0), v___x_1790_);
v___x_1792_ = lean_apply_4(v_toBind_1780_, lean_box(0), lean_box(0), v___x_1791_, v___f_1782_);
return v___x_1792_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12___boxed(lean_object* v_heq_1794_, lean_object* v_toPure_1795_, lean_object* v_toBind_1796_, lean_object* v___f_1797_, lean_object* v___f_1798_, lean_object* v_addProofEqualities_1799_, lean_object* v_____do__lift_1800_){
_start:
{
uint8_t v_addProofEqualities_boxed_1801_; uint8_t v_____do__lift_12683__boxed_1802_; lean_object* v_res_1803_; 
v_addProofEqualities_boxed_1801_ = lean_unbox(v_addProofEqualities_1799_);
v_____do__lift_12683__boxed_1802_ = lean_unbox(v_____do__lift_1800_);
v_res_1803_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__12(v_heq_1794_, v_toPure_1795_, v_toBind_1796_, v___f_1797_, v___f_1798_, v_addProofEqualities_boxed_1801_, v_____do__lift_12683__boxed_1802_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10(lean_object* v_toPure_1804_, lean_object* v_toBind_1805_, lean_object* v___f_1806_, lean_object* v___f_1807_, uint8_t v_addProofEqualities_1808_, lean_object* v_a_1809_, lean_object* v_inst_1810_, lean_object* v_heq_1811_){
_start:
{
lean_object* v___x_1812_; lean_object* v___f_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1812_ = lean_box(v_addProofEqualities_1808_);
lean_inc(v_toBind_1805_);
v___f_1813_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__12___boxed), 7, 6);
lean_closure_set(v___f_1813_, 0, v_heq_1811_);
lean_closure_set(v___f_1813_, 1, v_toPure_1804_);
lean_closure_set(v___f_1813_, 2, v_toBind_1805_);
lean_closure_set(v___f_1813_, 3, v___f_1806_);
lean_closure_set(v___f_1813_, 4, v___f_1807_);
lean_closure_set(v___f_1813_, 5, v___x_1812_);
v___x_1814_ = lean_alloc_closure((void*)(l_Lean_Meta_isProof___boxed), 6, 1);
lean_closure_set(v___x_1814_, 0, v_a_1809_);
v___x_1815_ = lean_apply_2(v_inst_1810_, lean_box(0), v___x_1814_);
v___x_1816_ = lean_apply_4(v_toBind_1805_, lean_box(0), lean_box(0), v___x_1815_, v___f_1813_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10___boxed(lean_object* v_toPure_1817_, lean_object* v_toBind_1818_, lean_object* v___f_1819_, lean_object* v___f_1820_, lean_object* v_addProofEqualities_1821_, lean_object* v_a_1822_, lean_object* v_inst_1823_, lean_object* v_heq_1824_){
_start:
{
uint8_t v_addProofEqualities_boxed_1825_; lean_object* v_res_1826_; 
v_addProofEqualities_boxed_1825_ = lean_unbox(v_addProofEqualities_1821_);
v_res_1826_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__10(v_toPure_1817_, v_toBind_1818_, v___f_1819_, v___f_1820_, v_addProofEqualities_boxed_1825_, v_a_1822_, v_inst_1823_, v_heq_1824_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11(lean_object* v_toPure_1827_, lean_object* v_inst_1828_, lean_object* v_toBind_1829_, uint8_t v_addEqualities_1830_, uint8_t v_addProofEqualities_1831_, lean_object* v_a_1832_, lean_object* v_x_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v_snd_1835_; lean_object* v_snd_1836_; lean_object* v_snd_1837_; lean_object* v_snd_1838_; lean_object* v_fst_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1933_; 
v_snd_1835_ = lean_ctor_get(v___y_1834_, 1);
lean_inc(v_snd_1835_);
v_snd_1836_ = lean_ctor_get(v_snd_1835_, 1);
lean_inc(v_snd_1836_);
v_snd_1837_ = lean_ctor_get(v_snd_1836_, 1);
lean_inc(v_snd_1837_);
v_snd_1838_ = lean_ctor_get(v_snd_1837_, 1);
lean_inc(v_snd_1838_);
v_fst_1839_ = lean_ctor_get(v___y_1834_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___y_1834_);
if (v_isSharedCheck_1933_ == 0)
{
lean_object* v_unused_1934_; 
v_unused_1934_ = lean_ctor_get(v___y_1834_, 1);
lean_dec(v_unused_1934_);
v___x_1841_ = v___y_1834_;
v_isShared_1842_ = v_isSharedCheck_1933_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_fst_1839_);
lean_dec(v___y_1834_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1933_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v_fst_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1931_; 
v_fst_1843_ = lean_ctor_get(v_snd_1835_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v_snd_1835_);
if (v_isSharedCheck_1931_ == 0)
{
lean_object* v_unused_1932_; 
v_unused_1932_ = lean_ctor_get(v_snd_1835_, 1);
lean_dec(v_unused_1932_);
v___x_1845_ = v_snd_1835_;
v_isShared_1846_ = v_isSharedCheck_1931_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_fst_1843_);
lean_dec(v_snd_1835_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1931_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v_fst_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1929_; 
v_fst_1847_ = lean_ctor_get(v_snd_1836_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_snd_1836_);
if (v_isSharedCheck_1929_ == 0)
{
lean_object* v_unused_1930_; 
v_unused_1930_ = lean_ctor_get(v_snd_1836_, 1);
lean_dec(v_unused_1930_);
v___x_1849_ = v_snd_1836_;
v_isShared_1850_ = v_isSharedCheck_1929_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_fst_1847_);
lean_dec(v_snd_1836_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1929_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v_fst_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1927_; 
v_fst_1851_ = lean_ctor_get(v_snd_1837_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v_snd_1837_);
if (v_isSharedCheck_1927_ == 0)
{
lean_object* v_unused_1928_; 
v_unused_1928_ = lean_ctor_get(v_snd_1837_, 1);
lean_dec(v_unused_1928_);
v___x_1853_ = v_snd_1837_;
v_isShared_1854_ = v_isSharedCheck_1927_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_fst_1851_);
lean_dec(v_snd_1837_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1927_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v_array_1855_; lean_object* v_start_1856_; lean_object* v_stop_1857_; uint8_t v___x_1858_; 
v_array_1855_ = lean_ctor_get(v_snd_1838_, 0);
v_start_1856_ = lean_ctor_get(v_snd_1838_, 1);
v_stop_1857_ = lean_ctor_get(v_snd_1838_, 2);
v___x_1858_ = lean_nat_dec_lt(v_start_1856_, v_stop_1857_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1860_; 
lean_dec_ref(v_a_1832_);
lean_dec(v_toBind_1829_);
lean_dec(v_inst_1828_);
if (v_isShared_1854_ == 0)
{
v___x_1860_ = v___x_1853_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_fst_1851_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_snd_1838_);
v___x_1860_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
lean_object* v___x_1862_; 
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 1, v___x_1860_);
v___x_1862_ = v___x_1849_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_fst_1847_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v___x_1860_);
v___x_1862_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
lean_object* v___x_1864_; 
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 1, v___x_1862_);
v___x_1864_ = v___x_1845_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_fst_1843_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1866_; 
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 1, v___x_1864_);
v___x_1866_ = v___x_1841_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_fst_1839_);
lean_ctor_set(v_reuseFailAlloc_1869_, 1, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1866_);
v___x_1868_ = lean_apply_2(v_toPure_1827_, lean_box(0), v___x_1867_);
return v___x_1868_;
}
}
}
}
}
else
{
lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1923_; 
lean_inc(v_stop_1857_);
lean_inc(v_start_1856_);
lean_inc_ref(v_array_1855_);
v_isSharedCheck_1923_ = !lean_is_exclusive(v_snd_1838_);
if (v_isSharedCheck_1923_ == 0)
{
lean_object* v_unused_1924_; lean_object* v_unused_1925_; lean_object* v_unused_1926_; 
v_unused_1924_ = lean_ctor_get(v_snd_1838_, 2);
lean_dec(v_unused_1924_);
v_unused_1925_ = lean_ctor_get(v_snd_1838_, 1);
lean_dec(v_unused_1925_);
v_unused_1926_ = lean_ctor_get(v_snd_1838_, 0);
lean_dec(v_unused_1926_);
v___x_1874_ = v_snd_1838_;
v_isShared_1875_ = v_isSharedCheck_1923_;
goto v_resetjp_1873_;
}
else
{
lean_dec(v_snd_1838_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1923_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v_array_1876_; lean_object* v_start_1877_; lean_object* v_stop_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1883_; 
v_array_1876_ = lean_ctor_get(v_fst_1851_, 0);
v_start_1877_ = lean_ctor_get(v_fst_1851_, 1);
v_stop_1878_ = lean_ctor_get(v_fst_1851_, 2);
v___x_1879_ = lean_array_fget(v_array_1855_, v_start_1856_);
v___x_1880_ = lean_unsigned_to_nat(1u);
v___x_1881_ = lean_nat_add(v_start_1856_, v___x_1880_);
lean_dec(v_start_1856_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 1, v___x_1881_);
v___x_1883_ = v___x_1874_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_array_1855_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v___x_1881_);
lean_ctor_set(v_reuseFailAlloc_1922_, 2, v_stop_1857_);
v___x_1883_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
uint8_t v___x_1884_; 
v___x_1884_ = lean_nat_dec_lt(v_start_1877_, v_stop_1878_);
if (v___x_1884_ == 0)
{
lean_object* v___x_1886_; 
lean_dec(v___x_1879_);
lean_dec_ref(v_a_1832_);
lean_dec(v_toBind_1829_);
lean_dec(v_inst_1828_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 1, v___x_1883_);
v___x_1886_ = v___x_1853_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_fst_1851_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v___x_1883_);
v___x_1886_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v___x_1888_; 
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 1, v___x_1886_);
v___x_1888_ = v___x_1849_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_fst_1847_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1890_; 
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 1, v___x_1888_);
v___x_1890_ = v___x_1845_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_fst_1843_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1892_; 
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 1, v___x_1890_);
v___x_1892_ = v___x_1841_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_fst_1839_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v___x_1890_);
v___x_1892_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
v___x_1894_ = lean_apply_2(v_toPure_1827_, lean_box(0), v___x_1893_);
return v___x_1894_;
}
}
}
}
}
else
{
lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1918_; 
lean_inc(v_stop_1878_);
lean_inc(v_start_1877_);
lean_inc_ref(v_array_1876_);
lean_del_object(v___x_1853_);
lean_del_object(v___x_1849_);
lean_del_object(v___x_1845_);
lean_del_object(v___x_1841_);
v_isSharedCheck_1918_ = !lean_is_exclusive(v_fst_1851_);
if (v_isSharedCheck_1918_ == 0)
{
lean_object* v_unused_1919_; lean_object* v_unused_1920_; lean_object* v_unused_1921_; 
v_unused_1919_ = lean_ctor_get(v_fst_1851_, 2);
lean_dec(v_unused_1919_);
v_unused_1920_ = lean_ctor_get(v_fst_1851_, 1);
lean_dec(v_unused_1920_);
v_unused_1921_ = lean_ctor_get(v_fst_1851_, 0);
lean_dec(v_unused_1921_);
v___x_1900_ = v_fst_1851_;
v_isShared_1901_ = v_isSharedCheck_1918_;
goto v_resetjp_1899_;
}
else
{
lean_dec(v_fst_1851_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1918_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1905_; 
v___x_1902_ = lean_array_fget(v_array_1876_, v_start_1877_);
v___x_1903_ = lean_nat_add(v_start_1877_, v___x_1880_);
lean_dec(v_start_1877_);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 1, v___x_1903_);
v___x_1905_ = v___x_1900_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_array_1876_);
lean_ctor_set(v_reuseFailAlloc_1917_, 1, v___x_1903_);
lean_ctor_set(v_reuseFailAlloc_1917_, 2, v_stop_1878_);
v___x_1905_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___f_1906_; lean_object* v___f_1907_; 
lean_inc(v___x_1879_);
lean_inc(v_toBind_1829_);
lean_inc(v_inst_1828_);
lean_inc(v_toPure_1827_);
v___f_1906_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__8), 10, 9);
lean_closure_set(v___f_1906_, 0, v_fst_1839_);
lean_closure_set(v___f_1906_, 1, v_fst_1843_);
lean_closure_set(v___f_1906_, 2, v_fst_1847_);
lean_closure_set(v___f_1906_, 3, v___x_1905_);
lean_closure_set(v___f_1906_, 4, v___x_1883_);
lean_closure_set(v___f_1906_, 5, v_toPure_1827_);
lean_closure_set(v___f_1906_, 6, v_inst_1828_);
lean_closure_set(v___f_1906_, 7, v_toBind_1829_);
lean_closure_set(v___f_1906_, 8, v___x_1879_);
v___f_1907_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9), 2, 1);
lean_closure_set(v___f_1907_, 0, v___f_1906_);
if (v_addEqualities_1830_ == 0)
{
lean_dec(v___x_1902_);
lean_dec(v___x_1879_);
lean_dec_ref(v_a_1832_);
lean_dec(v_inst_1828_);
goto v___jp_1908_;
}
else
{
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v___x_1912_; lean_object* v___f_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1912_ = lean_box(v_addProofEqualities_1831_);
lean_inc(v_inst_1828_);
lean_inc_ref(v_a_1832_);
lean_inc_ref(v___f_1907_);
lean_inc(v_toBind_1829_);
v___f_1913_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__10___boxed), 8, 7);
lean_closure_set(v___f_1913_, 0, v_toPure_1827_);
lean_closure_set(v___f_1913_, 1, v_toBind_1829_);
lean_closure_set(v___f_1913_, 2, v___f_1907_);
lean_closure_set(v___f_1913_, 3, v___f_1907_);
lean_closure_set(v___f_1913_, 4, v___x_1912_);
lean_closure_set(v___f_1913_, 5, v_a_1832_);
lean_closure_set(v___f_1913_, 6, v_inst_1828_);
v___x_1914_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEqHEq___boxed), 7, 2);
lean_closure_set(v___x_1914_, 0, v___x_1902_);
lean_closure_set(v___x_1914_, 1, v_a_1832_);
v___x_1915_ = lean_apply_2(v_inst_1828_, lean_box(0), v___x_1914_);
v___x_1916_ = lean_apply_4(v_toBind_1829_, lean_box(0), lean_box(0), v___x_1915_, v___f_1913_);
return v___x_1916_;
}
else
{
lean_dec_ref_known(v___x_1879_, 1);
lean_dec(v___x_1902_);
lean_dec_ref(v_a_1832_);
lean_dec(v_inst_1828_);
goto v___jp_1908_;
}
}
v___jp_1908_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1909_ = lean_box(0);
v___x_1910_ = lean_apply_2(v_toPure_1827_, lean_box(0), v___x_1909_);
v___x_1911_ = lean_apply_4(v_toBind_1829_, lean_box(0), lean_box(0), v___x_1910_, v___f_1907_);
return v___x_1911_;
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed(lean_object* v_toPure_1935_, lean_object* v_inst_1936_, lean_object* v_toBind_1937_, lean_object* v_addEqualities_1938_, lean_object* v_addProofEqualities_1939_, lean_object* v_a_1940_, lean_object* v_x_1941_, lean_object* v___y_1942_){
_start:
{
uint8_t v_addEqualities_boxed_1943_; uint8_t v_addProofEqualities_boxed_1944_; lean_object* v_res_1945_; 
v_addEqualities_boxed_1943_ = lean_unbox(v_addEqualities_1938_);
v_addProofEqualities_boxed_1944_ = lean_unbox(v_addProofEqualities_1939_);
v_res_1945_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__11(v_toPure_1935_, v_inst_1936_, v_toBind_1937_, v_addEqualities_boxed_1943_, v_addProofEqualities_boxed_1944_, v_a_1940_, v_x_1941_, v___y_1942_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__13(lean_object* v_toPure_1946_, lean_object* v_____do__lift_1947_){
_start:
{
lean_object* v___x_1948_; 
v___x_1948_ = lean_apply_2(v_toPure_1946_, lean_box(0), v_____do__lift_1947_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__14(lean_object* v_toPure_1949_, lean_object* v_____do__lift_1950_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = lean_apply_2(v_toPure_1949_, lean_box(0), v_____do__lift_1950_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__15(lean_object* v_fst_1952_, lean_object* v_fst_1953_, lean_object* v_____do__lift_1954_, lean_object* v_toPure_1955_, lean_object* v_____do__lift_1956_){
_start:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1957_, 0, v_fst_1952_);
lean_ctor_set(v___x_1957_, 1, v_fst_1953_);
v___x_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1958_, 0, v_____do__lift_1956_);
lean_ctor_set(v___x_1958_, 1, v___x_1957_);
v___x_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1959_, 0, v_____do__lift_1954_);
lean_ctor_set(v___x_1959_, 1, v___x_1958_);
v___x_1960_ = lean_apply_2(v_toPure_1955_, lean_box(0), v___x_1959_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__16(lean_object* v_fst_1961_, lean_object* v_fst_1962_, lean_object* v_toPure_1963_, lean_object* v_fst_1964_, lean_object* v_inst_1965_, lean_object* v_toBind_1966_, lean_object* v_____do__lift_1967_){
_start:
{
lean_object* v___f_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___f_1968_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__15), 5, 4);
lean_closure_set(v___f_1968_, 0, v_fst_1961_);
lean_closure_set(v___f_1968_, 1, v_fst_1962_);
lean_closure_set(v___f_1968_, 2, v_____do__lift_1967_);
lean_closure_set(v___f_1968_, 3, v_toPure_1963_);
v___x_1969_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1969_, 0, v_fst_1964_);
v___x_1970_ = lean_apply_2(v_inst_1965_, lean_box(0), v___x_1969_);
v___x_1971_ = lean_apply_4(v_toBind_1966_, lean_box(0), lean_box(0), v___x_1970_, v___f_1968_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__17(lean_object* v_toPure_1972_, lean_object* v_inst_1973_, lean_object* v_toBind_1974_, lean_object* v_motiveArgs_1975_, lean_object* v_____s_1976_){
_start:
{
lean_object* v_snd_1977_; lean_object* v_snd_1978_; lean_object* v_fst_1979_; lean_object* v_fst_1980_; lean_object* v_fst_1981_; lean_object* v___f_1982_; uint8_t v___x_1983_; uint8_t v___x_1984_; uint8_t v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v_snd_1977_ = lean_ctor_get(v_____s_1976_, 1);
lean_inc(v_snd_1977_);
v_snd_1978_ = lean_ctor_get(v_snd_1977_, 1);
lean_inc(v_snd_1978_);
v_fst_1979_ = lean_ctor_get(v_____s_1976_, 0);
lean_inc_n(v_fst_1979_, 2);
lean_dec_ref(v_____s_1976_);
v_fst_1980_ = lean_ctor_get(v_snd_1977_, 0);
lean_inc(v_fst_1980_);
lean_dec(v_snd_1977_);
v_fst_1981_ = lean_ctor_get(v_snd_1978_, 0);
lean_inc(v_fst_1981_);
lean_dec(v_snd_1978_);
lean_inc(v_toBind_1974_);
lean_inc(v_inst_1973_);
v___f_1982_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16), 7, 6);
lean_closure_set(v___f_1982_, 0, v_fst_1980_);
lean_closure_set(v___f_1982_, 1, v_fst_1981_);
lean_closure_set(v___f_1982_, 2, v_toPure_1972_);
lean_closure_set(v___f_1982_, 3, v_fst_1979_);
lean_closure_set(v___f_1982_, 4, v_inst_1973_);
lean_closure_set(v___f_1982_, 5, v_toBind_1974_);
v___x_1983_ = 0;
v___x_1984_ = 1;
v___x_1985_ = 1;
v___x_1986_ = lean_box(v___x_1983_);
v___x_1987_ = lean_box(v___x_1984_);
v___x_1988_ = lean_box(v___x_1983_);
v___x_1989_ = lean_box(v___x_1984_);
v___x_1990_ = lean_box(v___x_1985_);
v___x_1991_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1991_, 0, v_motiveArgs_1975_);
lean_closure_set(v___x_1991_, 1, v_fst_1979_);
lean_closure_set(v___x_1991_, 2, v___x_1986_);
lean_closure_set(v___x_1991_, 3, v___x_1987_);
lean_closure_set(v___x_1991_, 4, v___x_1988_);
lean_closure_set(v___x_1991_, 5, v___x_1989_);
lean_closure_set(v___x_1991_, 6, v___x_1990_);
v___x_1992_ = lean_apply_2(v_inst_1973_, lean_box(0), v___x_1991_);
v___x_1993_ = lean_apply_4(v_toBind_1974_, lean_box(0), lean_box(0), v___x_1992_, v___f_1982_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__18(lean_object* v_toMatcherInfo_1996_, lean_object* v_discrs_x27_1997_, lean_object* v_motiveArgs_1998_, lean_object* v_inst_1999_, lean_object* v___f_2000_, lean_object* v_toBind_2001_, lean_object* v___f_2002_, lean_object* v_motiveBody_x27_2003_){
_start:
{
lean_object* v_discrInfos_2004_; lean_object* v___x_2005_; lean_object* v_addHEqualities_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; size_t v_sz_2015_; size_t v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v_discrInfos_2004_ = lean_ctor_get(v_toMatcherInfo_1996_, 4);
lean_inc_ref(v_discrInfos_2004_);
lean_dec_ref(v_toMatcherInfo_1996_);
v___x_2005_ = lean_unsigned_to_nat(0u);
v_addHEqualities_2006_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__18___closed__0));
v___x_2007_ = lean_array_get_size(v_discrs_x27_1997_);
v___x_2008_ = l_Array_toSubarray___redArg(v_discrs_x27_1997_, v___x_2005_, v___x_2007_);
v___x_2009_ = lean_array_get_size(v_discrInfos_2004_);
v___x_2010_ = l_Array_toSubarray___redArg(v_discrInfos_2004_, v___x_2005_, v___x_2009_);
v___x_2011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2008_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v___x_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2012_, 0, v_addHEqualities_2006_);
lean_ctor_set(v___x_2012_, 1, v___x_2011_);
v___x_2013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2013_, 0, v_addHEqualities_2006_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
v___x_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2014_, 0, v_motiveBody_x27_2003_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
v_sz_2015_ = lean_array_size(v_motiveArgs_1998_);
v___x_2016_ = ((size_t)0ULL);
v___x_2017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1999_, v_motiveArgs_1998_, v___f_2000_, v_sz_2015_, v___x_2016_, v___x_2014_);
v___x_2018_ = lean_apply_4(v_toBind_2001_, lean_box(0), lean_box(0), v___x_2017_, v___f_2002_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19(lean_object* v_onMotive_2019_, lean_object* v_motiveArgs_2020_, lean_object* v_motiveBody_2021_, lean_object* v_toBind_2022_, lean_object* v___f_2023_, lean_object* v_____r_2024_){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = lean_apply_2(v_onMotive_2019_, v_motiveArgs_2020_, v_motiveBody_2021_);
v___x_2026_ = lean_apply_4(v_toBind_2022_, lean_box(0), lean_box(0), v___x_2025_, v___f_2023_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20(lean_object* v___f_2027_, lean_object* v_____r_2028_){
_start:
{
lean_object* v___x_2029_; 
v___x_2029_ = lean_apply_1(v___f_2027_, v_____r_2028_);
return v___x_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21(lean_object* v_toPure_2030_, lean_object* v_inst_2031_, lean_object* v_toBind_2032_, lean_object* v_toMatcherInfo_2033_, lean_object* v_discrs_x27_2034_, lean_object* v_inst_2035_, lean_object* v___f_2036_, lean_object* v_onMotive_2037_, lean_object* v_discrs_2038_, lean_object* v_inst_2039_, lean_object* v_motiveArgs_2040_, lean_object* v_motiveBody_2041_){
_start:
{
lean_object* v___f_2042_; lean_object* v___f_2043_; lean_object* v___f_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; 
lean_inc_ref_n(v_motiveArgs_2040_, 3);
lean_inc_n(v_toBind_2032_, 3);
v___f_2042_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__17), 5, 4);
lean_closure_set(v___f_2042_, 0, v_toPure_2030_);
lean_closure_set(v___f_2042_, 1, v_inst_2031_);
lean_closure_set(v___f_2042_, 2, v_toBind_2032_);
lean_closure_set(v___f_2042_, 3, v_motiveArgs_2040_);
lean_inc_ref(v_inst_2035_);
v___f_2043_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__18), 8, 7);
lean_closure_set(v___f_2043_, 0, v_toMatcherInfo_2033_);
lean_closure_set(v___f_2043_, 1, v_discrs_x27_2034_);
lean_closure_set(v___f_2043_, 2, v_motiveArgs_2040_);
lean_closure_set(v___f_2043_, 3, v_inst_2035_);
lean_closure_set(v___f_2043_, 4, v___f_2036_);
lean_closure_set(v___f_2043_, 5, v_toBind_2032_);
lean_closure_set(v___f_2043_, 6, v___f_2042_);
lean_inc_ref(v___f_2043_);
lean_inc_ref(v_motiveBody_2041_);
lean_inc(v_onMotive_2037_);
v___f_2044_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__19), 6, 5);
lean_closure_set(v___f_2044_, 0, v_onMotive_2037_);
lean_closure_set(v___f_2044_, 1, v_motiveArgs_2040_);
lean_closure_set(v___f_2044_, 2, v_motiveBody_2041_);
lean_closure_set(v___f_2044_, 3, v_toBind_2032_);
lean_closure_set(v___f_2044_, 4, v___f_2043_);
v___x_2045_ = lean_array_get_size(v_motiveArgs_2040_);
v___x_2046_ = lean_array_get_size(v_discrs_2038_);
v___x_2047_ = lean_nat_dec_eq(v___x_2045_, v___x_2046_);
if (v___x_2047_ == 0)
{
lean_object* v___f_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
lean_dec_ref(v___f_2043_);
lean_dec_ref(v_motiveBody_2041_);
lean_dec_ref(v_motiveArgs_2040_);
lean_dec(v_onMotive_2037_);
v___f_2048_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__20), 2, 1);
lean_closure_set(v___f_2048_, 0, v___f_2044_);
v___x_2049_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_2050_ = l_Nat_reprFast(v___x_2046_);
v___x_2051_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
v___x_2052_ = l_Lean_MessageData_ofFormat(v___x_2051_);
v___x_2053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2049_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
v___x_2054_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_2055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2053_);
lean_ctor_set(v___x_2055_, 1, v___x_2054_);
v___x_2056_ = l_Lean_throwError___redArg(v_inst_2035_, v_inst_2039_, v___x_2055_);
v___x_2057_ = lean_apply_4(v_toBind_2032_, lean_box(0), lean_box(0), v___x_2056_, v___f_2048_);
return v___x_2057_;
}
else
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
lean_dec_ref(v___f_2044_);
lean_dec_ref(v_inst_2039_);
lean_dec_ref(v_inst_2035_);
v___x_2058_ = lean_box(0);
v___x_2059_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__19(v_onMotive_2037_, v_motiveArgs_2040_, v_motiveBody_2041_, v_toBind_2032_, v___f_2043_, v___x_2058_);
return v___x_2059_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed(lean_object* v_toPure_2060_, lean_object* v_inst_2061_, lean_object* v_toBind_2062_, lean_object* v_toMatcherInfo_2063_, lean_object* v_discrs_x27_2064_, lean_object* v_inst_2065_, lean_object* v___f_2066_, lean_object* v_onMotive_2067_, lean_object* v_discrs_2068_, lean_object* v_inst_2069_, lean_object* v_motiveArgs_2070_, lean_object* v_motiveBody_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__21(v_toPure_2060_, v_inst_2061_, v_toBind_2062_, v_toMatcherInfo_2063_, v_discrs_x27_2064_, v_inst_2065_, v___f_2066_, v_onMotive_2067_, v_discrs_2068_, v_inst_2069_, v_motiveArgs_2070_, v_motiveBody_2071_);
lean_dec_ref(v_discrs_2068_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22(lean_object* v_fst_2073_, lean_object* v_numParams_2074_, lean_object* v_numDiscrs_2075_, lean_object* v_altInfos_2076_, lean_object* v_uElimPos_x3f_2077_, lean_object* v_snd_2078_, lean_object* v_overlaps_2079_, lean_object* v_matcherName_2080_, lean_object* v_matcherLevels_2081_, lean_object* v_params_x27_2082_, lean_object* v_fst_2083_, lean_object* v_discrs_x27_2084_, lean_object* v_fst_2085_, lean_object* v_toPure_2086_, lean_object* v_____do__lift_2087_){
_start:
{
lean_object* v_remaining_x27_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v_remaining_x27_2088_ = l_Array_append___redArg(v_fst_2073_, v_____do__lift_2087_);
v___x_2089_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2089_, 0, v_numParams_2074_);
lean_ctor_set(v___x_2089_, 1, v_numDiscrs_2075_);
lean_ctor_set(v___x_2089_, 2, v_altInfos_2076_);
lean_ctor_set(v___x_2089_, 3, v_uElimPos_x3f_2077_);
lean_ctor_set(v___x_2089_, 4, v_snd_2078_);
lean_ctor_set(v___x_2089_, 5, v_overlaps_2079_);
v___x_2090_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
lean_ctor_set(v___x_2090_, 1, v_matcherName_2080_);
lean_ctor_set(v___x_2090_, 2, v_matcherLevels_2081_);
lean_ctor_set(v___x_2090_, 3, v_params_x27_2082_);
lean_ctor_set(v___x_2090_, 4, v_fst_2083_);
lean_ctor_set(v___x_2090_, 5, v_discrs_x27_2084_);
lean_ctor_set(v___x_2090_, 6, v_fst_2085_);
lean_ctor_set(v___x_2090_, 7, v_remaining_x27_2088_);
v___x_2091_ = lean_apply_2(v_toPure_2086_, lean_box(0), v___x_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22___boxed(lean_object* v_fst_2092_, lean_object* v_numParams_2093_, lean_object* v_numDiscrs_2094_, lean_object* v_altInfos_2095_, lean_object* v_uElimPos_x3f_2096_, lean_object* v_snd_2097_, lean_object* v_overlaps_2098_, lean_object* v_matcherName_2099_, lean_object* v_matcherLevels_2100_, lean_object* v_params_x27_2101_, lean_object* v_fst_2102_, lean_object* v_discrs_x27_2103_, lean_object* v_fst_2104_, lean_object* v_toPure_2105_, lean_object* v_____do__lift_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__22(v_fst_2092_, v_numParams_2093_, v_numDiscrs_2094_, v_altInfos_2095_, v_uElimPos_x3f_2096_, v_snd_2097_, v_overlaps_2098_, v_matcherName_2099_, v_matcherLevels_2100_, v_params_x27_2101_, v_fst_2102_, v_discrs_x27_2103_, v_fst_2104_, v_toPure_2105_, v_____do__lift_2106_);
lean_dec_ref(v_____do__lift_2106_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23(lean_object* v_fst_2108_, lean_object* v_numParams_2109_, lean_object* v_numDiscrs_2110_, lean_object* v_altInfos_2111_, lean_object* v_uElimPos_x3f_2112_, lean_object* v_snd_2113_, lean_object* v_overlaps_2114_, lean_object* v_matcherName_2115_, lean_object* v_matcherLevels_2116_, lean_object* v_params_x27_2117_, lean_object* v_fst_2118_, lean_object* v_discrs_x27_2119_, lean_object* v_toPure_2120_, lean_object* v_onRemaining_2121_, lean_object* v_remaining_2122_, lean_object* v_toBind_2123_, lean_object* v_____s_2124_){
_start:
{
lean_object* v_fst_2125_; lean_object* v___f_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v_fst_2125_ = lean_ctor_get(v_____s_2124_, 0);
lean_inc(v_fst_2125_);
lean_dec_ref(v_____s_2124_);
v___f_2126_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__22___boxed), 15, 14);
lean_closure_set(v___f_2126_, 0, v_fst_2108_);
lean_closure_set(v___f_2126_, 1, v_numParams_2109_);
lean_closure_set(v___f_2126_, 2, v_numDiscrs_2110_);
lean_closure_set(v___f_2126_, 3, v_altInfos_2111_);
lean_closure_set(v___f_2126_, 4, v_uElimPos_x3f_2112_);
lean_closure_set(v___f_2126_, 5, v_snd_2113_);
lean_closure_set(v___f_2126_, 6, v_overlaps_2114_);
lean_closure_set(v___f_2126_, 7, v_matcherName_2115_);
lean_closure_set(v___f_2126_, 8, v_matcherLevels_2116_);
lean_closure_set(v___f_2126_, 9, v_params_x27_2117_);
lean_closure_set(v___f_2126_, 10, v_fst_2118_);
lean_closure_set(v___f_2126_, 11, v_discrs_x27_2119_);
lean_closure_set(v___f_2126_, 12, v_fst_2125_);
lean_closure_set(v___f_2126_, 13, v_toPure_2120_);
v___x_2127_ = lean_apply_1(v_onRemaining_2121_, v_remaining_2122_);
v___x_2128_ = lean_apply_4(v_toBind_2123_, lean_box(0), lean_box(0), v___x_2127_, v___f_2126_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed(lean_object** _args){
lean_object* v_fst_2129_ = _args[0];
lean_object* v_numParams_2130_ = _args[1];
lean_object* v_numDiscrs_2131_ = _args[2];
lean_object* v_altInfos_2132_ = _args[3];
lean_object* v_uElimPos_x3f_2133_ = _args[4];
lean_object* v_snd_2134_ = _args[5];
lean_object* v_overlaps_2135_ = _args[6];
lean_object* v_matcherName_2136_ = _args[7];
lean_object* v_matcherLevels_2137_ = _args[8];
lean_object* v_params_x27_2138_ = _args[9];
lean_object* v_fst_2139_ = _args[10];
lean_object* v_discrs_x27_2140_ = _args[11];
lean_object* v_toPure_2141_ = _args[12];
lean_object* v_onRemaining_2142_ = _args[13];
lean_object* v_remaining_2143_ = _args[14];
lean_object* v_toBind_2144_ = _args[15];
lean_object* v_____s_2145_ = _args[16];
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__23(v_fst_2129_, v_numParams_2130_, v_numDiscrs_2131_, v_altInfos_2132_, v_uElimPos_x3f_2133_, v_snd_2134_, v_overlaps_2135_, v_matcherName_2136_, v_matcherLevels_2137_, v_params_x27_2138_, v_fst_2139_, v_discrs_x27_2140_, v_toPure_2141_, v_onRemaining_2142_, v_remaining_2143_, v_toBind_2144_, v_____s_2145_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__24(lean_object* v_toPure_2147_, lean_object* v_next_2148_, lean_object* v_G_2149_, lean_object* v_____do__lift_2150_){
_start:
{
if (lean_obj_tag(v_____do__lift_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2152_; 
lean_dec(v_G_2149_);
v_a_2151_ = lean_ctor_get(v_____do__lift_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref_known(v_____do__lift_2150_, 1);
v___x_2152_ = lean_apply_2(v_toPure_2147_, lean_box(0), v_a_2151_);
return v___x_2152_;
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
lean_dec(v_toPure_2147_);
v_a_2153_ = lean_ctor_get(v_____do__lift_2150_, 0);
lean_inc(v_a_2153_);
lean_dec_ref_known(v_____do__lift_2150_, 1);
v___x_2154_ = lean_unsigned_to_nat(1u);
v___x_2155_ = lean_nat_add(v_next_2148_, v___x_2154_);
v___x_2156_ = lean_apply_4(v_G_2149_, v___x_2155_, v_a_2153_, lean_box(0), lean_box(0));
return v___x_2156_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__24___boxed(lean_object* v_toPure_2157_, lean_object* v_next_2158_, lean_object* v_G_2159_, lean_object* v_____do__lift_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__24(v_toPure_2157_, v_next_2158_, v_G_2159_, v_____do__lift_2160_);
lean_dec(v_next_2158_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25(lean_object* v_xs_2162_, lean_object* v_ys4_2163_, uint8_t v___x_2164_, uint8_t v___x_2165_, lean_object* v_inst_2166_, lean_object* v_alt_x27_2167_){
_start:
{
lean_object* v___x_2168_; uint8_t v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2168_ = l_Array_append___redArg(v_xs_2162_, v_ys4_2163_);
v___x_2169_ = 1;
v___x_2170_ = lean_box(v___x_2164_);
v___x_2171_ = lean_box(v___x_2165_);
v___x_2172_ = lean_box(v___x_2164_);
v___x_2173_ = lean_box(v___x_2165_);
v___x_2174_ = lean_box(v___x_2169_);
v___x_2175_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_2175_, 0, v___x_2168_);
lean_closure_set(v___x_2175_, 1, v_alt_x27_2167_);
lean_closure_set(v___x_2175_, 2, v___x_2170_);
lean_closure_set(v___x_2175_, 3, v___x_2171_);
lean_closure_set(v___x_2175_, 4, v___x_2172_);
lean_closure_set(v___x_2175_, 5, v___x_2173_);
lean_closure_set(v___x_2175_, 6, v___x_2174_);
v___x_2176_ = lean_apply_2(v_inst_2166_, lean_box(0), v___x_2175_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25___boxed(lean_object* v_xs_2177_, lean_object* v_ys4_2178_, lean_object* v___x_2179_, lean_object* v___x_2180_, lean_object* v_inst_2181_, lean_object* v_alt_x27_2182_){
_start:
{
uint8_t v___x_13117__boxed_2183_; uint8_t v___x_13118__boxed_2184_; lean_object* v_res_2185_; 
v___x_13117__boxed_2183_ = lean_unbox(v___x_2179_);
v___x_13118__boxed_2184_ = lean_unbox(v___x_2180_);
v_res_2185_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__25(v_xs_2177_, v_ys4_2178_, v___x_13117__boxed_2183_, v___x_13118__boxed_2184_, v_inst_2181_, v_alt_x27_2182_);
lean_dec_ref(v_ys4_2178_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26(lean_object* v_xs_2186_, lean_object* v_remaining_x27_2187_, lean_object* v_ys4_2188_, lean_object* v_onAlt_2189_, lean_object* v_next_2190_, lean_object* v_altType_2191_, lean_object* v_toBind_2192_, lean_object* v___f_2193_, lean_object* v_alt_2194_){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
lean_inc_ref(v_remaining_x27_2187_);
lean_inc_ref(v_xs_2186_);
v___x_2195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2195_, 0, v_xs_2186_);
lean_ctor_set(v___x_2195_, 1, v_xs_2186_);
lean_ctor_set(v___x_2195_, 2, v_remaining_x27_2187_);
lean_ctor_set(v___x_2195_, 3, v_remaining_x27_2187_);
lean_ctor_set(v___x_2195_, 4, v_ys4_2188_);
v___x_2196_ = lean_apply_4(v_onAlt_2189_, v_next_2190_, v_altType_2191_, v___x_2195_, v_alt_2194_);
v___x_2197_ = lean_apply_4(v_toBind_2192_, lean_box(0), lean_box(0), v___x_2196_, v___f_2193_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27(lean_object* v___x_2198_, lean_object* v_xs_2199_, lean_object* v_inst_2200_, lean_object* v_toBind_2201_, lean_object* v___f_2202_, lean_object* v_inst_2203_, lean_object* v_inst_2204_, lean_object* v_names_2205_){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
lean_inc_ref(v_xs_2199_);
v___x_2206_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLambda___boxed), 7, 2);
lean_closure_set(v___x_2206_, 0, v___x_2198_);
lean_closure_set(v___x_2206_, 1, v_xs_2199_);
v___x_2207_ = lean_apply_2(v_inst_2200_, lean_box(0), v___x_2206_);
v___x_2208_ = lean_apply_4(v_toBind_2201_, lean_box(0), lean_box(0), v___x_2207_, v___f_2202_);
v___x_2209_ = l_Lean_Meta_MatcherApp_withUserNames___redArg(v_inst_2203_, v_inst_2204_, v_xs_2199_, v_names_2205_, v___x_2208_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__28(lean_object* v_xs_2210_, uint8_t v___x_2211_, uint8_t v___x_2212_, lean_object* v_inst_2213_, lean_object* v_remaining_x27_2214_, lean_object* v_onAlt_2215_, lean_object* v_next_2216_, lean_object* v_toBind_2217_, lean_object* v___x_2218_, lean_object* v_inst_2219_, lean_object* v_inst_2220_, lean_object* v___f_2221_, lean_object* v_ys4_2222_, lean_object* v_altType_2223_){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___f_2226_; lean_object* v___f_2227_; lean_object* v___f_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2224_ = lean_box(v___x_2211_);
v___x_2225_ = lean_box(v___x_2212_);
lean_inc(v_inst_2213_);
lean_inc_ref(v_ys4_2222_);
lean_inc_ref_n(v_xs_2210_, 2);
v___f_2226_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__25___boxed), 6, 5);
lean_closure_set(v___f_2226_, 0, v_xs_2210_);
lean_closure_set(v___f_2226_, 1, v_ys4_2222_);
lean_closure_set(v___f_2226_, 2, v___x_2224_);
lean_closure_set(v___f_2226_, 3, v___x_2225_);
lean_closure_set(v___f_2226_, 4, v_inst_2213_);
lean_inc_n(v_toBind_2217_, 2);
v___f_2227_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__26), 9, 8);
lean_closure_set(v___f_2227_, 0, v_xs_2210_);
lean_closure_set(v___f_2227_, 1, v_remaining_x27_2214_);
lean_closure_set(v___f_2227_, 2, v_ys4_2222_);
lean_closure_set(v___f_2227_, 3, v_onAlt_2215_);
lean_closure_set(v___f_2227_, 4, v_next_2216_);
lean_closure_set(v___f_2227_, 5, v_altType_2223_);
lean_closure_set(v___f_2227_, 6, v_toBind_2217_);
lean_closure_set(v___f_2227_, 7, v___f_2226_);
lean_inc_ref(v_inst_2220_);
lean_inc_ref(v_inst_2219_);
lean_inc_ref(v___x_2218_);
v___f_2228_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__27), 8, 7);
lean_closure_set(v___f_2228_, 0, v___x_2218_);
lean_closure_set(v___f_2228_, 1, v_xs_2210_);
lean_closure_set(v___f_2228_, 2, v_inst_2213_);
lean_closure_set(v___f_2228_, 3, v_toBind_2217_);
lean_closure_set(v___f_2228_, 4, v___f_2227_);
lean_closure_set(v___f_2228_, 5, v_inst_2219_);
lean_closure_set(v___f_2228_, 6, v_inst_2220_);
v___x_2229_ = l_Lean_Meta_lambdaTelescope___redArg(v_inst_2219_, v_inst_2220_, v___x_2218_, v___f_2221_, v___x_2211_);
v___x_2230_ = lean_apply_4(v_toBind_2217_, lean_box(0), lean_box(0), v___x_2229_, v___f_2228_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__28___boxed(lean_object* v_xs_2231_, lean_object* v___x_2232_, lean_object* v___x_2233_, lean_object* v_inst_2234_, lean_object* v_remaining_x27_2235_, lean_object* v_onAlt_2236_, lean_object* v_next_2237_, lean_object* v_toBind_2238_, lean_object* v___x_2239_, lean_object* v_inst_2240_, lean_object* v_inst_2241_, lean_object* v___f_2242_, lean_object* v_ys4_2243_, lean_object* v_altType_2244_){
_start:
{
uint8_t v___x_13170__boxed_2245_; uint8_t v___x_13171__boxed_2246_; lean_object* v_res_2247_; 
v___x_13170__boxed_2245_ = lean_unbox(v___x_2232_);
v___x_13171__boxed_2246_ = lean_unbox(v___x_2233_);
v_res_2247_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__28(v_xs_2231_, v___x_13170__boxed_2245_, v___x_13171__boxed_2246_, v_inst_2234_, v_remaining_x27_2235_, v_onAlt_2236_, v_next_2237_, v_toBind_2238_, v___x_2239_, v_inst_2240_, v_inst_2241_, v___f_2242_, v_ys4_2243_, v_altType_2244_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29(uint8_t v___x_2248_, uint8_t v___x_2249_, lean_object* v_inst_2250_, lean_object* v_remaining_x27_2251_, lean_object* v_onAlt_2252_, lean_object* v_next_2253_, lean_object* v_toBind_2254_, lean_object* v___x_2255_, lean_object* v_inst_2256_, lean_object* v_inst_2257_, lean_object* v___f_2258_, lean_object* v_fst_2259_, lean_object* v_xs_2260_, lean_object* v_altType_2261_){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___f_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2262_ = lean_box(v___x_2248_);
v___x_2263_ = lean_box(v___x_2249_);
lean_inc_ref(v_inst_2257_);
lean_inc_ref(v_inst_2256_);
v___f_2264_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__28___boxed), 14, 12);
lean_closure_set(v___f_2264_, 0, v_xs_2260_);
lean_closure_set(v___f_2264_, 1, v___x_2262_);
lean_closure_set(v___f_2264_, 2, v___x_2263_);
lean_closure_set(v___f_2264_, 3, v_inst_2250_);
lean_closure_set(v___f_2264_, 4, v_remaining_x27_2251_);
lean_closure_set(v___f_2264_, 5, v_onAlt_2252_);
lean_closure_set(v___f_2264_, 6, v_next_2253_);
lean_closure_set(v___f_2264_, 7, v_toBind_2254_);
lean_closure_set(v___f_2264_, 8, v___x_2255_);
lean_closure_set(v___f_2264_, 9, v_inst_2256_);
lean_closure_set(v___f_2264_, 10, v_inst_2257_);
lean_closure_set(v___f_2264_, 11, v___f_2258_);
v___x_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2265_, 0, v_fst_2259_);
v___x_2266_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2256_, v_inst_2257_, v_altType_2261_, v___x_2265_, v___f_2264_, v___x_2248_, v___x_2248_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29___boxed(lean_object* v___x_2267_, lean_object* v___x_2268_, lean_object* v_inst_2269_, lean_object* v_remaining_x27_2270_, lean_object* v_onAlt_2271_, lean_object* v_next_2272_, lean_object* v_toBind_2273_, lean_object* v___x_2274_, lean_object* v_inst_2275_, lean_object* v_inst_2276_, lean_object* v___f_2277_, lean_object* v_fst_2278_, lean_object* v_xs_2279_, lean_object* v_altType_2280_){
_start:
{
uint8_t v___x_13205__boxed_2281_; uint8_t v___x_13206__boxed_2282_; lean_object* v_res_2283_; 
v___x_13205__boxed_2281_ = lean_unbox(v___x_2267_);
v___x_13206__boxed_2282_ = lean_unbox(v___x_2268_);
v_res_2283_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__29(v___x_13205__boxed_2281_, v___x_13206__boxed_2282_, v_inst_2269_, v_remaining_x27_2270_, v_onAlt_2271_, v_next_2272_, v_toBind_2273_, v___x_2274_, v_inst_2275_, v_inst_2276_, v___f_2277_, v_fst_2278_, v_xs_2279_, v_altType_2280_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__30(lean_object* v_fst_2284_, lean_object* v___x_2285_, lean_object* v___x_2286_, lean_object* v___x_2287_, lean_object* v_toPure_2288_, lean_object* v_alt_x27_2289_){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2290_ = lean_array_push(v_fst_2284_, v_alt_x27_2289_);
v___x_2291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2285_);
lean_ctor_set(v___x_2291_, 1, v___x_2286_);
v___x_2292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2287_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
v___x_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2290_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
v___x_2295_ = lean_apply_2(v_toPure_2288_, lean_box(0), v___x_2294_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31(lean_object* v___x_2296_, lean_object* v_toPure_2297_, lean_object* v_toBind_2298_, lean_object* v___f_2299_, uint8_t v___x_2300_, uint8_t v___x_2301_, lean_object* v_inst_2302_, lean_object* v_remaining_x27_2303_, lean_object* v_onAlt_2304_, lean_object* v_inst_2305_, lean_object* v_inst_2306_, lean_object* v___f_2307_, lean_object* v_fst_2308_, lean_object* v_next_2309_, lean_object* v_acc_2310_, lean_object* v_h_2311_, lean_object* v_G_2312_){
_start:
{
uint8_t v___x_2313_; 
v___x_2313_ = lean_nat_dec_lt(v_next_2309_, v___x_2296_);
if (v___x_2313_ == 0)
{
lean_object* v___x_2314_; 
lean_dec(v_G_2312_);
lean_dec(v_next_2309_);
lean_dec(v_fst_2308_);
lean_dec(v___f_2307_);
lean_dec_ref(v_inst_2306_);
lean_dec_ref(v_inst_2305_);
lean_dec(v_onAlt_2304_);
lean_dec_ref(v_remaining_x27_2303_);
lean_dec(v_inst_2302_);
lean_dec(v___f_2299_);
lean_dec(v_toBind_2298_);
v___x_2314_ = lean_apply_2(v_toPure_2297_, lean_box(0), v_acc_2310_);
return v___x_2314_;
}
else
{
lean_object* v_snd_2315_; lean_object* v_snd_2316_; lean_object* v_snd_2317_; lean_object* v_fst_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2428_; 
v_snd_2315_ = lean_ctor_get(v_acc_2310_, 1);
lean_inc(v_snd_2315_);
v_snd_2316_ = lean_ctor_get(v_snd_2315_, 1);
lean_inc(v_snd_2316_);
v_snd_2317_ = lean_ctor_get(v_snd_2316_, 1);
lean_inc(v_snd_2317_);
v_fst_2318_ = lean_ctor_get(v_acc_2310_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v_acc_2310_);
if (v_isSharedCheck_2428_ == 0)
{
lean_object* v_unused_2429_; 
v_unused_2429_ = lean_ctor_get(v_acc_2310_, 1);
lean_dec(v_unused_2429_);
v___x_2320_ = v_acc_2310_;
v_isShared_2321_ = v_isSharedCheck_2428_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_fst_2318_);
lean_dec(v_acc_2310_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2428_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v_fst_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2426_; 
v_fst_2322_ = lean_ctor_get(v_snd_2315_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v_snd_2315_);
if (v_isSharedCheck_2426_ == 0)
{
lean_object* v_unused_2427_; 
v_unused_2427_ = lean_ctor_get(v_snd_2315_, 1);
lean_dec(v_unused_2427_);
v___x_2324_ = v_snd_2315_;
v_isShared_2325_ = v_isSharedCheck_2426_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_fst_2322_);
lean_dec(v_snd_2315_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2426_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v_fst_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2424_; 
v_fst_2326_ = lean_ctor_get(v_snd_2316_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v_snd_2316_);
if (v_isSharedCheck_2424_ == 0)
{
lean_object* v_unused_2425_; 
v_unused_2425_ = lean_ctor_get(v_snd_2316_, 1);
lean_dec(v_unused_2425_);
v___x_2328_ = v_snd_2316_;
v_isShared_2329_ = v_isSharedCheck_2424_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_fst_2326_);
lean_dec(v_snd_2316_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2424_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v_array_2330_; lean_object* v_start_2331_; lean_object* v_stop_2332_; lean_object* v___f_2333_; lean_object* v___y_2335_; uint8_t v___x_2338_; 
v_array_2330_ = lean_ctor_get(v_snd_2317_, 0);
v_start_2331_ = lean_ctor_get(v_snd_2317_, 1);
v_stop_2332_ = lean_ctor_get(v_snd_2317_, 2);
lean_inc(v_next_2309_);
lean_inc(v_toPure_2297_);
v___f_2333_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__24___boxed), 4, 3);
lean_closure_set(v___f_2333_, 0, v_toPure_2297_);
lean_closure_set(v___f_2333_, 1, v_next_2309_);
lean_closure_set(v___f_2333_, 2, v_G_2312_);
v___x_2338_ = lean_nat_dec_lt(v_start_2331_, v_stop_2332_);
if (v___x_2338_ == 0)
{
lean_object* v___x_2340_; 
lean_dec(v_next_2309_);
lean_dec(v_fst_2308_);
lean_dec(v___f_2307_);
lean_dec_ref(v_inst_2306_);
lean_dec_ref(v_inst_2305_);
lean_dec(v_onAlt_2304_);
lean_dec_ref(v_remaining_x27_2303_);
lean_dec(v_inst_2302_);
if (v_isShared_2329_ == 0)
{
v___x_2340_ = v___x_2328_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_fst_2326_);
lean_ctor_set(v_reuseFailAlloc_2349_, 1, v_snd_2317_);
v___x_2340_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
lean_object* v___x_2342_; 
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 1, v___x_2340_);
v___x_2342_ = v___x_2324_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_fst_2322_);
lean_ctor_set(v_reuseFailAlloc_2348_, 1, v___x_2340_);
v___x_2342_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
lean_object* v___x_2344_; 
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 1, v___x_2342_);
v___x_2344_ = v___x_2320_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_fst_2318_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v___x_2342_);
v___x_2344_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
v___x_2346_ = lean_apply_2(v_toPure_2297_, lean_box(0), v___x_2345_);
v___y_2335_ = v___x_2346_;
goto v___jp_2334_;
}
}
}
}
else
{
lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2420_; 
lean_inc(v_stop_2332_);
lean_inc(v_start_2331_);
lean_inc_ref(v_array_2330_);
v_isSharedCheck_2420_ = !lean_is_exclusive(v_snd_2317_);
if (v_isSharedCheck_2420_ == 0)
{
lean_object* v_unused_2421_; lean_object* v_unused_2422_; lean_object* v_unused_2423_; 
v_unused_2421_ = lean_ctor_get(v_snd_2317_, 2);
lean_dec(v_unused_2421_);
v_unused_2422_ = lean_ctor_get(v_snd_2317_, 1);
lean_dec(v_unused_2422_);
v_unused_2423_ = lean_ctor_get(v_snd_2317_, 0);
lean_dec(v_unused_2423_);
v___x_2351_ = v_snd_2317_;
v_isShared_2352_ = v_isSharedCheck_2420_;
goto v_resetjp_2350_;
}
else
{
lean_dec(v_snd_2317_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2420_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v_array_2353_; lean_object* v_start_2354_; lean_object* v_stop_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2360_; 
v_array_2353_ = lean_ctor_get(v_fst_2326_, 0);
v_start_2354_ = lean_ctor_get(v_fst_2326_, 1);
v_stop_2355_ = lean_ctor_get(v_fst_2326_, 2);
v___x_2356_ = lean_array_fget(v_array_2330_, v_start_2331_);
v___x_2357_ = lean_unsigned_to_nat(1u);
v___x_2358_ = lean_nat_add(v_start_2331_, v___x_2357_);
lean_dec(v_start_2331_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 1, v___x_2358_);
v___x_2360_ = v___x_2351_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_array_2330_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v___x_2358_);
lean_ctor_set(v_reuseFailAlloc_2419_, 2, v_stop_2332_);
v___x_2360_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
uint8_t v___x_2361_; 
v___x_2361_ = lean_nat_dec_lt(v_start_2354_, v_stop_2355_);
if (v___x_2361_ == 0)
{
lean_object* v___x_2363_; 
lean_dec(v___x_2356_);
lean_dec(v_next_2309_);
lean_dec(v_fst_2308_);
lean_dec(v___f_2307_);
lean_dec_ref(v_inst_2306_);
lean_dec_ref(v_inst_2305_);
lean_dec(v_onAlt_2304_);
lean_dec_ref(v_remaining_x27_2303_);
lean_dec(v_inst_2302_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 1, v___x_2360_);
v___x_2363_ = v___x_2328_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_fst_2326_);
lean_ctor_set(v_reuseFailAlloc_2372_, 1, v___x_2360_);
v___x_2363_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2365_; 
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 1, v___x_2363_);
v___x_2365_ = v___x_2324_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_fst_2322_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v___x_2363_);
v___x_2365_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
lean_object* v___x_2367_; 
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 1, v___x_2365_);
v___x_2367_ = v___x_2320_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_fst_2318_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v___x_2365_);
v___x_2367_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
v___x_2369_ = lean_apply_2(v_toPure_2297_, lean_box(0), v___x_2368_);
v___y_2335_ = v___x_2369_;
goto v___jp_2334_;
}
}
}
}
else
{
lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2415_; 
lean_inc(v_stop_2355_);
lean_inc(v_start_2354_);
lean_inc_ref(v_array_2353_);
v_isSharedCheck_2415_ = !lean_is_exclusive(v_fst_2326_);
if (v_isSharedCheck_2415_ == 0)
{
lean_object* v_unused_2416_; lean_object* v_unused_2417_; lean_object* v_unused_2418_; 
v_unused_2416_ = lean_ctor_get(v_fst_2326_, 2);
lean_dec(v_unused_2416_);
v_unused_2417_ = lean_ctor_get(v_fst_2326_, 1);
lean_dec(v_unused_2417_);
v_unused_2418_ = lean_ctor_get(v_fst_2326_, 0);
lean_dec(v_unused_2418_);
v___x_2374_ = v_fst_2326_;
v_isShared_2375_ = v_isSharedCheck_2415_;
goto v_resetjp_2373_;
}
else
{
lean_dec(v_fst_2326_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2415_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v_array_2376_; lean_object* v_start_2377_; lean_object* v_stop_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2382_; 
v_array_2376_ = lean_ctor_get(v_fst_2322_, 0);
v_start_2377_ = lean_ctor_get(v_fst_2322_, 1);
v_stop_2378_ = lean_ctor_get(v_fst_2322_, 2);
v___x_2379_ = lean_array_fget(v_array_2353_, v_start_2354_);
v___x_2380_ = lean_nat_add(v_start_2354_, v___x_2357_);
lean_dec(v_start_2354_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set(v___x_2374_, 1, v___x_2380_);
v___x_2382_ = v___x_2374_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_array_2353_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v___x_2380_);
lean_ctor_set(v_reuseFailAlloc_2414_, 2, v_stop_2355_);
v___x_2382_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
uint8_t v___x_2383_; 
v___x_2383_ = lean_nat_dec_lt(v_start_2377_, v_stop_2378_);
if (v___x_2383_ == 0)
{
lean_object* v___x_2385_; 
lean_dec(v___x_2379_);
lean_dec(v___x_2356_);
lean_dec(v_next_2309_);
lean_dec(v_fst_2308_);
lean_dec(v___f_2307_);
lean_dec_ref(v_inst_2306_);
lean_dec_ref(v_inst_2305_);
lean_dec(v_onAlt_2304_);
lean_dec_ref(v_remaining_x27_2303_);
lean_dec(v_inst_2302_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 1, v___x_2360_);
lean_ctor_set(v___x_2328_, 0, v___x_2382_);
v___x_2385_ = v___x_2328_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2382_);
lean_ctor_set(v_reuseFailAlloc_2394_, 1, v___x_2360_);
v___x_2385_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2387_; 
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 1, v___x_2385_);
v___x_2387_ = v___x_2324_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_fst_2322_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v___x_2385_);
v___x_2387_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
lean_object* v___x_2389_; 
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 1, v___x_2387_);
v___x_2389_ = v___x_2320_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_fst_2318_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v___x_2387_);
v___x_2389_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
v___x_2391_ = lean_apply_2(v_toPure_2297_, lean_box(0), v___x_2390_);
v___y_2335_ = v___x_2391_;
goto v___jp_2334_;
}
}
}
}
else
{
lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2410_; 
lean_inc(v_stop_2378_);
lean_inc(v_start_2377_);
lean_inc_ref(v_array_2376_);
lean_del_object(v___x_2328_);
lean_del_object(v___x_2324_);
lean_del_object(v___x_2320_);
v_isSharedCheck_2410_ = !lean_is_exclusive(v_fst_2322_);
if (v_isSharedCheck_2410_ == 0)
{
lean_object* v_unused_2411_; lean_object* v_unused_2412_; lean_object* v_unused_2413_; 
v_unused_2411_ = lean_ctor_get(v_fst_2322_, 2);
lean_dec(v_unused_2411_);
v_unused_2412_ = lean_ctor_get(v_fst_2322_, 1);
lean_dec(v_unused_2412_);
v_unused_2413_ = lean_ctor_get(v_fst_2322_, 0);
lean_dec(v_unused_2413_);
v___x_2396_ = v_fst_2322_;
v_isShared_2397_ = v_isSharedCheck_2410_;
goto v_resetjp_2395_;
}
else
{
lean_dec(v_fst_2322_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2410_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___f_2401_; lean_object* v___x_2402_; lean_object* v___x_2404_; 
v___x_2398_ = lean_array_fget_borrowed(v_array_2376_, v_start_2377_);
v___x_2399_ = lean_box(v___x_2300_);
v___x_2400_ = lean_box(v___x_2301_);
lean_inc_ref(v_inst_2306_);
lean_inc_ref(v_inst_2305_);
lean_inc(v___x_2398_);
lean_inc(v_toBind_2298_);
v___f_2401_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__29___boxed), 14, 12);
lean_closure_set(v___f_2401_, 0, v___x_2399_);
lean_closure_set(v___f_2401_, 1, v___x_2400_);
lean_closure_set(v___f_2401_, 2, v_inst_2302_);
lean_closure_set(v___f_2401_, 3, v_remaining_x27_2303_);
lean_closure_set(v___f_2401_, 4, v_onAlt_2304_);
lean_closure_set(v___f_2401_, 5, v_next_2309_);
lean_closure_set(v___f_2401_, 6, v_toBind_2298_);
lean_closure_set(v___f_2401_, 7, v___x_2398_);
lean_closure_set(v___f_2401_, 8, v_inst_2305_);
lean_closure_set(v___f_2401_, 9, v_inst_2306_);
lean_closure_set(v___f_2401_, 10, v___f_2307_);
lean_closure_set(v___f_2401_, 11, v_fst_2308_);
v___x_2402_ = lean_nat_add(v_start_2377_, v___x_2357_);
lean_dec(v_start_2377_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 1, v___x_2402_);
v___x_2404_ = v___x_2396_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_array_2376_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v___x_2402_);
lean_ctor_set(v_reuseFailAlloc_2409_, 2, v_stop_2378_);
v___x_2404_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
lean_object* v___f_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___f_2405_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__30), 6, 5);
lean_closure_set(v___f_2405_, 0, v_fst_2318_);
lean_closure_set(v___f_2405_, 1, v___x_2382_);
lean_closure_set(v___f_2405_, 2, v___x_2360_);
lean_closure_set(v___f_2405_, 3, v___x_2404_);
lean_closure_set(v___f_2405_, 4, v_toPure_2297_);
v___x_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2379_);
v___x_2407_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2305_, v_inst_2306_, v___x_2356_, v___x_2406_, v___f_2401_, v___x_2300_, v___x_2300_);
lean_inc(v_toBind_2298_);
v___x_2408_ = lean_apply_4(v_toBind_2298_, lean_box(0), lean_box(0), v___x_2407_, v___f_2405_);
v___y_2335_ = v___x_2408_;
goto v___jp_2334_;
}
}
}
}
}
}
}
}
}
v___jp_2334_:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_inc(v_toBind_2298_);
v___x_2336_ = lean_apply_4(v_toBind_2298_, lean_box(0), lean_box(0), v___y_2335_, v___f_2299_);
v___x_2337_ = lean_apply_4(v_toBind_2298_, lean_box(0), lean_box(0), v___x_2336_, v___f_2333_);
return v___x_2337_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed(lean_object** _args){
lean_object* v___x_2430_ = _args[0];
lean_object* v_toPure_2431_ = _args[1];
lean_object* v_toBind_2432_ = _args[2];
lean_object* v___f_2433_ = _args[3];
lean_object* v___x_2434_ = _args[4];
lean_object* v___x_2435_ = _args[5];
lean_object* v_inst_2436_ = _args[6];
lean_object* v_remaining_x27_2437_ = _args[7];
lean_object* v_onAlt_2438_ = _args[8];
lean_object* v_inst_2439_ = _args[9];
lean_object* v_inst_2440_ = _args[10];
lean_object* v___f_2441_ = _args[11];
lean_object* v_fst_2442_ = _args[12];
lean_object* v_next_2443_ = _args[13];
lean_object* v_acc_2444_ = _args[14];
lean_object* v_h_2445_ = _args[15];
lean_object* v_G_2446_ = _args[16];
_start:
{
uint8_t v___x_13256__boxed_2447_; uint8_t v___x_13257__boxed_2448_; lean_object* v_res_2449_; 
v___x_13256__boxed_2447_ = lean_unbox(v___x_2434_);
v___x_13257__boxed_2448_ = lean_unbox(v___x_2435_);
v_res_2449_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__31(v___x_2430_, v_toPure_2431_, v_toBind_2432_, v___f_2433_, v___x_13256__boxed_2447_, v___x_13257__boxed_2448_, v_inst_2436_, v_remaining_x27_2437_, v_onAlt_2438_, v_inst_2439_, v_inst_2440_, v___f_2441_, v_fst_2442_, v_next_2443_, v_acc_2444_, v_h_2445_, v_G_2446_);
lean_dec(v___x_2430_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__32(lean_object* v_matcherApp_2450_, lean_object* v_alts_2451_, lean_object* v___x_2452_, lean_object* v___x_2453_, lean_object* v_remaining_x27_2454_, lean_object* v___f_2455_, lean_object* v_toBind_2456_, lean_object* v___f_2457_, lean_object* v_altTypes_2458_){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2459_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_2450_);
v___x_2460_ = lean_array_get_size(v___x_2459_);
v___x_2461_ = lean_array_get_size(v_altTypes_2458_);
lean_inc_n(v___x_2452_, 3);
v___x_2462_ = l_Array_toSubarray___redArg(v_alts_2451_, v___x_2452_, v___x_2453_);
v___x_2463_ = l_Array_toSubarray___redArg(v___x_2459_, v___x_2452_, v___x_2460_);
v___x_2464_ = l_Array_toSubarray___redArg(v_altTypes_2458_, v___x_2452_, v___x_2461_);
v___x_2465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2463_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
v___x_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2462_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2467_, 0, v_remaining_x27_2454_);
lean_ctor_set(v___x_2467_, 1, v___x_2466_);
v___x_2468_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2455_, v___x_2452_, v___x_2467_, lean_box(0));
v___x_2469_ = lean_apply_4(v_toBind_2456_, lean_box(0), lean_box(0), v___x_2468_, v___f_2457_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33(lean_object* v_alts_2470_, lean_object* v_toPure_2471_, lean_object* v_toBind_2472_, lean_object* v___f_2473_, uint8_t v___x_2474_, uint8_t v___x_2475_, lean_object* v_inst_2476_, lean_object* v_remaining_x27_2477_, lean_object* v_onAlt_2478_, lean_object* v_inst_2479_, lean_object* v_inst_2480_, lean_object* v___f_2481_, lean_object* v_fst_2482_, lean_object* v_matcherApp_2483_, lean_object* v___x_2484_, lean_object* v___f_2485_, lean_object* v_aux_2486_, lean_object* v_____r_2487_){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___f_2491_; lean_object* v___f_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2488_ = lean_array_get_size(v_alts_2470_);
v___x_2489_ = lean_box(v___x_2474_);
v___x_2490_ = lean_box(v___x_2475_);
lean_inc_ref(v_remaining_x27_2477_);
lean_inc(v_inst_2476_);
lean_inc_n(v_toBind_2472_, 2);
v___f_2491_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 17, 13);
lean_closure_set(v___f_2491_, 0, v___x_2488_);
lean_closure_set(v___f_2491_, 1, v_toPure_2471_);
lean_closure_set(v___f_2491_, 2, v_toBind_2472_);
lean_closure_set(v___f_2491_, 3, v___f_2473_);
lean_closure_set(v___f_2491_, 4, v___x_2489_);
lean_closure_set(v___f_2491_, 5, v___x_2490_);
lean_closure_set(v___f_2491_, 6, v_inst_2476_);
lean_closure_set(v___f_2491_, 7, v_remaining_x27_2477_);
lean_closure_set(v___f_2491_, 8, v_onAlt_2478_);
lean_closure_set(v___f_2491_, 9, v_inst_2479_);
lean_closure_set(v___f_2491_, 10, v_inst_2480_);
lean_closure_set(v___f_2491_, 11, v___f_2481_);
lean_closure_set(v___f_2491_, 12, v_fst_2482_);
v___f_2492_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 9, 8);
lean_closure_set(v___f_2492_, 0, v_matcherApp_2483_);
lean_closure_set(v___f_2492_, 1, v_alts_2470_);
lean_closure_set(v___f_2492_, 2, v___x_2484_);
lean_closure_set(v___f_2492_, 3, v___x_2488_);
lean_closure_set(v___f_2492_, 4, v_remaining_x27_2477_);
lean_closure_set(v___f_2492_, 5, v___f_2491_);
lean_closure_set(v___f_2492_, 6, v_toBind_2472_);
lean_closure_set(v___f_2492_, 7, v___f_2485_);
v___x_2493_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_2493_, 0, v___x_2488_);
lean_closure_set(v___x_2493_, 1, v_aux_2486_);
v___x_2494_ = lean_apply_2(v_inst_2476_, lean_box(0), v___x_2493_);
v___x_2495_ = lean_apply_4(v_toBind_2472_, lean_box(0), lean_box(0), v___x_2494_, v___f_2492_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed(lean_object** _args){
lean_object* v_alts_2496_ = _args[0];
lean_object* v_toPure_2497_ = _args[1];
lean_object* v_toBind_2498_ = _args[2];
lean_object* v___f_2499_ = _args[3];
lean_object* v___x_2500_ = _args[4];
lean_object* v___x_2501_ = _args[5];
lean_object* v_inst_2502_ = _args[6];
lean_object* v_remaining_x27_2503_ = _args[7];
lean_object* v_onAlt_2504_ = _args[8];
lean_object* v_inst_2505_ = _args[9];
lean_object* v_inst_2506_ = _args[10];
lean_object* v___f_2507_ = _args[11];
lean_object* v_fst_2508_ = _args[12];
lean_object* v_matcherApp_2509_ = _args[13];
lean_object* v___x_2510_ = _args[14];
lean_object* v___f_2511_ = _args[15];
lean_object* v_aux_2512_ = _args[16];
lean_object* v_____r_2513_ = _args[17];
_start:
{
uint8_t v___x_13513__boxed_2514_; uint8_t v___x_13514__boxed_2515_; lean_object* v_res_2516_; 
v___x_13513__boxed_2514_ = lean_unbox(v___x_2500_);
v___x_13514__boxed_2515_ = lean_unbox(v___x_2501_);
v_res_2516_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__33(v_alts_2496_, v_toPure_2497_, v_toBind_2498_, v___f_2499_, v___x_13513__boxed_2514_, v___x_13514__boxed_2515_, v_inst_2502_, v_remaining_x27_2503_, v_onAlt_2504_, v_inst_2505_, v_inst_2506_, v___f_2507_, v_fst_2508_, v_matcherApp_2509_, v___x_2510_, v___f_2511_, v_aux_2512_, v_____r_2513_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34(lean_object* v___x_2517_, lean_object* v_e_2518_){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = l_Lean_indentD(v_e_2518_);
v___x_2520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2517_);
lean_ctor_set(v___x_2520_, 1, v___x_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35(lean_object* v___x_2521_, lean_object* v___f_2522_, lean_object* v_runInBase_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = lean_apply_2(v_runInBase_2523_, lean_box(0), v___x_2521_);
v___x_2530_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2529_, v___f_2522_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed(lean_object* v___x_2531_, lean_object* v___f_2532_, lean_object* v_runInBase_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__35(v___x_2531_, v___f_2532_, v_runInBase_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__37(lean_object* v_toPure_2540_, lean_object* v_next_2541_, lean_object* v_G_2542_, lean_object* v_____do__lift_2543_){
_start:
{
if (lean_obj_tag(v_____do__lift_2543_) == 0)
{
lean_object* v_a_2544_; lean_object* v___x_2545_; 
lean_dec(v_G_2542_);
v_a_2544_ = lean_ctor_get(v_____do__lift_2543_, 0);
lean_inc(v_a_2544_);
lean_dec_ref_known(v_____do__lift_2543_, 1);
v___x_2545_ = lean_apply_2(v_toPure_2540_, lean_box(0), v_a_2544_);
return v___x_2545_;
}
else
{
lean_object* v_a_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
lean_dec(v_toPure_2540_);
v_a_2546_ = lean_ctor_get(v_____do__lift_2543_, 0);
lean_inc(v_a_2546_);
lean_dec_ref_known(v_____do__lift_2543_, 1);
v___x_2547_ = lean_unsigned_to_nat(1u);
v___x_2548_ = lean_nat_add(v_next_2541_, v___x_2547_);
v___x_2549_ = lean_apply_4(v_G_2542_, v___x_2548_, v_a_2546_, lean_box(0), lean_box(0));
return v___x_2549_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__37___boxed(lean_object* v_toPure_2550_, lean_object* v_next_2551_, lean_object* v_G_2552_, lean_object* v_____do__lift_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__37(v_toPure_2550_, v_next_2551_, v_G_2552_, v_____do__lift_2553_);
lean_dec(v_next_2551_);
return v_res_2554_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__5(void){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2563_ = lean_box(0);
v___x_2564_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__4));
v___x_2565_ = l_Lean_mkConst(v___x_2564_, v___x_2563_);
return v___x_2565_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__6(void){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2566_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__5);
v___x_2567_ = lean_unsigned_to_nat(2u);
v___x_2568_ = lean_mk_empty_array_with_capacity(v___x_2567_);
v___x_2569_ = lean_array_push(v___x_2568_, v___x_2566_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36(lean_object* v___x_2570_, lean_object* v_toPure_2571_, lean_object* v_inst_2572_, lean_object* v_alt_x27_2573_){
_start:
{
uint8_t v_hasUnitThunk_2574_; 
v_hasUnitThunk_2574_ = lean_ctor_get_uint8(v___x_2570_, sizeof(void*)*2);
if (v_hasUnitThunk_2574_ == 0)
{
lean_object* v___x_2575_; 
lean_dec(v_inst_2572_);
v___x_2575_ = lean_apply_2(v_toPure_2571_, lean_box(0), v_alt_x27_2573_);
return v___x_2575_;
}
else
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
lean_dec(v_toPure_2571_);
v___x_2576_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__2));
v___x_2577_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__6);
v___x_2578_ = lean_array_push(v___x_2577_, v_alt_x27_2573_);
v___x_2579_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___boxed), 7, 2);
lean_closure_set(v___x_2579_, 0, v___x_2576_);
lean_closure_set(v___x_2579_, 1, v___x_2578_);
v___x_2580_ = lean_apply_2(v_inst_2572_, lean_box(0), v___x_2579_);
return v___x_2580_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed(lean_object* v___x_2581_, lean_object* v_toPure_2582_, lean_object* v_inst_2583_, lean_object* v_alt_x27_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__36(v___x_2581_, v_toPure_2582_, v_inst_2583_, v_alt_x27_2584_);
lean_dec_ref(v___x_2581_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38(lean_object* v_ys_2586_, lean_object* v_ys2_2587_, lean_object* v_ys3_2588_, lean_object* v_ys4_2589_, uint8_t v___x_2590_, uint8_t v_useSplitter_2591_, lean_object* v_inst_2592_, lean_object* v_alt_x27_2593_){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; uint8_t v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2594_ = l_Array_append___redArg(v_ys_2586_, v_ys2_2587_);
v___x_2595_ = l_Array_append___redArg(v___x_2594_, v_ys3_2588_);
v___x_2596_ = l_Array_append___redArg(v___x_2595_, v_ys4_2589_);
v___x_2597_ = 1;
v___x_2598_ = lean_box(v___x_2590_);
v___x_2599_ = lean_box(v_useSplitter_2591_);
v___x_2600_ = lean_box(v___x_2590_);
v___x_2601_ = lean_box(v_useSplitter_2591_);
v___x_2602_ = lean_box(v___x_2597_);
v___x_2603_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_2603_, 0, v___x_2596_);
lean_closure_set(v___x_2603_, 1, v_alt_x27_2593_);
lean_closure_set(v___x_2603_, 2, v___x_2598_);
lean_closure_set(v___x_2603_, 3, v___x_2599_);
lean_closure_set(v___x_2603_, 4, v___x_2600_);
lean_closure_set(v___x_2603_, 5, v___x_2601_);
lean_closure_set(v___x_2603_, 6, v___x_2602_);
v___x_2604_ = lean_apply_2(v_inst_2592_, lean_box(0), v___x_2603_);
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed(lean_object* v_ys_2605_, lean_object* v_ys2_2606_, lean_object* v_ys3_2607_, lean_object* v_ys4_2608_, lean_object* v___x_2609_, lean_object* v_useSplitter_2610_, lean_object* v_inst_2611_, lean_object* v_alt_x27_2612_){
_start:
{
uint8_t v___x_13667__boxed_2613_; uint8_t v_useSplitter_boxed_2614_; lean_object* v_res_2615_; 
v___x_13667__boxed_2613_ = lean_unbox(v___x_2609_);
v_useSplitter_boxed_2614_ = lean_unbox(v_useSplitter_2610_);
v_res_2615_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__38(v_ys_2605_, v_ys2_2606_, v_ys3_2607_, v_ys4_2608_, v___x_13667__boxed_2613_, v_useSplitter_boxed_2614_, v_inst_2611_, v_alt_x27_2612_);
lean_dec_ref(v_ys4_2608_);
lean_dec_ref(v_ys3_2607_);
lean_dec_ref(v_ys2_2606_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39(lean_object* v_args_2616_, lean_object* v_ys_2617_, lean_object* v_ys2_2618_, lean_object* v_ys3_2619_, lean_object* v_ys4_2620_, lean_object* v_onAlt_2621_, lean_object* v_next_2622_, lean_object* v_altType_2623_, lean_object* v_toBind_2624_, lean_object* v___f_2625_, lean_object* v_alt_2626_){
_start:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2627_, 0, v_args_2616_);
lean_ctor_set(v___x_2627_, 1, v_ys_2617_);
lean_ctor_set(v___x_2627_, 2, v_ys2_2618_);
lean_ctor_set(v___x_2627_, 3, v_ys3_2619_);
lean_ctor_set(v___x_2627_, 4, v_ys4_2620_);
v___x_2628_ = lean_apply_4(v_onAlt_2621_, v_next_2622_, v_altType_2623_, v___x_2627_, v_alt_2626_);
v___x_2629_ = lean_apply_4(v_toBind_2624_, lean_box(0), lean_box(0), v___x_2628_, v___f_2625_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40(lean_object* v_toMonadExceptOf_2630_, lean_object* v_ys_2631_, lean_object* v_ys2_2632_, lean_object* v_ys3_2633_, uint8_t v___x_2634_, uint8_t v_useSplitter_2635_, lean_object* v_inst_2636_, lean_object* v_args_2637_, lean_object* v_onAlt_2638_, lean_object* v_next_2639_, lean_object* v_toBind_2640_, lean_object* v___x_2641_, lean_object* v___f_2642_, lean_object* v_ys4_2643_, lean_object* v_altType_2644_){
_start:
{
lean_object* v_tryCatch_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___f_2648_; lean_object* v___f_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v_tryCatch_2645_ = lean_ctor_get(v_toMonadExceptOf_2630_, 1);
lean_inc(v_tryCatch_2645_);
lean_dec_ref(v_toMonadExceptOf_2630_);
v___x_2646_ = lean_box(v___x_2634_);
v___x_2647_ = lean_box(v_useSplitter_2635_);
lean_inc(v_inst_2636_);
lean_inc_ref(v_ys4_2643_);
lean_inc_ref_n(v_ys3_2633_, 2);
lean_inc_ref(v_ys2_2632_);
lean_inc_ref(v_ys_2631_);
v___f_2648_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed), 8, 7);
lean_closure_set(v___f_2648_, 0, v_ys_2631_);
lean_closure_set(v___f_2648_, 1, v_ys2_2632_);
lean_closure_set(v___f_2648_, 2, v_ys3_2633_);
lean_closure_set(v___f_2648_, 3, v_ys4_2643_);
lean_closure_set(v___f_2648_, 4, v___x_2646_);
lean_closure_set(v___f_2648_, 5, v___x_2647_);
lean_closure_set(v___f_2648_, 6, v_inst_2636_);
lean_inc(v_toBind_2640_);
lean_inc_ref(v_args_2637_);
v___f_2649_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__39), 11, 10);
lean_closure_set(v___f_2649_, 0, v_args_2637_);
lean_closure_set(v___f_2649_, 1, v_ys_2631_);
lean_closure_set(v___f_2649_, 2, v_ys2_2632_);
lean_closure_set(v___f_2649_, 3, v_ys3_2633_);
lean_closure_set(v___f_2649_, 4, v_ys4_2643_);
lean_closure_set(v___f_2649_, 5, v_onAlt_2638_);
lean_closure_set(v___f_2649_, 6, v_next_2639_);
lean_closure_set(v___f_2649_, 7, v_altType_2644_);
lean_closure_set(v___f_2649_, 8, v_toBind_2640_);
lean_closure_set(v___f_2649_, 9, v___f_2648_);
v___x_2650_ = l_Array_append___redArg(v_args_2637_, v_ys3_2633_);
lean_dec_ref(v_ys3_2633_);
v___x_2651_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLambda___boxed), 7, 2);
lean_closure_set(v___x_2651_, 0, v___x_2641_);
lean_closure_set(v___x_2651_, 1, v___x_2650_);
v___x_2652_ = lean_apply_2(v_inst_2636_, lean_box(0), v___x_2651_);
v___x_2653_ = lean_apply_3(v_tryCatch_2645_, lean_box(0), v___x_2652_, v___f_2642_);
v___x_2654_ = lean_apply_4(v_toBind_2640_, lean_box(0), lean_box(0), v___x_2653_, v___f_2649_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed(lean_object* v_toMonadExceptOf_2655_, lean_object* v_ys_2656_, lean_object* v_ys2_2657_, lean_object* v_ys3_2658_, lean_object* v___x_2659_, lean_object* v_useSplitter_2660_, lean_object* v_inst_2661_, lean_object* v_args_2662_, lean_object* v_onAlt_2663_, lean_object* v_next_2664_, lean_object* v_toBind_2665_, lean_object* v___x_2666_, lean_object* v___f_2667_, lean_object* v_ys4_2668_, lean_object* v_altType_2669_){
_start:
{
uint8_t v___x_13703__boxed_2670_; uint8_t v_useSplitter_boxed_2671_; lean_object* v_res_2672_; 
v___x_13703__boxed_2670_ = lean_unbox(v___x_2659_);
v_useSplitter_boxed_2671_ = lean_unbox(v_useSplitter_2660_);
v_res_2672_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__40(v_toMonadExceptOf_2655_, v_ys_2656_, v_ys2_2657_, v_ys3_2658_, v___x_13703__boxed_2670_, v_useSplitter_boxed_2671_, v_inst_2661_, v_args_2662_, v_onAlt_2663_, v_next_2664_, v_toBind_2665_, v___x_2666_, v___f_2667_, v_ys4_2668_, v_altType_2669_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41(lean_object* v_toMonadExceptOf_2673_, lean_object* v_ys_2674_, lean_object* v_ys2_2675_, uint8_t v___x_2676_, uint8_t v_useSplitter_2677_, lean_object* v_inst_2678_, lean_object* v_args_2679_, lean_object* v_onAlt_2680_, lean_object* v_next_2681_, lean_object* v_toBind_2682_, lean_object* v___x_2683_, lean_object* v___f_2684_, lean_object* v_fst_2685_, lean_object* v_inst_2686_, lean_object* v_inst_2687_, lean_object* v_ys3_2688_, lean_object* v_altType_2689_){
_start:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___f_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2690_ = lean_box(v___x_2676_);
v___x_2691_ = lean_box(v_useSplitter_2677_);
v___f_2692_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed), 15, 13);
lean_closure_set(v___f_2692_, 0, v_toMonadExceptOf_2673_);
lean_closure_set(v___f_2692_, 1, v_ys_2674_);
lean_closure_set(v___f_2692_, 2, v_ys2_2675_);
lean_closure_set(v___f_2692_, 3, v_ys3_2688_);
lean_closure_set(v___f_2692_, 4, v___x_2690_);
lean_closure_set(v___f_2692_, 5, v___x_2691_);
lean_closure_set(v___f_2692_, 6, v_inst_2678_);
lean_closure_set(v___f_2692_, 7, v_args_2679_);
lean_closure_set(v___f_2692_, 8, v_onAlt_2680_);
lean_closure_set(v___f_2692_, 9, v_next_2681_);
lean_closure_set(v___f_2692_, 10, v_toBind_2682_);
lean_closure_set(v___f_2692_, 11, v___x_2683_);
lean_closure_set(v___f_2692_, 12, v___f_2684_);
v___x_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2693_, 0, v_fst_2685_);
v___x_2694_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2686_, v_inst_2687_, v_altType_2689_, v___x_2693_, v___f_2692_, v___x_2676_, v___x_2676_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed(lean_object** _args){
lean_object* v_toMonadExceptOf_2695_ = _args[0];
lean_object* v_ys_2696_ = _args[1];
lean_object* v_ys2_2697_ = _args[2];
lean_object* v___x_2698_ = _args[3];
lean_object* v_useSplitter_2699_ = _args[4];
lean_object* v_inst_2700_ = _args[5];
lean_object* v_args_2701_ = _args[6];
lean_object* v_onAlt_2702_ = _args[7];
lean_object* v_next_2703_ = _args[8];
lean_object* v_toBind_2704_ = _args[9];
lean_object* v___x_2705_ = _args[10];
lean_object* v___f_2706_ = _args[11];
lean_object* v_fst_2707_ = _args[12];
lean_object* v_inst_2708_ = _args[13];
lean_object* v_inst_2709_ = _args[14];
lean_object* v_ys3_2710_ = _args[15];
lean_object* v_altType_2711_ = _args[16];
_start:
{
uint8_t v___x_13733__boxed_2712_; uint8_t v_useSplitter_boxed_2713_; lean_object* v_res_2714_; 
v___x_13733__boxed_2712_ = lean_unbox(v___x_2698_);
v_useSplitter_boxed_2713_ = lean_unbox(v_useSplitter_2699_);
v_res_2714_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__41(v_toMonadExceptOf_2695_, v_ys_2696_, v_ys2_2697_, v___x_13733__boxed_2712_, v_useSplitter_boxed_2713_, v_inst_2700_, v_args_2701_, v_onAlt_2702_, v_next_2703_, v_toBind_2704_, v___x_2705_, v___f_2706_, v_fst_2707_, v_inst_2708_, v_inst_2709_, v_ys3_2710_, v_altType_2711_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__42(lean_object* v_toMonadExceptOf_2715_, lean_object* v_ys_2716_, uint8_t v___x_2717_, uint8_t v_useSplitter_2718_, lean_object* v_inst_2719_, lean_object* v_args_2720_, lean_object* v_onAlt_2721_, lean_object* v_next_2722_, lean_object* v_toBind_2723_, lean_object* v___x_2724_, lean_object* v___f_2725_, lean_object* v_fst_2726_, lean_object* v_inst_2727_, lean_object* v_inst_2728_, lean_object* v_numDiscrEqs_2729_, lean_object* v_ys2_2730_, lean_object* v_altType_2731_){
_start:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___f_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2732_ = lean_box(v___x_2717_);
v___x_2733_ = lean_box(v_useSplitter_2718_);
lean_inc_ref(v_inst_2728_);
lean_inc_ref(v_inst_2727_);
v___f_2734_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed), 17, 15);
lean_closure_set(v___f_2734_, 0, v_toMonadExceptOf_2715_);
lean_closure_set(v___f_2734_, 1, v_ys_2716_);
lean_closure_set(v___f_2734_, 2, v_ys2_2730_);
lean_closure_set(v___f_2734_, 3, v___x_2732_);
lean_closure_set(v___f_2734_, 4, v___x_2733_);
lean_closure_set(v___f_2734_, 5, v_inst_2719_);
lean_closure_set(v___f_2734_, 6, v_args_2720_);
lean_closure_set(v___f_2734_, 7, v_onAlt_2721_);
lean_closure_set(v___f_2734_, 8, v_next_2722_);
lean_closure_set(v___f_2734_, 9, v_toBind_2723_);
lean_closure_set(v___f_2734_, 10, v___x_2724_);
lean_closure_set(v___f_2734_, 11, v___f_2725_);
lean_closure_set(v___f_2734_, 12, v_fst_2726_);
lean_closure_set(v___f_2734_, 13, v_inst_2727_);
lean_closure_set(v___f_2734_, 14, v_inst_2728_);
v___x_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2735_, 0, v_numDiscrEqs_2729_);
v___x_2736_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2727_, v_inst_2728_, v_altType_2731_, v___x_2735_, v___f_2734_, v___x_2717_, v___x_2717_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__42___boxed(lean_object** _args){
lean_object* v_toMonadExceptOf_2737_ = _args[0];
lean_object* v_ys_2738_ = _args[1];
lean_object* v___x_2739_ = _args[2];
lean_object* v_useSplitter_2740_ = _args[3];
lean_object* v_inst_2741_ = _args[4];
lean_object* v_args_2742_ = _args[5];
lean_object* v_onAlt_2743_ = _args[6];
lean_object* v_next_2744_ = _args[7];
lean_object* v_toBind_2745_ = _args[8];
lean_object* v___x_2746_ = _args[9];
lean_object* v___f_2747_ = _args[10];
lean_object* v_fst_2748_ = _args[11];
lean_object* v_inst_2749_ = _args[12];
lean_object* v_inst_2750_ = _args[13];
lean_object* v_numDiscrEqs_2751_ = _args[14];
lean_object* v_ys2_2752_ = _args[15];
lean_object* v_altType_2753_ = _args[16];
_start:
{
uint8_t v___x_13761__boxed_2754_; uint8_t v_useSplitter_boxed_2755_; lean_object* v_res_2756_; 
v___x_13761__boxed_2754_ = lean_unbox(v___x_2739_);
v_useSplitter_boxed_2755_ = lean_unbox(v_useSplitter_2740_);
v_res_2756_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__42(v_toMonadExceptOf_2737_, v_ys_2738_, v___x_13761__boxed_2754_, v_useSplitter_boxed_2755_, v_inst_2741_, v_args_2742_, v_onAlt_2743_, v_next_2744_, v_toBind_2745_, v___x_2746_, v___f_2747_, v_fst_2748_, v_inst_2749_, v_inst_2750_, v_numDiscrEqs_2751_, v_ys2_2752_, v_altType_2753_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43(lean_object* v___x_2757_, lean_object* v_inst_2758_, lean_object* v_inst_2759_, lean_object* v___f_2760_, uint8_t v___x_2761_, lean_object* v_toBind_2762_, lean_object* v___f_2763_, lean_object* v_altType_2764_){
_start:
{
lean_object* v_numOverlaps_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v_numOverlaps_2765_ = lean_ctor_get(v___x_2757_, 1);
lean_inc(v_numOverlaps_2765_);
v___x_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2766_, 0, v_numOverlaps_2765_);
v___x_2767_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2758_, v_inst_2759_, v_altType_2764_, v___x_2766_, v___f_2760_, v___x_2761_, v___x_2761_);
v___x_2768_ = lean_apply_4(v_toBind_2762_, lean_box(0), lean_box(0), v___x_2767_, v___f_2763_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed(lean_object* v___x_2769_, lean_object* v_inst_2770_, lean_object* v_inst_2771_, lean_object* v___f_2772_, lean_object* v___x_2773_, lean_object* v_toBind_2774_, lean_object* v___f_2775_, lean_object* v_altType_2776_){
_start:
{
uint8_t v___x_13793__boxed_2777_; lean_object* v_res_2778_; 
v___x_13793__boxed_2777_ = lean_unbox(v___x_2773_);
v_res_2778_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__43(v___x_2769_, v_inst_2770_, v_inst_2771_, v___f_2772_, v___x_13793__boxed_2777_, v_toBind_2774_, v___f_2775_, v_altType_2776_);
lean_dec_ref(v___x_2769_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44(lean_object* v___f_2779_, lean_object* v_altType_2780_){
_start:
{
lean_object* v___x_2781_; 
v___x_2781_ = lean_apply_1(v___f_2779_, v_altType_2780_);
return v___x_2781_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2(void){
_start:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2786_ = lean_box(0);
v___x_2787_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1));
v___x_2788_ = l_Lean_mkConst(v___x_2787_, v___x_2786_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46(lean_object* v___x_2789_, lean_object* v_toPure_2790_, lean_object* v_toBind_2791_, lean_object* v___f_2792_, lean_object* v___x_2793_, lean_object* v_inst_2794_, lean_object* v___f_2795_, lean_object* v_altType_2796_){
_start:
{
uint8_t v_hasUnitThunk_2797_; 
v_hasUnitThunk_2797_ = lean_ctor_get_uint8(v___x_2789_, sizeof(void*)*2);
if (v_hasUnitThunk_2797_ == 0)
{
lean_object* v___x_2798_; lean_object* v___x_2799_; 
lean_dec(v___f_2795_);
lean_dec(v_inst_2794_);
v___x_2798_ = lean_apply_2(v_toPure_2790_, lean_box(0), v_altType_2796_);
v___x_2799_ = lean_apply_4(v_toBind_2791_, lean_box(0), lean_box(0), v___x_2798_, v___f_2792_);
return v___x_2799_;
}
else
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
lean_dec(v___f_2792_);
lean_dec(v_toPure_2790_);
v___x_2800_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2);
v___x_2801_ = lean_mk_empty_array_with_capacity(v___x_2793_);
v___x_2802_ = lean_array_push(v___x_2801_, v___x_2800_);
v___x_2803_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateForall___boxed), 7, 2);
lean_closure_set(v___x_2803_, 0, v_altType_2796_);
lean_closure_set(v___x_2803_, 1, v___x_2802_);
v___x_2804_ = lean_apply_2(v_inst_2794_, lean_box(0), v___x_2803_);
v___x_2805_ = lean_apply_4(v_toBind_2791_, lean_box(0), lean_box(0), v___x_2804_, v___f_2795_);
return v___x_2805_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46___boxed(lean_object* v___x_2806_, lean_object* v_toPure_2807_, lean_object* v_toBind_2808_, lean_object* v___f_2809_, lean_object* v___x_2810_, lean_object* v_inst_2811_, lean_object* v___f_2812_, lean_object* v_altType_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__46(v___x_2806_, v_toPure_2807_, v_toBind_2808_, v___f_2809_, v___x_2810_, v_inst_2811_, v___f_2812_, v_altType_2813_);
lean_dec(v___x_2810_);
lean_dec_ref(v___x_2806_);
return v_res_2814_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__45___closed__3(void){
_start:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2818_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__45___closed__2));
v___x_2819_ = lean_unsigned_to_nat(8u);
v___x_2820_ = lean_unsigned_to_nat(372u);
v___x_2821_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__45___closed__1));
v___x_2822_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__45___closed__0));
v___x_2823_ = l_mkPanicMessageWithDecl(v___x_2822_, v___x_2821_, v___x_2820_, v___x_2819_, v___x_2818_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45(lean_object* v___x_2824_, lean_object* v___x_2825_, lean_object* v_toMonadExceptOf_2826_, uint8_t v___x_2827_, uint8_t v_useSplitter_2828_, lean_object* v_inst_2829_, lean_object* v_onAlt_2830_, lean_object* v_next_2831_, lean_object* v_toBind_2832_, lean_object* v___x_2833_, lean_object* v___f_2834_, lean_object* v_fst_2835_, lean_object* v_inst_2836_, lean_object* v_inst_2837_, lean_object* v_numDiscrEqs_2838_, lean_object* v___f_2839_, lean_object* v___x_2840_, lean_object* v_toPure_2841_, lean_object* v___x_2842_, lean_object* v___x_2843_, lean_object* v_ys_2844_, lean_object* v_args_2845_){
_start:
{
lean_object* v_numFields_2846_; lean_object* v___x_2847_; uint8_t v___x_2848_; 
v_numFields_2846_ = lean_ctor_get(v___x_2824_, 0);
v___x_2847_ = lean_array_get_size(v_ys_2844_);
v___x_2848_ = lean_nat_dec_eq(v___x_2847_, v_numFields_2846_);
if (v___x_2848_ == 0)
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
lean_dec_ref(v_args_2845_);
lean_dec_ref(v_ys_2844_);
lean_dec_ref(v___x_2843_);
lean_dec(v___x_2842_);
lean_dec(v_toPure_2841_);
lean_dec_ref(v___x_2840_);
lean_dec(v___f_2839_);
lean_dec(v_numDiscrEqs_2838_);
lean_dec_ref(v_inst_2837_);
lean_dec_ref(v_inst_2836_);
lean_dec(v_fst_2835_);
lean_dec(v___f_2834_);
lean_dec_ref(v___x_2833_);
lean_dec(v_toBind_2832_);
lean_dec(v_next_2831_);
lean_dec(v_onAlt_2830_);
lean_dec(v_inst_2829_);
lean_dec_ref(v_toMonadExceptOf_2826_);
lean_dec_ref(v___x_2824_);
v___x_2849_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__45___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__45___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__45___closed__3);
v___x_2850_ = l_panic___redArg(v___x_2825_, v___x_2849_);
return v___x_2850_;
}
else
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___f_2853_; lean_object* v___x_2854_; lean_object* v___f_2855_; lean_object* v___f_2856_; lean_object* v___f_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2851_ = lean_box(v___x_2827_);
v___x_2852_ = lean_box(v_useSplitter_2828_);
lean_inc_ref(v_inst_2837_);
lean_inc_ref(v_inst_2836_);
lean_inc_n(v_toBind_2832_, 3);
lean_inc_n(v_inst_2829_, 2);
lean_inc_ref(v_ys_2844_);
v___f_2853_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__42___boxed), 17, 15);
lean_closure_set(v___f_2853_, 0, v_toMonadExceptOf_2826_);
lean_closure_set(v___f_2853_, 1, v_ys_2844_);
lean_closure_set(v___f_2853_, 2, v___x_2851_);
lean_closure_set(v___f_2853_, 3, v___x_2852_);
lean_closure_set(v___f_2853_, 4, v_inst_2829_);
lean_closure_set(v___f_2853_, 5, v_args_2845_);
lean_closure_set(v___f_2853_, 6, v_onAlt_2830_);
lean_closure_set(v___f_2853_, 7, v_next_2831_);
lean_closure_set(v___f_2853_, 8, v_toBind_2832_);
lean_closure_set(v___f_2853_, 9, v___x_2833_);
lean_closure_set(v___f_2853_, 10, v___f_2834_);
lean_closure_set(v___f_2853_, 11, v_fst_2835_);
lean_closure_set(v___f_2853_, 12, v_inst_2836_);
lean_closure_set(v___f_2853_, 13, v_inst_2837_);
lean_closure_set(v___f_2853_, 14, v_numDiscrEqs_2838_);
v___x_2854_ = lean_box(v___x_2827_);
v___f_2855_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed), 8, 7);
lean_closure_set(v___f_2855_, 0, v___x_2824_);
lean_closure_set(v___f_2855_, 1, v_inst_2836_);
lean_closure_set(v___f_2855_, 2, v_inst_2837_);
lean_closure_set(v___f_2855_, 3, v___f_2853_);
lean_closure_set(v___f_2855_, 4, v___x_2854_);
lean_closure_set(v___f_2855_, 5, v_toBind_2832_);
lean_closure_set(v___f_2855_, 6, v___f_2839_);
v___f_2856_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44), 2, 1);
lean_closure_set(v___f_2856_, 0, v___f_2855_);
lean_inc_ref(v___f_2856_);
v___f_2857_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46___boxed), 8, 7);
lean_closure_set(v___f_2857_, 0, v___x_2840_);
lean_closure_set(v___f_2857_, 1, v_toPure_2841_);
lean_closure_set(v___f_2857_, 2, v_toBind_2832_);
lean_closure_set(v___f_2857_, 3, v___f_2856_);
lean_closure_set(v___f_2857_, 4, v___x_2842_);
lean_closure_set(v___f_2857_, 5, v_inst_2829_);
lean_closure_set(v___f_2857_, 6, v___f_2856_);
v___x_2858_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateForall___boxed), 7, 2);
lean_closure_set(v___x_2858_, 0, v___x_2843_);
lean_closure_set(v___x_2858_, 1, v_ys_2844_);
v___x_2859_ = lean_apply_2(v_inst_2829_, lean_box(0), v___x_2858_);
v___x_2860_ = lean_apply_4(v_toBind_2832_, lean_box(0), lean_box(0), v___x_2859_, v___f_2857_);
return v___x_2860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45___boxed(lean_object** _args){
lean_object* v___x_2861_ = _args[0];
lean_object* v___x_2862_ = _args[1];
lean_object* v_toMonadExceptOf_2863_ = _args[2];
lean_object* v___x_2864_ = _args[3];
lean_object* v_useSplitter_2865_ = _args[4];
lean_object* v_inst_2866_ = _args[5];
lean_object* v_onAlt_2867_ = _args[6];
lean_object* v_next_2868_ = _args[7];
lean_object* v_toBind_2869_ = _args[8];
lean_object* v___x_2870_ = _args[9];
lean_object* v___f_2871_ = _args[10];
lean_object* v_fst_2872_ = _args[11];
lean_object* v_inst_2873_ = _args[12];
lean_object* v_inst_2874_ = _args[13];
lean_object* v_numDiscrEqs_2875_ = _args[14];
lean_object* v___f_2876_ = _args[15];
lean_object* v___x_2877_ = _args[16];
lean_object* v_toPure_2878_ = _args[17];
lean_object* v___x_2879_ = _args[18];
lean_object* v___x_2880_ = _args[19];
lean_object* v_ys_2881_ = _args[20];
lean_object* v_args_2882_ = _args[21];
_start:
{
uint8_t v___x_13890__boxed_2883_; uint8_t v_useSplitter_boxed_2884_; lean_object* v_res_2885_; 
v___x_13890__boxed_2883_ = lean_unbox(v___x_2864_);
v_useSplitter_boxed_2884_ = lean_unbox(v_useSplitter_2865_);
v_res_2885_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__45(v___x_2861_, v___x_2862_, v_toMonadExceptOf_2863_, v___x_13890__boxed_2883_, v_useSplitter_boxed_2884_, v_inst_2866_, v_onAlt_2867_, v_next_2868_, v_toBind_2869_, v___x_2870_, v___f_2871_, v_fst_2872_, v_inst_2873_, v_inst_2874_, v_numDiscrEqs_2875_, v___f_2876_, v___x_2877_, v_toPure_2878_, v___x_2879_, v___x_2880_, v_ys_2881_, v_args_2882_);
lean_dec(v___x_2862_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47(lean_object* v_fst_2886_, lean_object* v___x_2887_, lean_object* v___x_2888_, lean_object* v___x_2889_, lean_object* v___x_2890_, lean_object* v___x_2891_, lean_object* v_toPure_2892_, lean_object* v_alt_x27_2893_){
_start:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2894_ = lean_array_push(v_fst_2886_, v_alt_x27_2893_);
v___x_2895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2887_);
lean_ctor_set(v___x_2895_, 1, v___x_2888_);
v___x_2896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2889_);
lean_ctor_set(v___x_2896_, 1, v___x_2895_);
v___x_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2890_);
lean_ctor_set(v___x_2897_, 1, v___x_2896_);
v___x_2898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2891_);
lean_ctor_set(v___x_2898_, 1, v___x_2897_);
v___x_2899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2894_);
lean_ctor_set(v___x_2899_, 1, v___x_2898_);
v___x_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2899_);
v___x_2901_ = lean_apply_2(v_toPure_2892_, lean_box(0), v___x_2900_);
return v___x_2901_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__1(void){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2903_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__0));
v___x_2904_ = lean_unsigned_to_nat(6u);
v___x_2905_ = lean_unsigned_to_nat(370u);
v___x_2906_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__45___closed__1));
v___x_2907_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__45___closed__0));
v___x_2908_ = l_mkPanicMessageWithDecl(v___x_2907_, v___x_2906_, v___x_2905_, v___x_2904_, v___x_2903_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48(lean_object* v___x_2909_, lean_object* v_toPure_2910_, lean_object* v_toBind_2911_, lean_object* v___f_2912_, lean_object* v___x_2913_, lean_object* v___x_2914_, lean_object* v_inst_2915_, lean_object* v___x_2916_, lean_object* v_toMonadExceptOf_2917_, uint8_t v___x_2918_, uint8_t v_useSplitter_2919_, lean_object* v_onAlt_2920_, lean_object* v___f_2921_, lean_object* v_fst_2922_, lean_object* v_inst_2923_, lean_object* v_inst_2924_, lean_object* v_numDiscrEqs_2925_, lean_object* v_next_2926_, lean_object* v_acc_2927_, lean_object* v_h_2928_, lean_object* v_G_2929_){
_start:
{
uint8_t v___x_2930_; 
v___x_2930_ = lean_nat_dec_lt(v_next_2926_, v___x_2909_);
if (v___x_2930_ == 0)
{
lean_object* v___x_2931_; 
lean_dec(v_G_2929_);
lean_dec(v_next_2926_);
lean_dec(v_numDiscrEqs_2925_);
lean_dec_ref(v_inst_2924_);
lean_dec_ref(v_inst_2923_);
lean_dec(v_fst_2922_);
lean_dec(v___f_2921_);
lean_dec(v_onAlt_2920_);
lean_dec_ref(v_toMonadExceptOf_2917_);
lean_dec(v___x_2916_);
lean_dec(v_inst_2915_);
lean_dec(v___f_2912_);
lean_dec(v_toBind_2911_);
v___x_2931_ = lean_apply_2(v_toPure_2910_, lean_box(0), v_acc_2927_);
return v___x_2931_;
}
else
{
lean_object* v_snd_2932_; lean_object* v_snd_2933_; lean_object* v_snd_2934_; lean_object* v_snd_2935_; lean_object* v_snd_2936_; lean_object* v_fst_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_3147_; 
v_snd_2932_ = lean_ctor_get(v_acc_2927_, 1);
lean_inc(v_snd_2932_);
v_snd_2933_ = lean_ctor_get(v_snd_2932_, 1);
lean_inc(v_snd_2933_);
v_snd_2934_ = lean_ctor_get(v_snd_2933_, 1);
lean_inc(v_snd_2934_);
v_snd_2935_ = lean_ctor_get(v_snd_2934_, 1);
lean_inc(v_snd_2935_);
v_snd_2936_ = lean_ctor_get(v_snd_2935_, 1);
lean_inc(v_snd_2936_);
v_fst_2937_ = lean_ctor_get(v_acc_2927_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v_acc_2927_);
if (v_isSharedCheck_3147_ == 0)
{
lean_object* v_unused_3148_; 
v_unused_3148_ = lean_ctor_get(v_acc_2927_, 1);
lean_dec(v_unused_3148_);
v___x_2939_ = v_acc_2927_;
v_isShared_2940_ = v_isSharedCheck_3147_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_fst_2937_);
lean_dec(v_acc_2927_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_3147_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v_fst_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_3145_; 
v_fst_2941_ = lean_ctor_get(v_snd_2932_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v_snd_2932_);
if (v_isSharedCheck_3145_ == 0)
{
lean_object* v_unused_3146_; 
v_unused_3146_ = lean_ctor_get(v_snd_2932_, 1);
lean_dec(v_unused_3146_);
v___x_2943_ = v_snd_2932_;
v_isShared_2944_ = v_isSharedCheck_3145_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_fst_2941_);
lean_dec(v_snd_2932_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_3145_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v_fst_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_3143_; 
v_fst_2945_ = lean_ctor_get(v_snd_2933_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v_snd_2933_);
if (v_isSharedCheck_3143_ == 0)
{
lean_object* v_unused_3144_; 
v_unused_3144_ = lean_ctor_get(v_snd_2933_, 1);
lean_dec(v_unused_3144_);
v___x_2947_ = v_snd_2933_;
v_isShared_2948_ = v_isSharedCheck_3143_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_fst_2945_);
lean_dec(v_snd_2933_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_3143_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v_fst_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_3141_; 
v_fst_2949_ = lean_ctor_get(v_snd_2934_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v_snd_2934_);
if (v_isSharedCheck_3141_ == 0)
{
lean_object* v_unused_3142_; 
v_unused_3142_ = lean_ctor_get(v_snd_2934_, 1);
lean_dec(v_unused_3142_);
v___x_2951_ = v_snd_2934_;
v_isShared_2952_ = v_isSharedCheck_3141_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_fst_2949_);
lean_dec(v_snd_2934_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_3141_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v_fst_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_3139_; 
v_fst_2953_ = lean_ctor_get(v_snd_2935_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v_snd_2935_);
if (v_isSharedCheck_3139_ == 0)
{
lean_object* v_unused_3140_; 
v_unused_3140_ = lean_ctor_get(v_snd_2935_, 1);
lean_dec(v_unused_3140_);
v___x_2955_ = v_snd_2935_;
v_isShared_2956_ = v_isSharedCheck_3139_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_fst_2953_);
lean_dec(v_snd_2935_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_3139_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v_array_2957_; lean_object* v_start_2958_; lean_object* v_stop_2959_; lean_object* v___f_2960_; lean_object* v___y_2962_; uint8_t v___x_2965_; 
v_array_2957_ = lean_ctor_get(v_snd_2936_, 0);
v_start_2958_ = lean_ctor_get(v_snd_2936_, 1);
v_stop_2959_ = lean_ctor_get(v_snd_2936_, 2);
lean_inc(v_next_2926_);
lean_inc(v_toPure_2910_);
v___f_2960_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37___boxed), 4, 3);
lean_closure_set(v___f_2960_, 0, v_toPure_2910_);
lean_closure_set(v___f_2960_, 1, v_next_2926_);
lean_closure_set(v___f_2960_, 2, v_G_2929_);
v___x_2965_ = lean_nat_dec_lt(v_start_2958_, v_stop_2959_);
if (v___x_2965_ == 0)
{
lean_object* v___x_2967_; 
lean_dec(v_next_2926_);
lean_dec(v_numDiscrEqs_2925_);
lean_dec_ref(v_inst_2924_);
lean_dec_ref(v_inst_2923_);
lean_dec(v_fst_2922_);
lean_dec(v___f_2921_);
lean_dec(v_onAlt_2920_);
lean_dec_ref(v_toMonadExceptOf_2917_);
lean_dec(v___x_2916_);
lean_dec(v_inst_2915_);
if (v_isShared_2956_ == 0)
{
v___x_2967_ = v___x_2955_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_fst_2953_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_snd_2936_);
v___x_2967_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
lean_object* v___x_2969_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 1, v___x_2967_);
v___x_2969_ = v___x_2951_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_fst_2949_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v___x_2967_);
v___x_2969_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
lean_object* v___x_2971_; 
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 1, v___x_2969_);
v___x_2971_ = v___x_2947_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_fst_2945_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v___x_2969_);
v___x_2971_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
lean_object* v___x_2973_; 
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 1, v___x_2971_);
v___x_2973_ = v___x_2943_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_fst_2941_);
lean_ctor_set(v_reuseFailAlloc_2979_, 1, v___x_2971_);
v___x_2973_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
lean_object* v___x_2975_; 
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 1, v___x_2973_);
v___x_2975_ = v___x_2939_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_fst_2937_);
lean_ctor_set(v_reuseFailAlloc_2978_, 1, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2975_);
v___x_2977_ = lean_apply_2(v_toPure_2910_, lean_box(0), v___x_2976_);
v___y_2962_ = v___x_2977_;
goto v___jp_2961_;
}
}
}
}
}
}
else
{
lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_3135_; 
lean_inc(v_stop_2959_);
lean_inc(v_start_2958_);
lean_inc_ref(v_array_2957_);
v_isSharedCheck_3135_ = !lean_is_exclusive(v_snd_2936_);
if (v_isSharedCheck_3135_ == 0)
{
lean_object* v_unused_3136_; lean_object* v_unused_3137_; lean_object* v_unused_3138_; 
v_unused_3136_ = lean_ctor_get(v_snd_2936_, 2);
lean_dec(v_unused_3136_);
v_unused_3137_ = lean_ctor_get(v_snd_2936_, 1);
lean_dec(v_unused_3137_);
v_unused_3138_ = lean_ctor_get(v_snd_2936_, 0);
lean_dec(v_unused_3138_);
v___x_2984_ = v_snd_2936_;
v_isShared_2985_ = v_isSharedCheck_3135_;
goto v_resetjp_2983_;
}
else
{
lean_dec(v_snd_2936_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_3135_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v_array_2986_; lean_object* v_start_2987_; lean_object* v_stop_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2993_; 
v_array_2986_ = lean_ctor_get(v_fst_2953_, 0);
v_start_2987_ = lean_ctor_get(v_fst_2953_, 1);
v_stop_2988_ = lean_ctor_get(v_fst_2953_, 2);
v___x_2989_ = lean_array_fget(v_array_2957_, v_start_2958_);
v___x_2990_ = lean_unsigned_to_nat(1u);
v___x_2991_ = lean_nat_add(v_start_2958_, v___x_2990_);
lean_dec(v_start_2958_);
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 1, v___x_2991_);
v___x_2993_ = v___x_2984_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_array_2957_);
lean_ctor_set(v_reuseFailAlloc_3134_, 1, v___x_2991_);
lean_ctor_set(v_reuseFailAlloc_3134_, 2, v_stop_2959_);
v___x_2993_ = v_reuseFailAlloc_3134_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
uint8_t v___x_2994_; 
v___x_2994_ = lean_nat_dec_lt(v_start_2987_, v_stop_2988_);
if (v___x_2994_ == 0)
{
lean_object* v___x_2996_; 
lean_dec(v___x_2989_);
lean_dec(v_next_2926_);
lean_dec(v_numDiscrEqs_2925_);
lean_dec_ref(v_inst_2924_);
lean_dec_ref(v_inst_2923_);
lean_dec(v_fst_2922_);
lean_dec(v___f_2921_);
lean_dec(v_onAlt_2920_);
lean_dec_ref(v_toMonadExceptOf_2917_);
lean_dec(v___x_2916_);
lean_dec(v_inst_2915_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 1, v___x_2993_);
v___x_2996_ = v___x_2955_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_fst_2953_);
lean_ctor_set(v_reuseFailAlloc_3011_, 1, v___x_2993_);
v___x_2996_ = v_reuseFailAlloc_3011_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
lean_object* v___x_2998_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 1, v___x_2996_);
v___x_2998_ = v___x_2951_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_fst_2949_);
lean_ctor_set(v_reuseFailAlloc_3010_, 1, v___x_2996_);
v___x_2998_ = v_reuseFailAlloc_3010_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
lean_object* v___x_3000_; 
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 1, v___x_2998_);
v___x_3000_ = v___x_2947_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_fst_2945_);
lean_ctor_set(v_reuseFailAlloc_3009_, 1, v___x_2998_);
v___x_3000_ = v_reuseFailAlloc_3009_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
lean_object* v___x_3002_; 
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 1, v___x_3000_);
v___x_3002_ = v___x_2943_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_fst_2941_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v___x_3000_);
v___x_3002_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
lean_object* v___x_3004_; 
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 1, v___x_3002_);
v___x_3004_ = v___x_2939_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_fst_2937_);
lean_ctor_set(v_reuseFailAlloc_3007_, 1, v___x_3002_);
v___x_3004_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3004_);
v___x_3006_ = lean_apply_2(v_toPure_2910_, lean_box(0), v___x_3005_);
v___y_2962_ = v___x_3006_;
goto v___jp_2961_;
}
}
}
}
}
}
else
{
lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3130_; 
lean_inc(v_stop_2988_);
lean_inc(v_start_2987_);
lean_inc_ref(v_array_2986_);
v_isSharedCheck_3130_ = !lean_is_exclusive(v_fst_2953_);
if (v_isSharedCheck_3130_ == 0)
{
lean_object* v_unused_3131_; lean_object* v_unused_3132_; lean_object* v_unused_3133_; 
v_unused_3131_ = lean_ctor_get(v_fst_2953_, 2);
lean_dec(v_unused_3131_);
v_unused_3132_ = lean_ctor_get(v_fst_2953_, 1);
lean_dec(v_unused_3132_);
v_unused_3133_ = lean_ctor_get(v_fst_2953_, 0);
lean_dec(v_unused_3133_);
v___x_3013_ = v_fst_2953_;
v_isShared_3014_ = v_isSharedCheck_3130_;
goto v_resetjp_3012_;
}
else
{
lean_dec(v_fst_2953_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3130_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v_array_3015_; lean_object* v_start_3016_; lean_object* v_stop_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3021_; 
v_array_3015_ = lean_ctor_get(v_fst_2949_, 0);
v_start_3016_ = lean_ctor_get(v_fst_2949_, 1);
v_stop_3017_ = lean_ctor_get(v_fst_2949_, 2);
v___x_3018_ = lean_array_fget(v_array_2986_, v_start_2987_);
v___x_3019_ = lean_nat_add(v_start_2987_, v___x_2990_);
lean_dec(v_start_2987_);
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 1, v___x_3019_);
v___x_3021_ = v___x_3013_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_array_2986_);
lean_ctor_set(v_reuseFailAlloc_3129_, 1, v___x_3019_);
lean_ctor_set(v_reuseFailAlloc_3129_, 2, v_stop_2988_);
v___x_3021_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
uint8_t v___x_3022_; 
v___x_3022_ = lean_nat_dec_lt(v_start_3016_, v_stop_3017_);
if (v___x_3022_ == 0)
{
lean_object* v___x_3024_; 
lean_dec(v___x_3018_);
lean_dec(v___x_2989_);
lean_dec(v_next_2926_);
lean_dec(v_numDiscrEqs_2925_);
lean_dec_ref(v_inst_2924_);
lean_dec_ref(v_inst_2923_);
lean_dec(v_fst_2922_);
lean_dec(v___f_2921_);
lean_dec(v_onAlt_2920_);
lean_dec_ref(v_toMonadExceptOf_2917_);
lean_dec(v___x_2916_);
lean_dec(v_inst_2915_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 1, v___x_2993_);
lean_ctor_set(v___x_2955_, 0, v___x_3021_);
v___x_3024_ = v___x_2955_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v___x_3021_);
lean_ctor_set(v_reuseFailAlloc_3039_, 1, v___x_2993_);
v___x_3024_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
lean_object* v___x_3026_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 1, v___x_3024_);
v___x_3026_ = v___x_2951_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_fst_2949_);
lean_ctor_set(v_reuseFailAlloc_3038_, 1, v___x_3024_);
v___x_3026_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
lean_object* v___x_3028_; 
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 1, v___x_3026_);
v___x_3028_ = v___x_2947_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_fst_2945_);
lean_ctor_set(v_reuseFailAlloc_3037_, 1, v___x_3026_);
v___x_3028_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
lean_object* v___x_3030_; 
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 1, v___x_3028_);
v___x_3030_ = v___x_2943_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_fst_2941_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v___x_3028_);
v___x_3030_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
lean_object* v___x_3032_; 
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 1, v___x_3030_);
v___x_3032_ = v___x_2939_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_fst_2937_);
lean_ctor_set(v_reuseFailAlloc_3035_, 1, v___x_3030_);
v___x_3032_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
v___x_3034_ = lean_apply_2(v_toPure_2910_, lean_box(0), v___x_3033_);
v___y_2962_ = v___x_3034_;
goto v___jp_2961_;
}
}
}
}
}
}
else
{
lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3125_; 
lean_inc(v_stop_3017_);
lean_inc(v_start_3016_);
lean_inc_ref(v_array_3015_);
v_isSharedCheck_3125_ = !lean_is_exclusive(v_fst_2949_);
if (v_isSharedCheck_3125_ == 0)
{
lean_object* v_unused_3126_; lean_object* v_unused_3127_; lean_object* v_unused_3128_; 
v_unused_3126_ = lean_ctor_get(v_fst_2949_, 2);
lean_dec(v_unused_3126_);
v_unused_3127_ = lean_ctor_get(v_fst_2949_, 1);
lean_dec(v_unused_3127_);
v_unused_3128_ = lean_ctor_get(v_fst_2949_, 0);
lean_dec(v_unused_3128_);
v___x_3041_ = v_fst_2949_;
v_isShared_3042_ = v_isSharedCheck_3125_;
goto v_resetjp_3040_;
}
else
{
lean_dec(v_fst_2949_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3125_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v_array_3043_; lean_object* v_start_3044_; lean_object* v_stop_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3049_; 
v_array_3043_ = lean_ctor_get(v_fst_2945_, 0);
v_start_3044_ = lean_ctor_get(v_fst_2945_, 1);
v_stop_3045_ = lean_ctor_get(v_fst_2945_, 2);
v___x_3046_ = lean_array_fget(v_array_3015_, v_start_3016_);
v___x_3047_ = lean_nat_add(v_start_3016_, v___x_2990_);
lean_dec(v_start_3016_);
if (v_isShared_3042_ == 0)
{
lean_ctor_set(v___x_3041_, 1, v___x_3047_);
v___x_3049_ = v___x_3041_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_array_3015_);
lean_ctor_set(v_reuseFailAlloc_3124_, 1, v___x_3047_);
lean_ctor_set(v_reuseFailAlloc_3124_, 2, v_stop_3017_);
v___x_3049_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
uint8_t v___x_3050_; 
v___x_3050_ = lean_nat_dec_lt(v_start_3044_, v_stop_3045_);
if (v___x_3050_ == 0)
{
lean_object* v___x_3052_; 
lean_dec(v___x_3046_);
lean_dec(v___x_3018_);
lean_dec(v___x_2989_);
lean_dec(v_next_2926_);
lean_dec(v_numDiscrEqs_2925_);
lean_dec_ref(v_inst_2924_);
lean_dec_ref(v_inst_2923_);
lean_dec(v_fst_2922_);
lean_dec(v___f_2921_);
lean_dec(v_onAlt_2920_);
lean_dec_ref(v_toMonadExceptOf_2917_);
lean_dec(v___x_2916_);
lean_dec(v_inst_2915_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 1, v___x_2993_);
lean_ctor_set(v___x_2955_, 0, v___x_3021_);
v___x_3052_ = v___x_2955_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v___x_3021_);
lean_ctor_set(v_reuseFailAlloc_3067_, 1, v___x_2993_);
v___x_3052_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
lean_object* v___x_3054_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 1, v___x_3052_);
lean_ctor_set(v___x_2951_, 0, v___x_3049_);
v___x_3054_ = v___x_2951_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3049_);
lean_ctor_set(v_reuseFailAlloc_3066_, 1, v___x_3052_);
v___x_3054_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
lean_object* v___x_3056_; 
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 1, v___x_3054_);
v___x_3056_ = v___x_2947_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_fst_2945_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
lean_object* v___x_3058_; 
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 1, v___x_3056_);
v___x_3058_ = v___x_2943_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_fst_2941_);
lean_ctor_set(v_reuseFailAlloc_3064_, 1, v___x_3056_);
v___x_3058_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
lean_object* v___x_3060_; 
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 1, v___x_3058_);
v___x_3060_ = v___x_2939_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_fst_2937_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v___x_3058_);
v___x_3060_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3060_);
v___x_3062_ = lean_apply_2(v_toPure_2910_, lean_box(0), v___x_3061_);
v___y_2962_ = v___x_3062_;
goto v___jp_2961_;
}
}
}
}
}
}
else
{
lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3120_; 
lean_inc(v_stop_3045_);
lean_inc(v_start_3044_);
lean_inc_ref(v_array_3043_);
v_isSharedCheck_3120_ = !lean_is_exclusive(v_fst_2945_);
if (v_isSharedCheck_3120_ == 0)
{
lean_object* v_unused_3121_; lean_object* v_unused_3122_; lean_object* v_unused_3123_; 
v_unused_3121_ = lean_ctor_get(v_fst_2945_, 2);
lean_dec(v_unused_3121_);
v_unused_3122_ = lean_ctor_get(v_fst_2945_, 1);
lean_dec(v_unused_3122_);
v_unused_3123_ = lean_ctor_get(v_fst_2945_, 0);
lean_dec(v_unused_3123_);
v___x_3069_ = v_fst_2945_;
v_isShared_3070_ = v_isSharedCheck_3120_;
goto v_resetjp_3068_;
}
else
{
lean_dec(v_fst_2945_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3120_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v_array_3071_; lean_object* v_start_3072_; lean_object* v_stop_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3077_; 
v_array_3071_ = lean_ctor_get(v_fst_2941_, 0);
v_start_3072_ = lean_ctor_get(v_fst_2941_, 1);
v_stop_3073_ = lean_ctor_get(v_fst_2941_, 2);
v___x_3074_ = lean_array_fget(v_array_3043_, v_start_3044_);
v___x_3075_ = lean_nat_add(v_start_3044_, v___x_2990_);
lean_dec(v_start_3044_);
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 1, v___x_3075_);
v___x_3077_ = v___x_3069_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_array_3043_);
lean_ctor_set(v_reuseFailAlloc_3119_, 1, v___x_3075_);
lean_ctor_set(v_reuseFailAlloc_3119_, 2, v_stop_3045_);
v___x_3077_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
uint8_t v___x_3078_; 
v___x_3078_ = lean_nat_dec_lt(v_start_3072_, v_stop_3073_);
if (v___x_3078_ == 0)
{
lean_object* v___x_3080_; 
lean_dec(v___x_3074_);
lean_dec(v___x_3046_);
lean_dec(v___x_3018_);
lean_dec(v___x_2989_);
lean_dec(v_next_2926_);
lean_dec(v_numDiscrEqs_2925_);
lean_dec_ref(v_inst_2924_);
lean_dec_ref(v_inst_2923_);
lean_dec(v_fst_2922_);
lean_dec(v___f_2921_);
lean_dec(v_onAlt_2920_);
lean_dec_ref(v_toMonadExceptOf_2917_);
lean_dec(v___x_2916_);
lean_dec(v_inst_2915_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 1, v___x_2993_);
lean_ctor_set(v___x_2955_, 0, v___x_3021_);
v___x_3080_ = v___x_2955_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3021_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v___x_2993_);
v___x_3080_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
lean_object* v___x_3082_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 1, v___x_3080_);
lean_ctor_set(v___x_2951_, 0, v___x_3049_);
v___x_3082_ = v___x_2951_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3049_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v___x_3080_);
v___x_3082_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___x_3084_; 
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 1, v___x_3082_);
lean_ctor_set(v___x_2947_, 0, v___x_3077_);
v___x_3084_ = v___x_2947_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v___x_3077_);
lean_ctor_set(v_reuseFailAlloc_3093_, 1, v___x_3082_);
v___x_3084_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
lean_object* v___x_3086_; 
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 1, v___x_3084_);
v___x_3086_ = v___x_2943_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_fst_2941_);
lean_ctor_set(v_reuseFailAlloc_3092_, 1, v___x_3084_);
v___x_3086_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
lean_object* v___x_3088_; 
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 1, v___x_3086_);
v___x_3088_ = v___x_2939_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_fst_2937_);
lean_ctor_set(v_reuseFailAlloc_3091_, 1, v___x_3086_);
v___x_3088_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3088_);
v___x_3090_ = lean_apply_2(v_toPure_2910_, lean_box(0), v___x_3089_);
v___y_2962_ = v___x_3090_;
goto v___jp_2961_;
}
}
}
}
}
}
else
{
lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3115_; 
lean_inc(v_stop_3073_);
lean_inc(v_start_3072_);
lean_inc_ref(v_array_3071_);
lean_del_object(v___x_2955_);
lean_del_object(v___x_2951_);
lean_del_object(v___x_2947_);
lean_del_object(v___x_2943_);
lean_del_object(v___x_2939_);
v_isSharedCheck_3115_ = !lean_is_exclusive(v_fst_2941_);
if (v_isSharedCheck_3115_ == 0)
{
lean_object* v_unused_3116_; lean_object* v_unused_3117_; lean_object* v_unused_3118_; 
v_unused_3116_ = lean_ctor_get(v_fst_2941_, 2);
lean_dec(v_unused_3116_);
v_unused_3117_ = lean_ctor_get(v_fst_2941_, 1);
lean_dec(v_unused_3117_);
v_unused_3118_ = lean_ctor_get(v_fst_2941_, 0);
lean_dec(v_unused_3118_);
v___x_3097_ = v_fst_2941_;
v_isShared_3098_ = v_isSharedCheck_3115_;
goto v_resetjp_3096_;
}
else
{
lean_dec(v_fst_2941_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3115_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v_numOverlaps_3099_; uint8_t v___x_3100_; 
v_numOverlaps_3099_ = lean_ctor_get(v___x_3074_, 1);
v___x_3100_ = lean_nat_dec_eq(v_numOverlaps_3099_, v___x_2913_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; lean_object* v___x_3102_; 
lean_del_object(v___x_3097_);
lean_dec_ref(v___x_3077_);
lean_dec(v___x_3074_);
lean_dec(v_stop_3073_);
lean_dec(v_start_3072_);
lean_dec_ref(v_array_3071_);
lean_dec_ref(v___x_3049_);
lean_dec(v___x_3046_);
lean_dec_ref(v___x_3021_);
lean_dec(v___x_3018_);
lean_dec_ref(v___x_2993_);
lean_dec(v___x_2989_);
lean_dec(v_fst_2937_);
lean_dec(v_next_2926_);
lean_dec(v_numDiscrEqs_2925_);
lean_dec_ref(v_inst_2924_);
lean_dec_ref(v_inst_2923_);
lean_dec(v_fst_2922_);
lean_dec(v___f_2921_);
lean_dec(v_onAlt_2920_);
lean_dec_ref(v_toMonadExceptOf_2917_);
lean_dec(v___x_2916_);
lean_dec(v_inst_2915_);
lean_dec(v_toPure_2910_);
v___x_3101_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__1);
v___x_3102_ = l_panic___redArg(v___x_2914_, v___x_3101_);
v___y_2962_ = v___x_3102_;
goto v___jp_2961_;
}
else
{
lean_object* v___f_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___f_3107_; lean_object* v___x_3108_; lean_object* v___x_3110_; 
lean_inc(v_inst_2915_);
lean_inc_n(v_toPure_2910_, 2);
lean_inc(v___x_3046_);
v___f_3103_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed), 4, 3);
lean_closure_set(v___f_3103_, 0, v___x_3046_);
lean_closure_set(v___f_3103_, 1, v_toPure_2910_);
lean_closure_set(v___f_3103_, 2, v_inst_2915_);
v___x_3104_ = lean_array_fget_borrowed(v_array_3071_, v_start_3072_);
v___x_3105_ = lean_box(v___x_2918_);
v___x_3106_ = lean_box(v_useSplitter_2919_);
lean_inc(v___x_3074_);
lean_inc_ref(v_inst_2924_);
lean_inc_ref(v_inst_2923_);
lean_inc(v___x_3104_);
lean_inc(v_toBind_2911_);
v___f_3107_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__45___boxed), 22, 20);
lean_closure_set(v___f_3107_, 0, v___x_3046_);
lean_closure_set(v___f_3107_, 1, v___x_2916_);
lean_closure_set(v___f_3107_, 2, v_toMonadExceptOf_2917_);
lean_closure_set(v___f_3107_, 3, v___x_3105_);
lean_closure_set(v___f_3107_, 4, v___x_3106_);
lean_closure_set(v___f_3107_, 5, v_inst_2915_);
lean_closure_set(v___f_3107_, 6, v_onAlt_2920_);
lean_closure_set(v___f_3107_, 7, v_next_2926_);
lean_closure_set(v___f_3107_, 8, v_toBind_2911_);
lean_closure_set(v___f_3107_, 9, v___x_3104_);
lean_closure_set(v___f_3107_, 10, v___f_2921_);
lean_closure_set(v___f_3107_, 11, v_fst_2922_);
lean_closure_set(v___f_3107_, 12, v_inst_2923_);
lean_closure_set(v___f_3107_, 13, v_inst_2924_);
lean_closure_set(v___f_3107_, 14, v_numDiscrEqs_2925_);
lean_closure_set(v___f_3107_, 15, v___f_3103_);
lean_closure_set(v___f_3107_, 16, v___x_3074_);
lean_closure_set(v___f_3107_, 17, v_toPure_2910_);
lean_closure_set(v___f_3107_, 18, v___x_2990_);
lean_closure_set(v___f_3107_, 19, v___x_2989_);
v___x_3108_ = lean_nat_add(v_start_3072_, v___x_2990_);
lean_dec(v_start_3072_);
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 1, v___x_3108_);
v___x_3110_ = v___x_3097_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_array_3071_);
lean_ctor_set(v_reuseFailAlloc_3114_, 1, v___x_3108_);
lean_ctor_set(v_reuseFailAlloc_3114_, 2, v_stop_3073_);
v___x_3110_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
lean_object* v___f_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___f_3111_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__47), 8, 7);
lean_closure_set(v___f_3111_, 0, v_fst_2937_);
lean_closure_set(v___f_3111_, 1, v___x_3021_);
lean_closure_set(v___f_3111_, 2, v___x_2993_);
lean_closure_set(v___f_3111_, 3, v___x_3049_);
lean_closure_set(v___f_3111_, 4, v___x_3077_);
lean_closure_set(v___f_3111_, 5, v___x_3110_);
lean_closure_set(v___f_3111_, 6, v_toPure_2910_);
v___x_3112_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(v_inst_2924_, v_inst_2923_, v___x_3018_, v___x_3074_, v___f_3107_);
lean_inc(v_toBind_2911_);
v___x_3113_ = lean_apply_4(v_toBind_2911_, lean_box(0), lean_box(0), v___x_3112_, v___f_3111_);
v___y_2962_ = v___x_3113_;
goto v___jp_2961_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_2961_:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
lean_inc(v_toBind_2911_);
v___x_2963_ = lean_apply_4(v_toBind_2911_, lean_box(0), lean_box(0), v___y_2962_, v___f_2912_);
v___x_2964_ = lean_apply_4(v_toBind_2911_, lean_box(0), lean_box(0), v___x_2963_, v___f_2960_);
return v___x_2964_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed(lean_object** _args){
lean_object* v___x_3149_ = _args[0];
lean_object* v_toPure_3150_ = _args[1];
lean_object* v_toBind_3151_ = _args[2];
lean_object* v___f_3152_ = _args[3];
lean_object* v___x_3153_ = _args[4];
lean_object* v___x_3154_ = _args[5];
lean_object* v_inst_3155_ = _args[6];
lean_object* v___x_3156_ = _args[7];
lean_object* v_toMonadExceptOf_3157_ = _args[8];
lean_object* v___x_3158_ = _args[9];
lean_object* v_useSplitter_3159_ = _args[10];
lean_object* v_onAlt_3160_ = _args[11];
lean_object* v___f_3161_ = _args[12];
lean_object* v_fst_3162_ = _args[13];
lean_object* v_inst_3163_ = _args[14];
lean_object* v_inst_3164_ = _args[15];
lean_object* v_numDiscrEqs_3165_ = _args[16];
lean_object* v_next_3166_ = _args[17];
lean_object* v_acc_3167_ = _args[18];
lean_object* v_h_3168_ = _args[19];
lean_object* v_G_3169_ = _args[20];
_start:
{
uint8_t v___x_14009__boxed_3170_; uint8_t v_useSplitter_boxed_3171_; lean_object* v_res_3172_; 
v___x_14009__boxed_3170_ = lean_unbox(v___x_3158_);
v_useSplitter_boxed_3171_ = lean_unbox(v_useSplitter_3159_);
v_res_3172_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__48(v___x_3149_, v_toPure_3150_, v_toBind_3151_, v___f_3152_, v___x_3153_, v___x_3154_, v_inst_3155_, v___x_3156_, v_toMonadExceptOf_3157_, v___x_14009__boxed_3170_, v_useSplitter_boxed_3171_, v_onAlt_3160_, v___f_3161_, v_fst_3162_, v_inst_3163_, v_inst_3164_, v_numDiscrEqs_3165_, v_next_3166_, v_acc_3167_, v_h_3168_, v_G_3169_);
lean_dec(v___x_3154_);
lean_dec(v___x_3153_);
lean_dec(v___x_3149_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49(lean_object* v_fst_3173_, lean_object* v_numParams_3174_, lean_object* v_numDiscrs_3175_, lean_object* v_altInfos_3176_, lean_object* v_uElimPos_x3f_3177_, lean_object* v_snd_3178_, lean_object* v_overlaps_3179_, lean_object* v_splitterName_3180_, lean_object* v_matcherLevels_3181_, lean_object* v_params_x27_3182_, lean_object* v_fst_3183_, lean_object* v_discrs_x27_3184_, lean_object* v_fst_3185_, lean_object* v_toPure_3186_, lean_object* v_____do__lift_3187_){
_start:
{
lean_object* v_remaining_x27_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v_remaining_x27_3188_ = l_Array_append___redArg(v_fst_3173_, v_____do__lift_3187_);
v___x_3189_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3189_, 0, v_numParams_3174_);
lean_ctor_set(v___x_3189_, 1, v_numDiscrs_3175_);
lean_ctor_set(v___x_3189_, 2, v_altInfos_3176_);
lean_ctor_set(v___x_3189_, 3, v_uElimPos_x3f_3177_);
lean_ctor_set(v___x_3189_, 4, v_snd_3178_);
lean_ctor_set(v___x_3189_, 5, v_overlaps_3179_);
v___x_3190_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3189_);
lean_ctor_set(v___x_3190_, 1, v_splitterName_3180_);
lean_ctor_set(v___x_3190_, 2, v_matcherLevels_3181_);
lean_ctor_set(v___x_3190_, 3, v_params_x27_3182_);
lean_ctor_set(v___x_3190_, 4, v_fst_3183_);
lean_ctor_set(v___x_3190_, 5, v_discrs_x27_3184_);
lean_ctor_set(v___x_3190_, 6, v_fst_3185_);
lean_ctor_set(v___x_3190_, 7, v_remaining_x27_3188_);
v___x_3191_ = lean_apply_2(v_toPure_3186_, lean_box(0), v___x_3190_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed(lean_object* v_fst_3192_, lean_object* v_numParams_3193_, lean_object* v_numDiscrs_3194_, lean_object* v_altInfos_3195_, lean_object* v_uElimPos_x3f_3196_, lean_object* v_snd_3197_, lean_object* v_overlaps_3198_, lean_object* v_splitterName_3199_, lean_object* v_matcherLevels_3200_, lean_object* v_params_x27_3201_, lean_object* v_fst_3202_, lean_object* v_discrs_x27_3203_, lean_object* v_fst_3204_, lean_object* v_toPure_3205_, lean_object* v_____do__lift_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__49(v_fst_3192_, v_numParams_3193_, v_numDiscrs_3194_, v_altInfos_3195_, v_uElimPos_x3f_3196_, v_snd_3197_, v_overlaps_3198_, v_splitterName_3199_, v_matcherLevels_3200_, v_params_x27_3201_, v_fst_3202_, v_discrs_x27_3203_, v_fst_3204_, v_toPure_3205_, v_____do__lift_3206_);
lean_dec_ref(v_____do__lift_3206_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__50(lean_object* v_fst_3208_, lean_object* v_numParams_3209_, lean_object* v_numDiscrs_3210_, lean_object* v_altInfos_3211_, lean_object* v_uElimPos_x3f_3212_, lean_object* v_snd_3213_, lean_object* v_overlaps_3214_, lean_object* v_splitterName_3215_, lean_object* v_matcherLevels_3216_, lean_object* v_params_x27_3217_, lean_object* v_fst_3218_, lean_object* v_discrs_x27_3219_, lean_object* v_toPure_3220_, lean_object* v_onRemaining_3221_, lean_object* v_remaining_3222_, lean_object* v_toBind_3223_, lean_object* v_____s_3224_){
_start:
{
lean_object* v_fst_3225_; lean_object* v___f_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v_fst_3225_ = lean_ctor_get(v_____s_3224_, 0);
lean_inc(v_fst_3225_);
lean_dec_ref(v_____s_3224_);
v___f_3226_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed), 15, 14);
lean_closure_set(v___f_3226_, 0, v_fst_3208_);
lean_closure_set(v___f_3226_, 1, v_numParams_3209_);
lean_closure_set(v___f_3226_, 2, v_numDiscrs_3210_);
lean_closure_set(v___f_3226_, 3, v_altInfos_3211_);
lean_closure_set(v___f_3226_, 4, v_uElimPos_x3f_3212_);
lean_closure_set(v___f_3226_, 5, v_snd_3213_);
lean_closure_set(v___f_3226_, 6, v_overlaps_3214_);
lean_closure_set(v___f_3226_, 7, v_splitterName_3215_);
lean_closure_set(v___f_3226_, 8, v_matcherLevels_3216_);
lean_closure_set(v___f_3226_, 9, v_params_x27_3217_);
lean_closure_set(v___f_3226_, 10, v_fst_3218_);
lean_closure_set(v___f_3226_, 11, v_discrs_x27_3219_);
lean_closure_set(v___f_3226_, 12, v_fst_3225_);
lean_closure_set(v___f_3226_, 13, v_toPure_3220_);
v___x_3227_ = lean_apply_1(v_onRemaining_3221_, v_remaining_3222_);
v___x_3228_ = lean_apply_4(v_toBind_3223_, lean_box(0), lean_box(0), v___x_3227_, v___f_3226_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__50___boxed(lean_object** _args){
lean_object* v_fst_3229_ = _args[0];
lean_object* v_numParams_3230_ = _args[1];
lean_object* v_numDiscrs_3231_ = _args[2];
lean_object* v_altInfos_3232_ = _args[3];
lean_object* v_uElimPos_x3f_3233_ = _args[4];
lean_object* v_snd_3234_ = _args[5];
lean_object* v_overlaps_3235_ = _args[6];
lean_object* v_splitterName_3236_ = _args[7];
lean_object* v_matcherLevels_3237_ = _args[8];
lean_object* v_params_x27_3238_ = _args[9];
lean_object* v_fst_3239_ = _args[10];
lean_object* v_discrs_x27_3240_ = _args[11];
lean_object* v_toPure_3241_ = _args[12];
lean_object* v_onRemaining_3242_ = _args[13];
lean_object* v_remaining_3243_ = _args[14];
lean_object* v_toBind_3244_ = _args[15];
lean_object* v_____s_3245_ = _args[16];
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__50(v_fst_3229_, v_numParams_3230_, v_numDiscrs_3231_, v_altInfos_3232_, v_uElimPos_x3f_3233_, v_snd_3234_, v_overlaps_3235_, v_splitterName_3236_, v_matcherLevels_3237_, v_params_x27_3238_, v_fst_3239_, v_discrs_x27_3240_, v_toPure_3241_, v_onRemaining_3242_, v_remaining_3243_, v_toBind_3244_, v_____s_3245_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51(lean_object* v_splitterMatchInfo_3247_, lean_object* v_fst_3248_, lean_object* v_numParams_3249_, lean_object* v_numDiscrs_3250_, lean_object* v_altInfos_3251_, lean_object* v_uElimPos_x3f_3252_, lean_object* v_snd_3253_, lean_object* v_overlaps_3254_, lean_object* v_splitterName_3255_, lean_object* v_matcherLevels_3256_, lean_object* v_params_x27_3257_, lean_object* v_fst_3258_, lean_object* v_discrs_x27_3259_, lean_object* v_toPure_3260_, lean_object* v_onRemaining_3261_, lean_object* v_remaining_3262_, lean_object* v_toBind_3263_, lean_object* v_origAltTypes_3264_, lean_object* v_alts_3265_, lean_object* v___x_3266_, lean_object* v___x_3267_, lean_object* v_remaining_x27_3268_, lean_object* v___f_3269_, lean_object* v_altTypes_3270_){
_start:
{
lean_object* v_altInfos_3271_; lean_object* v___f_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
v_altInfos_3271_ = lean_ctor_get(v_splitterMatchInfo_3247_, 2);
lean_inc_ref(v_altInfos_3271_);
lean_dec_ref(v_splitterMatchInfo_3247_);
lean_inc(v_toBind_3263_);
lean_inc_ref(v_altInfos_3251_);
v___f_3272_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__50___boxed), 17, 16);
lean_closure_set(v___f_3272_, 0, v_fst_3248_);
lean_closure_set(v___f_3272_, 1, v_numParams_3249_);
lean_closure_set(v___f_3272_, 2, v_numDiscrs_3250_);
lean_closure_set(v___f_3272_, 3, v_altInfos_3251_);
lean_closure_set(v___f_3272_, 4, v_uElimPos_x3f_3252_);
lean_closure_set(v___f_3272_, 5, v_snd_3253_);
lean_closure_set(v___f_3272_, 6, v_overlaps_3254_);
lean_closure_set(v___f_3272_, 7, v_splitterName_3255_);
lean_closure_set(v___f_3272_, 8, v_matcherLevels_3256_);
lean_closure_set(v___f_3272_, 9, v_params_x27_3257_);
lean_closure_set(v___f_3272_, 10, v_fst_3258_);
lean_closure_set(v___f_3272_, 11, v_discrs_x27_3259_);
lean_closure_set(v___f_3272_, 12, v_toPure_3260_);
lean_closure_set(v___f_3272_, 13, v_onRemaining_3261_);
lean_closure_set(v___f_3272_, 14, v_remaining_3262_);
lean_closure_set(v___f_3272_, 15, v_toBind_3263_);
v___x_3273_ = lean_array_get_size(v_altInfos_3251_);
v___x_3274_ = lean_array_get_size(v_altInfos_3271_);
v___x_3275_ = lean_array_get_size(v_origAltTypes_3264_);
v___x_3276_ = lean_array_get_size(v_altTypes_3270_);
lean_inc_n(v___x_3266_, 5);
v___x_3277_ = l_Array_toSubarray___redArg(v_alts_3265_, v___x_3266_, v___x_3267_);
v___x_3278_ = l_Array_toSubarray___redArg(v_altInfos_3251_, v___x_3266_, v___x_3273_);
v___x_3279_ = l_Array_toSubarray___redArg(v_altInfos_3271_, v___x_3266_, v___x_3274_);
v___x_3280_ = l_Array_toSubarray___redArg(v_origAltTypes_3264_, v___x_3266_, v___x_3275_);
v___x_3281_ = l_Array_toSubarray___redArg(v_altTypes_3270_, v___x_3266_, v___x_3276_);
v___x_3282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3280_);
lean_ctor_set(v___x_3282_, 1, v___x_3281_);
v___x_3283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3279_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
v___x_3284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3278_);
lean_ctor_set(v___x_3284_, 1, v___x_3283_);
v___x_3285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3277_);
lean_ctor_set(v___x_3285_, 1, v___x_3284_);
v___x_3286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3286_, 0, v_remaining_x27_3268_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
v___x_3287_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3269_, v___x_3266_, v___x_3286_, lean_box(0));
v___x_3288_ = lean_apply_4(v_toBind_3263_, lean_box(0), lean_box(0), v___x_3287_, v___f_3272_);
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed(lean_object** _args){
lean_object* v_splitterMatchInfo_3289_ = _args[0];
lean_object* v_fst_3290_ = _args[1];
lean_object* v_numParams_3291_ = _args[2];
lean_object* v_numDiscrs_3292_ = _args[3];
lean_object* v_altInfos_3293_ = _args[4];
lean_object* v_uElimPos_x3f_3294_ = _args[5];
lean_object* v_snd_3295_ = _args[6];
lean_object* v_overlaps_3296_ = _args[7];
lean_object* v_splitterName_3297_ = _args[8];
lean_object* v_matcherLevels_3298_ = _args[9];
lean_object* v_params_x27_3299_ = _args[10];
lean_object* v_fst_3300_ = _args[11];
lean_object* v_discrs_x27_3301_ = _args[12];
lean_object* v_toPure_3302_ = _args[13];
lean_object* v_onRemaining_3303_ = _args[14];
lean_object* v_remaining_3304_ = _args[15];
lean_object* v_toBind_3305_ = _args[16];
lean_object* v_origAltTypes_3306_ = _args[17];
lean_object* v_alts_3307_ = _args[18];
lean_object* v___x_3308_ = _args[19];
lean_object* v___x_3309_ = _args[20];
lean_object* v_remaining_x27_3310_ = _args[21];
lean_object* v___f_3311_ = _args[22];
lean_object* v_altTypes_3312_ = _args[23];
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__51(v_splitterMatchInfo_3289_, v_fst_3290_, v_numParams_3291_, v_numDiscrs_3292_, v_altInfos_3293_, v_uElimPos_x3f_3294_, v_snd_3295_, v_overlaps_3296_, v_splitterName_3297_, v_matcherLevels_3298_, v_params_x27_3299_, v_fst_3300_, v_discrs_x27_3301_, v_toPure_3302_, v_onRemaining_3303_, v_remaining_3304_, v_toBind_3305_, v_origAltTypes_3306_, v_alts_3307_, v___x_3308_, v___x_3309_, v_remaining_x27_3310_, v___f_3311_, v_altTypes_3312_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52(lean_object* v___x_3314_, lean_object* v_aux2_3315_, lean_object* v_inst_3316_, lean_object* v_toBind_3317_, lean_object* v___f_3318_, lean_object* v_____r_3319_){
_start:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3320_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_3320_, 0, v___x_3314_);
lean_closure_set(v___x_3320_, 1, v_aux2_3315_);
v___x_3321_ = lean_apply_2(v_inst_3316_, lean_box(0), v___x_3320_);
v___x_3322_ = lean_apply_4(v_toBind_3317_, lean_box(0), lean_box(0), v___x_3321_, v___f_3318_);
return v___x_3322_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1(void){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3324_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__0));
v___x_3325_ = l_Lean_stringToMessageData(v___x_3324_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55(lean_object* v___x_3326_, lean_object* v_params_x27_3327_, lean_object* v_fst_3328_, lean_object* v_discrs_x27_3329_, lean_object* v_fst_3330_, lean_object* v_numParams_3331_, lean_object* v_numDiscrs_3332_, lean_object* v_altInfos_3333_, lean_object* v_uElimPos_x3f_3334_, lean_object* v_snd_3335_, lean_object* v_overlaps_3336_, lean_object* v_matcherLevels_3337_, lean_object* v_toPure_3338_, lean_object* v_onRemaining_3339_, lean_object* v_remaining_3340_, lean_object* v_toBind_3341_, lean_object* v_origAltTypes_3342_, lean_object* v_alts_3343_, lean_object* v___x_3344_, lean_object* v___x_3345_, lean_object* v_remaining_x27_3346_, lean_object* v___f_3347_, lean_object* v_inst_3348_, lean_object* v___x_3349_, uint8_t v___x_3350_, lean_object* v_liftWith_3351_, lean_object* v_restoreM_3352_, lean_object* v_matchEqns_3353_){
_start:
{
lean_object* v_splitterName_3354_; lean_object* v_splitterMatchInfo_3355_; lean_object* v___x_3356_; lean_object* v_aux2_3357_; lean_object* v_aux2_3358_; lean_object* v_aux2_3359_; lean_object* v___x_3360_; lean_object* v___f_3361_; lean_object* v___f_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___f_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___f_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v_splitterName_3354_ = lean_ctor_get(v_matchEqns_3353_, 1);
lean_inc_n(v_splitterName_3354_, 2);
v_splitterMatchInfo_3355_ = lean_ctor_get(v_matchEqns_3353_, 2);
lean_inc_ref(v_splitterMatchInfo_3355_);
lean_dec_ref(v_matchEqns_3353_);
v___x_3356_ = l_Lean_mkConst(v_splitterName_3354_, v___x_3326_);
v_aux2_3357_ = l_Lean_mkAppN(v___x_3356_, v_params_x27_3327_);
lean_inc_ref(v_fst_3328_);
v_aux2_3358_ = l_Lean_Expr_app___override(v_aux2_3357_, v_fst_3328_);
v_aux2_3359_ = l_Lean_mkAppN(v_aux2_3358_, v_discrs_x27_3329_);
lean_inc_ref_n(v_aux2_3359_, 2);
v___x_3360_ = l_Lean_indentExpr(v_aux2_3359_);
lean_inc(v___x_3345_);
lean_inc_n(v_toBind_3341_, 3);
v___f_3361_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed), 24, 23);
lean_closure_set(v___f_3361_, 0, v_splitterMatchInfo_3355_);
lean_closure_set(v___f_3361_, 1, v_fst_3330_);
lean_closure_set(v___f_3361_, 2, v_numParams_3331_);
lean_closure_set(v___f_3361_, 3, v_numDiscrs_3332_);
lean_closure_set(v___f_3361_, 4, v_altInfos_3333_);
lean_closure_set(v___f_3361_, 5, v_uElimPos_x3f_3334_);
lean_closure_set(v___f_3361_, 6, v_snd_3335_);
lean_closure_set(v___f_3361_, 7, v_overlaps_3336_);
lean_closure_set(v___f_3361_, 8, v_splitterName_3354_);
lean_closure_set(v___f_3361_, 9, v_matcherLevels_3337_);
lean_closure_set(v___f_3361_, 10, v_params_x27_3327_);
lean_closure_set(v___f_3361_, 11, v_fst_3328_);
lean_closure_set(v___f_3361_, 12, v_discrs_x27_3329_);
lean_closure_set(v___f_3361_, 13, v_toPure_3338_);
lean_closure_set(v___f_3361_, 14, v_onRemaining_3339_);
lean_closure_set(v___f_3361_, 15, v_remaining_3340_);
lean_closure_set(v___f_3361_, 16, v_toBind_3341_);
lean_closure_set(v___f_3361_, 17, v_origAltTypes_3342_);
lean_closure_set(v___f_3361_, 18, v_alts_3343_);
lean_closure_set(v___f_3361_, 19, v___x_3344_);
lean_closure_set(v___f_3361_, 20, v___x_3345_);
lean_closure_set(v___f_3361_, 21, v_remaining_x27_3346_);
lean_closure_set(v___f_3361_, 22, v___f_3347_);
lean_inc(v_inst_3348_);
v___f_3362_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__52), 6, 5);
lean_closure_set(v___f_3362_, 0, v___x_3345_);
lean_closure_set(v___f_3362_, 1, v_aux2_3359_);
lean_closure_set(v___f_3362_, 2, v_inst_3348_);
lean_closure_set(v___f_3362_, 3, v_toBind_3341_);
lean_closure_set(v___f_3362_, 4, v___f_3361_);
v___x_3363_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1);
v___x_3364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
lean_ctor_set(v___x_3364_, 1, v___x_3360_);
v___x_3365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3364_);
lean_ctor_set(v___x_3365_, 1, v___x_3349_);
v___f_3366_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34), 2, 1);
lean_closure_set(v___f_3366_, 0, v___x_3365_);
v___x_3367_ = lean_box(v___x_3350_);
v___x_3368_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_3368_, 0, v_aux2_3359_);
lean_closure_set(v___x_3368_, 1, v___x_3367_);
v___x_3369_ = lean_apply_2(v_inst_3348_, lean_box(0), v___x_3368_);
v___f_3370_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed), 8, 2);
lean_closure_set(v___f_3370_, 0, v___x_3369_);
lean_closure_set(v___f_3370_, 1, v___f_3366_);
v___x_3371_ = lean_apply_2(v_liftWith_3351_, lean_box(0), v___f_3370_);
v___x_3372_ = lean_apply_1(v_restoreM_3352_, lean_box(0));
v___x_3373_ = lean_apply_4(v_toBind_3341_, lean_box(0), lean_box(0), v___x_3371_, v___x_3372_);
v___x_3374_ = lean_apply_4(v_toBind_3341_, lean_box(0), lean_box(0), v___x_3373_, v___f_3362_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___boxed(lean_object** _args){
lean_object* v___x_3375_ = _args[0];
lean_object* v_params_x27_3376_ = _args[1];
lean_object* v_fst_3377_ = _args[2];
lean_object* v_discrs_x27_3378_ = _args[3];
lean_object* v_fst_3379_ = _args[4];
lean_object* v_numParams_3380_ = _args[5];
lean_object* v_numDiscrs_3381_ = _args[6];
lean_object* v_altInfos_3382_ = _args[7];
lean_object* v_uElimPos_x3f_3383_ = _args[8];
lean_object* v_snd_3384_ = _args[9];
lean_object* v_overlaps_3385_ = _args[10];
lean_object* v_matcherLevels_3386_ = _args[11];
lean_object* v_toPure_3387_ = _args[12];
lean_object* v_onRemaining_3388_ = _args[13];
lean_object* v_remaining_3389_ = _args[14];
lean_object* v_toBind_3390_ = _args[15];
lean_object* v_origAltTypes_3391_ = _args[16];
lean_object* v_alts_3392_ = _args[17];
lean_object* v___x_3393_ = _args[18];
lean_object* v___x_3394_ = _args[19];
lean_object* v_remaining_x27_3395_ = _args[20];
lean_object* v___f_3396_ = _args[21];
lean_object* v_inst_3397_ = _args[22];
lean_object* v___x_3398_ = _args[23];
lean_object* v___x_3399_ = _args[24];
lean_object* v_liftWith_3400_ = _args[25];
lean_object* v_restoreM_3401_ = _args[26];
lean_object* v_matchEqns_3402_ = _args[27];
_start:
{
uint8_t v___x_14533__boxed_3403_; lean_object* v_res_3404_; 
v___x_14533__boxed_3403_ = lean_unbox(v___x_3399_);
v_res_3404_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__55(v___x_3375_, v_params_x27_3376_, v_fst_3377_, v_discrs_x27_3378_, v_fst_3379_, v_numParams_3380_, v_numDiscrs_3381_, v_altInfos_3382_, v_uElimPos_x3f_3383_, v_snd_3384_, v_overlaps_3385_, v_matcherLevels_3386_, v_toPure_3387_, v_onRemaining_3388_, v_remaining_3389_, v_toBind_3390_, v_origAltTypes_3391_, v_alts_3392_, v___x_3393_, v___x_3394_, v_remaining_x27_3395_, v___f_3396_, v_inst_3397_, v___x_3398_, v___x_14533__boxed_3403_, v_liftWith_3400_, v_restoreM_3401_, v_matchEqns_3402_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53(lean_object* v___x_3405_, lean_object* v_params_x27_3406_, lean_object* v_fst_3407_, lean_object* v_discrs_x27_3408_, lean_object* v_fst_3409_, lean_object* v_numParams_3410_, lean_object* v_numDiscrs_3411_, lean_object* v_altInfos_3412_, lean_object* v_uElimPos_x3f_3413_, lean_object* v_snd_3414_, lean_object* v_overlaps_3415_, lean_object* v_matcherLevels_3416_, lean_object* v_toPure_3417_, lean_object* v_onRemaining_3418_, lean_object* v_remaining_3419_, lean_object* v_toBind_3420_, lean_object* v_alts_3421_, lean_object* v___x_3422_, lean_object* v___x_3423_, lean_object* v_remaining_x27_3424_, lean_object* v___f_3425_, lean_object* v_inst_3426_, lean_object* v___x_3427_, uint8_t v___x_3428_, lean_object* v_liftWith_3429_, lean_object* v_restoreM_3430_, lean_object* v_matcherName_3431_, lean_object* v_origAltTypes_3432_){
_start:
{
lean_object* v___x_3433_; lean_object* v___f_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3433_ = lean_box(v___x_3428_);
lean_inc(v_inst_3426_);
lean_inc(v_toBind_3420_);
v___f_3434_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___boxed), 28, 27);
lean_closure_set(v___f_3434_, 0, v___x_3405_);
lean_closure_set(v___f_3434_, 1, v_params_x27_3406_);
lean_closure_set(v___f_3434_, 2, v_fst_3407_);
lean_closure_set(v___f_3434_, 3, v_discrs_x27_3408_);
lean_closure_set(v___f_3434_, 4, v_fst_3409_);
lean_closure_set(v___f_3434_, 5, v_numParams_3410_);
lean_closure_set(v___f_3434_, 6, v_numDiscrs_3411_);
lean_closure_set(v___f_3434_, 7, v_altInfos_3412_);
lean_closure_set(v___f_3434_, 8, v_uElimPos_x3f_3413_);
lean_closure_set(v___f_3434_, 9, v_snd_3414_);
lean_closure_set(v___f_3434_, 10, v_overlaps_3415_);
lean_closure_set(v___f_3434_, 11, v_matcherLevels_3416_);
lean_closure_set(v___f_3434_, 12, v_toPure_3417_);
lean_closure_set(v___f_3434_, 13, v_onRemaining_3418_);
lean_closure_set(v___f_3434_, 14, v_remaining_3419_);
lean_closure_set(v___f_3434_, 15, v_toBind_3420_);
lean_closure_set(v___f_3434_, 16, v_origAltTypes_3432_);
lean_closure_set(v___f_3434_, 17, v_alts_3421_);
lean_closure_set(v___f_3434_, 18, v___x_3422_);
lean_closure_set(v___f_3434_, 19, v___x_3423_);
lean_closure_set(v___f_3434_, 20, v_remaining_x27_3424_);
lean_closure_set(v___f_3434_, 21, v___f_3425_);
lean_closure_set(v___f_3434_, 22, v_inst_3426_);
lean_closure_set(v___f_3434_, 23, v___x_3427_);
lean_closure_set(v___f_3434_, 24, v___x_3433_);
lean_closure_set(v___f_3434_, 25, v_liftWith_3429_);
lean_closure_set(v___f_3434_, 26, v_restoreM_3430_);
v___x_3435_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_getEquationsFor___boxed), 6, 1);
lean_closure_set(v___x_3435_, 0, v_matcherName_3431_);
v___x_3436_ = lean_apply_2(v_inst_3426_, lean_box(0), v___x_3435_);
v___x_3437_ = lean_apply_4(v_toBind_3420_, lean_box(0), lean_box(0), v___x_3436_, v___f_3434_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed(lean_object** _args){
lean_object* v___x_3438_ = _args[0];
lean_object* v_params_x27_3439_ = _args[1];
lean_object* v_fst_3440_ = _args[2];
lean_object* v_discrs_x27_3441_ = _args[3];
lean_object* v_fst_3442_ = _args[4];
lean_object* v_numParams_3443_ = _args[5];
lean_object* v_numDiscrs_3444_ = _args[6];
lean_object* v_altInfos_3445_ = _args[7];
lean_object* v_uElimPos_x3f_3446_ = _args[8];
lean_object* v_snd_3447_ = _args[9];
lean_object* v_overlaps_3448_ = _args[10];
lean_object* v_matcherLevels_3449_ = _args[11];
lean_object* v_toPure_3450_ = _args[12];
lean_object* v_onRemaining_3451_ = _args[13];
lean_object* v_remaining_3452_ = _args[14];
lean_object* v_toBind_3453_ = _args[15];
lean_object* v_alts_3454_ = _args[16];
lean_object* v___x_3455_ = _args[17];
lean_object* v___x_3456_ = _args[18];
lean_object* v_remaining_x27_3457_ = _args[19];
lean_object* v___f_3458_ = _args[20];
lean_object* v_inst_3459_ = _args[21];
lean_object* v___x_3460_ = _args[22];
lean_object* v___x_3461_ = _args[23];
lean_object* v_liftWith_3462_ = _args[24];
lean_object* v_restoreM_3463_ = _args[25];
lean_object* v_matcherName_3464_ = _args[26];
lean_object* v_origAltTypes_3465_ = _args[27];
_start:
{
uint8_t v___x_14595__boxed_3466_; lean_object* v_res_3467_; 
v___x_14595__boxed_3466_ = lean_unbox(v___x_3461_);
v_res_3467_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__53(v___x_3438_, v_params_x27_3439_, v_fst_3440_, v_discrs_x27_3441_, v_fst_3442_, v_numParams_3443_, v_numDiscrs_3444_, v_altInfos_3445_, v_uElimPos_x3f_3446_, v_snd_3447_, v_overlaps_3448_, v_matcherLevels_3449_, v_toPure_3450_, v_onRemaining_3451_, v_remaining_3452_, v_toBind_3453_, v_alts_3454_, v___x_3455_, v___x_3456_, v_remaining_x27_3457_, v___f_3458_, v_inst_3459_, v___x_3460_, v___x_14595__boxed_3466_, v_liftWith_3462_, v_restoreM_3463_, v_matcherName_3464_, v_origAltTypes_3465_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54(lean_object* v_alts_3468_, lean_object* v_toPure_3469_, lean_object* v_toBind_3470_, lean_object* v___f_3471_, lean_object* v___x_3472_, lean_object* v___x_3473_, lean_object* v_inst_3474_, lean_object* v___x_3475_, lean_object* v_toMonadExceptOf_3476_, uint8_t v___x_3477_, uint8_t v_useSplitter_3478_, lean_object* v_onAlt_3479_, lean_object* v___f_3480_, lean_object* v_fst_3481_, lean_object* v_inst_3482_, lean_object* v_inst_3483_, lean_object* v_numDiscrEqs_3484_, lean_object* v___x_3485_, lean_object* v_params_x27_3486_, lean_object* v_fst_3487_, lean_object* v_discrs_x27_3488_, lean_object* v_fst_3489_, lean_object* v_numParams_3490_, lean_object* v_numDiscrs_3491_, lean_object* v_altInfos_3492_, lean_object* v_uElimPos_x3f_3493_, lean_object* v_snd_3494_, lean_object* v_overlaps_3495_, lean_object* v_matcherLevels_3496_, lean_object* v_onRemaining_3497_, lean_object* v_remaining_3498_, lean_object* v_remaining_x27_3499_, lean_object* v___x_3500_, uint8_t v___x_3501_, lean_object* v_liftWith_3502_, lean_object* v_restoreM_3503_, lean_object* v_matcherName_3504_, lean_object* v_aux1_3505_, lean_object* v_____r_3506_){
_start:
{
lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___f_3510_; lean_object* v___x_3511_; lean_object* v___f_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3507_ = lean_array_get_size(v_alts_3468_);
v___x_3508_ = lean_box(v___x_3477_);
v___x_3509_ = lean_box(v_useSplitter_3478_);
lean_inc_n(v_inst_3474_, 2);
lean_inc(v___x_3472_);
lean_inc_n(v_toBind_3470_, 2);
lean_inc(v_toPure_3469_);
v___f_3510_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 21, 17);
lean_closure_set(v___f_3510_, 0, v___x_3507_);
lean_closure_set(v___f_3510_, 1, v_toPure_3469_);
lean_closure_set(v___f_3510_, 2, v_toBind_3470_);
lean_closure_set(v___f_3510_, 3, v___f_3471_);
lean_closure_set(v___f_3510_, 4, v___x_3472_);
lean_closure_set(v___f_3510_, 5, v___x_3473_);
lean_closure_set(v___f_3510_, 6, v_inst_3474_);
lean_closure_set(v___f_3510_, 7, v___x_3475_);
lean_closure_set(v___f_3510_, 8, v_toMonadExceptOf_3476_);
lean_closure_set(v___f_3510_, 9, v___x_3508_);
lean_closure_set(v___f_3510_, 10, v___x_3509_);
lean_closure_set(v___f_3510_, 11, v_onAlt_3479_);
lean_closure_set(v___f_3510_, 12, v___f_3480_);
lean_closure_set(v___f_3510_, 13, v_fst_3481_);
lean_closure_set(v___f_3510_, 14, v_inst_3482_);
lean_closure_set(v___f_3510_, 15, v_inst_3483_);
lean_closure_set(v___f_3510_, 16, v_numDiscrEqs_3484_);
v___x_3511_ = lean_box(v___x_3501_);
v___f_3512_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed), 28, 27);
lean_closure_set(v___f_3512_, 0, v___x_3485_);
lean_closure_set(v___f_3512_, 1, v_params_x27_3486_);
lean_closure_set(v___f_3512_, 2, v_fst_3487_);
lean_closure_set(v___f_3512_, 3, v_discrs_x27_3488_);
lean_closure_set(v___f_3512_, 4, v_fst_3489_);
lean_closure_set(v___f_3512_, 5, v_numParams_3490_);
lean_closure_set(v___f_3512_, 6, v_numDiscrs_3491_);
lean_closure_set(v___f_3512_, 7, v_altInfos_3492_);
lean_closure_set(v___f_3512_, 8, v_uElimPos_x3f_3493_);
lean_closure_set(v___f_3512_, 9, v_snd_3494_);
lean_closure_set(v___f_3512_, 10, v_overlaps_3495_);
lean_closure_set(v___f_3512_, 11, v_matcherLevels_3496_);
lean_closure_set(v___f_3512_, 12, v_toPure_3469_);
lean_closure_set(v___f_3512_, 13, v_onRemaining_3497_);
lean_closure_set(v___f_3512_, 14, v_remaining_3498_);
lean_closure_set(v___f_3512_, 15, v_toBind_3470_);
lean_closure_set(v___f_3512_, 16, v_alts_3468_);
lean_closure_set(v___f_3512_, 17, v___x_3472_);
lean_closure_set(v___f_3512_, 18, v___x_3507_);
lean_closure_set(v___f_3512_, 19, v_remaining_x27_3499_);
lean_closure_set(v___f_3512_, 20, v___f_3510_);
lean_closure_set(v___f_3512_, 21, v_inst_3474_);
lean_closure_set(v___f_3512_, 22, v___x_3500_);
lean_closure_set(v___f_3512_, 23, v___x_3511_);
lean_closure_set(v___f_3512_, 24, v_liftWith_3502_);
lean_closure_set(v___f_3512_, 25, v_restoreM_3503_);
lean_closure_set(v___f_3512_, 26, v_matcherName_3504_);
v___x_3513_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_3513_, 0, v___x_3507_);
lean_closure_set(v___x_3513_, 1, v_aux1_3505_);
v___x_3514_ = lean_apply_2(v_inst_3474_, lean_box(0), v___x_3513_);
v___x_3515_ = lean_apply_4(v_toBind_3470_, lean_box(0), lean_box(0), v___x_3514_, v___f_3512_);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed(lean_object** _args){
lean_object* v_alts_3516_ = _args[0];
lean_object* v_toPure_3517_ = _args[1];
lean_object* v_toBind_3518_ = _args[2];
lean_object* v___f_3519_ = _args[3];
lean_object* v___x_3520_ = _args[4];
lean_object* v___x_3521_ = _args[5];
lean_object* v_inst_3522_ = _args[6];
lean_object* v___x_3523_ = _args[7];
lean_object* v_toMonadExceptOf_3524_ = _args[8];
lean_object* v___x_3525_ = _args[9];
lean_object* v_useSplitter_3526_ = _args[10];
lean_object* v_onAlt_3527_ = _args[11];
lean_object* v___f_3528_ = _args[12];
lean_object* v_fst_3529_ = _args[13];
lean_object* v_inst_3530_ = _args[14];
lean_object* v_inst_3531_ = _args[15];
lean_object* v_numDiscrEqs_3532_ = _args[16];
lean_object* v___x_3533_ = _args[17];
lean_object* v_params_x27_3534_ = _args[18];
lean_object* v_fst_3535_ = _args[19];
lean_object* v_discrs_x27_3536_ = _args[20];
lean_object* v_fst_3537_ = _args[21];
lean_object* v_numParams_3538_ = _args[22];
lean_object* v_numDiscrs_3539_ = _args[23];
lean_object* v_altInfos_3540_ = _args[24];
lean_object* v_uElimPos_x3f_3541_ = _args[25];
lean_object* v_snd_3542_ = _args[26];
lean_object* v_overlaps_3543_ = _args[27];
lean_object* v_matcherLevels_3544_ = _args[28];
lean_object* v_onRemaining_3545_ = _args[29];
lean_object* v_remaining_3546_ = _args[30];
lean_object* v_remaining_x27_3547_ = _args[31];
lean_object* v___x_3548_ = _args[32];
lean_object* v___x_3549_ = _args[33];
lean_object* v_liftWith_3550_ = _args[34];
lean_object* v_restoreM_3551_ = _args[35];
lean_object* v_matcherName_3552_ = _args[36];
lean_object* v_aux1_3553_ = _args[37];
lean_object* v_____r_3554_ = _args[38];
_start:
{
uint8_t v___x_14629__boxed_3555_; uint8_t v_useSplitter_boxed_3556_; uint8_t v___x_14637__boxed_3557_; lean_object* v_res_3558_; 
v___x_14629__boxed_3555_ = lean_unbox(v___x_3525_);
v_useSplitter_boxed_3556_ = lean_unbox(v_useSplitter_3526_);
v___x_14637__boxed_3557_ = lean_unbox(v___x_3549_);
v_res_3558_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__54(v_alts_3516_, v_toPure_3517_, v_toBind_3518_, v___f_3519_, v___x_3520_, v___x_3521_, v_inst_3522_, v___x_3523_, v_toMonadExceptOf_3524_, v___x_14629__boxed_3555_, v_useSplitter_boxed_3556_, v_onAlt_3527_, v___f_3528_, v_fst_3529_, v_inst_3530_, v_inst_3531_, v_numDiscrEqs_3532_, v___x_3533_, v_params_x27_3534_, v_fst_3535_, v_discrs_x27_3536_, v_fst_3537_, v_numParams_3538_, v_numDiscrs_3539_, v_altInfos_3540_, v_uElimPos_x3f_3541_, v_snd_3542_, v_overlaps_3543_, v_matcherLevels_3544_, v_onRemaining_3545_, v_remaining_3546_, v_remaining_x27_3547_, v___x_3548_, v___x_14637__boxed_3557_, v_liftWith_3550_, v_restoreM_3551_, v_matcherName_3552_, v_aux1_3553_, v_____r_3554_);
return v_res_3558_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__1(void){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3560_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__0));
v___x_3561_ = l_Lean_stringToMessageData(v___x_3560_);
return v___x_3561_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__3(void){
_start:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3563_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__2));
v___x_3564_ = l_Lean_stringToMessageData(v___x_3563_);
return v___x_3564_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__5(void){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3566_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__4));
v___x_3567_ = l_Lean_stringToMessageData(v___x_3566_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57(lean_object* v_numParams_3568_, lean_object* v_numDiscrs_3569_, lean_object* v_altInfos_3570_, lean_object* v_uElimPos_x3f_3571_, lean_object* v_snd_3572_, lean_object* v_overlaps_3573_, lean_object* v_matcherName_3574_, lean_object* v_matcherLevels_3575_, lean_object* v_params_x27_3576_, lean_object* v_fst_3577_, lean_object* v_discrs_x27_3578_, lean_object* v_toPure_3579_, lean_object* v_onRemaining_3580_, lean_object* v_remaining_3581_, lean_object* v_toBind_3582_, lean_object* v_inst_3583_, lean_object* v_alts_3584_, lean_object* v___f_3585_, uint8_t v___x_3586_, lean_object* v_inst_3587_, lean_object* v_remaining_x27_3588_, lean_object* v_onAlt_3589_, lean_object* v_inst_3590_, lean_object* v___f_3591_, lean_object* v_matcherApp_3592_, lean_object* v___x_3593_, uint8_t v_useSplitter_3594_, uint8_t v_isCasesOn_3595_, lean_object* v___f_3596_, lean_object* v___x_3597_, lean_object* v___x_3598_, lean_object* v_toMonadExceptOf_3599_, lean_object* v___f_3600_, lean_object* v_numDiscrEqs_3601_, lean_object* v_____s_3602_){
_start:
{
lean_object* v_snd_3603_; lean_object* v_fst_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3670_; 
v_snd_3603_ = lean_ctor_get(v_____s_3602_, 1);
v_fst_3604_ = lean_ctor_get(v_____s_3602_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v_____s_3602_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3606_ = v_____s_3602_;
v_isShared_3607_ = v_isSharedCheck_3670_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_snd_3603_);
lean_inc(v_fst_3604_);
lean_dec(v_____s_3602_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3670_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v_fst_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3668_; 
v_fst_3608_ = lean_ctor_get(v_snd_3603_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v_snd_3603_);
if (v_isSharedCheck_3668_ == 0)
{
lean_object* v_unused_3669_; 
v_unused_3669_ = lean_ctor_get(v_snd_3603_, 1);
lean_dec(v_unused_3669_);
v___x_3610_ = v_snd_3603_;
v_isShared_3611_ = v_isSharedCheck_3668_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_fst_3608_);
lean_dec(v_snd_3603_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3668_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___f_3612_; 
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
lean_inc(v_fst_3604_);
v___f_3612_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed), 17, 16);
lean_closure_set(v___f_3612_, 0, v_fst_3604_);
lean_closure_set(v___f_3612_, 1, v_numParams_3568_);
lean_closure_set(v___f_3612_, 2, v_numDiscrs_3569_);
lean_closure_set(v___f_3612_, 3, v_altInfos_3570_);
lean_closure_set(v___f_3612_, 4, v_uElimPos_x3f_3571_);
lean_closure_set(v___f_3612_, 5, v_snd_3572_);
lean_closure_set(v___f_3612_, 6, v_overlaps_3573_);
lean_closure_set(v___f_3612_, 7, v_matcherName_3574_);
lean_closure_set(v___f_3612_, 8, v_matcherLevels_3575_);
lean_closure_set(v___f_3612_, 9, v_params_x27_3576_);
lean_closure_set(v___f_3612_, 10, v_fst_3577_);
lean_closure_set(v___f_3612_, 11, v_discrs_x27_3578_);
lean_closure_set(v___f_3612_, 12, v_toPure_3579_);
lean_closure_set(v___f_3612_, 13, v_onRemaining_3580_);
lean_closure_set(v___f_3612_, 14, v_remaining_3581_);
lean_closure_set(v___f_3612_, 15, v_toBind_3582_);
if (v_useSplitter_3594_ == 0)
{
lean_del_object(v___x_3606_);
lean_dec(v_fst_3604_);
lean_dec(v_numDiscrEqs_3601_);
lean_dec(v___f_3600_);
lean_dec_ref(v_toMonadExceptOf_3599_);
lean_dec(v___x_3598_);
lean_dec(v___x_3597_);
lean_dec(v___f_3596_);
lean_dec_ref(v_remaining_3581_);
lean_dec(v_onRemaining_3580_);
lean_dec_ref(v_overlaps_3573_);
lean_dec_ref(v_snd_3572_);
lean_dec(v_uElimPos_x3f_3571_);
lean_dec_ref(v_altInfos_3570_);
lean_dec(v_numDiscrs_3569_);
lean_dec(v_numParams_3568_);
goto v___jp_3613_;
}
else
{
if (v_isCasesOn_3595_ == 0)
{
lean_object* v_liftWith_3640_; lean_object* v_restoreM_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v_aux1_3644_; lean_object* v_aux1_3645_; lean_object* v_aux1_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3650_; 
lean_dec_ref(v___f_3612_);
lean_del_object(v___x_3610_);
lean_dec_ref(v_matcherApp_3592_);
lean_dec(v___f_3591_);
lean_dec(v___f_3585_);
v_liftWith_3640_ = lean_ctor_get(v_inst_3583_, 0);
lean_inc(v_liftWith_3640_);
v_restoreM_3641_ = lean_ctor_get(v_inst_3583_, 1);
lean_inc(v_restoreM_3641_);
lean_inc_ref(v_matcherLevels_3575_);
v___x_3642_ = lean_array_to_list(v_matcherLevels_3575_);
lean_inc(v___x_3642_);
lean_inc(v_matcherName_3574_);
v___x_3643_ = l_Lean_mkConst(v_matcherName_3574_, v___x_3642_);
v_aux1_3644_ = l_Lean_mkAppN(v___x_3643_, v_params_x27_3576_);
lean_inc_ref(v_fst_3577_);
v_aux1_3645_ = l_Lean_Expr_app___override(v_aux1_3644_, v_fst_3577_);
v_aux1_3646_ = l_Lean_mkAppN(v_aux1_3645_, v_discrs_x27_3578_);
lean_inc_ref(v_aux1_3646_);
v___x_3647_ = l_Lean_indentExpr(v_aux1_3646_);
v___x_3648_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__3);
if (v_isShared_3607_ == 0)
{
lean_ctor_set_tag(v___x_3606_, 7);
lean_ctor_set(v___x_3606_, 1, v___x_3647_);
lean_ctor_set(v___x_3606_, 0, v___x_3648_);
v___x_3650_ = v___x_3606_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3648_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v___x_3647_);
v___x_3650_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___f_3653_; uint8_t v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___f_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___f_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3651_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__5);
v___x_3652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3650_);
lean_ctor_set(v___x_3652_, 1, v___x_3651_);
v___f_3653_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34), 2, 1);
lean_closure_set(v___f_3653_, 0, v___x_3652_);
v___x_3654_ = 0;
v___x_3655_ = lean_box(v___x_3586_);
v___x_3656_ = lean_box(v_useSplitter_3594_);
v___x_3657_ = lean_box(v___x_3654_);
lean_inc_ref(v_aux1_3646_);
lean_inc(v_restoreM_3641_);
lean_inc(v_liftWith_3640_);
lean_inc(v_inst_3587_);
lean_inc_n(v_toBind_3582_, 2);
v___f_3658_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed), 39, 38);
lean_closure_set(v___f_3658_, 0, v_alts_3584_);
lean_closure_set(v___f_3658_, 1, v_toPure_3579_);
lean_closure_set(v___f_3658_, 2, v_toBind_3582_);
lean_closure_set(v___f_3658_, 3, v___f_3596_);
lean_closure_set(v___f_3658_, 4, v___x_3593_);
lean_closure_set(v___f_3658_, 5, v___x_3597_);
lean_closure_set(v___f_3658_, 6, v_inst_3587_);
lean_closure_set(v___f_3658_, 7, v___x_3598_);
lean_closure_set(v___f_3658_, 8, v_toMonadExceptOf_3599_);
lean_closure_set(v___f_3658_, 9, v___x_3655_);
lean_closure_set(v___f_3658_, 10, v___x_3656_);
lean_closure_set(v___f_3658_, 11, v_onAlt_3589_);
lean_closure_set(v___f_3658_, 12, v___f_3600_);
lean_closure_set(v___f_3658_, 13, v_fst_3608_);
lean_closure_set(v___f_3658_, 14, v_inst_3583_);
lean_closure_set(v___f_3658_, 15, v_inst_3590_);
lean_closure_set(v___f_3658_, 16, v_numDiscrEqs_3601_);
lean_closure_set(v___f_3658_, 17, v___x_3642_);
lean_closure_set(v___f_3658_, 18, v_params_x27_3576_);
lean_closure_set(v___f_3658_, 19, v_fst_3577_);
lean_closure_set(v___f_3658_, 20, v_discrs_x27_3578_);
lean_closure_set(v___f_3658_, 21, v_fst_3604_);
lean_closure_set(v___f_3658_, 22, v_numParams_3568_);
lean_closure_set(v___f_3658_, 23, v_numDiscrs_3569_);
lean_closure_set(v___f_3658_, 24, v_altInfos_3570_);
lean_closure_set(v___f_3658_, 25, v_uElimPos_x3f_3571_);
lean_closure_set(v___f_3658_, 26, v_snd_3572_);
lean_closure_set(v___f_3658_, 27, v_overlaps_3573_);
lean_closure_set(v___f_3658_, 28, v_matcherLevels_3575_);
lean_closure_set(v___f_3658_, 29, v_onRemaining_3580_);
lean_closure_set(v___f_3658_, 30, v_remaining_3581_);
lean_closure_set(v___f_3658_, 31, v_remaining_x27_3588_);
lean_closure_set(v___f_3658_, 32, v___x_3651_);
lean_closure_set(v___f_3658_, 33, v___x_3657_);
lean_closure_set(v___f_3658_, 34, v_liftWith_3640_);
lean_closure_set(v___f_3658_, 35, v_restoreM_3641_);
lean_closure_set(v___f_3658_, 36, v_matcherName_3574_);
lean_closure_set(v___f_3658_, 37, v_aux1_3646_);
v___x_3659_ = lean_box(v___x_3654_);
v___x_3660_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_3660_, 0, v_aux1_3646_);
lean_closure_set(v___x_3660_, 1, v___x_3659_);
v___x_3661_ = lean_apply_2(v_inst_3587_, lean_box(0), v___x_3660_);
v___f_3662_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed), 8, 2);
lean_closure_set(v___f_3662_, 0, v___x_3661_);
lean_closure_set(v___f_3662_, 1, v___f_3653_);
v___x_3663_ = lean_apply_2(v_liftWith_3640_, lean_box(0), v___f_3662_);
v___x_3664_ = lean_apply_1(v_restoreM_3641_, lean_box(0));
v___x_3665_ = lean_apply_4(v_toBind_3582_, lean_box(0), lean_box(0), v___x_3663_, v___x_3664_);
v___x_3666_ = lean_apply_4(v_toBind_3582_, lean_box(0), lean_box(0), v___x_3665_, v___f_3658_);
return v___x_3666_;
}
}
else
{
lean_del_object(v___x_3606_);
lean_dec(v_fst_3604_);
lean_dec(v_numDiscrEqs_3601_);
lean_dec(v___f_3600_);
lean_dec_ref(v_toMonadExceptOf_3599_);
lean_dec(v___x_3598_);
lean_dec(v___x_3597_);
lean_dec(v___f_3596_);
lean_dec_ref(v_remaining_3581_);
lean_dec(v_onRemaining_3580_);
lean_dec_ref(v_overlaps_3573_);
lean_dec_ref(v_snd_3572_);
lean_dec(v_uElimPos_x3f_3571_);
lean_dec_ref(v_altInfos_3570_);
lean_dec(v_numDiscrs_3569_);
lean_dec(v_numParams_3568_);
goto v___jp_3613_;
}
}
v___jp_3613_:
{
lean_object* v_liftWith_3614_; lean_object* v_restoreM_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v_aux_3618_; lean_object* v_aux_3619_; lean_object* v_aux_3620_; lean_object* v___x_3621_; uint8_t v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___f_3625_; lean_object* v___x_3626_; lean_object* v___x_3628_; 
v_liftWith_3614_ = lean_ctor_get(v_inst_3583_, 0);
lean_inc(v_liftWith_3614_);
v_restoreM_3615_ = lean_ctor_get(v_inst_3583_, 1);
lean_inc(v_restoreM_3615_);
v___x_3616_ = lean_array_to_list(v_matcherLevels_3575_);
v___x_3617_ = l_Lean_mkConst(v_matcherName_3574_, v___x_3616_);
v_aux_3618_ = l_Lean_mkAppN(v___x_3617_, v_params_x27_3576_);
lean_dec_ref(v_params_x27_3576_);
v_aux_3619_ = l_Lean_Expr_app___override(v_aux_3618_, v_fst_3577_);
v_aux_3620_ = l_Lean_mkAppN(v_aux_3619_, v_discrs_x27_3578_);
lean_dec_ref(v_discrs_x27_3578_);
lean_inc_ref_n(v_aux_3620_, 2);
v___x_3621_ = l_Lean_indentExpr(v_aux_3620_);
v___x_3622_ = 1;
v___x_3623_ = lean_box(v___x_3586_);
v___x_3624_ = lean_box(v___x_3622_);
lean_inc(v_inst_3587_);
lean_inc(v_toBind_3582_);
v___f_3625_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 18, 17);
lean_closure_set(v___f_3625_, 0, v_alts_3584_);
lean_closure_set(v___f_3625_, 1, v_toPure_3579_);
lean_closure_set(v___f_3625_, 2, v_toBind_3582_);
lean_closure_set(v___f_3625_, 3, v___f_3585_);
lean_closure_set(v___f_3625_, 4, v___x_3623_);
lean_closure_set(v___f_3625_, 5, v___x_3624_);
lean_closure_set(v___f_3625_, 6, v_inst_3587_);
lean_closure_set(v___f_3625_, 7, v_remaining_x27_3588_);
lean_closure_set(v___f_3625_, 8, v_onAlt_3589_);
lean_closure_set(v___f_3625_, 9, v_inst_3583_);
lean_closure_set(v___f_3625_, 10, v_inst_3590_);
lean_closure_set(v___f_3625_, 11, v___f_3591_);
lean_closure_set(v___f_3625_, 12, v_fst_3608_);
lean_closure_set(v___f_3625_, 13, v_matcherApp_3592_);
lean_closure_set(v___f_3625_, 14, v___x_3593_);
lean_closure_set(v___f_3625_, 15, v___f_3612_);
lean_closure_set(v___f_3625_, 16, v_aux_3620_);
v___x_3626_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__1);
if (v_isShared_3611_ == 0)
{
lean_ctor_set_tag(v___x_3610_, 7);
lean_ctor_set(v___x_3610_, 1, v___x_3621_);
lean_ctor_set(v___x_3610_, 0, v___x_3626_);
v___x_3628_ = v___x_3610_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3626_);
lean_ctor_set(v_reuseFailAlloc_3639_, 1, v___x_3621_);
v___x_3628_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
lean_object* v___f_3629_; uint8_t v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___f_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___f_3629_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34), 2, 1);
lean_closure_set(v___f_3629_, 0, v___x_3628_);
v___x_3630_ = 0;
v___x_3631_ = lean_box(v___x_3630_);
v___x_3632_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_3632_, 0, v_aux_3620_);
lean_closure_set(v___x_3632_, 1, v___x_3631_);
v___x_3633_ = lean_apply_2(v_inst_3587_, lean_box(0), v___x_3632_);
v___f_3634_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed), 8, 2);
lean_closure_set(v___f_3634_, 0, v___x_3633_);
lean_closure_set(v___f_3634_, 1, v___f_3629_);
v___x_3635_ = lean_apply_2(v_liftWith_3614_, lean_box(0), v___f_3634_);
v___x_3636_ = lean_apply_1(v_restoreM_3615_, lean_box(0));
lean_inc(v_toBind_3582_);
v___x_3637_ = lean_apply_4(v_toBind_3582_, lean_box(0), lean_box(0), v___x_3635_, v___x_3636_);
v___x_3638_ = lean_apply_4(v_toBind_3582_, lean_box(0), lean_box(0), v___x_3637_, v___f_3625_);
return v___x_3638_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed(lean_object** _args){
lean_object* v_numParams_3671_ = _args[0];
lean_object* v_numDiscrs_3672_ = _args[1];
lean_object* v_altInfos_3673_ = _args[2];
lean_object* v_uElimPos_x3f_3674_ = _args[3];
lean_object* v_snd_3675_ = _args[4];
lean_object* v_overlaps_3676_ = _args[5];
lean_object* v_matcherName_3677_ = _args[6];
lean_object* v_matcherLevels_3678_ = _args[7];
lean_object* v_params_x27_3679_ = _args[8];
lean_object* v_fst_3680_ = _args[9];
lean_object* v_discrs_x27_3681_ = _args[10];
lean_object* v_toPure_3682_ = _args[11];
lean_object* v_onRemaining_3683_ = _args[12];
lean_object* v_remaining_3684_ = _args[13];
lean_object* v_toBind_3685_ = _args[14];
lean_object* v_inst_3686_ = _args[15];
lean_object* v_alts_3687_ = _args[16];
lean_object* v___f_3688_ = _args[17];
lean_object* v___x_3689_ = _args[18];
lean_object* v_inst_3690_ = _args[19];
lean_object* v_remaining_x27_3691_ = _args[20];
lean_object* v_onAlt_3692_ = _args[21];
lean_object* v_inst_3693_ = _args[22];
lean_object* v___f_3694_ = _args[23];
lean_object* v_matcherApp_3695_ = _args[24];
lean_object* v___x_3696_ = _args[25];
lean_object* v_useSplitter_3697_ = _args[26];
lean_object* v_isCasesOn_3698_ = _args[27];
lean_object* v___f_3699_ = _args[28];
lean_object* v___x_3700_ = _args[29];
lean_object* v___x_3701_ = _args[30];
lean_object* v_toMonadExceptOf_3702_ = _args[31];
lean_object* v___f_3703_ = _args[32];
lean_object* v_numDiscrEqs_3704_ = _args[33];
lean_object* v_____s_3705_ = _args[34];
_start:
{
uint8_t v___x_14709__boxed_3706_; uint8_t v_useSplitter_boxed_3707_; uint8_t v_isCasesOn_boxed_3708_; lean_object* v_res_3709_; 
v___x_14709__boxed_3706_ = lean_unbox(v___x_3689_);
v_useSplitter_boxed_3707_ = lean_unbox(v_useSplitter_3697_);
v_isCasesOn_boxed_3708_ = lean_unbox(v_isCasesOn_3698_);
v_res_3709_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__57(v_numParams_3671_, v_numDiscrs_3672_, v_altInfos_3673_, v_uElimPos_x3f_3674_, v_snd_3675_, v_overlaps_3676_, v_matcherName_3677_, v_matcherLevels_3678_, v_params_x27_3679_, v_fst_3680_, v_discrs_x27_3681_, v_toPure_3682_, v_onRemaining_3683_, v_remaining_3684_, v_toBind_3685_, v_inst_3686_, v_alts_3687_, v___f_3688_, v___x_14709__boxed_3706_, v_inst_3690_, v_remaining_x27_3691_, v_onAlt_3692_, v_inst_3693_, v___f_3694_, v_matcherApp_3695_, v___x_3696_, v_useSplitter_boxed_3707_, v_isCasesOn_boxed_3708_, v___f_3699_, v___x_3700_, v___x_3701_, v_toMonadExceptOf_3702_, v___f_3703_, v_numDiscrEqs_3704_, v_____s_3705_);
return v_res_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56(lean_object* v_numParams_3710_, lean_object* v_numDiscrs_3711_, lean_object* v_altInfos_3712_, lean_object* v_uElimPos_x3f_3713_, lean_object* v_snd_3714_, lean_object* v_overlaps_3715_, lean_object* v_matcherName_3716_, lean_object* v_params_x27_3717_, lean_object* v_fst_3718_, lean_object* v_discrs_x27_3719_, lean_object* v_toPure_3720_, lean_object* v_onRemaining_3721_, lean_object* v_remaining_3722_, lean_object* v_toBind_3723_, lean_object* v_inst_3724_, lean_object* v_alts_3725_, lean_object* v___f_3726_, uint8_t v___x_3727_, lean_object* v_inst_3728_, lean_object* v_onAlt_3729_, lean_object* v_inst_3730_, lean_object* v___f_3731_, lean_object* v_matcherApp_3732_, uint8_t v_useSplitter_3733_, uint8_t v_isCasesOn_3734_, lean_object* v___f_3735_, lean_object* v___x_3736_, lean_object* v___x_3737_, lean_object* v_toMonadExceptOf_3738_, lean_object* v___f_3739_, lean_object* v_numDiscrEqs_3740_, lean_object* v_fst_3741_, lean_object* v___f_3742_, lean_object* v_matcherLevels_3743_){
_start:
{
lean_object* v___x_3744_; lean_object* v_remaining_x27_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___f_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; size_t v_sz_3756_; size_t v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3744_ = lean_unsigned_to_nat(0u);
v_remaining_x27_3745_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_3746_ = lean_box(v___x_3727_);
v___x_3747_ = lean_box(v_useSplitter_3733_);
v___x_3748_ = lean_box(v_isCasesOn_3734_);
lean_inc_ref(v_inst_3730_);
lean_inc(v_toBind_3723_);
lean_inc_ref(v_discrs_x27_3719_);
v___f_3749_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed), 35, 34);
lean_closure_set(v___f_3749_, 0, v_numParams_3710_);
lean_closure_set(v___f_3749_, 1, v_numDiscrs_3711_);
lean_closure_set(v___f_3749_, 2, v_altInfos_3712_);
lean_closure_set(v___f_3749_, 3, v_uElimPos_x3f_3713_);
lean_closure_set(v___f_3749_, 4, v_snd_3714_);
lean_closure_set(v___f_3749_, 5, v_overlaps_3715_);
lean_closure_set(v___f_3749_, 6, v_matcherName_3716_);
lean_closure_set(v___f_3749_, 7, v_matcherLevels_3743_);
lean_closure_set(v___f_3749_, 8, v_params_x27_3717_);
lean_closure_set(v___f_3749_, 9, v_fst_3718_);
lean_closure_set(v___f_3749_, 10, v_discrs_x27_3719_);
lean_closure_set(v___f_3749_, 11, v_toPure_3720_);
lean_closure_set(v___f_3749_, 12, v_onRemaining_3721_);
lean_closure_set(v___f_3749_, 13, v_remaining_3722_);
lean_closure_set(v___f_3749_, 14, v_toBind_3723_);
lean_closure_set(v___f_3749_, 15, v_inst_3724_);
lean_closure_set(v___f_3749_, 16, v_alts_3725_);
lean_closure_set(v___f_3749_, 17, v___f_3726_);
lean_closure_set(v___f_3749_, 18, v___x_3746_);
lean_closure_set(v___f_3749_, 19, v_inst_3728_);
lean_closure_set(v___f_3749_, 20, v_remaining_x27_3745_);
lean_closure_set(v___f_3749_, 21, v_onAlt_3729_);
lean_closure_set(v___f_3749_, 22, v_inst_3730_);
lean_closure_set(v___f_3749_, 23, v___f_3731_);
lean_closure_set(v___f_3749_, 24, v_matcherApp_3732_);
lean_closure_set(v___f_3749_, 25, v___x_3744_);
lean_closure_set(v___f_3749_, 26, v___x_3747_);
lean_closure_set(v___f_3749_, 27, v___x_3748_);
lean_closure_set(v___f_3749_, 28, v___f_3735_);
lean_closure_set(v___f_3749_, 29, v___x_3736_);
lean_closure_set(v___f_3749_, 30, v___x_3737_);
lean_closure_set(v___f_3749_, 31, v_toMonadExceptOf_3738_);
lean_closure_set(v___f_3749_, 32, v___f_3739_);
lean_closure_set(v___f_3749_, 33, v_numDiscrEqs_3740_);
v___x_3750_ = l_Array_reverse___redArg(v_fst_3741_);
v___x_3751_ = lean_array_get_size(v___x_3750_);
v___x_3752_ = l_Array_toSubarray___redArg(v___x_3750_, v___x_3744_, v___x_3751_);
v___x_3753_ = l_Array_reverse___redArg(v_discrs_x27_3719_);
v___x_3754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3744_);
lean_ctor_set(v___x_3754_, 1, v___x_3752_);
v___x_3755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3755_, 0, v_remaining_x27_3745_);
lean_ctor_set(v___x_3755_, 1, v___x_3754_);
v_sz_3756_ = lean_array_size(v___x_3753_);
v___x_3757_ = ((size_t)0ULL);
v___x_3758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3730_, v___x_3753_, v___f_3742_, v_sz_3756_, v___x_3757_, v___x_3755_);
v___x_3759_ = lean_apply_4(v_toBind_3723_, lean_box(0), lean_box(0), v___x_3758_, v___f_3749_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56___boxed(lean_object** _args){
lean_object* v_numParams_3760_ = _args[0];
lean_object* v_numDiscrs_3761_ = _args[1];
lean_object* v_altInfos_3762_ = _args[2];
lean_object* v_uElimPos_x3f_3763_ = _args[3];
lean_object* v_snd_3764_ = _args[4];
lean_object* v_overlaps_3765_ = _args[5];
lean_object* v_matcherName_3766_ = _args[6];
lean_object* v_params_x27_3767_ = _args[7];
lean_object* v_fst_3768_ = _args[8];
lean_object* v_discrs_x27_3769_ = _args[9];
lean_object* v_toPure_3770_ = _args[10];
lean_object* v_onRemaining_3771_ = _args[11];
lean_object* v_remaining_3772_ = _args[12];
lean_object* v_toBind_3773_ = _args[13];
lean_object* v_inst_3774_ = _args[14];
lean_object* v_alts_3775_ = _args[15];
lean_object* v___f_3776_ = _args[16];
lean_object* v___x_3777_ = _args[17];
lean_object* v_inst_3778_ = _args[18];
lean_object* v_onAlt_3779_ = _args[19];
lean_object* v_inst_3780_ = _args[20];
lean_object* v___f_3781_ = _args[21];
lean_object* v_matcherApp_3782_ = _args[22];
lean_object* v_useSplitter_3783_ = _args[23];
lean_object* v_isCasesOn_3784_ = _args[24];
lean_object* v___f_3785_ = _args[25];
lean_object* v___x_3786_ = _args[26];
lean_object* v___x_3787_ = _args[27];
lean_object* v_toMonadExceptOf_3788_ = _args[28];
lean_object* v___f_3789_ = _args[29];
lean_object* v_numDiscrEqs_3790_ = _args[30];
lean_object* v_fst_3791_ = _args[31];
lean_object* v___f_3792_ = _args[32];
lean_object* v_matcherLevels_3793_ = _args[33];
_start:
{
uint8_t v___x_14871__boxed_3794_; uint8_t v_useSplitter_boxed_3795_; uint8_t v_isCasesOn_boxed_3796_; lean_object* v_res_3797_; 
v___x_14871__boxed_3794_ = lean_unbox(v___x_3777_);
v_useSplitter_boxed_3795_ = lean_unbox(v_useSplitter_3783_);
v_isCasesOn_boxed_3796_ = lean_unbox(v_isCasesOn_3784_);
v_res_3797_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__56(v_numParams_3760_, v_numDiscrs_3761_, v_altInfos_3762_, v_uElimPos_x3f_3763_, v_snd_3764_, v_overlaps_3765_, v_matcherName_3766_, v_params_x27_3767_, v_fst_3768_, v_discrs_x27_3769_, v_toPure_3770_, v_onRemaining_3771_, v_remaining_3772_, v_toBind_3773_, v_inst_3774_, v_alts_3775_, v___f_3776_, v___x_14871__boxed_3794_, v_inst_3778_, v_onAlt_3779_, v_inst_3780_, v___f_3781_, v_matcherApp_3782_, v_useSplitter_boxed_3795_, v_isCasesOn_boxed_3796_, v___f_3785_, v___x_3786_, v___x_3787_, v_toMonadExceptOf_3788_, v___f_3789_, v_numDiscrEqs_3790_, v_fst_3791_, v___f_3792_, v_matcherLevels_3793_);
return v_res_3797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58(lean_object* v___f_3798_, lean_object* v_matcherLevels_3799_){
_start:
{
lean_object* v___x_3800_; 
v___x_3800_ = lean_apply_1(v___f_3798_, v_matcherLevels_3799_);
return v___x_3800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60(lean_object* v_toMatcherInfo_3801_, lean_object* v_matcherName_3802_, lean_object* v_params_x27_3803_, lean_object* v_discrs_x27_3804_, lean_object* v_toPure_3805_, lean_object* v_onRemaining_3806_, lean_object* v_remaining_3807_, lean_object* v_toBind_3808_, lean_object* v_inst_3809_, lean_object* v_alts_3810_, lean_object* v___f_3811_, uint8_t v___x_3812_, lean_object* v_inst_3813_, lean_object* v_onAlt_3814_, lean_object* v_inst_3815_, lean_object* v___f_3816_, lean_object* v_matcherApp_3817_, uint8_t v_useSplitter_3818_, uint8_t v_isCasesOn_3819_, lean_object* v___f_3820_, lean_object* v___x_3821_, lean_object* v___x_3822_, lean_object* v_toMonadExceptOf_3823_, lean_object* v___f_3824_, lean_object* v_numDiscrEqs_3825_, lean_object* v___f_3826_, lean_object* v_matcherLevels_3827_, lean_object* v_____x_3828_){
_start:
{
lean_object* v_snd_3829_; lean_object* v_snd_3830_; lean_object* v_fst_3831_; lean_object* v_fst_3832_; lean_object* v_fst_3833_; lean_object* v_snd_3834_; lean_object* v_numParams_3835_; lean_object* v_numDiscrs_3836_; lean_object* v_altInfos_3837_; lean_object* v_uElimPos_x3f_3838_; lean_object* v_overlaps_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___f_3843_; 
v_snd_3829_ = lean_ctor_get(v_____x_3828_, 1);
lean_inc(v_snd_3829_);
v_snd_3830_ = lean_ctor_get(v_snd_3829_, 1);
lean_inc(v_snd_3830_);
v_fst_3831_ = lean_ctor_get(v_____x_3828_, 0);
lean_inc(v_fst_3831_);
lean_dec_ref(v_____x_3828_);
v_fst_3832_ = lean_ctor_get(v_snd_3829_, 0);
lean_inc(v_fst_3832_);
lean_dec(v_snd_3829_);
v_fst_3833_ = lean_ctor_get(v_snd_3830_, 0);
lean_inc(v_fst_3833_);
v_snd_3834_ = lean_ctor_get(v_snd_3830_, 1);
lean_inc(v_snd_3834_);
lean_dec(v_snd_3830_);
v_numParams_3835_ = lean_ctor_get(v_toMatcherInfo_3801_, 0);
lean_inc(v_numParams_3835_);
v_numDiscrs_3836_ = lean_ctor_get(v_toMatcherInfo_3801_, 1);
lean_inc(v_numDiscrs_3836_);
v_altInfos_3837_ = lean_ctor_get(v_toMatcherInfo_3801_, 2);
lean_inc_ref(v_altInfos_3837_);
v_uElimPos_x3f_3838_ = lean_ctor_get(v_toMatcherInfo_3801_, 3);
lean_inc_n(v_uElimPos_x3f_3838_, 2);
v_overlaps_3839_ = lean_ctor_get(v_toMatcherInfo_3801_, 5);
lean_inc_ref(v_overlaps_3839_);
lean_dec_ref(v_toMatcherInfo_3801_);
v___x_3840_ = lean_box(v___x_3812_);
v___x_3841_ = lean_box(v_useSplitter_3818_);
v___x_3842_ = lean_box(v_isCasesOn_3819_);
lean_inc(v_toBind_3808_);
lean_inc(v_toPure_3805_);
v___f_3843_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56___boxed), 34, 33);
lean_closure_set(v___f_3843_, 0, v_numParams_3835_);
lean_closure_set(v___f_3843_, 1, v_numDiscrs_3836_);
lean_closure_set(v___f_3843_, 2, v_altInfos_3837_);
lean_closure_set(v___f_3843_, 3, v_uElimPos_x3f_3838_);
lean_closure_set(v___f_3843_, 4, v_snd_3834_);
lean_closure_set(v___f_3843_, 5, v_overlaps_3839_);
lean_closure_set(v___f_3843_, 6, v_matcherName_3802_);
lean_closure_set(v___f_3843_, 7, v_params_x27_3803_);
lean_closure_set(v___f_3843_, 8, v_fst_3831_);
lean_closure_set(v___f_3843_, 9, v_discrs_x27_3804_);
lean_closure_set(v___f_3843_, 10, v_toPure_3805_);
lean_closure_set(v___f_3843_, 11, v_onRemaining_3806_);
lean_closure_set(v___f_3843_, 12, v_remaining_3807_);
lean_closure_set(v___f_3843_, 13, v_toBind_3808_);
lean_closure_set(v___f_3843_, 14, v_inst_3809_);
lean_closure_set(v___f_3843_, 15, v_alts_3810_);
lean_closure_set(v___f_3843_, 16, v___f_3811_);
lean_closure_set(v___f_3843_, 17, v___x_3840_);
lean_closure_set(v___f_3843_, 18, v_inst_3813_);
lean_closure_set(v___f_3843_, 19, v_onAlt_3814_);
lean_closure_set(v___f_3843_, 20, v_inst_3815_);
lean_closure_set(v___f_3843_, 21, v___f_3816_);
lean_closure_set(v___f_3843_, 22, v_matcherApp_3817_);
lean_closure_set(v___f_3843_, 23, v___x_3841_);
lean_closure_set(v___f_3843_, 24, v___x_3842_);
lean_closure_set(v___f_3843_, 25, v___f_3820_);
lean_closure_set(v___f_3843_, 26, v___x_3821_);
lean_closure_set(v___f_3843_, 27, v___x_3822_);
lean_closure_set(v___f_3843_, 28, v_toMonadExceptOf_3823_);
lean_closure_set(v___f_3843_, 29, v___f_3824_);
lean_closure_set(v___f_3843_, 30, v_numDiscrEqs_3825_);
lean_closure_set(v___f_3843_, 31, v_fst_3833_);
lean_closure_set(v___f_3843_, 32, v___f_3826_);
if (lean_obj_tag(v_uElimPos_x3f_3838_) == 0)
{
lean_object* v___f_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; 
lean_dec(v_fst_3832_);
v___f_3844_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__58), 2, 1);
lean_closure_set(v___f_3844_, 0, v___f_3843_);
v___x_3845_ = lean_apply_2(v_toPure_3805_, lean_box(0), v_matcherLevels_3827_);
v___x_3846_ = lean_apply_4(v_toBind_3808_, lean_box(0), lean_box(0), v___x_3845_, v___f_3844_);
return v___x_3846_;
}
else
{
lean_object* v_val_3847_; lean_object* v___f_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
v_val_3847_ = lean_ctor_get(v_uElimPos_x3f_3838_, 0);
lean_inc(v_val_3847_);
lean_dec_ref_known(v_uElimPos_x3f_3838_, 1);
v___f_3848_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__58), 2, 1);
lean_closure_set(v___f_3848_, 0, v___f_3843_);
v___x_3849_ = lean_array_set(v_matcherLevels_3827_, v_val_3847_, v_fst_3832_);
lean_dec(v_val_3847_);
v___x_3850_ = lean_apply_2(v_toPure_3805_, lean_box(0), v___x_3849_);
v___x_3851_ = lean_apply_4(v_toBind_3808_, lean_box(0), lean_box(0), v___x_3850_, v___f_3848_);
return v___x_3851_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed(lean_object** _args){
lean_object* v_toMatcherInfo_3852_ = _args[0];
lean_object* v_matcherName_3853_ = _args[1];
lean_object* v_params_x27_3854_ = _args[2];
lean_object* v_discrs_x27_3855_ = _args[3];
lean_object* v_toPure_3856_ = _args[4];
lean_object* v_onRemaining_3857_ = _args[5];
lean_object* v_remaining_3858_ = _args[6];
lean_object* v_toBind_3859_ = _args[7];
lean_object* v_inst_3860_ = _args[8];
lean_object* v_alts_3861_ = _args[9];
lean_object* v___f_3862_ = _args[10];
lean_object* v___x_3863_ = _args[11];
lean_object* v_inst_3864_ = _args[12];
lean_object* v_onAlt_3865_ = _args[13];
lean_object* v_inst_3866_ = _args[14];
lean_object* v___f_3867_ = _args[15];
lean_object* v_matcherApp_3868_ = _args[16];
lean_object* v_useSplitter_3869_ = _args[17];
lean_object* v_isCasesOn_3870_ = _args[18];
lean_object* v___f_3871_ = _args[19];
lean_object* v___x_3872_ = _args[20];
lean_object* v___x_3873_ = _args[21];
lean_object* v_toMonadExceptOf_3874_ = _args[22];
lean_object* v___f_3875_ = _args[23];
lean_object* v_numDiscrEqs_3876_ = _args[24];
lean_object* v___f_3877_ = _args[25];
lean_object* v_matcherLevels_3878_ = _args[26];
lean_object* v_____x_3879_ = _args[27];
_start:
{
uint8_t v___x_14943__boxed_3880_; uint8_t v_useSplitter_boxed_3881_; uint8_t v_isCasesOn_boxed_3882_; lean_object* v_res_3883_; 
v___x_14943__boxed_3880_ = lean_unbox(v___x_3863_);
v_useSplitter_boxed_3881_ = lean_unbox(v_useSplitter_3869_);
v_isCasesOn_boxed_3882_ = lean_unbox(v_isCasesOn_3870_);
v_res_3883_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__60(v_toMatcherInfo_3852_, v_matcherName_3853_, v_params_x27_3854_, v_discrs_x27_3855_, v_toPure_3856_, v_onRemaining_3857_, v_remaining_3858_, v_toBind_3859_, v_inst_3860_, v_alts_3861_, v___f_3862_, v___x_14943__boxed_3880_, v_inst_3864_, v_onAlt_3865_, v_inst_3866_, v___f_3867_, v_matcherApp_3868_, v_useSplitter_boxed_3881_, v_isCasesOn_boxed_3882_, v___f_3871_, v___x_3872_, v___x_3873_, v_toMonadExceptOf_3874_, v___f_3875_, v_numDiscrEqs_3876_, v___f_3877_, v_matcherLevels_3878_, v_____x_3879_);
return v_res_3883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59(lean_object* v_toPure_3884_, lean_object* v_inst_3885_, lean_object* v_toBind_3886_, lean_object* v_toMatcherInfo_3887_, lean_object* v_inst_3888_, lean_object* v___f_3889_, lean_object* v_onMotive_3890_, lean_object* v_discrs_3891_, lean_object* v_inst_3892_, lean_object* v_matcherName_3893_, lean_object* v_params_x27_3894_, lean_object* v_onRemaining_3895_, lean_object* v_remaining_3896_, lean_object* v_inst_3897_, lean_object* v_alts_3898_, lean_object* v___f_3899_, lean_object* v_onAlt_3900_, lean_object* v___f_3901_, lean_object* v_matcherApp_3902_, uint8_t v_useSplitter_3903_, uint8_t v_isCasesOn_3904_, lean_object* v___f_3905_, lean_object* v___x_3906_, lean_object* v___x_3907_, lean_object* v_toMonadExceptOf_3908_, lean_object* v___f_3909_, lean_object* v_numDiscrEqs_3910_, lean_object* v___f_3911_, lean_object* v_matcherLevels_3912_, lean_object* v_motive_3913_, lean_object* v_discrs_x27_3914_){
_start:
{
lean_object* v___f_3915_; uint8_t v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___f_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
lean_inc_ref_n(v_inst_3888_, 2);
lean_inc_ref(v_discrs_x27_3914_);
lean_inc_ref(v_toMatcherInfo_3887_);
lean_inc_n(v_toBind_3886_, 2);
lean_inc(v_inst_3885_);
lean_inc(v_toPure_3884_);
v___f_3915_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed), 12, 10);
lean_closure_set(v___f_3915_, 0, v_toPure_3884_);
lean_closure_set(v___f_3915_, 1, v_inst_3885_);
lean_closure_set(v___f_3915_, 2, v_toBind_3886_);
lean_closure_set(v___f_3915_, 3, v_toMatcherInfo_3887_);
lean_closure_set(v___f_3915_, 4, v_discrs_x27_3914_);
lean_closure_set(v___f_3915_, 5, v_inst_3888_);
lean_closure_set(v___f_3915_, 6, v___f_3889_);
lean_closure_set(v___f_3915_, 7, v_onMotive_3890_);
lean_closure_set(v___f_3915_, 8, v_discrs_3891_);
lean_closure_set(v___f_3915_, 9, v_inst_3892_);
v___x_3916_ = 0;
v___x_3917_ = lean_box(v___x_3916_);
v___x_3918_ = lean_box(v_useSplitter_3903_);
v___x_3919_ = lean_box(v_isCasesOn_3904_);
lean_inc_ref(v_inst_3897_);
v___f_3920_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed), 28, 27);
lean_closure_set(v___f_3920_, 0, v_toMatcherInfo_3887_);
lean_closure_set(v___f_3920_, 1, v_matcherName_3893_);
lean_closure_set(v___f_3920_, 2, v_params_x27_3894_);
lean_closure_set(v___f_3920_, 3, v_discrs_x27_3914_);
lean_closure_set(v___f_3920_, 4, v_toPure_3884_);
lean_closure_set(v___f_3920_, 5, v_onRemaining_3895_);
lean_closure_set(v___f_3920_, 6, v_remaining_3896_);
lean_closure_set(v___f_3920_, 7, v_toBind_3886_);
lean_closure_set(v___f_3920_, 8, v_inst_3897_);
lean_closure_set(v___f_3920_, 9, v_alts_3898_);
lean_closure_set(v___f_3920_, 10, v___f_3899_);
lean_closure_set(v___f_3920_, 11, v___x_3917_);
lean_closure_set(v___f_3920_, 12, v_inst_3885_);
lean_closure_set(v___f_3920_, 13, v_onAlt_3900_);
lean_closure_set(v___f_3920_, 14, v_inst_3888_);
lean_closure_set(v___f_3920_, 15, v___f_3901_);
lean_closure_set(v___f_3920_, 16, v_matcherApp_3902_);
lean_closure_set(v___f_3920_, 17, v___x_3918_);
lean_closure_set(v___f_3920_, 18, v___x_3919_);
lean_closure_set(v___f_3920_, 19, v___f_3905_);
lean_closure_set(v___f_3920_, 20, v___x_3906_);
lean_closure_set(v___f_3920_, 21, v___x_3907_);
lean_closure_set(v___f_3920_, 22, v_toMonadExceptOf_3908_);
lean_closure_set(v___f_3920_, 23, v___f_3909_);
lean_closure_set(v___f_3920_, 24, v_numDiscrEqs_3910_);
lean_closure_set(v___f_3920_, 25, v___f_3911_);
lean_closure_set(v___f_3920_, 26, v_matcherLevels_3912_);
v___x_3921_ = l_Lean_Meta_lambdaTelescope___redArg(v_inst_3897_, v_inst_3888_, v_motive_3913_, v___f_3915_, v___x_3916_);
v___x_3922_ = lean_apply_4(v_toBind_3886_, lean_box(0), lean_box(0), v___x_3921_, v___f_3920_);
return v___x_3922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed(lean_object** _args){
lean_object* v_toPure_3923_ = _args[0];
lean_object* v_inst_3924_ = _args[1];
lean_object* v_toBind_3925_ = _args[2];
lean_object* v_toMatcherInfo_3926_ = _args[3];
lean_object* v_inst_3927_ = _args[4];
lean_object* v___f_3928_ = _args[5];
lean_object* v_onMotive_3929_ = _args[6];
lean_object* v_discrs_3930_ = _args[7];
lean_object* v_inst_3931_ = _args[8];
lean_object* v_matcherName_3932_ = _args[9];
lean_object* v_params_x27_3933_ = _args[10];
lean_object* v_onRemaining_3934_ = _args[11];
lean_object* v_remaining_3935_ = _args[12];
lean_object* v_inst_3936_ = _args[13];
lean_object* v_alts_3937_ = _args[14];
lean_object* v___f_3938_ = _args[15];
lean_object* v_onAlt_3939_ = _args[16];
lean_object* v___f_3940_ = _args[17];
lean_object* v_matcherApp_3941_ = _args[18];
lean_object* v_useSplitter_3942_ = _args[19];
lean_object* v_isCasesOn_3943_ = _args[20];
lean_object* v___f_3944_ = _args[21];
lean_object* v___x_3945_ = _args[22];
lean_object* v___x_3946_ = _args[23];
lean_object* v_toMonadExceptOf_3947_ = _args[24];
lean_object* v___f_3948_ = _args[25];
lean_object* v_numDiscrEqs_3949_ = _args[26];
lean_object* v___f_3950_ = _args[27];
lean_object* v_matcherLevels_3951_ = _args[28];
lean_object* v_motive_3952_ = _args[29];
lean_object* v_discrs_x27_3953_ = _args[30];
_start:
{
uint8_t v_useSplitter_boxed_3954_; uint8_t v_isCasesOn_boxed_3955_; lean_object* v_res_3956_; 
v_useSplitter_boxed_3954_ = lean_unbox(v_useSplitter_3942_);
v_isCasesOn_boxed_3955_ = lean_unbox(v_isCasesOn_3943_);
v_res_3956_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__59(v_toPure_3923_, v_inst_3924_, v_toBind_3925_, v_toMatcherInfo_3926_, v_inst_3927_, v___f_3928_, v_onMotive_3929_, v_discrs_3930_, v_inst_3931_, v_matcherName_3932_, v_params_x27_3933_, v_onRemaining_3934_, v_remaining_3935_, v_inst_3936_, v_alts_3937_, v___f_3938_, v_onAlt_3939_, v___f_3940_, v_matcherApp_3941_, v_useSplitter_boxed_3954_, v_isCasesOn_boxed_3955_, v___f_3944_, v___x_3945_, v___x_3946_, v_toMonadExceptOf_3947_, v___f_3948_, v_numDiscrEqs_3949_, v___f_3950_, v_matcherLevels_3951_, v_motive_3952_, v_discrs_x27_3953_);
return v_res_3956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__61(lean_object* v_toPure_3957_, lean_object* v_inst_3958_, lean_object* v_toBind_3959_, lean_object* v_toMatcherInfo_3960_, lean_object* v_inst_3961_, lean_object* v___f_3962_, lean_object* v_onMotive_3963_, lean_object* v_discrs_3964_, lean_object* v_inst_3965_, lean_object* v_matcherName_3966_, lean_object* v_onRemaining_3967_, lean_object* v_remaining_3968_, lean_object* v_inst_3969_, lean_object* v_alts_3970_, lean_object* v___f_3971_, lean_object* v_onAlt_3972_, lean_object* v___f_3973_, lean_object* v_matcherApp_3974_, uint8_t v_useSplitter_3975_, uint8_t v_isCasesOn_3976_, lean_object* v___f_3977_, lean_object* v___x_3978_, lean_object* v___x_3979_, lean_object* v_toMonadExceptOf_3980_, lean_object* v___f_3981_, lean_object* v_numDiscrEqs_3982_, lean_object* v___f_3983_, lean_object* v_matcherLevels_3984_, lean_object* v_motive_3985_, lean_object* v_onParams_3986_, lean_object* v_params_x27_3987_){
_start:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___f_3990_; size_t v_sz_3991_; size_t v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
v___x_3988_ = lean_box(v_useSplitter_3975_);
v___x_3989_ = lean_box(v_isCasesOn_3976_);
lean_inc_ref(v_discrs_3964_);
lean_inc_ref(v_inst_3961_);
lean_inc(v_toBind_3959_);
v___f_3990_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed), 31, 30);
lean_closure_set(v___f_3990_, 0, v_toPure_3957_);
lean_closure_set(v___f_3990_, 1, v_inst_3958_);
lean_closure_set(v___f_3990_, 2, v_toBind_3959_);
lean_closure_set(v___f_3990_, 3, v_toMatcherInfo_3960_);
lean_closure_set(v___f_3990_, 4, v_inst_3961_);
lean_closure_set(v___f_3990_, 5, v___f_3962_);
lean_closure_set(v___f_3990_, 6, v_onMotive_3963_);
lean_closure_set(v___f_3990_, 7, v_discrs_3964_);
lean_closure_set(v___f_3990_, 8, v_inst_3965_);
lean_closure_set(v___f_3990_, 9, v_matcherName_3966_);
lean_closure_set(v___f_3990_, 10, v_params_x27_3987_);
lean_closure_set(v___f_3990_, 11, v_onRemaining_3967_);
lean_closure_set(v___f_3990_, 12, v_remaining_3968_);
lean_closure_set(v___f_3990_, 13, v_inst_3969_);
lean_closure_set(v___f_3990_, 14, v_alts_3970_);
lean_closure_set(v___f_3990_, 15, v___f_3971_);
lean_closure_set(v___f_3990_, 16, v_onAlt_3972_);
lean_closure_set(v___f_3990_, 17, v___f_3973_);
lean_closure_set(v___f_3990_, 18, v_matcherApp_3974_);
lean_closure_set(v___f_3990_, 19, v___x_3988_);
lean_closure_set(v___f_3990_, 20, v___x_3989_);
lean_closure_set(v___f_3990_, 21, v___f_3977_);
lean_closure_set(v___f_3990_, 22, v___x_3978_);
lean_closure_set(v___f_3990_, 23, v___x_3979_);
lean_closure_set(v___f_3990_, 24, v_toMonadExceptOf_3980_);
lean_closure_set(v___f_3990_, 25, v___f_3981_);
lean_closure_set(v___f_3990_, 26, v_numDiscrEqs_3982_);
lean_closure_set(v___f_3990_, 27, v___f_3983_);
lean_closure_set(v___f_3990_, 28, v_matcherLevels_3984_);
lean_closure_set(v___f_3990_, 29, v_motive_3985_);
v_sz_3991_ = lean_array_size(v_discrs_3964_);
v___x_3992_ = ((size_t)0ULL);
v___x_3993_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_3961_, v_onParams_3986_, v_sz_3991_, v___x_3992_, v_discrs_3964_);
v___x_3994_ = lean_apply_4(v_toBind_3959_, lean_box(0), lean_box(0), v___x_3993_, v___f_3990_);
return v___x_3994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__61___boxed(lean_object** _args){
lean_object* v_toPure_3995_ = _args[0];
lean_object* v_inst_3996_ = _args[1];
lean_object* v_toBind_3997_ = _args[2];
lean_object* v_toMatcherInfo_3998_ = _args[3];
lean_object* v_inst_3999_ = _args[4];
lean_object* v___f_4000_ = _args[5];
lean_object* v_onMotive_4001_ = _args[6];
lean_object* v_discrs_4002_ = _args[7];
lean_object* v_inst_4003_ = _args[8];
lean_object* v_matcherName_4004_ = _args[9];
lean_object* v_onRemaining_4005_ = _args[10];
lean_object* v_remaining_4006_ = _args[11];
lean_object* v_inst_4007_ = _args[12];
lean_object* v_alts_4008_ = _args[13];
lean_object* v___f_4009_ = _args[14];
lean_object* v_onAlt_4010_ = _args[15];
lean_object* v___f_4011_ = _args[16];
lean_object* v_matcherApp_4012_ = _args[17];
lean_object* v_useSplitter_4013_ = _args[18];
lean_object* v_isCasesOn_4014_ = _args[19];
lean_object* v___f_4015_ = _args[20];
lean_object* v___x_4016_ = _args[21];
lean_object* v___x_4017_ = _args[22];
lean_object* v_toMonadExceptOf_4018_ = _args[23];
lean_object* v___f_4019_ = _args[24];
lean_object* v_numDiscrEqs_4020_ = _args[25];
lean_object* v___f_4021_ = _args[26];
lean_object* v_matcherLevels_4022_ = _args[27];
lean_object* v_motive_4023_ = _args[28];
lean_object* v_onParams_4024_ = _args[29];
lean_object* v_params_x27_4025_ = _args[30];
_start:
{
uint8_t v_useSplitter_boxed_4026_; uint8_t v_isCasesOn_boxed_4027_; lean_object* v_res_4028_; 
v_useSplitter_boxed_4026_ = lean_unbox(v_useSplitter_4013_);
v_isCasesOn_boxed_4027_ = lean_unbox(v_isCasesOn_4014_);
v_res_4028_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__61(v_toPure_3995_, v_inst_3996_, v_toBind_3997_, v_toMatcherInfo_3998_, v_inst_3999_, v___f_4000_, v_onMotive_4001_, v_discrs_4002_, v_inst_4003_, v_matcherName_4004_, v_onRemaining_4005_, v_remaining_4006_, v_inst_4007_, v_alts_4008_, v___f_4009_, v_onAlt_4010_, v___f_4011_, v_matcherApp_4012_, v_useSplitter_boxed_4026_, v_isCasesOn_boxed_4027_, v___f_4015_, v___x_4016_, v___x_4017_, v_toMonadExceptOf_4018_, v___f_4019_, v_numDiscrEqs_4020_, v___f_4021_, v_matcherLevels_4022_, v_motive_4023_, v_onParams_4024_, v_params_x27_4025_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__62(lean_object* v_toPure_4029_, lean_object* v_inst_4030_, lean_object* v_toBind_4031_, lean_object* v_toMatcherInfo_4032_, lean_object* v_inst_4033_, lean_object* v___f_4034_, lean_object* v_onMotive_4035_, lean_object* v_discrs_4036_, lean_object* v_inst_4037_, lean_object* v_matcherName_4038_, lean_object* v_onRemaining_4039_, lean_object* v_remaining_4040_, lean_object* v_inst_4041_, lean_object* v_alts_4042_, lean_object* v___f_4043_, lean_object* v_onAlt_4044_, lean_object* v___f_4045_, lean_object* v_matcherApp_4046_, uint8_t v_useSplitter_4047_, uint8_t v_isCasesOn_4048_, lean_object* v___f_4049_, lean_object* v___x_4050_, lean_object* v___x_4051_, lean_object* v_toMonadExceptOf_4052_, lean_object* v___f_4053_, lean_object* v___f_4054_, lean_object* v_matcherLevels_4055_, lean_object* v_motive_4056_, lean_object* v_onParams_4057_, lean_object* v_params_4058_, lean_object* v_numDiscrEqs_4059_){
_start:
{
lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___f_4062_; size_t v_sz_4063_; size_t v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4060_ = lean_box(v_useSplitter_4047_);
v___x_4061_ = lean_box(v_isCasesOn_4048_);
lean_inc(v_onParams_4057_);
lean_inc_ref(v_inst_4033_);
lean_inc(v_toBind_4031_);
v___f_4062_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61___boxed), 31, 30);
lean_closure_set(v___f_4062_, 0, v_toPure_4029_);
lean_closure_set(v___f_4062_, 1, v_inst_4030_);
lean_closure_set(v___f_4062_, 2, v_toBind_4031_);
lean_closure_set(v___f_4062_, 3, v_toMatcherInfo_4032_);
lean_closure_set(v___f_4062_, 4, v_inst_4033_);
lean_closure_set(v___f_4062_, 5, v___f_4034_);
lean_closure_set(v___f_4062_, 6, v_onMotive_4035_);
lean_closure_set(v___f_4062_, 7, v_discrs_4036_);
lean_closure_set(v___f_4062_, 8, v_inst_4037_);
lean_closure_set(v___f_4062_, 9, v_matcherName_4038_);
lean_closure_set(v___f_4062_, 10, v_onRemaining_4039_);
lean_closure_set(v___f_4062_, 11, v_remaining_4040_);
lean_closure_set(v___f_4062_, 12, v_inst_4041_);
lean_closure_set(v___f_4062_, 13, v_alts_4042_);
lean_closure_set(v___f_4062_, 14, v___f_4043_);
lean_closure_set(v___f_4062_, 15, v_onAlt_4044_);
lean_closure_set(v___f_4062_, 16, v___f_4045_);
lean_closure_set(v___f_4062_, 17, v_matcherApp_4046_);
lean_closure_set(v___f_4062_, 18, v___x_4060_);
lean_closure_set(v___f_4062_, 19, v___x_4061_);
lean_closure_set(v___f_4062_, 20, v___f_4049_);
lean_closure_set(v___f_4062_, 21, v___x_4050_);
lean_closure_set(v___f_4062_, 22, v___x_4051_);
lean_closure_set(v___f_4062_, 23, v_toMonadExceptOf_4052_);
lean_closure_set(v___f_4062_, 24, v___f_4053_);
lean_closure_set(v___f_4062_, 25, v_numDiscrEqs_4059_);
lean_closure_set(v___f_4062_, 26, v___f_4054_);
lean_closure_set(v___f_4062_, 27, v_matcherLevels_4055_);
lean_closure_set(v___f_4062_, 28, v_motive_4056_);
lean_closure_set(v___f_4062_, 29, v_onParams_4057_);
v_sz_4063_ = lean_array_size(v_params_4058_);
v___x_4064_ = ((size_t)0ULL);
v___x_4065_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_4033_, v_onParams_4057_, v_sz_4063_, v___x_4064_, v_params_4058_);
v___x_4066_ = lean_apply_4(v_toBind_4031_, lean_box(0), lean_box(0), v___x_4065_, v___f_4062_);
return v___x_4066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__62___boxed(lean_object** _args){
lean_object* v_toPure_4067_ = _args[0];
lean_object* v_inst_4068_ = _args[1];
lean_object* v_toBind_4069_ = _args[2];
lean_object* v_toMatcherInfo_4070_ = _args[3];
lean_object* v_inst_4071_ = _args[4];
lean_object* v___f_4072_ = _args[5];
lean_object* v_onMotive_4073_ = _args[6];
lean_object* v_discrs_4074_ = _args[7];
lean_object* v_inst_4075_ = _args[8];
lean_object* v_matcherName_4076_ = _args[9];
lean_object* v_onRemaining_4077_ = _args[10];
lean_object* v_remaining_4078_ = _args[11];
lean_object* v_inst_4079_ = _args[12];
lean_object* v_alts_4080_ = _args[13];
lean_object* v___f_4081_ = _args[14];
lean_object* v_onAlt_4082_ = _args[15];
lean_object* v___f_4083_ = _args[16];
lean_object* v_matcherApp_4084_ = _args[17];
lean_object* v_useSplitter_4085_ = _args[18];
lean_object* v_isCasesOn_4086_ = _args[19];
lean_object* v___f_4087_ = _args[20];
lean_object* v___x_4088_ = _args[21];
lean_object* v___x_4089_ = _args[22];
lean_object* v_toMonadExceptOf_4090_ = _args[23];
lean_object* v___f_4091_ = _args[24];
lean_object* v___f_4092_ = _args[25];
lean_object* v_matcherLevels_4093_ = _args[26];
lean_object* v_motive_4094_ = _args[27];
lean_object* v_onParams_4095_ = _args[28];
lean_object* v_params_4096_ = _args[29];
lean_object* v_numDiscrEqs_4097_ = _args[30];
_start:
{
uint8_t v_useSplitter_boxed_4098_; uint8_t v_isCasesOn_boxed_4099_; lean_object* v_res_4100_; 
v_useSplitter_boxed_4098_ = lean_unbox(v_useSplitter_4085_);
v_isCasesOn_boxed_4099_ = lean_unbox(v_isCasesOn_4086_);
v_res_4100_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__62(v_toPure_4067_, v_inst_4068_, v_toBind_4069_, v_toMatcherInfo_4070_, v_inst_4071_, v___f_4072_, v_onMotive_4073_, v_discrs_4074_, v_inst_4075_, v_matcherName_4076_, v_onRemaining_4077_, v_remaining_4078_, v_inst_4079_, v_alts_4080_, v___f_4081_, v_onAlt_4082_, v___f_4083_, v_matcherApp_4084_, v_useSplitter_boxed_4098_, v_isCasesOn_boxed_4099_, v___f_4087_, v___x_4088_, v___x_4089_, v_toMonadExceptOf_4090_, v___f_4091_, v___f_4092_, v_matcherLevels_4093_, v_motive_4094_, v_onParams_4095_, v_params_4096_, v_numDiscrEqs_4097_);
return v_res_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63(lean_object* v___f_4101_, lean_object* v_numDiscrEqs_4102_){
_start:
{
lean_object* v___x_4103_; 
v___x_4103_ = lean_apply_1(v___f_4101_, v_numDiscrEqs_4102_);
return v___x_4103_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__1(void){
_start:
{
lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___x_4105_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__0));
v___x_4106_ = l_Lean_stringToMessageData(v___x_4105_);
return v___x_4106_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__3(void){
_start:
{
lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4108_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__2));
v___x_4109_ = l_Lean_stringToMessageData(v___x_4108_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__65(lean_object* v_matcherName_4110_, lean_object* v_inst_4111_, lean_object* v_inst_4112_, lean_object* v_toBind_4113_, lean_object* v___f_4114_, lean_object* v_toPure_4115_, lean_object* v___f_4116_, lean_object* v_____do__lift_4117_){
_start:
{
if (lean_obj_tag(v_____do__lift_4117_) == 0)
{
lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
lean_dec(v___f_4116_);
lean_dec(v_toPure_4115_);
v___x_4118_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__1);
v___x_4119_ = l_Lean_MessageData_ofName(v_matcherName_4110_);
v___x_4120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4120_, 0, v___x_4118_);
lean_ctor_set(v___x_4120_, 1, v___x_4119_);
v___x_4121_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__3);
v___x_4122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4120_);
lean_ctor_set(v___x_4122_, 1, v___x_4121_);
v___x_4123_ = l_Lean_throwError___redArg(v_inst_4111_, v_inst_4112_, v___x_4122_);
v___x_4124_ = lean_apply_4(v_toBind_4113_, lean_box(0), lean_box(0), v___x_4123_, v___f_4114_);
return v___x_4124_;
}
else
{
lean_object* v_val_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; 
lean_dec(v___f_4114_);
lean_dec_ref(v_inst_4112_);
lean_dec_ref(v_inst_4111_);
lean_dec(v_matcherName_4110_);
v_val_4125_ = lean_ctor_get(v_____do__lift_4117_, 0);
v___x_4126_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_4125_);
v___x_4127_ = lean_apply_2(v_toPure_4115_, lean_box(0), v___x_4126_);
v___x_4128_ = lean_apply_4(v_toBind_4113_, lean_box(0), lean_box(0), v___x_4127_, v___f_4116_);
return v___x_4128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__65___boxed(lean_object* v_matcherName_4129_, lean_object* v_inst_4130_, lean_object* v_inst_4131_, lean_object* v_toBind_4132_, lean_object* v___f_4133_, lean_object* v_toPure_4134_, lean_object* v___f_4135_, lean_object* v_____do__lift_4136_){
_start:
{
lean_object* v_res_4137_; 
v_res_4137_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__65(v_matcherName_4129_, v_inst_4130_, v_inst_4131_, v_toBind_4132_, v___f_4133_, v_toPure_4134_, v___f_4135_, v_____do__lift_4136_);
lean_dec(v_____do__lift_4136_);
return v_res_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__66(lean_object* v_matcherApp_4138_, lean_object* v_toPure_4139_, lean_object* v_inst_4140_, lean_object* v_toBind_4141_, lean_object* v_inst_4142_, lean_object* v___f_4143_, lean_object* v_onMotive_4144_, lean_object* v_inst_4145_, lean_object* v_onRemaining_4146_, lean_object* v_inst_4147_, lean_object* v___f_4148_, lean_object* v_onAlt_4149_, lean_object* v___f_4150_, uint8_t v_useSplitter_4151_, lean_object* v___f_4152_, lean_object* v___x_4153_, lean_object* v___x_4154_, lean_object* v_toMonadExceptOf_4155_, lean_object* v___f_4156_, lean_object* v___f_4157_, lean_object* v_onParams_4158_, lean_object* v_inst_4159_, lean_object* v_____do__lift_4160_){
_start:
{
lean_object* v_toMatcherInfo_4161_; lean_object* v_matcherName_4162_; lean_object* v_matcherLevels_4163_; lean_object* v_params_4164_; lean_object* v_motive_4165_; lean_object* v_discrs_4166_; lean_object* v_alts_4167_; lean_object* v_remaining_4168_; uint8_t v_isCasesOn_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___f_4172_; 
v_toMatcherInfo_4161_ = lean_ctor_get(v_matcherApp_4138_, 0);
lean_inc_ref(v_toMatcherInfo_4161_);
v_matcherName_4162_ = lean_ctor_get(v_matcherApp_4138_, 1);
lean_inc_n(v_matcherName_4162_, 3);
v_matcherLevels_4163_ = lean_ctor_get(v_matcherApp_4138_, 2);
lean_inc_ref(v_matcherLevels_4163_);
v_params_4164_ = lean_ctor_get(v_matcherApp_4138_, 3);
lean_inc_ref(v_params_4164_);
v_motive_4165_ = lean_ctor_get(v_matcherApp_4138_, 4);
lean_inc_ref(v_motive_4165_);
v_discrs_4166_ = lean_ctor_get(v_matcherApp_4138_, 5);
lean_inc_ref(v_discrs_4166_);
v_alts_4167_ = lean_ctor_get(v_matcherApp_4138_, 6);
lean_inc_ref(v_alts_4167_);
v_remaining_4168_ = lean_ctor_get(v_matcherApp_4138_, 7);
lean_inc_ref(v_remaining_4168_);
v_isCasesOn_4169_ = l_Lean_isCasesOnRecursor(v_____do__lift_4160_, v_matcherName_4162_);
v___x_4170_ = lean_box(v_useSplitter_4151_);
v___x_4171_ = lean_box(v_isCasesOn_4169_);
lean_inc_ref(v_inst_4145_);
lean_inc_ref(v_inst_4142_);
lean_inc(v_toBind_4141_);
lean_inc(v_toPure_4139_);
v___f_4172_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__62___boxed), 31, 30);
lean_closure_set(v___f_4172_, 0, v_toPure_4139_);
lean_closure_set(v___f_4172_, 1, v_inst_4140_);
lean_closure_set(v___f_4172_, 2, v_toBind_4141_);
lean_closure_set(v___f_4172_, 3, v_toMatcherInfo_4161_);
lean_closure_set(v___f_4172_, 4, v_inst_4142_);
lean_closure_set(v___f_4172_, 5, v___f_4143_);
lean_closure_set(v___f_4172_, 6, v_onMotive_4144_);
lean_closure_set(v___f_4172_, 7, v_discrs_4166_);
lean_closure_set(v___f_4172_, 8, v_inst_4145_);
lean_closure_set(v___f_4172_, 9, v_matcherName_4162_);
lean_closure_set(v___f_4172_, 10, v_onRemaining_4146_);
lean_closure_set(v___f_4172_, 11, v_remaining_4168_);
lean_closure_set(v___f_4172_, 12, v_inst_4147_);
lean_closure_set(v___f_4172_, 13, v_alts_4167_);
lean_closure_set(v___f_4172_, 14, v___f_4148_);
lean_closure_set(v___f_4172_, 15, v_onAlt_4149_);
lean_closure_set(v___f_4172_, 16, v___f_4150_);
lean_closure_set(v___f_4172_, 17, v_matcherApp_4138_);
lean_closure_set(v___f_4172_, 18, v___x_4170_);
lean_closure_set(v___f_4172_, 19, v___x_4171_);
lean_closure_set(v___f_4172_, 20, v___f_4152_);
lean_closure_set(v___f_4172_, 21, v___x_4153_);
lean_closure_set(v___f_4172_, 22, v___x_4154_);
lean_closure_set(v___f_4172_, 23, v_toMonadExceptOf_4155_);
lean_closure_set(v___f_4172_, 24, v___f_4156_);
lean_closure_set(v___f_4172_, 25, v___f_4157_);
lean_closure_set(v___f_4172_, 26, v_matcherLevels_4163_);
lean_closure_set(v___f_4172_, 27, v_motive_4165_);
lean_closure_set(v___f_4172_, 28, v_onParams_4158_);
lean_closure_set(v___f_4172_, 29, v_params_4164_);
if (v_isCasesOn_4169_ == 0)
{
lean_object* v___f_4173_; lean_object* v___f_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; 
v___f_4173_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63), 2, 1);
lean_closure_set(v___f_4173_, 0, v___f_4172_);
lean_inc_ref(v___f_4173_);
lean_inc(v_toBind_4141_);
lean_inc_ref(v_inst_4142_);
lean_inc(v_matcherName_4162_);
v___f_4174_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__65___boxed), 8, 7);
lean_closure_set(v___f_4174_, 0, v_matcherName_4162_);
lean_closure_set(v___f_4174_, 1, v_inst_4142_);
lean_closure_set(v___f_4174_, 2, v_inst_4145_);
lean_closure_set(v___f_4174_, 3, v_toBind_4141_);
lean_closure_set(v___f_4174_, 4, v___f_4173_);
lean_closure_set(v___f_4174_, 5, v_toPure_4139_);
lean_closure_set(v___f_4174_, 6, v___f_4173_);
v___x_4175_ = l_Lean_Meta_getMatcherInfo_x3f___redArg(v_inst_4142_, v_inst_4159_, v_matcherName_4162_);
v___x_4176_ = lean_apply_4(v_toBind_4141_, lean_box(0), lean_box(0), v___x_4175_, v___f_4174_);
return v___x_4176_;
}
else
{
lean_object* v___f_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
lean_dec(v_matcherName_4162_);
lean_dec_ref(v_inst_4159_);
lean_dec_ref(v_inst_4145_);
lean_dec_ref(v_inst_4142_);
v___f_4177_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63), 2, 1);
lean_closure_set(v___f_4177_, 0, v___f_4172_);
v___x_4178_ = lean_unsigned_to_nat(0u);
v___x_4179_ = lean_apply_2(v_toPure_4139_, lean_box(0), v___x_4178_);
v___x_4180_ = lean_apply_4(v_toBind_4141_, lean_box(0), lean_box(0), v___x_4179_, v___f_4177_);
return v___x_4180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__66___boxed(lean_object** _args){
lean_object* v_matcherApp_4181_ = _args[0];
lean_object* v_toPure_4182_ = _args[1];
lean_object* v_inst_4183_ = _args[2];
lean_object* v_toBind_4184_ = _args[3];
lean_object* v_inst_4185_ = _args[4];
lean_object* v___f_4186_ = _args[5];
lean_object* v_onMotive_4187_ = _args[6];
lean_object* v_inst_4188_ = _args[7];
lean_object* v_onRemaining_4189_ = _args[8];
lean_object* v_inst_4190_ = _args[9];
lean_object* v___f_4191_ = _args[10];
lean_object* v_onAlt_4192_ = _args[11];
lean_object* v___f_4193_ = _args[12];
lean_object* v_useSplitter_4194_ = _args[13];
lean_object* v___f_4195_ = _args[14];
lean_object* v___x_4196_ = _args[15];
lean_object* v___x_4197_ = _args[16];
lean_object* v_toMonadExceptOf_4198_ = _args[17];
lean_object* v___f_4199_ = _args[18];
lean_object* v___f_4200_ = _args[19];
lean_object* v_onParams_4201_ = _args[20];
lean_object* v_inst_4202_ = _args[21];
lean_object* v_____do__lift_4203_ = _args[22];
_start:
{
uint8_t v_useSplitter_boxed_4204_; lean_object* v_res_4205_; 
v_useSplitter_boxed_4204_ = lean_unbox(v_useSplitter_4194_);
v_res_4205_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__66(v_matcherApp_4181_, v_toPure_4182_, v_inst_4183_, v_toBind_4184_, v_inst_4185_, v___f_4186_, v_onMotive_4187_, v_inst_4188_, v_onRemaining_4189_, v_inst_4190_, v___f_4191_, v_onAlt_4192_, v___f_4193_, v_useSplitter_boxed_4204_, v___f_4195_, v___x_4196_, v___x_4197_, v_toMonadExceptOf_4198_, v___f_4199_, v___f_4200_, v_onParams_4201_, v_inst_4202_, v_____do__lift_4203_);
return v_res_4205_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0(void){
_start:
{
lean_object* v___x_4206_; 
v___x_4206_ = l_Subarray_empty(lean_box(0));
return v___x_4206_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__1(void){
_start:
{
lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4207_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0);
v___x_4208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4208_, 0, v___x_4207_);
lean_ctor_set(v___x_4208_, 1, v___x_4207_);
return v___x_4208_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__2(void){
_start:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4209_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__1);
v___x_4210_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0);
v___x_4211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4211_, 0, v___x_4210_);
lean_ctor_set(v___x_4211_, 1, v___x_4209_);
return v___x_4211_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__3(void){
_start:
{
lean_object* v___x_4212_; 
v___x_4212_ = l_Array_instInhabited(lean_box(0));
return v___x_4212_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__4(void){
_start:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4213_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__2);
v___x_4214_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0);
v___x_4215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4214_);
lean_ctor_set(v___x_4215_, 1, v___x_4213_);
return v___x_4215_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__5(void){
_start:
{
lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; 
v___x_4216_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__4, &l_Lean_Meta_MatcherApp_transform___redArg___closed__4_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__4);
v___x_4217_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0);
v___x_4218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4218_, 0, v___x_4217_);
lean_ctor_set(v___x_4218_, 1, v___x_4216_);
return v___x_4218_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__6(void){
_start:
{
lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; 
v___x_4219_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__5);
v___x_4220_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__3);
v___x_4221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4221_, 0, v___x_4220_);
lean_ctor_set(v___x_4221_, 1, v___x_4219_);
return v___x_4221_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__7(void){
_start:
{
lean_object* v___x_4222_; lean_object* v___x_4223_; 
v___x_4222_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__6);
v___x_4223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4223_, 0, v___x_4222_);
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg(lean_object* v_inst_4224_, lean_object* v_inst_4225_, lean_object* v_inst_4226_, lean_object* v_inst_4227_, lean_object* v_inst_4228_, lean_object* v_matcherApp_4229_, uint8_t v_useSplitter_4230_, uint8_t v_addEqualities_4231_, uint8_t v_addProofEqualities_4232_, lean_object* v_onParams_4233_, lean_object* v_onMotive_4234_, lean_object* v_onAlt_4235_, lean_object* v_onRemaining_4236_){
_start:
{
lean_object* v_toApplicative_4237_; lean_object* v_toBind_4238_; lean_object* v_getEnv_4239_; lean_object* v_toPure_4240_; lean_object* v_toMonadExceptOf_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___f_4244_; lean_object* v___f_4245_; lean_object* v___f_4246_; lean_object* v___x_4247_; lean_object* v___f_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___f_4251_; lean_object* v___f_4252_; lean_object* v___f_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___f_4256_; lean_object* v___x_4257_; 
v_toApplicative_4237_ = lean_ctor_get(v_inst_4226_, 0);
v_toBind_4238_ = lean_ctor_get(v_inst_4226_, 1);
lean_inc_n(v_toBind_4238_, 4);
v_getEnv_4239_ = lean_ctor_get(v_inst_4228_, 0);
lean_inc(v_getEnv_4239_);
v_toPure_4240_ = lean_ctor_get(v_toApplicative_4237_, 1);
lean_inc_n(v_toPure_4240_, 5);
v_toMonadExceptOf_4241_ = lean_ctor_get(v_inst_4227_, 0);
lean_inc_ref(v_toMonadExceptOf_4241_);
v___x_4242_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__7, &l_Lean_Meta_MatcherApp_transform___redArg___closed__7_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__7);
lean_inc_ref_n(v_inst_4226_, 4);
v___x_4243_ = l_instInhabitedOfMonad___redArg(v_inst_4226_, v___x_4242_);
lean_inc_ref(v_inst_4227_);
v___f_4244_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4244_, 0, v_inst_4226_);
lean_closure_set(v___f_4244_, 1, v_inst_4227_);
lean_inc_n(v_inst_4224_, 3);
v___f_4245_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4245_, 0, v_inst_4224_);
v___f_4246_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4246_, 0, v_inst_4226_);
lean_closure_set(v___f_4246_, 1, v___f_4245_);
v___x_4247_ = l_Lean_instInhabitedExpr;
v___f_4248_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__5), 6, 3);
lean_closure_set(v___f_4248_, 0, v_toPure_4240_);
lean_closure_set(v___f_4248_, 1, v_inst_4224_);
lean_closure_set(v___f_4248_, 2, v_toBind_4238_);
v___x_4249_ = lean_box(v_addEqualities_4231_);
v___x_4250_ = lean_box(v_addProofEqualities_4232_);
v___f_4251_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed), 8, 5);
lean_closure_set(v___f_4251_, 0, v_toPure_4240_);
lean_closure_set(v___f_4251_, 1, v_inst_4224_);
lean_closure_set(v___f_4251_, 2, v_toBind_4238_);
lean_closure_set(v___f_4251_, 3, v___x_4249_);
lean_closure_set(v___f_4251_, 4, v___x_4250_);
v___f_4252_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__13), 2, 1);
lean_closure_set(v___f_4252_, 0, v_toPure_4240_);
v___f_4253_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14), 2, 1);
lean_closure_set(v___f_4253_, 0, v_toPure_4240_);
v___x_4254_ = l_instInhabitedOfMonad___redArg(v_inst_4226_, v___x_4247_);
v___x_4255_ = lean_box(v_useSplitter_4230_);
v___f_4256_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__66___boxed), 23, 22);
lean_closure_set(v___f_4256_, 0, v_matcherApp_4229_);
lean_closure_set(v___f_4256_, 1, v_toPure_4240_);
lean_closure_set(v___f_4256_, 2, v_inst_4224_);
lean_closure_set(v___f_4256_, 3, v_toBind_4238_);
lean_closure_set(v___f_4256_, 4, v_inst_4226_);
lean_closure_set(v___f_4256_, 5, v___f_4251_);
lean_closure_set(v___f_4256_, 6, v_onMotive_4234_);
lean_closure_set(v___f_4256_, 7, v_inst_4227_);
lean_closure_set(v___f_4256_, 8, v_onRemaining_4236_);
lean_closure_set(v___f_4256_, 9, v_inst_4225_);
lean_closure_set(v___f_4256_, 10, v___f_4253_);
lean_closure_set(v___f_4256_, 11, v_onAlt_4235_);
lean_closure_set(v___f_4256_, 12, v___f_4246_);
lean_closure_set(v___f_4256_, 13, v___x_4255_);
lean_closure_set(v___f_4256_, 14, v___f_4252_);
lean_closure_set(v___f_4256_, 15, v___x_4243_);
lean_closure_set(v___f_4256_, 16, v___x_4254_);
lean_closure_set(v___f_4256_, 17, v_toMonadExceptOf_4241_);
lean_closure_set(v___f_4256_, 18, v___f_4244_);
lean_closure_set(v___f_4256_, 19, v___f_4248_);
lean_closure_set(v___f_4256_, 20, v_onParams_4233_);
lean_closure_set(v___f_4256_, 21, v_inst_4228_);
v___x_4257_ = lean_apply_4(v_toBind_4238_, lean_box(0), lean_box(0), v_getEnv_4239_, v___f_4256_);
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___boxed(lean_object* v_inst_4258_, lean_object* v_inst_4259_, lean_object* v_inst_4260_, lean_object* v_inst_4261_, lean_object* v_inst_4262_, lean_object* v_matcherApp_4263_, lean_object* v_useSplitter_4264_, lean_object* v_addEqualities_4265_, lean_object* v_addProofEqualities_4266_, lean_object* v_onParams_4267_, lean_object* v_onMotive_4268_, lean_object* v_onAlt_4269_, lean_object* v_onRemaining_4270_){
_start:
{
uint8_t v_useSplitter_boxed_4271_; uint8_t v_addEqualities_boxed_4272_; uint8_t v_addProofEqualities_boxed_4273_; lean_object* v_res_4274_; 
v_useSplitter_boxed_4271_ = lean_unbox(v_useSplitter_4264_);
v_addEqualities_boxed_4272_ = lean_unbox(v_addEqualities_4265_);
v_addProofEqualities_boxed_4273_ = lean_unbox(v_addProofEqualities_4266_);
v_res_4274_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_4258_, v_inst_4259_, v_inst_4260_, v_inst_4261_, v_inst_4262_, v_matcherApp_4263_, v_useSplitter_boxed_4271_, v_addEqualities_boxed_4272_, v_addProofEqualities_boxed_4273_, v_onParams_4267_, v_onMotive_4268_, v_onAlt_4269_, v_onRemaining_4270_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform(lean_object* v_n_4275_, lean_object* v_inst_4276_, lean_object* v_inst_4277_, lean_object* v_inst_4278_, lean_object* v_inst_4279_, lean_object* v_inst_4280_, lean_object* v_inst_4281_, lean_object* v_inst_4282_, lean_object* v_inst_4283_, lean_object* v_matcherApp_4284_, uint8_t v_useSplitter_4285_, uint8_t v_addEqualities_4286_, uint8_t v_addProofEqualities_4287_, lean_object* v_onParams_4288_, lean_object* v_onMotive_4289_, lean_object* v_onAlt_4290_, lean_object* v_onRemaining_4291_){
_start:
{
lean_object* v___x_4292_; 
v___x_4292_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_4276_, v_inst_4277_, v_inst_4278_, v_inst_4279_, v_inst_4280_, v_matcherApp_4284_, v_useSplitter_4285_, v_addEqualities_4286_, v_addProofEqualities_4287_, v_onParams_4288_, v_onMotive_4289_, v_onAlt_4290_, v_onRemaining_4291_);
return v___x_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___boxed(lean_object** _args){
lean_object* v_n_4293_ = _args[0];
lean_object* v_inst_4294_ = _args[1];
lean_object* v_inst_4295_ = _args[2];
lean_object* v_inst_4296_ = _args[3];
lean_object* v_inst_4297_ = _args[4];
lean_object* v_inst_4298_ = _args[5];
lean_object* v_inst_4299_ = _args[6];
lean_object* v_inst_4300_ = _args[7];
lean_object* v_inst_4301_ = _args[8];
lean_object* v_matcherApp_4302_ = _args[9];
lean_object* v_useSplitter_4303_ = _args[10];
lean_object* v_addEqualities_4304_ = _args[11];
lean_object* v_addProofEqualities_4305_ = _args[12];
lean_object* v_onParams_4306_ = _args[13];
lean_object* v_onMotive_4307_ = _args[14];
lean_object* v_onAlt_4308_ = _args[15];
lean_object* v_onRemaining_4309_ = _args[16];
_start:
{
uint8_t v_useSplitter_boxed_4310_; uint8_t v_addEqualities_boxed_4311_; uint8_t v_addProofEqualities_boxed_4312_; lean_object* v_res_4313_; 
v_useSplitter_boxed_4310_ = lean_unbox(v_useSplitter_4303_);
v_addEqualities_boxed_4311_ = lean_unbox(v_addEqualities_4304_);
v_addProofEqualities_boxed_4312_ = lean_unbox(v_addProofEqualities_4305_);
v_res_4313_ = l_Lean_Meta_MatcherApp_transform(v_n_4293_, v_inst_4294_, v_inst_4295_, v_inst_4296_, v_inst_4297_, v_inst_4298_, v_inst_4299_, v_inst_4300_, v_inst_4301_, v_matcherApp_4302_, v_useSplitter_boxed_4310_, v_addEqualities_boxed_4311_, v_addProofEqualities_boxed_4312_, v_onParams_4306_, v_onMotive_4307_, v_onAlt_4308_, v_onRemaining_4309_);
lean_dec(v_inst_4301_);
lean_dec(v_inst_4300_);
lean_dec_ref(v_inst_4299_);
return v_res_4313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0(lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_){
_start:
{
lean_object* v___x_4320_; 
v___x_4320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4320_, 0, v___y_4314_);
return v___x_4320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0___boxed(lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__0(v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_);
lean_dec(v___y_4325_);
lean_dec_ref(v___y_4324_);
lean_dec(v___y_4323_);
lean_dec_ref(v___y_4322_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1(lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_){
_start:
{
lean_object* v___x_4334_; 
v___x_4334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4334_, 0, v___y_4328_);
return v___x_4334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1___boxed(lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__1(v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_);
lean_dec(v___y_4339_);
lean_dec_ref(v___y_4338_);
lean_dec(v___y_4337_);
lean_dec_ref(v___y_4336_);
return v_res_4341_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(lean_object* v_opts_4342_, lean_object* v_opt_4343_){
_start:
{
lean_object* v_name_4344_; lean_object* v_defValue_4345_; lean_object* v_map_4346_; lean_object* v___x_4347_; 
v_name_4344_ = lean_ctor_get(v_opt_4343_, 0);
v_defValue_4345_ = lean_ctor_get(v_opt_4343_, 1);
v_map_4346_ = lean_ctor_get(v_opts_4342_, 0);
v___x_4347_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4346_, v_name_4344_);
if (lean_obj_tag(v___x_4347_) == 0)
{
uint8_t v___x_4348_; 
v___x_4348_ = lean_unbox(v_defValue_4345_);
return v___x_4348_;
}
else
{
lean_object* v_val_4349_; 
v_val_4349_ = lean_ctor_get(v___x_4347_, 0);
lean_inc(v_val_4349_);
lean_dec_ref_known(v___x_4347_, 1);
if (lean_obj_tag(v_val_4349_) == 1)
{
uint8_t v_v_4350_; 
v_v_4350_ = lean_ctor_get_uint8(v_val_4349_, 0);
lean_dec_ref_known(v_val_4349_, 0);
return v_v_4350_;
}
else
{
uint8_t v___x_4351_; 
lean_dec(v_val_4349_);
v___x_4351_ = lean_unbox(v_defValue_4345_);
return v___x_4351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11___boxed(lean_object* v_opts_4352_, lean_object* v_opt_4353_){
_start:
{
uint8_t v_res_4354_; lean_object* v_r_4355_; 
v_res_4354_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(v_opts_4352_, v_opt_4353_);
lean_dec_ref(v_opt_4353_);
lean_dec_ref(v_opts_4352_);
v_r_4355_ = lean_box(v_res_4354_);
return v_r_4355_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_4364_, uint8_t v___y_4365_, lean_object* v_x_4366_){
_start:
{
if (lean_obj_tag(v_x_4366_) == 1)
{
lean_object* v_pre_4367_; 
v_pre_4367_ = lean_ctor_get(v_x_4366_, 0);
switch(lean_obj_tag(v_pre_4367_))
{
case 1:
{
lean_object* v_pre_4368_; 
v_pre_4368_ = lean_ctor_get(v_pre_4367_, 0);
switch(lean_obj_tag(v_pre_4368_))
{
case 0:
{
lean_object* v_str_4369_; lean_object* v_str_4370_; lean_object* v___x_4371_; uint8_t v___x_4372_; 
v_str_4369_ = lean_ctor_get(v_x_4366_, 1);
v_str_4370_ = lean_ctor_get(v_pre_4367_, 1);
v___x_4371_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_4372_ = lean_string_dec_eq(v_str_4370_, v___x_4371_);
if (v___x_4372_ == 0)
{
lean_object* v___x_4373_; uint8_t v___x_4374_; 
v___x_4373_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_4374_ = lean_string_dec_eq(v_str_4370_, v___x_4373_);
if (v___x_4374_ == 0)
{
return v___x_4374_;
}
else
{
lean_object* v___x_4375_; uint8_t v___x_4376_; 
v___x_4375_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_4376_ = lean_string_dec_eq(v_str_4369_, v___x_4375_);
if (v___x_4376_ == 0)
{
return v___x_4376_;
}
else
{
return v_suppressElabErrors_4364_;
}
}
}
else
{
lean_object* v___x_4377_; uint8_t v___x_4378_; 
v___x_4377_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_4378_ = lean_string_dec_eq(v_str_4369_, v___x_4377_);
if (v___x_4378_ == 0)
{
return v___x_4378_;
}
else
{
return v_suppressElabErrors_4364_;
}
}
}
case 1:
{
lean_object* v_pre_4379_; 
v_pre_4379_ = lean_ctor_get(v_pre_4368_, 0);
if (lean_obj_tag(v_pre_4379_) == 0)
{
lean_object* v_str_4380_; lean_object* v_str_4381_; lean_object* v_str_4382_; lean_object* v___x_4383_; uint8_t v___x_4384_; 
v_str_4380_ = lean_ctor_get(v_x_4366_, 1);
v_str_4381_ = lean_ctor_get(v_pre_4367_, 1);
v_str_4382_ = lean_ctor_get(v_pre_4368_, 1);
v___x_4383_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_4384_ = lean_string_dec_eq(v_str_4382_, v___x_4383_);
if (v___x_4384_ == 0)
{
return v___x_4384_;
}
else
{
lean_object* v___x_4385_; uint8_t v___x_4386_; 
v___x_4385_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_4386_ = lean_string_dec_eq(v_str_4381_, v___x_4385_);
if (v___x_4386_ == 0)
{
return v___x_4386_;
}
else
{
lean_object* v___x_4387_; uint8_t v___x_4388_; 
v___x_4387_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_4388_ = lean_string_dec_eq(v_str_4380_, v___x_4387_);
if (v___x_4388_ == 0)
{
return v___x_4388_;
}
else
{
return v_suppressElabErrors_4364_;
}
}
}
}
else
{
return v___y_4365_;
}
}
default: 
{
return v___y_4365_;
}
}
}
case 0:
{
lean_object* v_str_4389_; lean_object* v___x_4390_; uint8_t v___x_4391_; 
v_str_4389_ = lean_ctor_get(v_x_4366_, 1);
v___x_4390_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_4391_ = lean_string_dec_eq(v_str_4389_, v___x_4390_);
if (v___x_4391_ == 0)
{
return v___x_4391_;
}
else
{
return v_suppressElabErrors_4364_;
}
}
default: 
{
return v___y_4365_;
}
}
}
else
{
return v___y_4365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_4392_, lean_object* v___y_4393_, lean_object* v_x_4394_){
_start:
{
uint8_t v_suppressElabErrors_boxed_4395_; uint8_t v___y_32260__boxed_4396_; uint8_t v_res_4397_; lean_object* v_r_4398_; 
v_suppressElabErrors_boxed_4395_ = lean_unbox(v_suppressElabErrors_4392_);
v___y_32260__boxed_4396_ = lean_unbox(v___y_4393_);
v_res_4397_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_4395_, v___y_32260__boxed_4396_, v_x_4394_);
lean_dec(v_x_4394_);
v_r_4398_ = lean_box(v_res_4397_);
return v_r_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(lean_object* v_ref_4400_, lean_object* v_msgData_4401_, uint8_t v_severity_4402_, uint8_t v_isSilent_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_){
_start:
{
lean_object* v___y_4410_; lean_object* v___y_4411_; lean_object* v___y_4412_; uint8_t v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4415_; uint8_t v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4418_; lean_object* v___y_4446_; lean_object* v___y_4447_; lean_object* v___y_4448_; uint8_t v___y_4449_; uint8_t v___y_4450_; lean_object* v___y_4451_; uint8_t v___y_4452_; lean_object* v___y_4453_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v___y_4473_; uint8_t v___y_4474_; uint8_t v___y_4475_; lean_object* v___y_4476_; uint8_t v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4482_; lean_object* v___y_4483_; uint8_t v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; uint8_t v___y_4487_; uint8_t v___y_4488_; uint8_t v___x_4493_; lean_object* v___y_4495_; uint8_t v___y_4496_; lean_object* v___y_4497_; lean_object* v___y_4498_; lean_object* v___y_4499_; uint8_t v___y_4500_; uint8_t v___y_4501_; uint8_t v___y_4503_; uint8_t v___x_4518_; 
v___x_4493_ = 2;
v___x_4518_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4402_, v___x_4493_);
if (v___x_4518_ == 0)
{
v___y_4503_ = v___x_4518_;
goto v___jp_4502_;
}
else
{
uint8_t v___x_4519_; 
lean_inc_ref(v_msgData_4401_);
v___x_4519_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4401_);
v___y_4503_ = v___x_4519_;
goto v___jp_4502_;
}
v___jp_4409_:
{
lean_object* v___x_4419_; lean_object* v_currNamespace_4420_; lean_object* v_openDecls_4421_; lean_object* v_env_4422_; lean_object* v_nextMacroScope_4423_; lean_object* v_ngen_4424_; lean_object* v_auxDeclNGen_4425_; lean_object* v_traceState_4426_; lean_object* v_cache_4427_; lean_object* v_messages_4428_; lean_object* v_infoState_4429_; lean_object* v_snapshotTasks_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4444_; 
v___x_4419_ = lean_st_ref_take(v___y_4418_);
v_currNamespace_4420_ = lean_ctor_get(v___y_4417_, 6);
v_openDecls_4421_ = lean_ctor_get(v___y_4417_, 7);
v_env_4422_ = lean_ctor_get(v___x_4419_, 0);
v_nextMacroScope_4423_ = lean_ctor_get(v___x_4419_, 1);
v_ngen_4424_ = lean_ctor_get(v___x_4419_, 2);
v_auxDeclNGen_4425_ = lean_ctor_get(v___x_4419_, 3);
v_traceState_4426_ = lean_ctor_get(v___x_4419_, 4);
v_cache_4427_ = lean_ctor_get(v___x_4419_, 5);
v_messages_4428_ = lean_ctor_get(v___x_4419_, 6);
v_infoState_4429_ = lean_ctor_get(v___x_4419_, 7);
v_snapshotTasks_4430_ = lean_ctor_get(v___x_4419_, 8);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4432_ = v___x_4419_;
v_isShared_4433_ = v_isSharedCheck_4444_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_snapshotTasks_4430_);
lean_inc(v_infoState_4429_);
lean_inc(v_messages_4428_);
lean_inc(v_cache_4427_);
lean_inc(v_traceState_4426_);
lean_inc(v_auxDeclNGen_4425_);
lean_inc(v_ngen_4424_);
lean_inc(v_nextMacroScope_4423_);
lean_inc(v_env_4422_);
lean_dec(v___x_4419_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4444_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4439_; 
lean_inc(v_openDecls_4421_);
lean_inc(v_currNamespace_4420_);
v___x_4434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4434_, 0, v_currNamespace_4420_);
lean_ctor_set(v___x_4434_, 1, v_openDecls_4421_);
v___x_4435_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4435_, 0, v___x_4434_);
lean_ctor_set(v___x_4435_, 1, v___y_4412_);
lean_inc_ref(v___y_4415_);
lean_inc_ref(v___y_4414_);
v___x_4436_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4436_, 0, v___y_4414_);
lean_ctor_set(v___x_4436_, 1, v___y_4411_);
lean_ctor_set(v___x_4436_, 2, v___y_4410_);
lean_ctor_set(v___x_4436_, 3, v___y_4415_);
lean_ctor_set(v___x_4436_, 4, v___x_4435_);
lean_ctor_set_uint8(v___x_4436_, sizeof(void*)*5, v___y_4416_);
lean_ctor_set_uint8(v___x_4436_, sizeof(void*)*5 + 1, v___y_4413_);
lean_ctor_set_uint8(v___x_4436_, sizeof(void*)*5 + 2, v_isSilent_4403_);
v___x_4437_ = l_Lean_MessageLog_add(v___x_4436_, v_messages_4428_);
if (v_isShared_4433_ == 0)
{
lean_ctor_set(v___x_4432_, 6, v___x_4437_);
v___x_4439_ = v___x_4432_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_env_4422_);
lean_ctor_set(v_reuseFailAlloc_4443_, 1, v_nextMacroScope_4423_);
lean_ctor_set(v_reuseFailAlloc_4443_, 2, v_ngen_4424_);
lean_ctor_set(v_reuseFailAlloc_4443_, 3, v_auxDeclNGen_4425_);
lean_ctor_set(v_reuseFailAlloc_4443_, 4, v_traceState_4426_);
lean_ctor_set(v_reuseFailAlloc_4443_, 5, v_cache_4427_);
lean_ctor_set(v_reuseFailAlloc_4443_, 6, v___x_4437_);
lean_ctor_set(v_reuseFailAlloc_4443_, 7, v_infoState_4429_);
lean_ctor_set(v_reuseFailAlloc_4443_, 8, v_snapshotTasks_4430_);
v___x_4439_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; 
v___x_4440_ = lean_st_ref_put(v___y_4418_, v___x_4439_);
v___x_4441_ = lean_box(0);
v___x_4442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4442_, 0, v___x_4441_);
return v___x_4442_;
}
}
}
v___jp_4445_:
{
lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v_a_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4469_; 
v___x_4454_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4401_);
v___x_4455_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(v___x_4454_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_);
v_a_4456_ = lean_ctor_get(v___x_4455_, 0);
v_isSharedCheck_4469_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4469_ == 0)
{
v___x_4458_ = v___x_4455_;
v_isShared_4459_ = v_isSharedCheck_4469_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_a_4456_);
lean_dec(v___x_4455_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4469_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; 
lean_inc_ref_n(v___y_4447_, 2);
v___x_4460_ = l_Lean_FileMap_toPosition(v___y_4447_, v___y_4448_);
lean_dec(v___y_4448_);
v___x_4461_ = l_Lean_FileMap_toPosition(v___y_4447_, v___y_4453_);
lean_dec(v___y_4453_);
v___x_4462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4462_, 0, v___x_4461_);
v___x_4463_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___closed__0));
if (v___y_4449_ == 0)
{
lean_del_object(v___x_4458_);
lean_dec_ref(v___y_4446_);
v___y_4410_ = v___x_4462_;
v___y_4411_ = v___x_4460_;
v___y_4412_ = v_a_4456_;
v___y_4413_ = v___y_4450_;
v___y_4414_ = v___y_4451_;
v___y_4415_ = v___x_4463_;
v___y_4416_ = v___y_4452_;
v___y_4417_ = v___y_4406_;
v___y_4418_ = v___y_4407_;
goto v___jp_4409_;
}
else
{
uint8_t v___x_4464_; 
lean_inc(v_a_4456_);
v___x_4464_ = l_Lean_MessageData_hasTag(v___y_4446_, v_a_4456_);
if (v___x_4464_ == 0)
{
lean_object* v___x_4465_; lean_object* v___x_4467_; 
lean_dec_ref_known(v___x_4462_, 1);
lean_dec_ref(v___x_4460_);
lean_dec(v_a_4456_);
v___x_4465_ = lean_box(0);
if (v_isShared_4459_ == 0)
{
lean_ctor_set(v___x_4458_, 0, v___x_4465_);
v___x_4467_ = v___x_4458_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v___x_4465_);
v___x_4467_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
return v___x_4467_;
}
}
else
{
lean_del_object(v___x_4458_);
v___y_4410_ = v___x_4462_;
v___y_4411_ = v___x_4460_;
v___y_4412_ = v_a_4456_;
v___y_4413_ = v___y_4450_;
v___y_4414_ = v___y_4451_;
v___y_4415_ = v___x_4463_;
v___y_4416_ = v___y_4452_;
v___y_4417_ = v___y_4406_;
v___y_4418_ = v___y_4407_;
goto v___jp_4409_;
}
}
}
}
v___jp_4470_:
{
lean_object* v___x_4479_; 
v___x_4479_ = l_Lean_Syntax_getTailPos_x3f(v___y_4473_, v___y_4477_);
lean_dec(v___y_4473_);
if (lean_obj_tag(v___x_4479_) == 0)
{
lean_inc(v___y_4478_);
v___y_4446_ = v___y_4471_;
v___y_4447_ = v___y_4472_;
v___y_4448_ = v___y_4478_;
v___y_4449_ = v___y_4474_;
v___y_4450_ = v___y_4475_;
v___y_4451_ = v___y_4476_;
v___y_4452_ = v___y_4477_;
v___y_4453_ = v___y_4478_;
goto v___jp_4445_;
}
else
{
lean_object* v_val_4480_; 
v_val_4480_ = lean_ctor_get(v___x_4479_, 0);
lean_inc(v_val_4480_);
lean_dec_ref_known(v___x_4479_, 1);
v___y_4446_ = v___y_4471_;
v___y_4447_ = v___y_4472_;
v___y_4448_ = v___y_4478_;
v___y_4449_ = v___y_4474_;
v___y_4450_ = v___y_4475_;
v___y_4451_ = v___y_4476_;
v___y_4452_ = v___y_4477_;
v___y_4453_ = v_val_4480_;
goto v___jp_4445_;
}
}
v___jp_4481_:
{
lean_object* v_ref_4489_; lean_object* v___x_4490_; 
v_ref_4489_ = l_Lean_replaceRef(v_ref_4400_, v___y_4485_);
v___x_4490_ = l_Lean_Syntax_getPos_x3f(v_ref_4489_, v___y_4487_);
if (lean_obj_tag(v___x_4490_) == 0)
{
lean_object* v___x_4491_; 
v___x_4491_ = lean_unsigned_to_nat(0u);
v___y_4471_ = v___y_4482_;
v___y_4472_ = v___y_4483_;
v___y_4473_ = v_ref_4489_;
v___y_4474_ = v___y_4484_;
v___y_4475_ = v___y_4488_;
v___y_4476_ = v___y_4486_;
v___y_4477_ = v___y_4487_;
v___y_4478_ = v___x_4491_;
goto v___jp_4470_;
}
else
{
lean_object* v_val_4492_; 
v_val_4492_ = lean_ctor_get(v___x_4490_, 0);
lean_inc(v_val_4492_);
lean_dec_ref_known(v___x_4490_, 1);
v___y_4471_ = v___y_4482_;
v___y_4472_ = v___y_4483_;
v___y_4473_ = v_ref_4489_;
v___y_4474_ = v___y_4484_;
v___y_4475_ = v___y_4488_;
v___y_4476_ = v___y_4486_;
v___y_4477_ = v___y_4487_;
v___y_4478_ = v_val_4492_;
goto v___jp_4470_;
}
}
v___jp_4494_:
{
if (v___y_4501_ == 0)
{
v___y_4482_ = v___y_4498_;
v___y_4483_ = v___y_4495_;
v___y_4484_ = v___y_4496_;
v___y_4485_ = v___y_4497_;
v___y_4486_ = v___y_4499_;
v___y_4487_ = v___y_4500_;
v___y_4488_ = v_severity_4402_;
goto v___jp_4481_;
}
else
{
v___y_4482_ = v___y_4498_;
v___y_4483_ = v___y_4495_;
v___y_4484_ = v___y_4496_;
v___y_4485_ = v___y_4497_;
v___y_4486_ = v___y_4499_;
v___y_4487_ = v___y_4500_;
v___y_4488_ = v___x_4493_;
goto v___jp_4481_;
}
}
v___jp_4502_:
{
if (v___y_4503_ == 0)
{
lean_object* v_fileName_4504_; lean_object* v_fileMap_4505_; lean_object* v_options_4506_; lean_object* v_ref_4507_; uint8_t v_suppressElabErrors_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___f_4511_; uint8_t v___x_4512_; uint8_t v___x_4513_; 
v_fileName_4504_ = lean_ctor_get(v___y_4406_, 0);
v_fileMap_4505_ = lean_ctor_get(v___y_4406_, 1);
v_options_4506_ = lean_ctor_get(v___y_4406_, 2);
v_ref_4507_ = lean_ctor_get(v___y_4406_, 5);
v_suppressElabErrors_4508_ = lean_ctor_get_uint8(v___y_4406_, sizeof(void*)*14 + 1);
v___x_4509_ = lean_box(v_suppressElabErrors_4508_);
v___x_4510_ = lean_box(v___y_4503_);
v___f_4511_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4511_, 0, v___x_4509_);
lean_closure_set(v___f_4511_, 1, v___x_4510_);
v___x_4512_ = 1;
v___x_4513_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4402_, v___x_4512_);
if (v___x_4513_ == 0)
{
v___y_4495_ = v_fileMap_4505_;
v___y_4496_ = v_suppressElabErrors_4508_;
v___y_4497_ = v_ref_4507_;
v___y_4498_ = v___f_4511_;
v___y_4499_ = v_fileName_4504_;
v___y_4500_ = v___y_4503_;
v___y_4501_ = v___x_4513_;
goto v___jp_4494_;
}
else
{
lean_object* v___x_4514_; uint8_t v___x_4515_; 
v___x_4514_ = l_Lean_warningAsError;
v___x_4515_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(v_options_4506_, v___x_4514_);
v___y_4495_ = v_fileMap_4505_;
v___y_4496_ = v_suppressElabErrors_4508_;
v___y_4497_ = v_ref_4507_;
v___y_4498_ = v___f_4511_;
v___y_4499_ = v_fileName_4504_;
v___y_4500_ = v___y_4503_;
v___y_4501_ = v___x_4515_;
goto v___jp_4494_;
}
}
else
{
lean_object* v___x_4516_; lean_object* v___x_4517_; 
lean_dec_ref(v_msgData_4401_);
v___x_4516_ = lean_box(0);
v___x_4517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4517_, 0, v___x_4516_);
return v___x_4517_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_4520_, lean_object* v_msgData_4521_, lean_object* v_severity_4522_, lean_object* v_isSilent_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_){
_start:
{
uint8_t v_severity_boxed_4529_; uint8_t v_isSilent_boxed_4530_; lean_object* v_res_4531_; 
v_severity_boxed_4529_ = lean_unbox(v_severity_4522_);
v_isSilent_boxed_4530_ = lean_unbox(v_isSilent_4523_);
v_res_4531_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(v_ref_4520_, v_msgData_4521_, v_severity_boxed_4529_, v_isSilent_boxed_4530_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
lean_dec(v___y_4527_);
lean_dec_ref(v___y_4526_);
lean_dec(v___y_4525_);
lean_dec_ref(v___y_4524_);
lean_dec(v_ref_4520_);
return v_res_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(lean_object* v_msgData_4532_, uint8_t v_severity_4533_, uint8_t v_isSilent_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
lean_object* v_ref_4540_; lean_object* v___x_4541_; 
v_ref_4540_ = lean_ctor_get(v___y_4537_, 5);
v___x_4541_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(v_ref_4540_, v_msgData_4532_, v_severity_4533_, v_isSilent_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
return v___x_4541_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0___boxed(lean_object* v_msgData_4542_, lean_object* v_severity_4543_, lean_object* v_isSilent_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
uint8_t v_severity_boxed_4550_; uint8_t v_isSilent_boxed_4551_; lean_object* v_res_4552_; 
v_severity_boxed_4550_ = lean_unbox(v_severity_4543_);
v_isSilent_boxed_4551_ = lean_unbox(v_isSilent_4544_);
v_res_4552_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(v_msgData_4542_, v_severity_boxed_4550_, v_isSilent_boxed_4551_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_);
lean_dec(v___y_4548_);
lean_dec_ref(v___y_4547_);
lean_dec(v___y_4546_);
lean_dec_ref(v___y_4545_);
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(lean_object* v_msgData_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_){
_start:
{
uint8_t v___x_4559_; uint8_t v___x_4560_; lean_object* v___x_4561_; 
v___x_4559_ = 0;
v___x_4560_ = 0;
v___x_4561_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(v_msgData_4553_, v___x_4559_, v___x_4560_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
return v___x_4561_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0___boxed(lean_object* v_msgData_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_){
_start:
{
lean_object* v_res_4568_; 
v_res_4568_ = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(v_msgData_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_);
lean_dec(v___y_4566_);
lean_dec_ref(v___y_4565_);
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
return v_res_4568_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1(void){
_start:
{
lean_object* v___x_4570_; lean_object* v___x_4571_; 
v___x_4570_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0));
v___x_4571_ = l_Lean_stringToMessageData(v___x_4570_);
return v___x_4571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2(uint8_t v___x_4572_, lean_object* v___altIdx_4573_, lean_object* v_expAltType_4574_, lean_object* v___altFVars_4575_, lean_object* v_alt_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_){
_start:
{
lean_object* v___x_4582_; 
lean_inc(v___y_4580_);
lean_inc_ref(v___y_4579_);
lean_inc(v___y_4578_);
lean_inc_ref(v___y_4577_);
lean_inc_ref(v_alt_4576_);
v___x_4582_ = lean_infer_type(v_alt_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
if (lean_obj_tag(v___x_4582_) == 0)
{
lean_object* v_a_4583_; lean_object* v___x_4584_; 
v_a_4583_ = lean_ctor_get(v___x_4582_, 0);
lean_inc(v_a_4583_);
lean_dec_ref_known(v___x_4582_, 1);
v___x_4584_ = l_Lean_Meta_mkEq(v_expAltType_4574_, v_a_4583_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
if (lean_obj_tag(v___x_4584_) == 0)
{
lean_object* v_a_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; 
v_a_4585_ = lean_ctor_get(v___x_4584_, 0);
lean_inc(v_a_4585_);
lean_dec_ref_known(v___x_4584_, 1);
v___x_4586_ = lean_box(0);
v___x_4587_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4585_, v___x_4586_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
if (lean_obj_tag(v___x_4587_) == 0)
{
lean_object* v_a_4588_; lean_object* v___y_4590_; lean_object* v___x_4600_; lean_object* v___x_4601_; 
v_a_4588_ = lean_ctor_get(v___x_4587_, 0);
lean_inc(v_a_4588_);
lean_dec_ref_known(v___x_4587_, 1);
v___x_4600_ = l_Lean_Expr_mvarId_x21(v_a_4588_);
v___x_4601_ = l_Lean_Meta_Split_simpMatchTarget(v___x_4600_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
if (lean_obj_tag(v___x_4601_) == 0)
{
lean_object* v_a_4602_; lean_object* v___x_4603_; 
v_a_4602_ = lean_ctor_get(v___x_4601_, 0);
lean_inc_n(v_a_4602_, 2);
lean_dec_ref_known(v___x_4601_, 1);
v___x_4603_ = l_Lean_MVarId_refl(v_a_4602_, v___x_4572_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
if (lean_obj_tag(v___x_4603_) == 0)
{
lean_dec(v_a_4602_);
v___y_4590_ = v___x_4603_;
goto v___jp_4589_;
}
else
{
lean_object* v_a_4604_; uint8_t v___y_4606_; uint8_t v___x_4619_; 
v_a_4604_ = lean_ctor_get(v___x_4603_, 0);
lean_inc(v_a_4604_);
v___x_4619_ = l_Lean_Exception_isInterrupt(v_a_4604_);
if (v___x_4619_ == 0)
{
uint8_t v___x_4620_; 
v___x_4620_ = l_Lean_Exception_isRuntime(v_a_4604_);
v___y_4606_ = v___x_4620_;
goto v___jp_4605_;
}
else
{
lean_dec(v_a_4604_);
v___y_4606_ = v___x_4619_;
goto v___jp_4605_;
}
v___jp_4605_:
{
if (v___y_4606_ == 0)
{
lean_object* v___x_4608_; uint8_t v_isShared_4609_; uint8_t v_isSharedCheck_4617_; 
v_isSharedCheck_4617_ = !lean_is_exclusive(v___x_4603_);
if (v_isSharedCheck_4617_ == 0)
{
lean_object* v_unused_4618_; 
v_unused_4618_ = lean_ctor_get(v___x_4603_, 0);
lean_dec(v_unused_4618_);
v___x_4608_ = v___x_4603_;
v_isShared_4609_ = v_isSharedCheck_4617_;
goto v_resetjp_4607_;
}
else
{
lean_dec(v___x_4603_);
v___x_4608_ = lean_box(0);
v_isShared_4609_ = v_isSharedCheck_4617_;
goto v_resetjp_4607_;
}
v_resetjp_4607_:
{
lean_object* v___x_4610_; lean_object* v___x_4612_; 
v___x_4610_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1, &l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1);
lean_inc(v_a_4602_);
if (v_isShared_4609_ == 0)
{
lean_ctor_set(v___x_4608_, 0, v_a_4602_);
v___x_4612_ = v___x_4608_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v_a_4602_);
v___x_4612_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
lean_object* v___x_4613_; lean_object* v___x_4614_; 
v___x_4613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4613_, 0, v___x_4610_);
lean_ctor_set(v___x_4613_, 1, v___x_4612_);
v___x_4614_ = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(v___x_4613_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
if (lean_obj_tag(v___x_4614_) == 0)
{
lean_object* v___x_4615_; 
lean_dec_ref_known(v___x_4614_, 1);
v___x_4615_ = l_Lean_MVarId_admit(v_a_4602_, v___x_4572_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
v___y_4590_ = v___x_4615_;
goto v___jp_4589_;
}
else
{
lean_dec(v_a_4602_);
v___y_4590_ = v___x_4614_;
goto v___jp_4589_;
}
}
}
}
else
{
lean_dec(v_a_4602_);
v___y_4590_ = v___x_4603_;
goto v___jp_4589_;
}
}
}
}
else
{
lean_object* v_a_4621_; lean_object* v___x_4623_; uint8_t v_isShared_4624_; uint8_t v_isSharedCheck_4628_; 
lean_dec(v_a_4588_);
lean_dec_ref(v_alt_4576_);
v_a_4621_ = lean_ctor_get(v___x_4601_, 0);
v_isSharedCheck_4628_ = !lean_is_exclusive(v___x_4601_);
if (v_isSharedCheck_4628_ == 0)
{
v___x_4623_ = v___x_4601_;
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
else
{
lean_inc(v_a_4621_);
lean_dec(v___x_4601_);
v___x_4623_ = lean_box(0);
v_isShared_4624_ = v_isSharedCheck_4628_;
goto v_resetjp_4622_;
}
v_resetjp_4622_:
{
lean_object* v___x_4626_; 
if (v_isShared_4624_ == 0)
{
v___x_4626_ = v___x_4623_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v_a_4621_);
v___x_4626_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
return v___x_4626_;
}
}
}
v___jp_4589_:
{
if (lean_obj_tag(v___y_4590_) == 0)
{
lean_object* v___x_4591_; 
lean_dec_ref_known(v___y_4590_, 1);
v___x_4591_ = l_Lean_Meta_mkEqMPR(v_a_4588_, v_alt_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
return v___x_4591_;
}
else
{
lean_object* v_a_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4599_; 
lean_dec(v_a_4588_);
lean_dec_ref(v_alt_4576_);
v_a_4592_ = lean_ctor_get(v___y_4590_, 0);
v_isSharedCheck_4599_ = !lean_is_exclusive(v___y_4590_);
if (v_isSharedCheck_4599_ == 0)
{
v___x_4594_ = v___y_4590_;
v_isShared_4595_ = v_isSharedCheck_4599_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_a_4592_);
lean_dec(v___y_4590_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4599_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
lean_object* v___x_4597_; 
if (v_isShared_4595_ == 0)
{
v___x_4597_ = v___x_4594_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v_a_4592_);
v___x_4597_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
return v___x_4597_;
}
}
}
}
}
else
{
lean_dec_ref(v_alt_4576_);
return v___x_4587_;
}
}
else
{
lean_dec_ref(v_alt_4576_);
return v___x_4584_;
}
}
else
{
lean_dec_ref(v_alt_4576_);
lean_dec_ref(v_expAltType_4574_);
return v___x_4582_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___boxed(lean_object* v___x_4629_, lean_object* v___altIdx_4630_, lean_object* v_expAltType_4631_, lean_object* v___altFVars_4632_, lean_object* v_alt_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_){
_start:
{
uint8_t v___x_32583__boxed_4639_; lean_object* v_res_4640_; 
v___x_32583__boxed_4639_ = lean_unbox(v___x_4629_);
v_res_4640_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__2(v___x_32583__boxed_4639_, v___altIdx_4630_, v_expAltType_4631_, v___altFVars_4632_, v_alt_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
lean_dec(v___y_4637_);
lean_dec_ref(v___y_4636_);
lean_dec(v___y_4635_);
lean_dec_ref(v___y_4634_);
lean_dec_ref(v___altFVars_4632_);
lean_dec(v___altIdx_4630_);
return v_res_4640_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(lean_object* v___x_4641_, lean_object* v_e_4642_){
_start:
{
uint8_t v___x_4643_; lean_object* v_d_4645_; lean_object* v_b_4646_; 
v___x_4643_ = l_Lean_Expr_hasFVar(v_e_4642_);
if (v___x_4643_ == 0)
{
return v___x_4643_;
}
else
{
switch(lean_obj_tag(v_e_4642_))
{
case 7:
{
lean_object* v_binderType_4649_; lean_object* v_body_4650_; 
v_binderType_4649_ = lean_ctor_get(v_e_4642_, 1);
v_body_4650_ = lean_ctor_get(v_e_4642_, 2);
v_d_4645_ = v_binderType_4649_;
v_b_4646_ = v_body_4650_;
goto v___jp_4644_;
}
case 6:
{
lean_object* v_binderType_4651_; lean_object* v_body_4652_; 
v_binderType_4651_ = lean_ctor_get(v_e_4642_, 1);
v_body_4652_ = lean_ctor_get(v_e_4642_, 2);
v_d_4645_ = v_binderType_4651_;
v_b_4646_ = v_body_4652_;
goto v___jp_4644_;
}
case 10:
{
lean_object* v_expr_4653_; 
v_expr_4653_ = lean_ctor_get(v_e_4642_, 1);
v_e_4642_ = v_expr_4653_;
goto _start;
}
case 8:
{
lean_object* v_type_4655_; lean_object* v_value_4656_; lean_object* v_body_4657_; uint8_t v___x_4658_; 
v_type_4655_ = lean_ctor_get(v_e_4642_, 1);
v_value_4656_ = lean_ctor_get(v_e_4642_, 2);
v_body_4657_ = lean_ctor_get(v_e_4642_, 3);
v___x_4658_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4641_, v_type_4655_);
if (v___x_4658_ == 0)
{
uint8_t v___x_4659_; 
v___x_4659_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4641_, v_value_4656_);
if (v___x_4659_ == 0)
{
v_e_4642_ = v_body_4657_;
goto _start;
}
else
{
return v___x_4643_;
}
}
else
{
return v___x_4643_;
}
}
case 5:
{
lean_object* v_fn_4661_; lean_object* v_arg_4662_; uint8_t v___x_4663_; 
v_fn_4661_ = lean_ctor_get(v_e_4642_, 0);
v_arg_4662_ = lean_ctor_get(v_e_4642_, 1);
v___x_4663_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4641_, v_fn_4661_);
if (v___x_4663_ == 0)
{
v_e_4642_ = v_arg_4662_;
goto _start;
}
else
{
return v___x_4643_;
}
}
case 11:
{
lean_object* v_struct_4665_; 
v_struct_4665_ = lean_ctor_get(v_e_4642_, 2);
v_e_4642_ = v_struct_4665_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4667_; lean_object* v___x_4668_; uint8_t v___x_4669_; 
v_fvarId_4667_ = lean_ctor_get(v_e_4642_, 0);
v___x_4668_ = l_Lean_Expr_fvarId_x21(v___x_4641_);
v___x_4669_ = l_Lean_instBEqFVarId_beq(v_fvarId_4667_, v___x_4668_);
lean_dec(v___x_4668_);
return v___x_4669_;
}
default: 
{
uint8_t v___x_4670_; 
v___x_4670_ = 0;
return v___x_4670_;
}
}
}
v___jp_4644_:
{
uint8_t v___x_4647_; 
v___x_4647_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4641_, v_d_4645_);
if (v___x_4647_ == 0)
{
v_e_4642_ = v_b_4646_;
goto _start;
}
else
{
return v___x_4643_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1___boxed(lean_object* v___x_4671_, lean_object* v_e_4672_){
_start:
{
uint8_t v_res_4673_; lean_object* v_r_4674_; 
v_res_4673_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4671_, v_e_4672_);
lean_dec_ref(v_e_4672_);
lean_dec_ref(v___x_4671_);
v_r_4674_ = lean_box(v_res_4673_);
return v_r_4674_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4676_; lean_object* v___x_4677_; 
v___x_4676_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__0));
v___x_4677_ = l_Lean_stringToMessageData(v___x_4676_);
return v___x_4677_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4679_; lean_object* v___x_4680_; 
v___x_4679_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__2));
v___x_4680_ = l_Lean_stringToMessageData(v___x_4679_);
return v___x_4680_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_4682_; lean_object* v___x_4683_; 
v___x_4682_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__4));
v___x_4683_ = l_Lean_stringToMessageData(v___x_4682_);
return v___x_4683_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(lean_object* v_a_4684_, lean_object* v_termAlt_4685_, lean_object* v_a_4686_, lean_object* v_b_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_){
_start:
{
lean_object* v_array_4693_; lean_object* v_start_4694_; lean_object* v_stop_4695_; lean_object* v___x_4697_; uint8_t v_isShared_4698_; uint8_t v_isSharedCheck_4723_; 
v_array_4693_ = lean_ctor_get(v_a_4686_, 0);
v_start_4694_ = lean_ctor_get(v_a_4686_, 1);
v_stop_4695_ = lean_ctor_get(v_a_4686_, 2);
v_isSharedCheck_4723_ = !lean_is_exclusive(v_a_4686_);
if (v_isSharedCheck_4723_ == 0)
{
v___x_4697_ = v_a_4686_;
v_isShared_4698_ = v_isSharedCheck_4723_;
goto v_resetjp_4696_;
}
else
{
lean_inc(v_stop_4695_);
lean_inc(v_start_4694_);
lean_inc(v_array_4693_);
lean_dec(v_a_4686_);
v___x_4697_ = lean_box(0);
v_isShared_4698_ = v_isSharedCheck_4723_;
goto v_resetjp_4696_;
}
v_resetjp_4696_:
{
uint8_t v___x_4699_; 
v___x_4699_ = lean_nat_dec_lt(v_start_4694_, v_stop_4695_);
if (v___x_4699_ == 0)
{
lean_object* v___x_4700_; 
lean_del_object(v___x_4697_);
lean_dec(v_stop_4695_);
lean_dec(v_start_4694_);
lean_dec_ref(v_array_4693_);
lean_dec_ref(v_termAlt_4685_);
lean_dec_ref(v_a_4684_);
v___x_4700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4700_, 0, v_b_4687_);
return v___x_4700_;
}
else
{
lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4705_; 
v___x_4701_ = lean_box(0);
v___x_4702_ = lean_unsigned_to_nat(1u);
v___x_4703_ = lean_nat_add(v_start_4694_, v___x_4702_);
lean_inc_ref(v_array_4693_);
if (v_isShared_4698_ == 0)
{
lean_ctor_set(v___x_4697_, 1, v___x_4703_);
v___x_4705_ = v___x_4697_;
goto v_reusejp_4704_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v_array_4693_);
lean_ctor_set(v_reuseFailAlloc_4722_, 1, v___x_4703_);
lean_ctor_set(v_reuseFailAlloc_4722_, 2, v_stop_4695_);
v___x_4705_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4704_;
}
v_reusejp_4704_:
{
lean_object* v___x_4706_; uint8_t v___x_4707_; 
v___x_4706_ = lean_array_fget(v_array_4693_, v_start_4694_);
lean_dec(v_start_4694_);
lean_dec_ref(v_array_4693_);
v___x_4707_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4706_, v_a_4684_);
if (v___x_4707_ == 0)
{
lean_dec(v___x_4706_);
v_a_4686_ = v___x_4705_;
v_b_4687_ = v___x_4701_;
goto _start;
}
else
{
lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; 
v___x_4709_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1);
lean_inc_ref(v_a_4684_);
v___x_4710_ = l_Lean_MessageData_ofExpr(v_a_4684_);
v___x_4711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4711_, 0, v___x_4709_);
lean_ctor_set(v___x_4711_, 1, v___x_4710_);
v___x_4712_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3);
v___x_4713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4713_, 0, v___x_4711_);
lean_ctor_set(v___x_4713_, 1, v___x_4712_);
lean_inc_ref(v_termAlt_4685_);
v___x_4714_ = l_Lean_MessageData_ofExpr(v_termAlt_4685_);
v___x_4715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4715_, 0, v___x_4713_);
lean_ctor_set(v___x_4715_, 1, v___x_4714_);
v___x_4716_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5);
v___x_4717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4717_, 0, v___x_4715_);
lean_ctor_set(v___x_4717_, 1, v___x_4716_);
v___x_4718_ = l_Lean_MessageData_ofExpr(v___x_4706_);
v___x_4719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4719_, 0, v___x_4717_);
lean_ctor_set(v___x_4719_, 1, v___x_4718_);
v___x_4720_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_4719_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_);
if (lean_obj_tag(v___x_4720_) == 0)
{
lean_dec_ref_known(v___x_4720_, 1);
v_a_4686_ = v___x_4705_;
v_b_4687_ = v___x_4701_;
goto _start;
}
else
{
lean_dec_ref(v___x_4705_);
lean_dec_ref(v_termAlt_4685_);
lean_dec_ref(v_a_4684_);
return v___x_4720_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___boxed(lean_object* v_a_4724_, lean_object* v_termAlt_4725_, lean_object* v_a_4726_, lean_object* v_b_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_){
_start:
{
lean_object* v_res_4733_; 
v_res_4733_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_4724_, v_termAlt_4725_, v_a_4726_, v_b_4727_, v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_);
lean_dec(v___y_4731_);
lean_dec_ref(v___y_4730_);
lean_dec(v___y_4729_);
lean_dec_ref(v___y_4728_);
return v_res_4733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(lean_object* v_nExtra_4734_, lean_object* v_v_4735_, uint8_t v___x_4736_, uint8_t v___x_4737_, uint8_t v___x_4738_, lean_object* v_xs_4739_, lean_object* v_termAltBody_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_){
_start:
{
lean_object* v___x_4746_; 
lean_inc(v___y_4744_);
lean_inc_ref(v___y_4743_);
lean_inc(v___y_4742_);
lean_inc_ref(v___y_4741_);
v___x_4746_ = lean_infer_type(v_termAltBody_4740_, v___y_4741_, v___y_4742_, v___y_4743_, v___y_4744_);
if (lean_obj_tag(v___x_4746_) == 0)
{
lean_object* v_a_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; 
v_a_4747_ = lean_ctor_get(v___x_4746_, 0);
lean_inc_n(v_a_4747_, 2);
lean_dec_ref_known(v___x_4746_, 1);
v___x_4748_ = lean_array_get_size(v_xs_4739_);
v___x_4749_ = lean_nat_sub(v___x_4748_, v_nExtra_4734_);
v___x_4750_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_4749_);
lean_inc_ref(v_xs_4739_);
v___x_4751_ = l_Array_toSubarray___redArg(v_xs_4739_, v___x_4750_, v___x_4749_);
v___x_4752_ = l_Array_toSubarray___redArg(v_xs_4739_, v___x_4749_, v___x_4748_);
v___x_4753_ = lean_box(0);
v___x_4754_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_4747_, v_v_4735_, v___x_4752_, v___x_4753_, v___y_4741_, v___y_4742_, v___y_4743_, v___y_4744_);
if (lean_obj_tag(v___x_4754_) == 0)
{
lean_object* v___x_4755_; lean_object* v___x_4756_; 
lean_dec_ref_known(v___x_4754_, 1);
v___x_4755_ = l_Subarray_copy___redArg(v___x_4751_);
v___x_4756_ = l_Lean_Meta_mkLambdaFVars(v___x_4755_, v_a_4747_, v___x_4736_, v___x_4737_, v___x_4736_, v___x_4737_, v___x_4738_, v___y_4741_, v___y_4742_, v___y_4743_, v___y_4744_);
lean_dec_ref(v___x_4755_);
return v___x_4756_;
}
else
{
lean_object* v_a_4757_; lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4764_; 
lean_dec_ref(v___x_4751_);
lean_dec(v_a_4747_);
v_a_4757_ = lean_ctor_get(v___x_4754_, 0);
v_isSharedCheck_4764_ = !lean_is_exclusive(v___x_4754_);
if (v_isSharedCheck_4764_ == 0)
{
v___x_4759_ = v___x_4754_;
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
else
{
lean_inc(v_a_4757_);
lean_dec(v___x_4754_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
lean_object* v___x_4762_; 
if (v_isShared_4760_ == 0)
{
v___x_4762_ = v___x_4759_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v_a_4757_);
v___x_4762_ = v_reuseFailAlloc_4763_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
return v___x_4762_;
}
}
}
}
else
{
lean_dec_ref(v_xs_4739_);
lean_dec(v_v_4735_);
return v___x_4746_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed(lean_object* v_nExtra_4765_, lean_object* v_v_4766_, lean_object* v___x_4767_, lean_object* v___x_4768_, lean_object* v___x_4769_, lean_object* v_xs_4770_, lean_object* v_termAltBody_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_){
_start:
{
uint8_t v___x_32872__boxed_4777_; uint8_t v___x_32873__boxed_4778_; uint8_t v___x_32874__boxed_4779_; lean_object* v_res_4780_; 
v___x_32872__boxed_4777_ = lean_unbox(v___x_4767_);
v___x_32873__boxed_4778_ = lean_unbox(v___x_4768_);
v___x_32874__boxed_4779_ = lean_unbox(v___x_4769_);
v_res_4780_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(v_nExtra_4765_, v_v_4766_, v___x_32872__boxed_4777_, v___x_32873__boxed_4778_, v___x_32874__boxed_4779_, v_xs_4770_, v_termAltBody_4771_, v___y_4772_, v___y_4773_, v___y_4774_, v___y_4775_);
lean_dec(v___y_4775_);
lean_dec_ref(v___y_4774_);
lean_dec(v___y_4773_);
lean_dec_ref(v___y_4772_);
lean_dec(v_nExtra_4765_);
return v_res_4780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(lean_object* v_nExtra_4781_, size_t v_sz_4782_, size_t v_i_4783_, lean_object* v_bs_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_){
_start:
{
uint8_t v___x_4790_; 
v___x_4790_ = lean_usize_dec_lt(v_i_4783_, v_sz_4782_);
if (v___x_4790_ == 0)
{
lean_object* v___x_4791_; 
lean_dec(v_nExtra_4781_);
v___x_4791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4791_, 0, v_bs_4784_);
return v___x_4791_;
}
else
{
uint8_t v___x_4792_; uint8_t v___x_4793_; lean_object* v_v_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___f_4798_; lean_object* v___x_4799_; 
v___x_4792_ = 0;
v___x_4793_ = 1;
v_v_4794_ = lean_array_uget_borrowed(v_bs_4784_, v_i_4783_);
v___x_4795_ = lean_box(v___x_4792_);
v___x_4796_ = lean_box(v___x_4790_);
v___x_4797_ = lean_box(v___x_4793_);
lean_inc_n(v_v_4794_, 2);
lean_inc(v_nExtra_4781_);
v___f_4798_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4798_, 0, v_nExtra_4781_);
lean_closure_set(v___f_4798_, 1, v_v_4794_);
lean_closure_set(v___f_4798_, 2, v___x_4795_);
lean_closure_set(v___f_4798_, 3, v___x_4796_);
lean_closure_set(v___f_4798_, 4, v___x_4797_);
v___x_4799_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_v_4794_, v___f_4798_, v___x_4792_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_);
if (lean_obj_tag(v___x_4799_) == 0)
{
lean_object* v_a_4800_; lean_object* v___x_4801_; lean_object* v_bs_x27_4802_; size_t v___x_4803_; size_t v___x_4804_; lean_object* v___x_4805_; 
v_a_4800_ = lean_ctor_get(v___x_4799_, 0);
lean_inc(v_a_4800_);
lean_dec_ref_known(v___x_4799_, 1);
v___x_4801_ = lean_unsigned_to_nat(0u);
v_bs_x27_4802_ = lean_array_uset(v_bs_4784_, v_i_4783_, v___x_4801_);
v___x_4803_ = ((size_t)1ULL);
v___x_4804_ = lean_usize_add(v_i_4783_, v___x_4803_);
v___x_4805_ = lean_array_uset(v_bs_x27_4802_, v_i_4783_, v_a_4800_);
v_i_4783_ = v___x_4804_;
v_bs_4784_ = v___x_4805_;
goto _start;
}
else
{
lean_object* v_a_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4814_; 
lean_dec_ref(v_bs_4784_);
lean_dec(v_nExtra_4781_);
v_a_4807_ = lean_ctor_get(v___x_4799_, 0);
v_isSharedCheck_4814_ = !lean_is_exclusive(v___x_4799_);
if (v_isSharedCheck_4814_ == 0)
{
v___x_4809_ = v___x_4799_;
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
else
{
lean_inc(v_a_4807_);
lean_dec(v___x_4799_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
lean_object* v___x_4812_; 
if (v_isShared_4810_ == 0)
{
v___x_4812_ = v___x_4809_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4813_; 
v_reuseFailAlloc_4813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4813_, 0, v_a_4807_);
v___x_4812_ = v_reuseFailAlloc_4813_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
return v___x_4812_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___boxed(lean_object* v_nExtra_4815_, lean_object* v_sz_4816_, lean_object* v_i_4817_, lean_object* v_bs_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_){
_start:
{
size_t v_sz_boxed_4824_; size_t v_i_boxed_4825_; lean_object* v_res_4826_; 
v_sz_boxed_4824_ = lean_unbox_usize(v_sz_4816_);
lean_dec(v_sz_4816_);
v_i_boxed_4825_ = lean_unbox_usize(v_i_4817_);
lean_dec(v_i_4817_);
v_res_4826_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(v_nExtra_4815_, v_sz_boxed_4824_, v_i_boxed_4825_, v_bs_4818_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_);
lean_dec(v___y_4822_);
lean_dec_ref(v___y_4821_);
lean_dec(v___y_4820_);
lean_dec_ref(v___y_4819_);
return v_res_4826_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0(void){
_start:
{
lean_object* v___x_4827_; lean_object* v___x_4828_; 
v___x_4827_ = lean_box(0);
v___x_4828_ = l_Lean_Expr_sort___override(v___x_4827_);
return v___x_4828_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1(void){
_start:
{
lean_object* v___x_4829_; lean_object* v___x_4830_; 
v___x_4829_ = lean_box(0);
v___x_4830_ = l_Lean_Level_succ___override(v___x_4829_);
return v___x_4830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3(lean_object* v_nExtra_4831_, uint8_t v___x_4832_, uint8_t v___x_4833_, lean_object* v_alts_4834_, lean_object* v_toMatcherInfo_4835_, lean_object* v_matcherName_4836_, lean_object* v_params_4837_, lean_object* v_matcherLevels_4838_, lean_object* v_motiveArgs_4839_, lean_object* v_body_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_){
_start:
{
lean_object* v___x_4846_; 
lean_inc(v_nExtra_4831_);
v___x_4846_ = l_Lean_Meta_arrowDomainsN(v_nExtra_4831_, v_body_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
if (lean_obj_tag(v___x_4846_) == 0)
{
lean_object* v_a_4847_; lean_object* v___x_4848_; uint8_t v___x_4849_; lean_object* v___x_4850_; 
v_a_4847_ = lean_ctor_get(v___x_4846_, 0);
lean_inc(v_a_4847_);
lean_dec_ref_known(v___x_4846_, 1);
v___x_4848_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0, &l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0);
v___x_4849_ = 1;
v___x_4850_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_4839_, v___x_4848_, v___x_4832_, v___x_4833_, v___x_4832_, v___x_4833_, v___x_4849_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
if (lean_obj_tag(v___x_4850_) == 0)
{
lean_object* v_a_4851_; size_t v_sz_4852_; size_t v___x_4853_; lean_object* v___x_4854_; 
v_a_4851_ = lean_ctor_get(v___x_4850_, 0);
lean_inc(v_a_4851_);
lean_dec_ref_known(v___x_4850_, 1);
v_sz_4852_ = lean_array_size(v_alts_4834_);
v___x_4853_ = ((size_t)0ULL);
v___x_4854_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(v_nExtra_4831_, v_sz_4852_, v___x_4853_, v_alts_4834_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
if (lean_obj_tag(v___x_4854_) == 0)
{
lean_object* v_a_4855_; lean_object* v_matcherLevels_4857_; lean_object* v___y_4858_; lean_object* v___y_4859_; lean_object* v_uElimPos_x3f_4864_; 
v_a_4855_ = lean_ctor_get(v___x_4854_, 0);
lean_inc(v_a_4855_);
lean_dec_ref_known(v___x_4854_, 1);
v_uElimPos_x3f_4864_ = lean_ctor_get(v_toMatcherInfo_4835_, 3);
if (lean_obj_tag(v_uElimPos_x3f_4864_) == 0)
{
v_matcherLevels_4857_ = v_matcherLevels_4838_;
v___y_4858_ = v___y_4843_;
v___y_4859_ = v___y_4844_;
goto v___jp_4856_;
}
else
{
lean_object* v_val_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; 
v_val_4865_ = lean_ctor_get(v_uElimPos_x3f_4864_, 0);
v___x_4866_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1, &l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1);
v___x_4867_ = lean_array_set(v_matcherLevels_4838_, v_val_4865_, v___x_4866_);
v_matcherLevels_4857_ = v___x_4867_;
v___y_4858_ = v___y_4843_;
v___y_4859_ = v___y_4844_;
goto v___jp_4856_;
}
v___jp_4856_:
{
lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; 
v___x_4860_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_4861_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4861_, 0, v_toMatcherInfo_4835_);
lean_ctor_set(v___x_4861_, 1, v_matcherName_4836_);
lean_ctor_set(v___x_4861_, 2, v_matcherLevels_4857_);
lean_ctor_set(v___x_4861_, 3, v_params_4837_);
lean_ctor_set(v___x_4861_, 4, v_a_4851_);
lean_ctor_set(v___x_4861_, 5, v_motiveArgs_4839_);
lean_ctor_set(v___x_4861_, 6, v_a_4855_);
lean_ctor_set(v___x_4861_, 7, v___x_4860_);
v___x_4862_ = l_Lean_Meta_MatcherApp_toExpr(v___x_4861_);
v___x_4863_ = l_Lean_mkArrowN(v_a_4847_, v___x_4862_, v___y_4858_, v___y_4859_);
lean_dec(v_a_4847_);
return v___x_4863_;
}
}
else
{
lean_object* v_a_4868_; lean_object* v___x_4870_; uint8_t v_isShared_4871_; uint8_t v_isSharedCheck_4875_; 
lean_dec(v_a_4851_);
lean_dec(v_a_4847_);
lean_dec_ref(v_motiveArgs_4839_);
lean_dec_ref(v_matcherLevels_4838_);
lean_dec_ref(v_params_4837_);
lean_dec(v_matcherName_4836_);
lean_dec_ref(v_toMatcherInfo_4835_);
v_a_4868_ = lean_ctor_get(v___x_4854_, 0);
v_isSharedCheck_4875_ = !lean_is_exclusive(v___x_4854_);
if (v_isSharedCheck_4875_ == 0)
{
v___x_4870_ = v___x_4854_;
v_isShared_4871_ = v_isSharedCheck_4875_;
goto v_resetjp_4869_;
}
else
{
lean_inc(v_a_4868_);
lean_dec(v___x_4854_);
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
v_reuseFailAlloc_4874_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_dec(v_a_4847_);
lean_dec_ref(v_motiveArgs_4839_);
lean_dec_ref(v_matcherLevels_4838_);
lean_dec_ref(v_params_4837_);
lean_dec(v_matcherName_4836_);
lean_dec_ref(v_toMatcherInfo_4835_);
lean_dec_ref(v_alts_4834_);
lean_dec(v_nExtra_4831_);
return v___x_4850_;
}
}
else
{
lean_object* v_a_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_4883_; 
lean_dec_ref(v_motiveArgs_4839_);
lean_dec_ref(v_matcherLevels_4838_);
lean_dec_ref(v_params_4837_);
lean_dec(v_matcherName_4836_);
lean_dec_ref(v_toMatcherInfo_4835_);
lean_dec_ref(v_alts_4834_);
lean_dec(v_nExtra_4831_);
v_a_4876_ = lean_ctor_get(v___x_4846_, 0);
v_isSharedCheck_4883_ = !lean_is_exclusive(v___x_4846_);
if (v_isSharedCheck_4883_ == 0)
{
v___x_4878_ = v___x_4846_;
v_isShared_4879_ = v_isSharedCheck_4883_;
goto v_resetjp_4877_;
}
else
{
lean_inc(v_a_4876_);
lean_dec(v___x_4846_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed(lean_object* v_nExtra_4884_, lean_object* v___x_4885_, lean_object* v___x_4886_, lean_object* v_alts_4887_, lean_object* v_toMatcherInfo_4888_, lean_object* v_matcherName_4889_, lean_object* v_params_4890_, lean_object* v_matcherLevels_4891_, lean_object* v_motiveArgs_4892_, lean_object* v_body_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_){
_start:
{
uint8_t v___x_33007__boxed_4899_; uint8_t v___x_33008__boxed_4900_; lean_object* v_res_4901_; 
v___x_33007__boxed_4899_ = lean_unbox(v___x_4885_);
v___x_33008__boxed_4900_ = lean_unbox(v___x_4886_);
v_res_4901_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__3(v_nExtra_4884_, v___x_33007__boxed_4899_, v___x_33008__boxed_4900_, v_alts_4887_, v_toMatcherInfo_4888_, v_matcherName_4889_, v_params_4890_, v_matcherLevels_4891_, v_motiveArgs_4892_, v_body_4893_, v___y_4894_, v___y_4895_, v___y_4896_, v___y_4897_);
lean_dec(v___y_4897_);
lean_dec_ref(v___y_4896_);
lean_dec(v___y_4895_);
lean_dec_ref(v___y_4894_);
return v_res_4901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(lean_object* v_k_4902_, lean_object* v_ys_4903_, lean_object* v_args_4904_, lean_object* v___mask_4905_, lean_object* v___bodyType_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_){
_start:
{
lean_object* v___x_4912_; 
lean_inc(v___y_4910_);
lean_inc_ref(v___y_4909_);
lean_inc(v___y_4908_);
lean_inc_ref(v___y_4907_);
v___x_4912_ = lean_apply_7(v_k_4902_, v_ys_4903_, v_args_4904_, v___y_4907_, v___y_4908_, v___y_4909_, v___y_4910_, lean_box(0));
return v___x_4912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed(lean_object* v_k_4913_, lean_object* v_ys_4914_, lean_object* v_args_4915_, lean_object* v___mask_4916_, lean_object* v___bodyType_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_){
_start:
{
lean_object* v_res_4923_; 
v_res_4923_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(v_k_4913_, v_ys_4914_, v_args_4915_, v___mask_4916_, v___bodyType_4917_, v___y_4918_, v___y_4919_, v___y_4920_, v___y_4921_);
lean_dec(v___y_4921_);
lean_dec_ref(v___y_4920_);
lean_dec(v___y_4919_);
lean_dec_ref(v___y_4918_);
lean_dec_ref(v___bodyType_4917_);
lean_dec_ref(v___mask_4916_);
return v_res_4923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(lean_object* v_origAltType_4924_, lean_object* v_altInfo_4925_, lean_object* v_k_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_){
_start:
{
lean_object* v___f_4932_; lean_object* v___x_4933_; 
v___f_4932_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_4932_, 0, v_k_4926_);
v___x_4933_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_origAltType_4924_, v_altInfo_4925_, v___f_4932_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_);
if (lean_obj_tag(v___x_4933_) == 0)
{
lean_object* v_a_4934_; lean_object* v___x_4936_; uint8_t v_isShared_4937_; uint8_t v_isSharedCheck_4941_; 
v_a_4934_ = lean_ctor_get(v___x_4933_, 0);
v_isSharedCheck_4941_ = !lean_is_exclusive(v___x_4933_);
if (v_isSharedCheck_4941_ == 0)
{
v___x_4936_ = v___x_4933_;
v_isShared_4937_ = v_isSharedCheck_4941_;
goto v_resetjp_4935_;
}
else
{
lean_inc(v_a_4934_);
lean_dec(v___x_4933_);
v___x_4936_ = lean_box(0);
v_isShared_4937_ = v_isSharedCheck_4941_;
goto v_resetjp_4935_;
}
v_resetjp_4935_:
{
lean_object* v___x_4939_; 
if (v_isShared_4937_ == 0)
{
v___x_4939_ = v___x_4936_;
goto v_reusejp_4938_;
}
else
{
lean_object* v_reuseFailAlloc_4940_; 
v_reuseFailAlloc_4940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4940_, 0, v_a_4934_);
v___x_4939_ = v_reuseFailAlloc_4940_;
goto v_reusejp_4938_;
}
v_reusejp_4938_:
{
return v___x_4939_;
}
}
}
else
{
lean_object* v_a_4942_; lean_object* v___x_4944_; uint8_t v_isShared_4945_; uint8_t v_isSharedCheck_4949_; 
v_a_4942_ = lean_ctor_get(v___x_4933_, 0);
v_isSharedCheck_4949_ = !lean_is_exclusive(v___x_4933_);
if (v_isSharedCheck_4949_ == 0)
{
v___x_4944_ = v___x_4933_;
v_isShared_4945_ = v_isSharedCheck_4949_;
goto v_resetjp_4943_;
}
else
{
lean_inc(v_a_4942_);
lean_dec(v___x_4933_);
v___x_4944_ = lean_box(0);
v_isShared_4945_ = v_isSharedCheck_4949_;
goto v_resetjp_4943_;
}
v_resetjp_4943_:
{
lean_object* v___x_4947_; 
if (v_isShared_4945_ == 0)
{
v___x_4947_ = v___x_4944_;
goto v_reusejp_4946_;
}
else
{
lean_object* v_reuseFailAlloc_4948_; 
v_reuseFailAlloc_4948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4948_, 0, v_a_4942_);
v___x_4947_ = v_reuseFailAlloc_4948_;
goto v_reusejp_4946_;
}
v_reusejp_4946_:
{
return v___x_4947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___boxed(lean_object* v_origAltType_4950_, lean_object* v_altInfo_4951_, lean_object* v_k_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_){
_start:
{
lean_object* v_res_4958_; 
v_res_4958_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v_origAltType_4950_, v_altInfo_4951_, v_k_4952_, v___y_4953_, v___y_4954_, v___y_4955_, v___y_4956_);
lean_dec(v___y_4956_);
lean_dec_ref(v___y_4955_);
lean_dec(v___y_4954_);
lean_dec_ref(v___y_4953_);
return v_res_4958_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(lean_object* v___x_4959_, lean_object* v___x_4960_, lean_object* v___f_4961_, lean_object* v_fst_4962_, lean_object* v___x_4963_, lean_object* v___x_4964_, lean_object* v___x_4965_, lean_object* v___x_4966_, lean_object* v___x_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_){
_start:
{
lean_object* v___x_4973_; 
v___x_4973_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v___x_4959_, v___x_4960_, v___f_4961_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_);
if (lean_obj_tag(v___x_4973_) == 0)
{
lean_object* v_a_4974_; lean_object* v___x_4976_; uint8_t v_isShared_4977_; uint8_t v_isSharedCheck_4988_; 
v_a_4974_ = lean_ctor_get(v___x_4973_, 0);
v_isSharedCheck_4988_ = !lean_is_exclusive(v___x_4973_);
if (v_isSharedCheck_4988_ == 0)
{
v___x_4976_ = v___x_4973_;
v_isShared_4977_ = v_isSharedCheck_4988_;
goto v_resetjp_4975_;
}
else
{
lean_inc(v_a_4974_);
lean_dec(v___x_4973_);
v___x_4976_ = lean_box(0);
v_isShared_4977_ = v_isSharedCheck_4988_;
goto v_resetjp_4975_;
}
v_resetjp_4975_:
{
lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4986_; 
v___x_4978_ = lean_array_push(v_fst_4962_, v_a_4974_);
v___x_4979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4979_, 0, v___x_4963_);
lean_ctor_set(v___x_4979_, 1, v___x_4964_);
v___x_4980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4980_, 0, v___x_4965_);
lean_ctor_set(v___x_4980_, 1, v___x_4979_);
v___x_4981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4981_, 0, v___x_4966_);
lean_ctor_set(v___x_4981_, 1, v___x_4980_);
v___x_4982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4982_, 0, v___x_4967_);
lean_ctor_set(v___x_4982_, 1, v___x_4981_);
v___x_4983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4983_, 0, v___x_4978_);
lean_ctor_set(v___x_4983_, 1, v___x_4982_);
v___x_4984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4984_, 0, v___x_4983_);
if (v_isShared_4977_ == 0)
{
lean_ctor_set(v___x_4976_, 0, v___x_4984_);
v___x_4986_ = v___x_4976_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4987_; 
v_reuseFailAlloc_4987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4987_, 0, v___x_4984_);
v___x_4986_ = v_reuseFailAlloc_4987_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
return v___x_4986_;
}
}
}
else
{
lean_object* v_a_4989_; lean_object* v___x_4991_; uint8_t v_isShared_4992_; uint8_t v_isSharedCheck_4996_; 
lean_dec_ref(v___x_4967_);
lean_dec_ref(v___x_4966_);
lean_dec_ref(v___x_4965_);
lean_dec_ref(v___x_4964_);
lean_dec_ref(v___x_4963_);
lean_dec(v_fst_4962_);
v_a_4989_ = lean_ctor_get(v___x_4973_, 0);
v_isSharedCheck_4996_ = !lean_is_exclusive(v___x_4973_);
if (v_isSharedCheck_4996_ == 0)
{
v___x_4991_ = v___x_4973_;
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
else
{
lean_inc(v_a_4989_);
lean_dec(v___x_4973_);
v___x_4991_ = lean_box(0);
v_isShared_4992_ = v_isSharedCheck_4996_;
goto v_resetjp_4990_;
}
v_resetjp_4990_:
{
lean_object* v___x_4994_; 
if (v_isShared_4992_ == 0)
{
v___x_4994_ = v___x_4991_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4995_; 
v_reuseFailAlloc_4995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4995_, 0, v_a_4989_);
v___x_4994_ = v_reuseFailAlloc_4995_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
return v___x_4994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed(lean_object* v___x_4997_, lean_object* v___x_4998_, lean_object* v___f_4999_, lean_object* v_fst_5000_, lean_object* v___x_5001_, lean_object* v___x_5002_, lean_object* v___x_5003_, lean_object* v___x_5004_, lean_object* v___x_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_){
_start:
{
lean_object* v_res_5011_; 
v_res_5011_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(v___x_4997_, v___x_4998_, v___f_4999_, v_fst_5000_, v___x_5001_, v___x_5002_, v___x_5003_, v___x_5004_, v___x_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_);
lean_dec(v___y_5009_);
lean_dec_ref(v___y_5008_);
lean_dec(v___y_5007_);
lean_dec_ref(v___y_5006_);
return v_res_5011_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(lean_object* v_args_5012_, lean_object* v_ys_5013_, lean_object* v_ys2_5014_, lean_object* v_ys3_5015_, lean_object* v_onAlt_5016_, lean_object* v_a_5017_, uint8_t v___x_5018_, uint8_t v_useSplitter_5019_, lean_object* v___x_5020_, lean_object* v_ys4_5021_, lean_object* v_altType_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_){
_start:
{
lean_object* v___y_5029_; lean_object* v___x_5039_; lean_object* v___x_5040_; 
lean_inc_ref(v_args_5012_);
v___x_5039_ = l_Array_append___redArg(v_args_5012_, v_ys3_5015_);
v___x_5040_ = l_Lean_Meta_instantiateLambda(v___x_5020_, v___x_5039_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_);
lean_dec_ref(v___x_5039_);
if (lean_obj_tag(v___x_5040_) == 0)
{
v___y_5029_ = v___x_5040_;
goto v___jp_5028_;
}
else
{
lean_object* v_a_5041_; uint8_t v___y_5043_; uint8_t v___x_5046_; 
v_a_5041_ = lean_ctor_get(v___x_5040_, 0);
lean_inc(v_a_5041_);
v___x_5046_ = l_Lean_Exception_isInterrupt(v_a_5041_);
if (v___x_5046_ == 0)
{
uint8_t v___x_5047_; 
v___x_5047_ = l_Lean_Exception_isRuntime(v_a_5041_);
v___y_5043_ = v___x_5047_;
goto v___jp_5042_;
}
else
{
lean_dec(v_a_5041_);
v___y_5043_ = v___x_5046_;
goto v___jp_5042_;
}
v___jp_5042_:
{
if (v___y_5043_ == 0)
{
lean_object* v___x_5044_; lean_object* v___x_5045_; 
lean_dec_ref_known(v___x_5040_, 1);
v___x_5044_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2);
v___x_5045_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_5044_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_);
v___y_5029_ = v___x_5045_;
goto v___jp_5028_;
}
else
{
v___y_5029_ = v___x_5040_;
goto v___jp_5028_;
}
}
}
v___jp_5028_:
{
if (lean_obj_tag(v___y_5029_) == 0)
{
lean_object* v_a_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; 
v_a_5030_ = lean_ctor_get(v___y_5029_, 0);
lean_inc(v_a_5030_);
lean_dec_ref_known(v___y_5029_, 1);
lean_inc_ref(v_ys4_5021_);
lean_inc_ref(v_ys3_5015_);
lean_inc_ref(v_ys2_5014_);
lean_inc_ref(v_ys_5013_);
v___x_5031_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5031_, 0, v_args_5012_);
lean_ctor_set(v___x_5031_, 1, v_ys_5013_);
lean_ctor_set(v___x_5031_, 2, v_ys2_5014_);
lean_ctor_set(v___x_5031_, 3, v_ys3_5015_);
lean_ctor_set(v___x_5031_, 4, v_ys4_5021_);
lean_inc(v___y_5026_);
lean_inc_ref(v___y_5025_);
lean_inc(v___y_5024_);
lean_inc_ref(v___y_5023_);
v___x_5032_ = lean_apply_9(v_onAlt_5016_, v_a_5017_, v_altType_5022_, v___x_5031_, v_a_5030_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_, lean_box(0));
if (lean_obj_tag(v___x_5032_) == 0)
{
lean_object* v_a_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; uint8_t v___x_5037_; lean_object* v___x_5038_; 
v_a_5033_ = lean_ctor_get(v___x_5032_, 0);
lean_inc(v_a_5033_);
lean_dec_ref_known(v___x_5032_, 1);
v___x_5034_ = l_Array_append___redArg(v_ys_5013_, v_ys2_5014_);
lean_dec_ref(v_ys2_5014_);
v___x_5035_ = l_Array_append___redArg(v___x_5034_, v_ys3_5015_);
lean_dec_ref(v_ys3_5015_);
v___x_5036_ = l_Array_append___redArg(v___x_5035_, v_ys4_5021_);
lean_dec_ref(v_ys4_5021_);
v___x_5037_ = 1;
v___x_5038_ = l_Lean_Meta_mkLambdaFVars(v___x_5036_, v_a_5033_, v___x_5018_, v_useSplitter_5019_, v___x_5018_, v_useSplitter_5019_, v___x_5037_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_);
lean_dec_ref(v___x_5036_);
return v___x_5038_;
}
else
{
lean_dec_ref(v_ys4_5021_);
lean_dec_ref(v_ys3_5015_);
lean_dec_ref(v_ys2_5014_);
lean_dec_ref(v_ys_5013_);
return v___x_5032_;
}
}
else
{
lean_dec_ref(v_altType_5022_);
lean_dec_ref(v_ys4_5021_);
lean_dec(v_a_5017_);
lean_dec_ref(v_onAlt_5016_);
lean_dec_ref(v_ys3_5015_);
lean_dec_ref(v_ys2_5014_);
lean_dec_ref(v_ys_5013_);
lean_dec_ref(v_args_5012_);
return v___y_5029_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed(lean_object* v_args_5048_, lean_object* v_ys_5049_, lean_object* v_ys2_5050_, lean_object* v_ys3_5051_, lean_object* v_onAlt_5052_, lean_object* v_a_5053_, lean_object* v___x_5054_, lean_object* v_useSplitter_5055_, lean_object* v___x_5056_, lean_object* v_ys4_5057_, lean_object* v_altType_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_){
_start:
{
uint8_t v___x_33261__boxed_5064_; uint8_t v_useSplitter_boxed_5065_; lean_object* v_res_5066_; 
v___x_33261__boxed_5064_ = lean_unbox(v___x_5054_);
v_useSplitter_boxed_5065_ = lean_unbox(v_useSplitter_5055_);
v_res_5066_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(v_args_5048_, v_ys_5049_, v_ys2_5050_, v_ys3_5051_, v_onAlt_5052_, v_a_5053_, v___x_33261__boxed_5064_, v_useSplitter_boxed_5065_, v___x_5056_, v_ys4_5057_, v_altType_5058_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_);
lean_dec(v___y_5062_);
lean_dec_ref(v___y_5061_);
lean_dec(v___y_5060_);
lean_dec_ref(v___y_5059_);
return v_res_5066_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(lean_object* v_args_5067_, lean_object* v_ys_5068_, lean_object* v_ys2_5069_, lean_object* v_onAlt_5070_, lean_object* v_a_5071_, uint8_t v___x_5072_, uint8_t v_useSplitter_5073_, lean_object* v___x_5074_, lean_object* v_extraEqualities_5075_, lean_object* v_ys3_5076_, lean_object* v_altType_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_){
_start:
{
lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___f_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; 
v___x_5083_ = lean_box(v___x_5072_);
v___x_5084_ = lean_box(v_useSplitter_5073_);
v___f_5085_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed), 16, 9);
lean_closure_set(v___f_5085_, 0, v_args_5067_);
lean_closure_set(v___f_5085_, 1, v_ys_5068_);
lean_closure_set(v___f_5085_, 2, v_ys2_5069_);
lean_closure_set(v___f_5085_, 3, v_ys3_5076_);
lean_closure_set(v___f_5085_, 4, v_onAlt_5070_);
lean_closure_set(v___f_5085_, 5, v_a_5071_);
lean_closure_set(v___f_5085_, 6, v___x_5083_);
lean_closure_set(v___f_5085_, 7, v___x_5084_);
lean_closure_set(v___f_5085_, 8, v___x_5074_);
v___x_5086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5086_, 0, v_extraEqualities_5075_);
v___x_5087_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_5077_, v___x_5086_, v___f_5085_, v___x_5072_, v___x_5072_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_);
return v___x_5087_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed(lean_object* v_args_5088_, lean_object* v_ys_5089_, lean_object* v_ys2_5090_, lean_object* v_onAlt_5091_, lean_object* v_a_5092_, lean_object* v___x_5093_, lean_object* v_useSplitter_5094_, lean_object* v___x_5095_, lean_object* v_extraEqualities_5096_, lean_object* v_ys3_5097_, lean_object* v_altType_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_){
_start:
{
uint8_t v___x_33326__boxed_5104_; uint8_t v_useSplitter_boxed_5105_; lean_object* v_res_5106_; 
v___x_33326__boxed_5104_ = lean_unbox(v___x_5093_);
v_useSplitter_boxed_5105_ = lean_unbox(v_useSplitter_5094_);
v_res_5106_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(v_args_5088_, v_ys_5089_, v_ys2_5090_, v_onAlt_5091_, v_a_5092_, v___x_33326__boxed_5104_, v_useSplitter_boxed_5105_, v___x_5095_, v_extraEqualities_5096_, v_ys3_5097_, v_altType_5098_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_);
lean_dec(v___y_5102_);
lean_dec_ref(v___y_5101_);
lean_dec(v___y_5100_);
lean_dec_ref(v___y_5099_);
return v_res_5106_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(lean_object* v_args_5107_, lean_object* v_ys_5108_, lean_object* v_onAlt_5109_, lean_object* v_a_5110_, uint8_t v___x_5111_, uint8_t v_useSplitter_5112_, lean_object* v___x_5113_, lean_object* v_extraEqualities_5114_, lean_object* v_numDiscrEqs_5115_, lean_object* v_ys2_5116_, lean_object* v_altType_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_){
_start:
{
lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___f_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; 
v___x_5123_ = lean_box(v___x_5111_);
v___x_5124_ = lean_box(v_useSplitter_5112_);
v___f_5125_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_5125_, 0, v_args_5107_);
lean_closure_set(v___f_5125_, 1, v_ys_5108_);
lean_closure_set(v___f_5125_, 2, v_ys2_5116_);
lean_closure_set(v___f_5125_, 3, v_onAlt_5109_);
lean_closure_set(v___f_5125_, 4, v_a_5110_);
lean_closure_set(v___f_5125_, 5, v___x_5123_);
lean_closure_set(v___f_5125_, 6, v___x_5124_);
lean_closure_set(v___f_5125_, 7, v___x_5113_);
lean_closure_set(v___f_5125_, 8, v_extraEqualities_5114_);
v___x_5126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5126_, 0, v_numDiscrEqs_5115_);
v___x_5127_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_5117_, v___x_5126_, v___f_5125_, v___x_5111_, v___x_5111_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
return v___x_5127_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed(lean_object* v_args_5128_, lean_object* v_ys_5129_, lean_object* v_onAlt_5130_, lean_object* v_a_5131_, lean_object* v___x_5132_, lean_object* v_useSplitter_5133_, lean_object* v___x_5134_, lean_object* v_extraEqualities_5135_, lean_object* v_numDiscrEqs_5136_, lean_object* v_ys2_5137_, lean_object* v_altType_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_){
_start:
{
uint8_t v___x_33357__boxed_5144_; uint8_t v_useSplitter_boxed_5145_; lean_object* v_res_5146_; 
v___x_33357__boxed_5144_ = lean_unbox(v___x_5132_);
v_useSplitter_boxed_5145_ = lean_unbox(v_useSplitter_5133_);
v_res_5146_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(v_args_5128_, v_ys_5129_, v_onAlt_5130_, v_a_5131_, v___x_33357__boxed_5144_, v_useSplitter_boxed_5145_, v___x_5134_, v_extraEqualities_5135_, v_numDiscrEqs_5136_, v_ys2_5137_, v_altType_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_);
lean_dec(v___y_5142_);
lean_dec_ref(v___y_5141_);
lean_dec(v___y_5140_);
lean_dec_ref(v___y_5139_);
return v_res_5146_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0(void){
_start:
{
lean_object* v___x_5147_; 
v___x_5147_ = l_instMonadEIO(lean_box(0));
return v___x_5147_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(lean_object* v_msg_5152_, lean_object* v___y_5153_, lean_object* v___y_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_){
_start:
{
lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v_toApplicative_5160_; lean_object* v___x_5162_; uint8_t v_isShared_5163_; uint8_t v_isSharedCheck_5221_; 
v___x_5158_ = lean_obj_once(&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0, &l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0_once, _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0);
v___x_5159_ = l_StateRefT_x27_instMonad___redArg(v___x_5158_);
v_toApplicative_5160_ = lean_ctor_get(v___x_5159_, 0);
v_isSharedCheck_5221_ = !lean_is_exclusive(v___x_5159_);
if (v_isSharedCheck_5221_ == 0)
{
lean_object* v_unused_5222_; 
v_unused_5222_ = lean_ctor_get(v___x_5159_, 1);
lean_dec(v_unused_5222_);
v___x_5162_ = v___x_5159_;
v_isShared_5163_ = v_isSharedCheck_5221_;
goto v_resetjp_5161_;
}
else
{
lean_inc(v_toApplicative_5160_);
lean_dec(v___x_5159_);
v___x_5162_ = lean_box(0);
v_isShared_5163_ = v_isSharedCheck_5221_;
goto v_resetjp_5161_;
}
v_resetjp_5161_:
{
lean_object* v_toFunctor_5164_; lean_object* v_toSeq_5165_; lean_object* v_toSeqLeft_5166_; lean_object* v_toSeqRight_5167_; lean_object* v___x_5169_; uint8_t v_isShared_5170_; uint8_t v_isSharedCheck_5219_; 
v_toFunctor_5164_ = lean_ctor_get(v_toApplicative_5160_, 0);
v_toSeq_5165_ = lean_ctor_get(v_toApplicative_5160_, 2);
v_toSeqLeft_5166_ = lean_ctor_get(v_toApplicative_5160_, 3);
v_toSeqRight_5167_ = lean_ctor_get(v_toApplicative_5160_, 4);
v_isSharedCheck_5219_ = !lean_is_exclusive(v_toApplicative_5160_);
if (v_isSharedCheck_5219_ == 0)
{
lean_object* v_unused_5220_; 
v_unused_5220_ = lean_ctor_get(v_toApplicative_5160_, 1);
lean_dec(v_unused_5220_);
v___x_5169_ = v_toApplicative_5160_;
v_isShared_5170_ = v_isSharedCheck_5219_;
goto v_resetjp_5168_;
}
else
{
lean_inc(v_toSeqRight_5167_);
lean_inc(v_toSeqLeft_5166_);
lean_inc(v_toSeq_5165_);
lean_inc(v_toFunctor_5164_);
lean_dec(v_toApplicative_5160_);
v___x_5169_ = lean_box(0);
v_isShared_5170_ = v_isSharedCheck_5219_;
goto v_resetjp_5168_;
}
v_resetjp_5168_:
{
lean_object* v___f_5171_; lean_object* v___f_5172_; lean_object* v___f_5173_; lean_object* v___f_5174_; lean_object* v___x_5175_; lean_object* v___f_5176_; lean_object* v___f_5177_; lean_object* v___f_5178_; lean_object* v___x_5180_; 
v___f_5171_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__1));
v___f_5172_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__2));
lean_inc_ref(v_toFunctor_5164_);
v___f_5173_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5173_, 0, v_toFunctor_5164_);
v___f_5174_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5174_, 0, v_toFunctor_5164_);
v___x_5175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5175_, 0, v___f_5173_);
lean_ctor_set(v___x_5175_, 1, v___f_5174_);
v___f_5176_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5176_, 0, v_toSeqRight_5167_);
v___f_5177_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5177_, 0, v_toSeqLeft_5166_);
v___f_5178_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5178_, 0, v_toSeq_5165_);
if (v_isShared_5170_ == 0)
{
lean_ctor_set(v___x_5169_, 4, v___f_5176_);
lean_ctor_set(v___x_5169_, 3, v___f_5177_);
lean_ctor_set(v___x_5169_, 2, v___f_5178_);
lean_ctor_set(v___x_5169_, 1, v___f_5171_);
lean_ctor_set(v___x_5169_, 0, v___x_5175_);
v___x_5180_ = v___x_5169_;
goto v_reusejp_5179_;
}
else
{
lean_object* v_reuseFailAlloc_5218_; 
v_reuseFailAlloc_5218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5218_, 0, v___x_5175_);
lean_ctor_set(v_reuseFailAlloc_5218_, 1, v___f_5171_);
lean_ctor_set(v_reuseFailAlloc_5218_, 2, v___f_5178_);
lean_ctor_set(v_reuseFailAlloc_5218_, 3, v___f_5177_);
lean_ctor_set(v_reuseFailAlloc_5218_, 4, v___f_5176_);
v___x_5180_ = v_reuseFailAlloc_5218_;
goto v_reusejp_5179_;
}
v_reusejp_5179_:
{
lean_object* v___x_5182_; 
if (v_isShared_5163_ == 0)
{
lean_ctor_set(v___x_5162_, 1, v___f_5172_);
lean_ctor_set(v___x_5162_, 0, v___x_5180_);
v___x_5182_ = v___x_5162_;
goto v_reusejp_5181_;
}
else
{
lean_object* v_reuseFailAlloc_5217_; 
v_reuseFailAlloc_5217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5217_, 0, v___x_5180_);
lean_ctor_set(v_reuseFailAlloc_5217_, 1, v___f_5172_);
v___x_5182_ = v_reuseFailAlloc_5217_;
goto v_reusejp_5181_;
}
v_reusejp_5181_:
{
lean_object* v___x_5183_; lean_object* v_toApplicative_5184_; lean_object* v___x_5186_; uint8_t v_isShared_5187_; uint8_t v_isSharedCheck_5215_; 
v___x_5183_ = l_StateRefT_x27_instMonad___redArg(v___x_5182_);
v_toApplicative_5184_ = lean_ctor_get(v___x_5183_, 0);
v_isSharedCheck_5215_ = !lean_is_exclusive(v___x_5183_);
if (v_isSharedCheck_5215_ == 0)
{
lean_object* v_unused_5216_; 
v_unused_5216_ = lean_ctor_get(v___x_5183_, 1);
lean_dec(v_unused_5216_);
v___x_5186_ = v___x_5183_;
v_isShared_5187_ = v_isSharedCheck_5215_;
goto v_resetjp_5185_;
}
else
{
lean_inc(v_toApplicative_5184_);
lean_dec(v___x_5183_);
v___x_5186_ = lean_box(0);
v_isShared_5187_ = v_isSharedCheck_5215_;
goto v_resetjp_5185_;
}
v_resetjp_5185_:
{
lean_object* v_toFunctor_5188_; lean_object* v_toSeq_5189_; lean_object* v_toSeqLeft_5190_; lean_object* v_toSeqRight_5191_; lean_object* v___x_5193_; uint8_t v_isShared_5194_; uint8_t v_isSharedCheck_5213_; 
v_toFunctor_5188_ = lean_ctor_get(v_toApplicative_5184_, 0);
v_toSeq_5189_ = lean_ctor_get(v_toApplicative_5184_, 2);
v_toSeqLeft_5190_ = lean_ctor_get(v_toApplicative_5184_, 3);
v_toSeqRight_5191_ = lean_ctor_get(v_toApplicative_5184_, 4);
v_isSharedCheck_5213_ = !lean_is_exclusive(v_toApplicative_5184_);
if (v_isSharedCheck_5213_ == 0)
{
lean_object* v_unused_5214_; 
v_unused_5214_ = lean_ctor_get(v_toApplicative_5184_, 1);
lean_dec(v_unused_5214_);
v___x_5193_ = v_toApplicative_5184_;
v_isShared_5194_ = v_isSharedCheck_5213_;
goto v_resetjp_5192_;
}
else
{
lean_inc(v_toSeqRight_5191_);
lean_inc(v_toSeqLeft_5190_);
lean_inc(v_toSeq_5189_);
lean_inc(v_toFunctor_5188_);
lean_dec(v_toApplicative_5184_);
v___x_5193_ = lean_box(0);
v_isShared_5194_ = v_isSharedCheck_5213_;
goto v_resetjp_5192_;
}
v_resetjp_5192_:
{
lean_object* v___f_5195_; lean_object* v___f_5196_; lean_object* v___f_5197_; lean_object* v___f_5198_; lean_object* v___x_5199_; lean_object* v___f_5200_; lean_object* v___f_5201_; lean_object* v___f_5202_; lean_object* v___x_5204_; 
v___f_5195_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__3));
v___f_5196_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__4));
lean_inc_ref(v_toFunctor_5188_);
v___f_5197_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5197_, 0, v_toFunctor_5188_);
v___f_5198_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5198_, 0, v_toFunctor_5188_);
v___x_5199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5199_, 0, v___f_5197_);
lean_ctor_set(v___x_5199_, 1, v___f_5198_);
v___f_5200_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5200_, 0, v_toSeqRight_5191_);
v___f_5201_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5201_, 0, v_toSeqLeft_5190_);
v___f_5202_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5202_, 0, v_toSeq_5189_);
if (v_isShared_5194_ == 0)
{
lean_ctor_set(v___x_5193_, 4, v___f_5200_);
lean_ctor_set(v___x_5193_, 3, v___f_5201_);
lean_ctor_set(v___x_5193_, 2, v___f_5202_);
lean_ctor_set(v___x_5193_, 1, v___f_5195_);
lean_ctor_set(v___x_5193_, 0, v___x_5199_);
v___x_5204_ = v___x_5193_;
goto v_reusejp_5203_;
}
else
{
lean_object* v_reuseFailAlloc_5212_; 
v_reuseFailAlloc_5212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5212_, 0, v___x_5199_);
lean_ctor_set(v_reuseFailAlloc_5212_, 1, v___f_5195_);
lean_ctor_set(v_reuseFailAlloc_5212_, 2, v___f_5202_);
lean_ctor_set(v_reuseFailAlloc_5212_, 3, v___f_5201_);
lean_ctor_set(v_reuseFailAlloc_5212_, 4, v___f_5200_);
v___x_5204_ = v_reuseFailAlloc_5212_;
goto v_reusejp_5203_;
}
v_reusejp_5203_:
{
lean_object* v___x_5206_; 
if (v_isShared_5187_ == 0)
{
lean_ctor_set(v___x_5186_, 1, v___f_5196_);
lean_ctor_set(v___x_5186_, 0, v___x_5204_);
v___x_5206_ = v___x_5186_;
goto v_reusejp_5205_;
}
else
{
lean_object* v_reuseFailAlloc_5211_; 
v_reuseFailAlloc_5211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5211_, 0, v___x_5204_);
lean_ctor_set(v_reuseFailAlloc_5211_, 1, v___f_5196_);
v___x_5206_ = v_reuseFailAlloc_5211_;
goto v_reusejp_5205_;
}
v_reusejp_5205_:
{
lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_27442__overap_5209_; lean_object* v___x_5210_; 
v___x_5207_ = l_Lean_instInhabitedExpr;
v___x_5208_ = l_instInhabitedOfMonad___redArg(v___x_5206_, v___x_5207_);
v___x_27442__overap_5209_ = lean_panic_fn_borrowed(v___x_5208_, v_msg_5152_);
lean_dec(v___x_5208_);
lean_inc(v___y_5156_);
lean_inc_ref(v___y_5155_);
lean_inc(v___y_5154_);
lean_inc_ref(v___y_5153_);
v___x_5210_ = lean_apply_5(v___x_27442__overap_5209_, v___y_5153_, v___y_5154_, v___y_5155_, v___y_5156_, lean_box(0));
return v___x_5210_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed(lean_object* v_msg_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_){
_start:
{
lean_object* v_res_5229_; 
v_res_5229_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(v_msg_5223_, v___y_5224_, v___y_5225_, v___y_5226_, v___y_5227_);
lean_dec(v___y_5227_);
lean_dec_ref(v___y_5226_);
lean_dec(v___y_5225_);
lean_dec_ref(v___y_5224_);
return v_res_5229_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(lean_object* v___x_5230_, lean_object* v___x_5231_, lean_object* v___x_5232_, lean_object* v_onAlt_5233_, lean_object* v_a_5234_, uint8_t v___x_5235_, uint8_t v_useSplitter_5236_, lean_object* v___x_5237_, lean_object* v_extraEqualities_5238_, lean_object* v_numDiscrEqs_5239_, lean_object* v___x_5240_, lean_object* v_ys_5241_, lean_object* v_args_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_){
_start:
{
lean_object* v_numFields_5248_; lean_object* v_numOverlaps_5249_; uint8_t v_hasUnitThunk_5250_; lean_object* v___x_5251_; uint8_t v___x_5252_; 
v_numFields_5248_ = lean_ctor_get(v___x_5230_, 0);
v_numOverlaps_5249_ = lean_ctor_get(v___x_5230_, 1);
v_hasUnitThunk_5250_ = lean_ctor_get_uint8(v___x_5230_, sizeof(void*)*2);
v___x_5251_ = lean_array_get_size(v_ys_5241_);
v___x_5252_ = lean_nat_dec_eq(v___x_5251_, v_numFields_5248_);
if (v___x_5252_ == 0)
{
lean_object* v___x_5253_; lean_object* v___x_5254_; 
lean_dec_ref(v_args_5242_);
lean_dec_ref(v_ys_5241_);
lean_dec(v_numDiscrEqs_5239_);
lean_dec(v_extraEqualities_5238_);
lean_dec_ref(v___x_5237_);
lean_dec(v_a_5234_);
lean_dec_ref(v_onAlt_5233_);
lean_dec_ref(v___x_5231_);
v___x_5253_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__45___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__45___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__45___closed__3);
v___x_5254_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(v___x_5253_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_);
return v___x_5254_;
}
else
{
lean_object* v___x_5255_; 
v___x_5255_ = l_Lean_Meta_instantiateForall(v___x_5231_, v_ys_5241_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_);
if (lean_obj_tag(v___x_5255_) == 0)
{
lean_object* v_a_5256_; lean_object* v___x_5258_; uint8_t v_isShared_5259_; uint8_t v_isSharedCheck_5286_; 
v_a_5256_ = lean_ctor_get(v___x_5255_, 0);
v_isSharedCheck_5286_ = !lean_is_exclusive(v___x_5255_);
if (v_isSharedCheck_5286_ == 0)
{
v___x_5258_ = v___x_5255_;
v_isShared_5259_ = v_isSharedCheck_5286_;
goto v_resetjp_5257_;
}
else
{
lean_inc(v_a_5256_);
lean_dec(v___x_5255_);
v___x_5258_ = lean_box(0);
v_isShared_5259_ = v_isSharedCheck_5286_;
goto v_resetjp_5257_;
}
v_resetjp_5257_:
{
uint8_t v_hasUnitThunk_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; lean_object* v___f_5263_; lean_object* v_altType_5265_; lean_object* v___y_5266_; lean_object* v___y_5267_; lean_object* v___y_5268_; lean_object* v___y_5269_; 
v_hasUnitThunk_5260_ = lean_ctor_get_uint8(v___x_5232_, sizeof(void*)*2);
v___x_5261_ = lean_box(v___x_5235_);
v___x_5262_ = lean_box(v_useSplitter_5236_);
v___f_5263_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed), 16, 9);
lean_closure_set(v___f_5263_, 0, v_args_5242_);
lean_closure_set(v___f_5263_, 1, v_ys_5241_);
lean_closure_set(v___f_5263_, 2, v_onAlt_5233_);
lean_closure_set(v___f_5263_, 3, v_a_5234_);
lean_closure_set(v___f_5263_, 4, v___x_5261_);
lean_closure_set(v___f_5263_, 5, v___x_5262_);
lean_closure_set(v___f_5263_, 6, v___x_5237_);
lean_closure_set(v___f_5263_, 7, v_extraEqualities_5238_);
lean_closure_set(v___f_5263_, 8, v_numDiscrEqs_5239_);
if (v_hasUnitThunk_5260_ == 0)
{
v_altType_5265_ = v_a_5256_;
v___y_5266_ = v___y_5243_;
v___y_5267_ = v___y_5244_;
v___y_5268_ = v___y_5245_;
v___y_5269_ = v___y_5246_;
goto v___jp_5264_;
}
else
{
lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; 
v___x_5281_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2);
v___x_5282_ = lean_mk_empty_array_with_capacity(v___x_5240_);
v___x_5283_ = lean_array_push(v___x_5282_, v___x_5281_);
v___x_5284_ = l_Lean_Meta_instantiateForall(v_a_5256_, v___x_5283_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_);
lean_dec_ref(v___x_5283_);
if (lean_obj_tag(v___x_5284_) == 0)
{
lean_object* v_a_5285_; 
v_a_5285_ = lean_ctor_get(v___x_5284_, 0);
lean_inc(v_a_5285_);
lean_dec_ref_known(v___x_5284_, 1);
v_altType_5265_ = v_a_5285_;
v___y_5266_ = v___y_5243_;
v___y_5267_ = v___y_5244_;
v___y_5268_ = v___y_5245_;
v___y_5269_ = v___y_5246_;
goto v___jp_5264_;
}
else
{
lean_dec_ref(v___f_5263_);
lean_del_object(v___x_5258_);
return v___x_5284_;
}
}
v___jp_5264_:
{
lean_object* v___x_5271_; 
lean_inc(v_numOverlaps_5249_);
if (v_isShared_5259_ == 0)
{
lean_ctor_set_tag(v___x_5258_, 1);
lean_ctor_set(v___x_5258_, 0, v_numOverlaps_5249_);
v___x_5271_ = v___x_5258_;
goto v_reusejp_5270_;
}
else
{
lean_object* v_reuseFailAlloc_5280_; 
v_reuseFailAlloc_5280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5280_, 0, v_numOverlaps_5249_);
v___x_5271_ = v_reuseFailAlloc_5280_;
goto v_reusejp_5270_;
}
v_reusejp_5270_:
{
lean_object* v___x_5272_; 
v___x_5272_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_5265_, v___x_5271_, v___f_5263_, v___x_5235_, v___x_5235_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_);
if (lean_obj_tag(v___x_5272_) == 0)
{
if (v_hasUnitThunk_5250_ == 0)
{
return v___x_5272_;
}
else
{
lean_object* v_a_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; 
v_a_5273_ = lean_ctor_get(v___x_5272_, 0);
lean_inc(v_a_5273_);
lean_dec_ref_known(v___x_5272_, 1);
v___x_5274_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__2));
v___x_5275_ = lean_unsigned_to_nat(2u);
v___x_5276_ = lean_mk_empty_array_with_capacity(v___x_5275_);
lean_dec_ref(v___x_5276_);
v___x_5277_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__36___closed__6);
v___x_5278_ = lean_array_push(v___x_5277_, v_a_5273_);
v___x_5279_ = l_Lean_Meta_mkAppM(v___x_5274_, v___x_5278_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_);
return v___x_5279_;
}
}
else
{
return v___x_5272_;
}
}
}
}
}
else
{
lean_dec_ref(v_args_5242_);
lean_dec_ref(v_ys_5241_);
lean_dec(v_numDiscrEqs_5239_);
lean_dec(v_extraEqualities_5238_);
lean_dec_ref(v___x_5237_);
lean_dec(v_a_5234_);
lean_dec_ref(v_onAlt_5233_);
return v___x_5255_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_5287_ = _args[0];
lean_object* v___x_5288_ = _args[1];
lean_object* v___x_5289_ = _args[2];
lean_object* v_onAlt_5290_ = _args[3];
lean_object* v_a_5291_ = _args[4];
lean_object* v___x_5292_ = _args[5];
lean_object* v_useSplitter_5293_ = _args[6];
lean_object* v___x_5294_ = _args[7];
lean_object* v_extraEqualities_5295_ = _args[8];
lean_object* v_numDiscrEqs_5296_ = _args[9];
lean_object* v___x_5297_ = _args[10];
lean_object* v_ys_5298_ = _args[11];
lean_object* v_args_5299_ = _args[12];
lean_object* v___y_5300_ = _args[13];
lean_object* v___y_5301_ = _args[14];
lean_object* v___y_5302_ = _args[15];
lean_object* v___y_5303_ = _args[16];
lean_object* v___y_5304_ = _args[17];
_start:
{
uint8_t v___x_33561__boxed_5305_; uint8_t v_useSplitter_boxed_5306_; lean_object* v_res_5307_; 
v___x_33561__boxed_5305_ = lean_unbox(v___x_5292_);
v_useSplitter_boxed_5306_ = lean_unbox(v_useSplitter_5293_);
v_res_5307_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(v___x_5287_, v___x_5288_, v___x_5289_, v_onAlt_5290_, v_a_5291_, v___x_33561__boxed_5305_, v_useSplitter_boxed_5306_, v___x_5294_, v_extraEqualities_5295_, v_numDiscrEqs_5296_, v___x_5297_, v_ys_5298_, v_args_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_);
lean_dec(v___y_5303_);
lean_dec_ref(v___y_5302_);
lean_dec(v___y_5301_);
lean_dec_ref(v___y_5300_);
lean_dec(v___x_5297_);
lean_dec_ref(v___x_5289_);
lean_dec_ref(v___x_5287_);
return v_res_5307_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(lean_object* v_msg_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_){
_start:
{
lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v_toApplicative_5316_; lean_object* v___x_5318_; uint8_t v_isShared_5319_; uint8_t v_isSharedCheck_5377_; 
v___x_5314_ = lean_obj_once(&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0, &l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0_once, _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0);
v___x_5315_ = l_StateRefT_x27_instMonad___redArg(v___x_5314_);
v_toApplicative_5316_ = lean_ctor_get(v___x_5315_, 0);
v_isSharedCheck_5377_ = !lean_is_exclusive(v___x_5315_);
if (v_isSharedCheck_5377_ == 0)
{
lean_object* v_unused_5378_; 
v_unused_5378_ = lean_ctor_get(v___x_5315_, 1);
lean_dec(v_unused_5378_);
v___x_5318_ = v___x_5315_;
v_isShared_5319_ = v_isSharedCheck_5377_;
goto v_resetjp_5317_;
}
else
{
lean_inc(v_toApplicative_5316_);
lean_dec(v___x_5315_);
v___x_5318_ = lean_box(0);
v_isShared_5319_ = v_isSharedCheck_5377_;
goto v_resetjp_5317_;
}
v_resetjp_5317_:
{
lean_object* v_toFunctor_5320_; lean_object* v_toSeq_5321_; lean_object* v_toSeqLeft_5322_; lean_object* v_toSeqRight_5323_; lean_object* v___x_5325_; uint8_t v_isShared_5326_; uint8_t v_isSharedCheck_5375_; 
v_toFunctor_5320_ = lean_ctor_get(v_toApplicative_5316_, 0);
v_toSeq_5321_ = lean_ctor_get(v_toApplicative_5316_, 2);
v_toSeqLeft_5322_ = lean_ctor_get(v_toApplicative_5316_, 3);
v_toSeqRight_5323_ = lean_ctor_get(v_toApplicative_5316_, 4);
v_isSharedCheck_5375_ = !lean_is_exclusive(v_toApplicative_5316_);
if (v_isSharedCheck_5375_ == 0)
{
lean_object* v_unused_5376_; 
v_unused_5376_ = lean_ctor_get(v_toApplicative_5316_, 1);
lean_dec(v_unused_5376_);
v___x_5325_ = v_toApplicative_5316_;
v_isShared_5326_ = v_isSharedCheck_5375_;
goto v_resetjp_5324_;
}
else
{
lean_inc(v_toSeqRight_5323_);
lean_inc(v_toSeqLeft_5322_);
lean_inc(v_toSeq_5321_);
lean_inc(v_toFunctor_5320_);
lean_dec(v_toApplicative_5316_);
v___x_5325_ = lean_box(0);
v_isShared_5326_ = v_isSharedCheck_5375_;
goto v_resetjp_5324_;
}
v_resetjp_5324_:
{
lean_object* v___f_5327_; lean_object* v___f_5328_; lean_object* v___f_5329_; lean_object* v___f_5330_; lean_object* v___x_5331_; lean_object* v___f_5332_; lean_object* v___f_5333_; lean_object* v___f_5334_; lean_object* v___x_5336_; 
v___f_5327_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__1));
v___f_5328_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__2));
lean_inc_ref(v_toFunctor_5320_);
v___f_5329_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5329_, 0, v_toFunctor_5320_);
v___f_5330_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5330_, 0, v_toFunctor_5320_);
v___x_5331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5331_, 0, v___f_5329_);
lean_ctor_set(v___x_5331_, 1, v___f_5330_);
v___f_5332_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5332_, 0, v_toSeqRight_5323_);
v___f_5333_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5333_, 0, v_toSeqLeft_5322_);
v___f_5334_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5334_, 0, v_toSeq_5321_);
if (v_isShared_5326_ == 0)
{
lean_ctor_set(v___x_5325_, 4, v___f_5332_);
lean_ctor_set(v___x_5325_, 3, v___f_5333_);
lean_ctor_set(v___x_5325_, 2, v___f_5334_);
lean_ctor_set(v___x_5325_, 1, v___f_5327_);
lean_ctor_set(v___x_5325_, 0, v___x_5331_);
v___x_5336_ = v___x_5325_;
goto v_reusejp_5335_;
}
else
{
lean_object* v_reuseFailAlloc_5374_; 
v_reuseFailAlloc_5374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5374_, 0, v___x_5331_);
lean_ctor_set(v_reuseFailAlloc_5374_, 1, v___f_5327_);
lean_ctor_set(v_reuseFailAlloc_5374_, 2, v___f_5334_);
lean_ctor_set(v_reuseFailAlloc_5374_, 3, v___f_5333_);
lean_ctor_set(v_reuseFailAlloc_5374_, 4, v___f_5332_);
v___x_5336_ = v_reuseFailAlloc_5374_;
goto v_reusejp_5335_;
}
v_reusejp_5335_:
{
lean_object* v___x_5338_; 
if (v_isShared_5319_ == 0)
{
lean_ctor_set(v___x_5318_, 1, v___f_5328_);
lean_ctor_set(v___x_5318_, 0, v___x_5336_);
v___x_5338_ = v___x_5318_;
goto v_reusejp_5337_;
}
else
{
lean_object* v_reuseFailAlloc_5373_; 
v_reuseFailAlloc_5373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5373_, 0, v___x_5336_);
lean_ctor_set(v_reuseFailAlloc_5373_, 1, v___f_5328_);
v___x_5338_ = v_reuseFailAlloc_5373_;
goto v_reusejp_5337_;
}
v_reusejp_5337_:
{
lean_object* v___x_5339_; lean_object* v_toApplicative_5340_; lean_object* v___x_5342_; uint8_t v_isShared_5343_; uint8_t v_isSharedCheck_5371_; 
v___x_5339_ = l_StateRefT_x27_instMonad___redArg(v___x_5338_);
v_toApplicative_5340_ = lean_ctor_get(v___x_5339_, 0);
v_isSharedCheck_5371_ = !lean_is_exclusive(v___x_5339_);
if (v_isSharedCheck_5371_ == 0)
{
lean_object* v_unused_5372_; 
v_unused_5372_ = lean_ctor_get(v___x_5339_, 1);
lean_dec(v_unused_5372_);
v___x_5342_ = v___x_5339_;
v_isShared_5343_ = v_isSharedCheck_5371_;
goto v_resetjp_5341_;
}
else
{
lean_inc(v_toApplicative_5340_);
lean_dec(v___x_5339_);
v___x_5342_ = lean_box(0);
v_isShared_5343_ = v_isSharedCheck_5371_;
goto v_resetjp_5341_;
}
v_resetjp_5341_:
{
lean_object* v_toFunctor_5344_; lean_object* v_toSeq_5345_; lean_object* v_toSeqLeft_5346_; lean_object* v_toSeqRight_5347_; lean_object* v___x_5349_; uint8_t v_isShared_5350_; uint8_t v_isSharedCheck_5369_; 
v_toFunctor_5344_ = lean_ctor_get(v_toApplicative_5340_, 0);
v_toSeq_5345_ = lean_ctor_get(v_toApplicative_5340_, 2);
v_toSeqLeft_5346_ = lean_ctor_get(v_toApplicative_5340_, 3);
v_toSeqRight_5347_ = lean_ctor_get(v_toApplicative_5340_, 4);
v_isSharedCheck_5369_ = !lean_is_exclusive(v_toApplicative_5340_);
if (v_isSharedCheck_5369_ == 0)
{
lean_object* v_unused_5370_; 
v_unused_5370_ = lean_ctor_get(v_toApplicative_5340_, 1);
lean_dec(v_unused_5370_);
v___x_5349_ = v_toApplicative_5340_;
v_isShared_5350_ = v_isSharedCheck_5369_;
goto v_resetjp_5348_;
}
else
{
lean_inc(v_toSeqRight_5347_);
lean_inc(v_toSeqLeft_5346_);
lean_inc(v_toSeq_5345_);
lean_inc(v_toFunctor_5344_);
lean_dec(v_toApplicative_5340_);
v___x_5349_ = lean_box(0);
v_isShared_5350_ = v_isSharedCheck_5369_;
goto v_resetjp_5348_;
}
v_resetjp_5348_:
{
lean_object* v___f_5351_; lean_object* v___f_5352_; lean_object* v___f_5353_; lean_object* v___f_5354_; lean_object* v___x_5355_; lean_object* v___f_5356_; lean_object* v___f_5357_; lean_object* v___f_5358_; lean_object* v___x_5360_; 
v___f_5351_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__3));
v___f_5352_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__4));
lean_inc_ref(v_toFunctor_5344_);
v___f_5353_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5353_, 0, v_toFunctor_5344_);
v___f_5354_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5354_, 0, v_toFunctor_5344_);
v___x_5355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5355_, 0, v___f_5353_);
lean_ctor_set(v___x_5355_, 1, v___f_5354_);
v___f_5356_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5356_, 0, v_toSeqRight_5347_);
v___f_5357_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5357_, 0, v_toSeqLeft_5346_);
v___f_5358_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5358_, 0, v_toSeq_5345_);
if (v_isShared_5350_ == 0)
{
lean_ctor_set(v___x_5349_, 4, v___f_5356_);
lean_ctor_set(v___x_5349_, 3, v___f_5357_);
lean_ctor_set(v___x_5349_, 2, v___f_5358_);
lean_ctor_set(v___x_5349_, 1, v___f_5351_);
lean_ctor_set(v___x_5349_, 0, v___x_5355_);
v___x_5360_ = v___x_5349_;
goto v_reusejp_5359_;
}
else
{
lean_object* v_reuseFailAlloc_5368_; 
v_reuseFailAlloc_5368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5368_, 0, v___x_5355_);
lean_ctor_set(v_reuseFailAlloc_5368_, 1, v___f_5351_);
lean_ctor_set(v_reuseFailAlloc_5368_, 2, v___f_5358_);
lean_ctor_set(v_reuseFailAlloc_5368_, 3, v___f_5357_);
lean_ctor_set(v_reuseFailAlloc_5368_, 4, v___f_5356_);
v___x_5360_ = v_reuseFailAlloc_5368_;
goto v_reusejp_5359_;
}
v_reusejp_5359_:
{
lean_object* v___x_5362_; 
if (v_isShared_5343_ == 0)
{
lean_ctor_set(v___x_5342_, 1, v___f_5352_);
lean_ctor_set(v___x_5342_, 0, v___x_5360_);
v___x_5362_ = v___x_5342_;
goto v_reusejp_5361_;
}
else
{
lean_object* v_reuseFailAlloc_5367_; 
v_reuseFailAlloc_5367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5367_, 0, v___x_5360_);
lean_ctor_set(v_reuseFailAlloc_5367_, 1, v___f_5352_);
v___x_5362_ = v_reuseFailAlloc_5367_;
goto v_reusejp_5361_;
}
v_reusejp_5361_:
{
lean_object* v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_27462__overap_5365_; lean_object* v___x_5366_; 
v___x_5363_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__7, &l_Lean_Meta_MatcherApp_transform___redArg___closed__7_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__7);
v___x_5364_ = l_instInhabitedOfMonad___redArg(v___x_5362_, v___x_5363_);
v___x_27462__overap_5365_ = lean_panic_fn_borrowed(v___x_5364_, v_msg_5308_);
lean_dec(v___x_5364_);
lean_inc(v___y_5312_);
lean_inc_ref(v___y_5311_);
lean_inc(v___y_5310_);
lean_inc_ref(v___y_5309_);
v___x_5366_ = lean_apply_5(v___x_27462__overap_5365_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_, lean_box(0));
return v___x_5366_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___boxed(lean_object* v_msg_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_){
_start:
{
lean_object* v_res_5385_; 
v_res_5385_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(v_msg_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_);
lean_dec(v___y_5383_);
lean_dec_ref(v___y_5382_);
lean_dec(v___y_5381_);
lean_dec_ref(v___y_5380_);
return v_res_5385_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(lean_object* v___x_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_){
_start:
{
lean_object* v___x_5392_; 
v___x_5392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5392_, 0, v___x_5386_);
return v___x_5392_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed(lean_object* v___x_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_){
_start:
{
lean_object* v_res_5399_; 
v_res_5399_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(v___x_5393_, v___y_5394_, v___y_5395_, v___y_5396_, v___y_5397_);
lean_dec(v___y_5397_);
lean_dec_ref(v___y_5396_);
lean_dec(v___y_5395_);
lean_dec_ref(v___y_5394_);
return v_res_5399_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(lean_object* v_upperBound_5400_, lean_object* v_onAlt_5401_, uint8_t v_useSplitter_5402_, lean_object* v_extraEqualities_5403_, lean_object* v_numDiscrEqs_5404_, lean_object* v_a_5405_, lean_object* v_b_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_){
_start:
{
lean_object* v___y_5413_; uint8_t v___x_5436_; 
v___x_5436_ = lean_nat_dec_lt(v_a_5405_, v_upperBound_5400_);
if (v___x_5436_ == 0)
{
lean_object* v___x_5437_; 
lean_dec(v_a_5405_);
lean_dec(v_numDiscrEqs_5404_);
lean_dec(v_extraEqualities_5403_);
lean_dec_ref(v_onAlt_5401_);
v___x_5437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5437_, 0, v_b_5406_);
return v___x_5437_;
}
else
{
lean_object* v_snd_5438_; lean_object* v_snd_5439_; lean_object* v_snd_5440_; lean_object* v_snd_5441_; lean_object* v_snd_5442_; lean_object* v_fst_5443_; lean_object* v___x_5445_; uint8_t v_isShared_5446_; uint8_t v_isSharedCheck_5647_; 
v_snd_5438_ = lean_ctor_get(v_b_5406_, 1);
lean_inc(v_snd_5438_);
v_snd_5439_ = lean_ctor_get(v_snd_5438_, 1);
lean_inc(v_snd_5439_);
v_snd_5440_ = lean_ctor_get(v_snd_5439_, 1);
lean_inc(v_snd_5440_);
v_snd_5441_ = lean_ctor_get(v_snd_5440_, 1);
lean_inc(v_snd_5441_);
v_snd_5442_ = lean_ctor_get(v_snd_5441_, 1);
lean_inc(v_snd_5442_);
v_fst_5443_ = lean_ctor_get(v_b_5406_, 0);
v_isSharedCheck_5647_ = !lean_is_exclusive(v_b_5406_);
if (v_isSharedCheck_5647_ == 0)
{
lean_object* v_unused_5648_; 
v_unused_5648_ = lean_ctor_get(v_b_5406_, 1);
lean_dec(v_unused_5648_);
v___x_5445_ = v_b_5406_;
v_isShared_5446_ = v_isSharedCheck_5647_;
goto v_resetjp_5444_;
}
else
{
lean_inc(v_fst_5443_);
lean_dec(v_b_5406_);
v___x_5445_ = lean_box(0);
v_isShared_5446_ = v_isSharedCheck_5647_;
goto v_resetjp_5444_;
}
v_resetjp_5444_:
{
lean_object* v_fst_5447_; lean_object* v___x_5449_; uint8_t v_isShared_5450_; uint8_t v_isSharedCheck_5645_; 
v_fst_5447_ = lean_ctor_get(v_snd_5438_, 0);
v_isSharedCheck_5645_ = !lean_is_exclusive(v_snd_5438_);
if (v_isSharedCheck_5645_ == 0)
{
lean_object* v_unused_5646_; 
v_unused_5646_ = lean_ctor_get(v_snd_5438_, 1);
lean_dec(v_unused_5646_);
v___x_5449_ = v_snd_5438_;
v_isShared_5450_ = v_isSharedCheck_5645_;
goto v_resetjp_5448_;
}
else
{
lean_inc(v_fst_5447_);
lean_dec(v_snd_5438_);
v___x_5449_ = lean_box(0);
v_isShared_5450_ = v_isSharedCheck_5645_;
goto v_resetjp_5448_;
}
v_resetjp_5448_:
{
lean_object* v_fst_5451_; lean_object* v___x_5453_; uint8_t v_isShared_5454_; uint8_t v_isSharedCheck_5643_; 
v_fst_5451_ = lean_ctor_get(v_snd_5439_, 0);
v_isSharedCheck_5643_ = !lean_is_exclusive(v_snd_5439_);
if (v_isSharedCheck_5643_ == 0)
{
lean_object* v_unused_5644_; 
v_unused_5644_ = lean_ctor_get(v_snd_5439_, 1);
lean_dec(v_unused_5644_);
v___x_5453_ = v_snd_5439_;
v_isShared_5454_ = v_isSharedCheck_5643_;
goto v_resetjp_5452_;
}
else
{
lean_inc(v_fst_5451_);
lean_dec(v_snd_5439_);
v___x_5453_ = lean_box(0);
v_isShared_5454_ = v_isSharedCheck_5643_;
goto v_resetjp_5452_;
}
v_resetjp_5452_:
{
lean_object* v_fst_5455_; lean_object* v___x_5457_; uint8_t v_isShared_5458_; uint8_t v_isSharedCheck_5641_; 
v_fst_5455_ = lean_ctor_get(v_snd_5440_, 0);
v_isSharedCheck_5641_ = !lean_is_exclusive(v_snd_5440_);
if (v_isSharedCheck_5641_ == 0)
{
lean_object* v_unused_5642_; 
v_unused_5642_ = lean_ctor_get(v_snd_5440_, 1);
lean_dec(v_unused_5642_);
v___x_5457_ = v_snd_5440_;
v_isShared_5458_ = v_isSharedCheck_5641_;
goto v_resetjp_5456_;
}
else
{
lean_inc(v_fst_5455_);
lean_dec(v_snd_5440_);
v___x_5457_ = lean_box(0);
v_isShared_5458_ = v_isSharedCheck_5641_;
goto v_resetjp_5456_;
}
v_resetjp_5456_:
{
lean_object* v_fst_5459_; lean_object* v___x_5461_; uint8_t v_isShared_5462_; uint8_t v_isSharedCheck_5639_; 
v_fst_5459_ = lean_ctor_get(v_snd_5441_, 0);
v_isSharedCheck_5639_ = !lean_is_exclusive(v_snd_5441_);
if (v_isSharedCheck_5639_ == 0)
{
lean_object* v_unused_5640_; 
v_unused_5640_ = lean_ctor_get(v_snd_5441_, 1);
lean_dec(v_unused_5640_);
v___x_5461_ = v_snd_5441_;
v_isShared_5462_ = v_isSharedCheck_5639_;
goto v_resetjp_5460_;
}
else
{
lean_inc(v_fst_5459_);
lean_dec(v_snd_5441_);
v___x_5461_ = lean_box(0);
v_isShared_5462_ = v_isSharedCheck_5639_;
goto v_resetjp_5460_;
}
v_resetjp_5460_:
{
lean_object* v_array_5463_; lean_object* v_start_5464_; lean_object* v_stop_5465_; uint8_t v___x_5466_; 
v_array_5463_ = lean_ctor_get(v_snd_5442_, 0);
v_start_5464_ = lean_ctor_get(v_snd_5442_, 1);
v_stop_5465_ = lean_ctor_get(v_snd_5442_, 2);
v___x_5466_ = lean_nat_dec_lt(v_start_5464_, v_stop_5465_);
if (v___x_5466_ == 0)
{
lean_object* v___x_5468_; 
if (v_isShared_5462_ == 0)
{
v___x_5468_ = v___x_5461_;
goto v_reusejp_5467_;
}
else
{
lean_object* v_reuseFailAlloc_5483_; 
v_reuseFailAlloc_5483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5483_, 0, v_fst_5459_);
lean_ctor_set(v_reuseFailAlloc_5483_, 1, v_snd_5442_);
v___x_5468_ = v_reuseFailAlloc_5483_;
goto v_reusejp_5467_;
}
v_reusejp_5467_:
{
lean_object* v___x_5470_; 
if (v_isShared_5458_ == 0)
{
lean_ctor_set(v___x_5457_, 1, v___x_5468_);
v___x_5470_ = v___x_5457_;
goto v_reusejp_5469_;
}
else
{
lean_object* v_reuseFailAlloc_5482_; 
v_reuseFailAlloc_5482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5482_, 0, v_fst_5455_);
lean_ctor_set(v_reuseFailAlloc_5482_, 1, v___x_5468_);
v___x_5470_ = v_reuseFailAlloc_5482_;
goto v_reusejp_5469_;
}
v_reusejp_5469_:
{
lean_object* v___x_5472_; 
if (v_isShared_5454_ == 0)
{
lean_ctor_set(v___x_5453_, 1, v___x_5470_);
v___x_5472_ = v___x_5453_;
goto v_reusejp_5471_;
}
else
{
lean_object* v_reuseFailAlloc_5481_; 
v_reuseFailAlloc_5481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5481_, 0, v_fst_5451_);
lean_ctor_set(v_reuseFailAlloc_5481_, 1, v___x_5470_);
v___x_5472_ = v_reuseFailAlloc_5481_;
goto v_reusejp_5471_;
}
v_reusejp_5471_:
{
lean_object* v___x_5474_; 
if (v_isShared_5450_ == 0)
{
lean_ctor_set(v___x_5449_, 1, v___x_5472_);
v___x_5474_ = v___x_5449_;
goto v_reusejp_5473_;
}
else
{
lean_object* v_reuseFailAlloc_5480_; 
v_reuseFailAlloc_5480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5480_, 0, v_fst_5447_);
lean_ctor_set(v_reuseFailAlloc_5480_, 1, v___x_5472_);
v___x_5474_ = v_reuseFailAlloc_5480_;
goto v_reusejp_5473_;
}
v_reusejp_5473_:
{
lean_object* v___x_5476_; 
if (v_isShared_5446_ == 0)
{
lean_ctor_set(v___x_5445_, 1, v___x_5474_);
v___x_5476_ = v___x_5445_;
goto v_reusejp_5475_;
}
else
{
lean_object* v_reuseFailAlloc_5479_; 
v_reuseFailAlloc_5479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5479_, 0, v_fst_5443_);
lean_ctor_set(v_reuseFailAlloc_5479_, 1, v___x_5474_);
v___x_5476_ = v_reuseFailAlloc_5479_;
goto v_reusejp_5475_;
}
v_reusejp_5475_:
{
lean_object* v___x_5477_; lean_object* v___f_5478_; 
v___x_5477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5477_, 0, v___x_5476_);
v___f_5478_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5478_, 0, v___x_5477_);
v___y_5413_ = v___f_5478_;
goto v___jp_5412_;
}
}
}
}
}
}
else
{
lean_object* v___x_5485_; uint8_t v_isShared_5486_; uint8_t v_isSharedCheck_5635_; 
lean_inc(v_stop_5465_);
lean_inc(v_start_5464_);
lean_inc_ref(v_array_5463_);
v_isSharedCheck_5635_ = !lean_is_exclusive(v_snd_5442_);
if (v_isSharedCheck_5635_ == 0)
{
lean_object* v_unused_5636_; lean_object* v_unused_5637_; lean_object* v_unused_5638_; 
v_unused_5636_ = lean_ctor_get(v_snd_5442_, 2);
lean_dec(v_unused_5636_);
v_unused_5637_ = lean_ctor_get(v_snd_5442_, 1);
lean_dec(v_unused_5637_);
v_unused_5638_ = lean_ctor_get(v_snd_5442_, 0);
lean_dec(v_unused_5638_);
v___x_5485_ = v_snd_5442_;
v_isShared_5486_ = v_isSharedCheck_5635_;
goto v_resetjp_5484_;
}
else
{
lean_dec(v_snd_5442_);
v___x_5485_ = lean_box(0);
v_isShared_5486_ = v_isSharedCheck_5635_;
goto v_resetjp_5484_;
}
v_resetjp_5484_:
{
lean_object* v_array_5487_; lean_object* v_start_5488_; lean_object* v_stop_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; lean_object* v___x_5494_; 
v_array_5487_ = lean_ctor_get(v_fst_5459_, 0);
v_start_5488_ = lean_ctor_get(v_fst_5459_, 1);
v_stop_5489_ = lean_ctor_get(v_fst_5459_, 2);
v___x_5490_ = lean_array_fget(v_array_5463_, v_start_5464_);
v___x_5491_ = lean_unsigned_to_nat(1u);
v___x_5492_ = lean_nat_add(v_start_5464_, v___x_5491_);
lean_dec(v_start_5464_);
if (v_isShared_5486_ == 0)
{
lean_ctor_set(v___x_5485_, 1, v___x_5492_);
v___x_5494_ = v___x_5485_;
goto v_reusejp_5493_;
}
else
{
lean_object* v_reuseFailAlloc_5634_; 
v_reuseFailAlloc_5634_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5634_, 0, v_array_5463_);
lean_ctor_set(v_reuseFailAlloc_5634_, 1, v___x_5492_);
lean_ctor_set(v_reuseFailAlloc_5634_, 2, v_stop_5465_);
v___x_5494_ = v_reuseFailAlloc_5634_;
goto v_reusejp_5493_;
}
v_reusejp_5493_:
{
uint8_t v___x_5495_; 
v___x_5495_ = lean_nat_dec_lt(v_start_5488_, v_stop_5489_);
if (v___x_5495_ == 0)
{
lean_object* v___x_5497_; 
lean_dec(v___x_5490_);
if (v_isShared_5462_ == 0)
{
lean_ctor_set(v___x_5461_, 1, v___x_5494_);
v___x_5497_ = v___x_5461_;
goto v_reusejp_5496_;
}
else
{
lean_object* v_reuseFailAlloc_5512_; 
v_reuseFailAlloc_5512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5512_, 0, v_fst_5459_);
lean_ctor_set(v_reuseFailAlloc_5512_, 1, v___x_5494_);
v___x_5497_ = v_reuseFailAlloc_5512_;
goto v_reusejp_5496_;
}
v_reusejp_5496_:
{
lean_object* v___x_5499_; 
if (v_isShared_5458_ == 0)
{
lean_ctor_set(v___x_5457_, 1, v___x_5497_);
v___x_5499_ = v___x_5457_;
goto v_reusejp_5498_;
}
else
{
lean_object* v_reuseFailAlloc_5511_; 
v_reuseFailAlloc_5511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5511_, 0, v_fst_5455_);
lean_ctor_set(v_reuseFailAlloc_5511_, 1, v___x_5497_);
v___x_5499_ = v_reuseFailAlloc_5511_;
goto v_reusejp_5498_;
}
v_reusejp_5498_:
{
lean_object* v___x_5501_; 
if (v_isShared_5454_ == 0)
{
lean_ctor_set(v___x_5453_, 1, v___x_5499_);
v___x_5501_ = v___x_5453_;
goto v_reusejp_5500_;
}
else
{
lean_object* v_reuseFailAlloc_5510_; 
v_reuseFailAlloc_5510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5510_, 0, v_fst_5451_);
lean_ctor_set(v_reuseFailAlloc_5510_, 1, v___x_5499_);
v___x_5501_ = v_reuseFailAlloc_5510_;
goto v_reusejp_5500_;
}
v_reusejp_5500_:
{
lean_object* v___x_5503_; 
if (v_isShared_5450_ == 0)
{
lean_ctor_set(v___x_5449_, 1, v___x_5501_);
v___x_5503_ = v___x_5449_;
goto v_reusejp_5502_;
}
else
{
lean_object* v_reuseFailAlloc_5509_; 
v_reuseFailAlloc_5509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5509_, 0, v_fst_5447_);
lean_ctor_set(v_reuseFailAlloc_5509_, 1, v___x_5501_);
v___x_5503_ = v_reuseFailAlloc_5509_;
goto v_reusejp_5502_;
}
v_reusejp_5502_:
{
lean_object* v___x_5505_; 
if (v_isShared_5446_ == 0)
{
lean_ctor_set(v___x_5445_, 1, v___x_5503_);
v___x_5505_ = v___x_5445_;
goto v_reusejp_5504_;
}
else
{
lean_object* v_reuseFailAlloc_5508_; 
v_reuseFailAlloc_5508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5508_, 0, v_fst_5443_);
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
v___y_5413_ = v___f_5507_;
goto v___jp_5412_;
}
}
}
}
}
}
else
{
lean_object* v___x_5514_; uint8_t v_isShared_5515_; uint8_t v_isSharedCheck_5630_; 
lean_inc(v_stop_5489_);
lean_inc(v_start_5488_);
lean_inc_ref(v_array_5487_);
v_isSharedCheck_5630_ = !lean_is_exclusive(v_fst_5459_);
if (v_isSharedCheck_5630_ == 0)
{
lean_object* v_unused_5631_; lean_object* v_unused_5632_; lean_object* v_unused_5633_; 
v_unused_5631_ = lean_ctor_get(v_fst_5459_, 2);
lean_dec(v_unused_5631_);
v_unused_5632_ = lean_ctor_get(v_fst_5459_, 1);
lean_dec(v_unused_5632_);
v_unused_5633_ = lean_ctor_get(v_fst_5459_, 0);
lean_dec(v_unused_5633_);
v___x_5514_ = v_fst_5459_;
v_isShared_5515_ = v_isSharedCheck_5630_;
goto v_resetjp_5513_;
}
else
{
lean_dec(v_fst_5459_);
v___x_5514_ = lean_box(0);
v_isShared_5515_ = v_isSharedCheck_5630_;
goto v_resetjp_5513_;
}
v_resetjp_5513_:
{
lean_object* v_array_5516_; lean_object* v_start_5517_; lean_object* v_stop_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5522_; 
v_array_5516_ = lean_ctor_get(v_fst_5455_, 0);
v_start_5517_ = lean_ctor_get(v_fst_5455_, 1);
v_stop_5518_ = lean_ctor_get(v_fst_5455_, 2);
v___x_5519_ = lean_array_fget(v_array_5487_, v_start_5488_);
v___x_5520_ = lean_nat_add(v_start_5488_, v___x_5491_);
lean_dec(v_start_5488_);
if (v_isShared_5515_ == 0)
{
lean_ctor_set(v___x_5514_, 1, v___x_5520_);
v___x_5522_ = v___x_5514_;
goto v_reusejp_5521_;
}
else
{
lean_object* v_reuseFailAlloc_5629_; 
v_reuseFailAlloc_5629_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5629_, 0, v_array_5487_);
lean_ctor_set(v_reuseFailAlloc_5629_, 1, v___x_5520_);
lean_ctor_set(v_reuseFailAlloc_5629_, 2, v_stop_5489_);
v___x_5522_ = v_reuseFailAlloc_5629_;
goto v_reusejp_5521_;
}
v_reusejp_5521_:
{
uint8_t v___x_5523_; 
v___x_5523_ = lean_nat_dec_lt(v_start_5517_, v_stop_5518_);
if (v___x_5523_ == 0)
{
lean_object* v___x_5525_; 
lean_dec(v___x_5519_);
lean_dec(v___x_5490_);
if (v_isShared_5462_ == 0)
{
lean_ctor_set(v___x_5461_, 1, v___x_5494_);
lean_ctor_set(v___x_5461_, 0, v___x_5522_);
v___x_5525_ = v___x_5461_;
goto v_reusejp_5524_;
}
else
{
lean_object* v_reuseFailAlloc_5540_; 
v_reuseFailAlloc_5540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5540_, 0, v___x_5522_);
lean_ctor_set(v_reuseFailAlloc_5540_, 1, v___x_5494_);
v___x_5525_ = v_reuseFailAlloc_5540_;
goto v_reusejp_5524_;
}
v_reusejp_5524_:
{
lean_object* v___x_5527_; 
if (v_isShared_5458_ == 0)
{
lean_ctor_set(v___x_5457_, 1, v___x_5525_);
v___x_5527_ = v___x_5457_;
goto v_reusejp_5526_;
}
else
{
lean_object* v_reuseFailAlloc_5539_; 
v_reuseFailAlloc_5539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5539_, 0, v_fst_5455_);
lean_ctor_set(v_reuseFailAlloc_5539_, 1, v___x_5525_);
v___x_5527_ = v_reuseFailAlloc_5539_;
goto v_reusejp_5526_;
}
v_reusejp_5526_:
{
lean_object* v___x_5529_; 
if (v_isShared_5454_ == 0)
{
lean_ctor_set(v___x_5453_, 1, v___x_5527_);
v___x_5529_ = v___x_5453_;
goto v_reusejp_5528_;
}
else
{
lean_object* v_reuseFailAlloc_5538_; 
v_reuseFailAlloc_5538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5538_, 0, v_fst_5451_);
lean_ctor_set(v_reuseFailAlloc_5538_, 1, v___x_5527_);
v___x_5529_ = v_reuseFailAlloc_5538_;
goto v_reusejp_5528_;
}
v_reusejp_5528_:
{
lean_object* v___x_5531_; 
if (v_isShared_5450_ == 0)
{
lean_ctor_set(v___x_5449_, 1, v___x_5529_);
v___x_5531_ = v___x_5449_;
goto v_reusejp_5530_;
}
else
{
lean_object* v_reuseFailAlloc_5537_; 
v_reuseFailAlloc_5537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5537_, 0, v_fst_5447_);
lean_ctor_set(v_reuseFailAlloc_5537_, 1, v___x_5529_);
v___x_5531_ = v_reuseFailAlloc_5537_;
goto v_reusejp_5530_;
}
v_reusejp_5530_:
{
lean_object* v___x_5533_; 
if (v_isShared_5446_ == 0)
{
lean_ctor_set(v___x_5445_, 1, v___x_5531_);
v___x_5533_ = v___x_5445_;
goto v_reusejp_5532_;
}
else
{
lean_object* v_reuseFailAlloc_5536_; 
v_reuseFailAlloc_5536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5536_, 0, v_fst_5443_);
lean_ctor_set(v_reuseFailAlloc_5536_, 1, v___x_5531_);
v___x_5533_ = v_reuseFailAlloc_5536_;
goto v_reusejp_5532_;
}
v_reusejp_5532_:
{
lean_object* v___x_5534_; lean_object* v___f_5535_; 
v___x_5534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5534_, 0, v___x_5533_);
v___f_5535_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5535_, 0, v___x_5534_);
v___y_5413_ = v___f_5535_;
goto v___jp_5412_;
}
}
}
}
}
}
else
{
lean_object* v___x_5542_; uint8_t v_isShared_5543_; uint8_t v_isSharedCheck_5625_; 
lean_inc(v_stop_5518_);
lean_inc(v_start_5517_);
lean_inc_ref(v_array_5516_);
v_isSharedCheck_5625_ = !lean_is_exclusive(v_fst_5455_);
if (v_isSharedCheck_5625_ == 0)
{
lean_object* v_unused_5626_; lean_object* v_unused_5627_; lean_object* v_unused_5628_; 
v_unused_5626_ = lean_ctor_get(v_fst_5455_, 2);
lean_dec(v_unused_5626_);
v_unused_5627_ = lean_ctor_get(v_fst_5455_, 1);
lean_dec(v_unused_5627_);
v_unused_5628_ = lean_ctor_get(v_fst_5455_, 0);
lean_dec(v_unused_5628_);
v___x_5542_ = v_fst_5455_;
v_isShared_5543_ = v_isSharedCheck_5625_;
goto v_resetjp_5541_;
}
else
{
lean_dec(v_fst_5455_);
v___x_5542_ = lean_box(0);
v_isShared_5543_ = v_isSharedCheck_5625_;
goto v_resetjp_5541_;
}
v_resetjp_5541_:
{
lean_object* v_array_5544_; lean_object* v_start_5545_; lean_object* v_stop_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5550_; 
v_array_5544_ = lean_ctor_get(v_fst_5451_, 0);
v_start_5545_ = lean_ctor_get(v_fst_5451_, 1);
v_stop_5546_ = lean_ctor_get(v_fst_5451_, 2);
v___x_5547_ = lean_array_fget(v_array_5516_, v_start_5517_);
v___x_5548_ = lean_nat_add(v_start_5517_, v___x_5491_);
lean_dec(v_start_5517_);
if (v_isShared_5543_ == 0)
{
lean_ctor_set(v___x_5542_, 1, v___x_5548_);
v___x_5550_ = v___x_5542_;
goto v_reusejp_5549_;
}
else
{
lean_object* v_reuseFailAlloc_5624_; 
v_reuseFailAlloc_5624_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5624_, 0, v_array_5516_);
lean_ctor_set(v_reuseFailAlloc_5624_, 1, v___x_5548_);
lean_ctor_set(v_reuseFailAlloc_5624_, 2, v_stop_5518_);
v___x_5550_ = v_reuseFailAlloc_5624_;
goto v_reusejp_5549_;
}
v_reusejp_5549_:
{
uint8_t v___x_5551_; 
v___x_5551_ = lean_nat_dec_lt(v_start_5545_, v_stop_5546_);
if (v___x_5551_ == 0)
{
lean_object* v___x_5553_; 
lean_dec(v___x_5547_);
lean_dec(v___x_5519_);
lean_dec(v___x_5490_);
if (v_isShared_5462_ == 0)
{
lean_ctor_set(v___x_5461_, 1, v___x_5494_);
lean_ctor_set(v___x_5461_, 0, v___x_5522_);
v___x_5553_ = v___x_5461_;
goto v_reusejp_5552_;
}
else
{
lean_object* v_reuseFailAlloc_5568_; 
v_reuseFailAlloc_5568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5568_, 0, v___x_5522_);
lean_ctor_set(v_reuseFailAlloc_5568_, 1, v___x_5494_);
v___x_5553_ = v_reuseFailAlloc_5568_;
goto v_reusejp_5552_;
}
v_reusejp_5552_:
{
lean_object* v___x_5555_; 
if (v_isShared_5458_ == 0)
{
lean_ctor_set(v___x_5457_, 1, v___x_5553_);
lean_ctor_set(v___x_5457_, 0, v___x_5550_);
v___x_5555_ = v___x_5457_;
goto v_reusejp_5554_;
}
else
{
lean_object* v_reuseFailAlloc_5567_; 
v_reuseFailAlloc_5567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5567_, 0, v___x_5550_);
lean_ctor_set(v_reuseFailAlloc_5567_, 1, v___x_5553_);
v___x_5555_ = v_reuseFailAlloc_5567_;
goto v_reusejp_5554_;
}
v_reusejp_5554_:
{
lean_object* v___x_5557_; 
if (v_isShared_5454_ == 0)
{
lean_ctor_set(v___x_5453_, 1, v___x_5555_);
v___x_5557_ = v___x_5453_;
goto v_reusejp_5556_;
}
else
{
lean_object* v_reuseFailAlloc_5566_; 
v_reuseFailAlloc_5566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5566_, 0, v_fst_5451_);
lean_ctor_set(v_reuseFailAlloc_5566_, 1, v___x_5555_);
v___x_5557_ = v_reuseFailAlloc_5566_;
goto v_reusejp_5556_;
}
v_reusejp_5556_:
{
lean_object* v___x_5559_; 
if (v_isShared_5450_ == 0)
{
lean_ctor_set(v___x_5449_, 1, v___x_5557_);
v___x_5559_ = v___x_5449_;
goto v_reusejp_5558_;
}
else
{
lean_object* v_reuseFailAlloc_5565_; 
v_reuseFailAlloc_5565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5565_, 0, v_fst_5447_);
lean_ctor_set(v_reuseFailAlloc_5565_, 1, v___x_5557_);
v___x_5559_ = v_reuseFailAlloc_5565_;
goto v_reusejp_5558_;
}
v_reusejp_5558_:
{
lean_object* v___x_5561_; 
if (v_isShared_5446_ == 0)
{
lean_ctor_set(v___x_5445_, 1, v___x_5559_);
v___x_5561_ = v___x_5445_;
goto v_reusejp_5560_;
}
else
{
lean_object* v_reuseFailAlloc_5564_; 
v_reuseFailAlloc_5564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5564_, 0, v_fst_5443_);
lean_ctor_set(v_reuseFailAlloc_5564_, 1, v___x_5559_);
v___x_5561_ = v_reuseFailAlloc_5564_;
goto v_reusejp_5560_;
}
v_reusejp_5560_:
{
lean_object* v___x_5562_; lean_object* v___f_5563_; 
v___x_5562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5562_, 0, v___x_5561_);
v___f_5563_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5563_, 0, v___x_5562_);
v___y_5413_ = v___f_5563_;
goto v___jp_5412_;
}
}
}
}
}
}
else
{
lean_object* v___x_5570_; uint8_t v_isShared_5571_; uint8_t v_isSharedCheck_5620_; 
lean_inc(v_stop_5546_);
lean_inc(v_start_5545_);
lean_inc_ref(v_array_5544_);
v_isSharedCheck_5620_ = !lean_is_exclusive(v_fst_5451_);
if (v_isSharedCheck_5620_ == 0)
{
lean_object* v_unused_5621_; lean_object* v_unused_5622_; lean_object* v_unused_5623_; 
v_unused_5621_ = lean_ctor_get(v_fst_5451_, 2);
lean_dec(v_unused_5621_);
v_unused_5622_ = lean_ctor_get(v_fst_5451_, 1);
lean_dec(v_unused_5622_);
v_unused_5623_ = lean_ctor_get(v_fst_5451_, 0);
lean_dec(v_unused_5623_);
v___x_5570_ = v_fst_5451_;
v_isShared_5571_ = v_isSharedCheck_5620_;
goto v_resetjp_5569_;
}
else
{
lean_dec(v_fst_5451_);
v___x_5570_ = lean_box(0);
v_isShared_5571_ = v_isSharedCheck_5620_;
goto v_resetjp_5569_;
}
v_resetjp_5569_:
{
lean_object* v_array_5572_; lean_object* v_start_5573_; lean_object* v_stop_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5578_; 
v_array_5572_ = lean_ctor_get(v_fst_5447_, 0);
v_start_5573_ = lean_ctor_get(v_fst_5447_, 1);
v_stop_5574_ = lean_ctor_get(v_fst_5447_, 2);
v___x_5575_ = lean_array_fget(v_array_5544_, v_start_5545_);
v___x_5576_ = lean_nat_add(v_start_5545_, v___x_5491_);
lean_dec(v_start_5545_);
if (v_isShared_5571_ == 0)
{
lean_ctor_set(v___x_5570_, 1, v___x_5576_);
v___x_5578_ = v___x_5570_;
goto v_reusejp_5577_;
}
else
{
lean_object* v_reuseFailAlloc_5619_; 
v_reuseFailAlloc_5619_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5619_, 0, v_array_5544_);
lean_ctor_set(v_reuseFailAlloc_5619_, 1, v___x_5576_);
lean_ctor_set(v_reuseFailAlloc_5619_, 2, v_stop_5546_);
v___x_5578_ = v_reuseFailAlloc_5619_;
goto v_reusejp_5577_;
}
v_reusejp_5577_:
{
uint8_t v___x_5579_; 
v___x_5579_ = lean_nat_dec_lt(v_start_5573_, v_stop_5574_);
if (v___x_5579_ == 0)
{
lean_object* v___x_5581_; 
lean_dec(v___x_5575_);
lean_dec(v___x_5547_);
lean_dec(v___x_5519_);
lean_dec(v___x_5490_);
if (v_isShared_5462_ == 0)
{
lean_ctor_set(v___x_5461_, 1, v___x_5494_);
lean_ctor_set(v___x_5461_, 0, v___x_5522_);
v___x_5581_ = v___x_5461_;
goto v_reusejp_5580_;
}
else
{
lean_object* v_reuseFailAlloc_5596_; 
v_reuseFailAlloc_5596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5596_, 0, v___x_5522_);
lean_ctor_set(v_reuseFailAlloc_5596_, 1, v___x_5494_);
v___x_5581_ = v_reuseFailAlloc_5596_;
goto v_reusejp_5580_;
}
v_reusejp_5580_:
{
lean_object* v___x_5583_; 
if (v_isShared_5458_ == 0)
{
lean_ctor_set(v___x_5457_, 1, v___x_5581_);
lean_ctor_set(v___x_5457_, 0, v___x_5550_);
v___x_5583_ = v___x_5457_;
goto v_reusejp_5582_;
}
else
{
lean_object* v_reuseFailAlloc_5595_; 
v_reuseFailAlloc_5595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5595_, 0, v___x_5550_);
lean_ctor_set(v_reuseFailAlloc_5595_, 1, v___x_5581_);
v___x_5583_ = v_reuseFailAlloc_5595_;
goto v_reusejp_5582_;
}
v_reusejp_5582_:
{
lean_object* v___x_5585_; 
if (v_isShared_5454_ == 0)
{
lean_ctor_set(v___x_5453_, 1, v___x_5583_);
lean_ctor_set(v___x_5453_, 0, v___x_5578_);
v___x_5585_ = v___x_5453_;
goto v_reusejp_5584_;
}
else
{
lean_object* v_reuseFailAlloc_5594_; 
v_reuseFailAlloc_5594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5594_, 0, v___x_5578_);
lean_ctor_set(v_reuseFailAlloc_5594_, 1, v___x_5583_);
v___x_5585_ = v_reuseFailAlloc_5594_;
goto v_reusejp_5584_;
}
v_reusejp_5584_:
{
lean_object* v___x_5587_; 
if (v_isShared_5450_ == 0)
{
lean_ctor_set(v___x_5449_, 1, v___x_5585_);
v___x_5587_ = v___x_5449_;
goto v_reusejp_5586_;
}
else
{
lean_object* v_reuseFailAlloc_5593_; 
v_reuseFailAlloc_5593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5593_, 0, v_fst_5447_);
lean_ctor_set(v_reuseFailAlloc_5593_, 1, v___x_5585_);
v___x_5587_ = v_reuseFailAlloc_5593_;
goto v_reusejp_5586_;
}
v_reusejp_5586_:
{
lean_object* v___x_5589_; 
if (v_isShared_5446_ == 0)
{
lean_ctor_set(v___x_5445_, 1, v___x_5587_);
v___x_5589_ = v___x_5445_;
goto v_reusejp_5588_;
}
else
{
lean_object* v_reuseFailAlloc_5592_; 
v_reuseFailAlloc_5592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5592_, 0, v_fst_5443_);
lean_ctor_set(v_reuseFailAlloc_5592_, 1, v___x_5587_);
v___x_5589_ = v_reuseFailAlloc_5592_;
goto v_reusejp_5588_;
}
v_reusejp_5588_:
{
lean_object* v___x_5590_; lean_object* v___f_5591_; 
v___x_5590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5590_, 0, v___x_5589_);
v___f_5591_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5591_, 0, v___x_5590_);
v___y_5413_ = v___f_5591_;
goto v___jp_5412_;
}
}
}
}
}
}
else
{
lean_object* v___x_5598_; uint8_t v_isShared_5599_; uint8_t v_isSharedCheck_5615_; 
lean_inc(v_stop_5574_);
lean_inc(v_start_5573_);
lean_inc_ref(v_array_5572_);
lean_del_object(v___x_5461_);
lean_del_object(v___x_5457_);
lean_del_object(v___x_5453_);
lean_del_object(v___x_5449_);
lean_del_object(v___x_5445_);
v_isSharedCheck_5615_ = !lean_is_exclusive(v_fst_5447_);
if (v_isSharedCheck_5615_ == 0)
{
lean_object* v_unused_5616_; lean_object* v_unused_5617_; lean_object* v_unused_5618_; 
v_unused_5616_ = lean_ctor_get(v_fst_5447_, 2);
lean_dec(v_unused_5616_);
v_unused_5617_ = lean_ctor_get(v_fst_5447_, 1);
lean_dec(v_unused_5617_);
v_unused_5618_ = lean_ctor_get(v_fst_5447_, 0);
lean_dec(v_unused_5618_);
v___x_5598_ = v_fst_5447_;
v_isShared_5599_ = v_isSharedCheck_5615_;
goto v_resetjp_5597_;
}
else
{
lean_dec(v_fst_5447_);
v___x_5598_ = lean_box(0);
v_isShared_5599_ = v_isSharedCheck_5615_;
goto v_resetjp_5597_;
}
v_resetjp_5597_:
{
lean_object* v_numOverlaps_5600_; lean_object* v___x_5601_; uint8_t v___x_5602_; 
v_numOverlaps_5600_ = lean_ctor_get(v___x_5575_, 1);
v___x_5601_ = lean_unsigned_to_nat(0u);
v___x_5602_ = lean_nat_dec_eq(v_numOverlaps_5600_, v___x_5601_);
if (v___x_5602_ == 0)
{
lean_object* v___x_5603_; lean_object* v___x_5604_; 
lean_del_object(v___x_5598_);
lean_dec_ref(v___x_5578_);
lean_dec(v___x_5575_);
lean_dec(v_stop_5574_);
lean_dec(v_start_5573_);
lean_dec_ref(v_array_5572_);
lean_dec_ref(v___x_5550_);
lean_dec(v___x_5547_);
lean_dec_ref(v___x_5522_);
lean_dec(v___x_5519_);
lean_dec_ref(v___x_5494_);
lean_dec(v___x_5490_);
lean_dec(v_fst_5443_);
v___x_5603_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__48___closed__1);
v___x_5604_ = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___boxed), 6, 1);
lean_closure_set(v___x_5604_, 0, v___x_5603_);
v___y_5413_ = v___x_5604_;
goto v___jp_5412_;
}
else
{
uint8_t v___x_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; lean_object* v___x_5608_; lean_object* v___f_5609_; lean_object* v___x_5610_; lean_object* v___x_5612_; 
v___x_5605_ = 0;
v___x_5606_ = lean_array_fget_borrowed(v_array_5572_, v_start_5573_);
v___x_5607_ = lean_box(v___x_5605_);
v___x_5608_ = lean_box(v_useSplitter_5402_);
lean_inc(v_numDiscrEqs_5404_);
lean_inc(v_extraEqualities_5403_);
lean_inc(v___x_5606_);
lean_inc(v_a_5405_);
lean_inc_ref(v_onAlt_5401_);
lean_inc(v___x_5575_);
v___f_5609_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed), 18, 11);
lean_closure_set(v___f_5609_, 0, v___x_5547_);
lean_closure_set(v___f_5609_, 1, v___x_5490_);
lean_closure_set(v___f_5609_, 2, v___x_5575_);
lean_closure_set(v___f_5609_, 3, v_onAlt_5401_);
lean_closure_set(v___f_5609_, 4, v_a_5405_);
lean_closure_set(v___f_5609_, 5, v___x_5607_);
lean_closure_set(v___f_5609_, 6, v___x_5608_);
lean_closure_set(v___f_5609_, 7, v___x_5606_);
lean_closure_set(v___f_5609_, 8, v_extraEqualities_5403_);
lean_closure_set(v___f_5609_, 9, v_numDiscrEqs_5404_);
lean_closure_set(v___f_5609_, 10, v___x_5491_);
v___x_5610_ = lean_nat_add(v_start_5573_, v___x_5491_);
lean_dec(v_start_5573_);
if (v_isShared_5599_ == 0)
{
lean_ctor_set(v___x_5598_, 1, v___x_5610_);
v___x_5612_ = v___x_5598_;
goto v_reusejp_5611_;
}
else
{
lean_object* v_reuseFailAlloc_5614_; 
v_reuseFailAlloc_5614_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5614_, 0, v_array_5572_);
lean_ctor_set(v_reuseFailAlloc_5614_, 1, v___x_5610_);
lean_ctor_set(v_reuseFailAlloc_5614_, 2, v_stop_5574_);
v___x_5612_ = v_reuseFailAlloc_5614_;
goto v_reusejp_5611_;
}
v_reusejp_5611_:
{
lean_object* v___f_5613_; 
v___f_5613_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed), 14, 9);
lean_closure_set(v___f_5613_, 0, v___x_5519_);
lean_closure_set(v___f_5613_, 1, v___x_5575_);
lean_closure_set(v___f_5613_, 2, v___f_5609_);
lean_closure_set(v___f_5613_, 3, v_fst_5443_);
lean_closure_set(v___f_5613_, 4, v___x_5522_);
lean_closure_set(v___f_5613_, 5, v___x_5494_);
lean_closure_set(v___f_5613_, 6, v___x_5550_);
lean_closure_set(v___f_5613_, 7, v___x_5578_);
lean_closure_set(v___f_5613_, 8, v___x_5612_);
v___y_5413_ = v___f_5613_;
goto v___jp_5412_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_5412_:
{
lean_object* v___x_5414_; 
lean_inc(v___y_5410_);
lean_inc_ref(v___y_5409_);
lean_inc(v___y_5408_);
lean_inc_ref(v___y_5407_);
v___x_5414_ = lean_apply_5(v___y_5413_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_, lean_box(0));
if (lean_obj_tag(v___x_5414_) == 0)
{
lean_object* v_a_5415_; lean_object* v___x_5417_; uint8_t v_isShared_5418_; uint8_t v_isSharedCheck_5427_; 
v_a_5415_ = lean_ctor_get(v___x_5414_, 0);
v_isSharedCheck_5427_ = !lean_is_exclusive(v___x_5414_);
if (v_isSharedCheck_5427_ == 0)
{
v___x_5417_ = v___x_5414_;
v_isShared_5418_ = v_isSharedCheck_5427_;
goto v_resetjp_5416_;
}
else
{
lean_inc(v_a_5415_);
lean_dec(v___x_5414_);
v___x_5417_ = lean_box(0);
v_isShared_5418_ = v_isSharedCheck_5427_;
goto v_resetjp_5416_;
}
v_resetjp_5416_:
{
if (lean_obj_tag(v_a_5415_) == 0)
{
lean_object* v_a_5419_; lean_object* v___x_5421_; 
lean_dec(v_a_5405_);
lean_dec(v_numDiscrEqs_5404_);
lean_dec(v_extraEqualities_5403_);
lean_dec_ref(v_onAlt_5401_);
v_a_5419_ = lean_ctor_get(v_a_5415_, 0);
lean_inc(v_a_5419_);
lean_dec_ref_known(v_a_5415_, 1);
if (v_isShared_5418_ == 0)
{
lean_ctor_set(v___x_5417_, 0, v_a_5419_);
v___x_5421_ = v___x_5417_;
goto v_reusejp_5420_;
}
else
{
lean_object* v_reuseFailAlloc_5422_; 
v_reuseFailAlloc_5422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5422_, 0, v_a_5419_);
v___x_5421_ = v_reuseFailAlloc_5422_;
goto v_reusejp_5420_;
}
v_reusejp_5420_:
{
return v___x_5421_;
}
}
else
{
lean_object* v_a_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; 
lean_del_object(v___x_5417_);
v_a_5423_ = lean_ctor_get(v_a_5415_, 0);
lean_inc(v_a_5423_);
lean_dec_ref_known(v_a_5415_, 1);
v___x_5424_ = lean_unsigned_to_nat(1u);
v___x_5425_ = lean_nat_add(v_a_5405_, v___x_5424_);
lean_dec(v_a_5405_);
v_a_5405_ = v___x_5425_;
v_b_5406_ = v_a_5423_;
goto _start;
}
}
}
else
{
lean_object* v_a_5428_; lean_object* v___x_5430_; uint8_t v_isShared_5431_; uint8_t v_isSharedCheck_5435_; 
lean_dec(v_a_5405_);
lean_dec(v_numDiscrEqs_5404_);
lean_dec(v_extraEqualities_5403_);
lean_dec_ref(v_onAlt_5401_);
v_a_5428_ = lean_ctor_get(v___x_5414_, 0);
v_isSharedCheck_5435_ = !lean_is_exclusive(v___x_5414_);
if (v_isSharedCheck_5435_ == 0)
{
v___x_5430_ = v___x_5414_;
v_isShared_5431_ = v_isSharedCheck_5435_;
goto v_resetjp_5429_;
}
else
{
lean_inc(v_a_5428_);
lean_dec(v___x_5414_);
v___x_5430_ = lean_box(0);
v_isShared_5431_ = v_isSharedCheck_5435_;
goto v_resetjp_5429_;
}
v_resetjp_5429_:
{
lean_object* v___x_5433_; 
if (v_isShared_5431_ == 0)
{
v___x_5433_ = v___x_5430_;
goto v_reusejp_5432_;
}
else
{
lean_object* v_reuseFailAlloc_5434_; 
v_reuseFailAlloc_5434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5434_, 0, v_a_5428_);
v___x_5433_ = v_reuseFailAlloc_5434_;
goto v_reusejp_5432_;
}
v_reusejp_5432_:
{
return v___x_5433_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___boxed(lean_object* v_upperBound_5649_, lean_object* v_onAlt_5650_, lean_object* v_useSplitter_5651_, lean_object* v_extraEqualities_5652_, lean_object* v_numDiscrEqs_5653_, lean_object* v_a_5654_, lean_object* v_b_5655_, lean_object* v___y_5656_, lean_object* v___y_5657_, lean_object* v___y_5658_, lean_object* v___y_5659_, lean_object* v___y_5660_){
_start:
{
uint8_t v_useSplitter_boxed_5661_; lean_object* v_res_5662_; 
v_useSplitter_boxed_5661_ = lean_unbox(v_useSplitter_5651_);
v_res_5662_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v_upperBound_5649_, v_onAlt_5650_, v_useSplitter_boxed_5661_, v_extraEqualities_5652_, v_numDiscrEqs_5653_, v_a_5654_, v_b_5655_, v___y_5656_, v___y_5657_, v___y_5658_, v___y_5659_);
lean_dec(v___y_5659_);
lean_dec_ref(v___y_5658_);
lean_dec(v___y_5657_);
lean_dec_ref(v___y_5656_);
lean_dec(v_upperBound_5649_);
return v_res_5662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7___lam__0(lean_object* v_fst_5663_, lean_object* v_fst_5664_, lean_object* v_fst_5665_, lean_object* v___x_5666_, lean_object* v___x_5667_, lean_object* v___x_5668_, lean_object* v_heq_x3f_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_){
_start:
{
if (lean_obj_tag(v_heq_x3f_5669_) == 1)
{
lean_object* v_val_5675_; lean_object* v___x_5677_; uint8_t v_isShared_5678_; uint8_t v_isSharedCheck_5709_; 
lean_dec(v___x_5668_);
v_val_5675_ = lean_ctor_get(v_heq_x3f_5669_, 0);
v_isSharedCheck_5709_ = !lean_is_exclusive(v_heq_x3f_5669_);
if (v_isSharedCheck_5709_ == 0)
{
v___x_5677_ = v_heq_x3f_5669_;
v_isShared_5678_ = v_isSharedCheck_5709_;
goto v_resetjp_5676_;
}
else
{
lean_inc(v_val_5675_);
lean_dec(v_heq_x3f_5669_);
v___x_5677_ = lean_box(0);
v_isShared_5678_ = v_isSharedCheck_5709_;
goto v_resetjp_5676_;
}
v_resetjp_5676_:
{
lean_object* v___x_5679_; 
lean_inc(v_val_5675_);
v___x_5679_ = l_Lean_mkArrow(v_val_5675_, v_fst_5663_, v___y_5672_, v___y_5673_);
if (lean_obj_tag(v___x_5679_) == 0)
{
lean_object* v_a_5680_; lean_object* v___x_5682_; uint8_t v_isShared_5683_; uint8_t v_isSharedCheck_5700_; 
v_a_5680_ = lean_ctor_get(v___x_5679_, 0);
v_isSharedCheck_5700_ = !lean_is_exclusive(v___x_5679_);
if (v_isSharedCheck_5700_ == 0)
{
v___x_5682_ = v___x_5679_;
v_isShared_5683_ = v_isSharedCheck_5700_;
goto v_resetjp_5681_;
}
else
{
lean_inc(v_a_5680_);
lean_dec(v___x_5679_);
v___x_5682_ = lean_box(0);
v_isShared_5683_ = v_isSharedCheck_5700_;
goto v_resetjp_5681_;
}
v_resetjp_5681_:
{
uint8_t v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5687_; 
v___x_5684_ = l_Lean_Expr_isHEq(v_val_5675_);
lean_dec(v_val_5675_);
v___x_5685_ = lean_box(v___x_5684_);
if (v_isShared_5678_ == 0)
{
lean_ctor_set(v___x_5677_, 0, v___x_5685_);
v___x_5687_ = v___x_5677_;
goto v_reusejp_5686_;
}
else
{
lean_object* v_reuseFailAlloc_5699_; 
v_reuseFailAlloc_5699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5699_, 0, v___x_5685_);
v___x_5687_ = v_reuseFailAlloc_5699_;
goto v_reusejp_5686_;
}
v_reusejp_5686_:
{
lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5697_; 
v___x_5688_ = lean_array_push(v_fst_5664_, v___x_5687_);
v___x_5689_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7___closed__0));
v___x_5690_ = lean_array_push(v_fst_5665_, v___x_5689_);
v___x_5691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5691_, 0, v___x_5666_);
lean_ctor_set(v___x_5691_, 1, v___x_5667_);
v___x_5692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5692_, 0, v___x_5690_);
lean_ctor_set(v___x_5692_, 1, v___x_5691_);
v___x_5693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5693_, 0, v___x_5688_);
lean_ctor_set(v___x_5693_, 1, v___x_5692_);
v___x_5694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5694_, 0, v_a_5680_);
lean_ctor_set(v___x_5694_, 1, v___x_5693_);
v___x_5695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5695_, 0, v___x_5694_);
if (v_isShared_5683_ == 0)
{
lean_ctor_set(v___x_5682_, 0, v___x_5695_);
v___x_5697_ = v___x_5682_;
goto v_reusejp_5696_;
}
else
{
lean_object* v_reuseFailAlloc_5698_; 
v_reuseFailAlloc_5698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5698_, 0, v___x_5695_);
v___x_5697_ = v_reuseFailAlloc_5698_;
goto v_reusejp_5696_;
}
v_reusejp_5696_:
{
return v___x_5697_;
}
}
}
}
else
{
lean_object* v_a_5701_; lean_object* v___x_5703_; uint8_t v_isShared_5704_; uint8_t v_isSharedCheck_5708_; 
lean_del_object(v___x_5677_);
lean_dec(v_val_5675_);
lean_dec_ref(v___x_5667_);
lean_dec_ref(v___x_5666_);
lean_dec(v_fst_5665_);
lean_dec(v_fst_5664_);
v_a_5701_ = lean_ctor_get(v___x_5679_, 0);
v_isSharedCheck_5708_ = !lean_is_exclusive(v___x_5679_);
if (v_isSharedCheck_5708_ == 0)
{
v___x_5703_ = v___x_5679_;
v_isShared_5704_ = v_isSharedCheck_5708_;
goto v_resetjp_5702_;
}
else
{
lean_inc(v_a_5701_);
lean_dec(v___x_5679_);
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
}
else
{
lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; 
lean_dec(v_heq_x3f_5669_);
v___x_5710_ = lean_box(0);
v___x_5711_ = lean_array_push(v_fst_5664_, v___x_5710_);
v___x_5712_ = lean_array_push(v_fst_5665_, v___x_5668_);
v___x_5713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5713_, 0, v___x_5666_);
lean_ctor_set(v___x_5713_, 1, v___x_5667_);
v___x_5714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5714_, 0, v___x_5712_);
lean_ctor_set(v___x_5714_, 1, v___x_5713_);
v___x_5715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5715_, 0, v___x_5711_);
lean_ctor_set(v___x_5715_, 1, v___x_5714_);
v___x_5716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5716_, 0, v_fst_5663_);
lean_ctor_set(v___x_5716_, 1, v___x_5715_);
v___x_5717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5717_, 0, v___x_5716_);
v___x_5718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5718_, 0, v___x_5717_);
return v___x_5718_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7___lam__0___boxed(lean_object* v_fst_5719_, lean_object* v_fst_5720_, lean_object* v_fst_5721_, lean_object* v___x_5722_, lean_object* v___x_5723_, lean_object* v___x_5724_, lean_object* v_heq_x3f_5725_, lean_object* v___y_5726_, lean_object* v___y_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_, lean_object* v___y_5730_){
_start:
{
lean_object* v_res_5731_; 
v_res_5731_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7___lam__0(v_fst_5719_, v_fst_5720_, v_fst_5721_, v___x_5722_, v___x_5723_, v___x_5724_, v_heq_x3f_5725_, v___y_5726_, v___y_5727_, v___y_5728_, v___y_5729_);
lean_dec(v___y_5729_);
lean_dec_ref(v___y_5728_);
lean_dec(v___y_5727_);
lean_dec_ref(v___y_5726_);
return v_res_5731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(uint8_t v_addEqualities_5732_, uint8_t v_addProofEqualities_5733_, lean_object* v_as_5734_, size_t v_sz_5735_, size_t v_i_5736_, lean_object* v_b_5737_, lean_object* v___y_5738_, lean_object* v___y_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_){
_start:
{
lean_object* v___y_5744_; uint8_t v___x_5766_; 
v___x_5766_ = lean_usize_dec_lt(v_i_5736_, v_sz_5735_);
if (v___x_5766_ == 0)
{
lean_object* v___x_5767_; 
v___x_5767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5767_, 0, v_b_5737_);
return v___x_5767_;
}
else
{
lean_object* v_snd_5768_; lean_object* v_snd_5769_; lean_object* v_snd_5770_; lean_object* v_snd_5771_; lean_object* v_fst_5772_; lean_object* v___x_5774_; uint8_t v_isShared_5775_; uint8_t v_isSharedCheck_5885_; 
v_snd_5768_ = lean_ctor_get(v_b_5737_, 1);
lean_inc(v_snd_5768_);
v_snd_5769_ = lean_ctor_get(v_snd_5768_, 1);
lean_inc(v_snd_5769_);
v_snd_5770_ = lean_ctor_get(v_snd_5769_, 1);
lean_inc(v_snd_5770_);
v_snd_5771_ = lean_ctor_get(v_snd_5770_, 1);
lean_inc(v_snd_5771_);
v_fst_5772_ = lean_ctor_get(v_b_5737_, 0);
v_isSharedCheck_5885_ = !lean_is_exclusive(v_b_5737_);
if (v_isSharedCheck_5885_ == 0)
{
lean_object* v_unused_5886_; 
v_unused_5886_ = lean_ctor_get(v_b_5737_, 1);
lean_dec(v_unused_5886_);
v___x_5774_ = v_b_5737_;
v_isShared_5775_ = v_isSharedCheck_5885_;
goto v_resetjp_5773_;
}
else
{
lean_inc(v_fst_5772_);
lean_dec(v_b_5737_);
v___x_5774_ = lean_box(0);
v_isShared_5775_ = v_isSharedCheck_5885_;
goto v_resetjp_5773_;
}
v_resetjp_5773_:
{
lean_object* v_fst_5776_; lean_object* v___x_5778_; uint8_t v_isShared_5779_; uint8_t v_isSharedCheck_5883_; 
v_fst_5776_ = lean_ctor_get(v_snd_5768_, 0);
v_isSharedCheck_5883_ = !lean_is_exclusive(v_snd_5768_);
if (v_isSharedCheck_5883_ == 0)
{
lean_object* v_unused_5884_; 
v_unused_5884_ = lean_ctor_get(v_snd_5768_, 1);
lean_dec(v_unused_5884_);
v___x_5778_ = v_snd_5768_;
v_isShared_5779_ = v_isSharedCheck_5883_;
goto v_resetjp_5777_;
}
else
{
lean_inc(v_fst_5776_);
lean_dec(v_snd_5768_);
v___x_5778_ = lean_box(0);
v_isShared_5779_ = v_isSharedCheck_5883_;
goto v_resetjp_5777_;
}
v_resetjp_5777_:
{
lean_object* v_fst_5780_; lean_object* v___x_5782_; uint8_t v_isShared_5783_; uint8_t v_isSharedCheck_5881_; 
v_fst_5780_ = lean_ctor_get(v_snd_5769_, 0);
v_isSharedCheck_5881_ = !lean_is_exclusive(v_snd_5769_);
if (v_isSharedCheck_5881_ == 0)
{
lean_object* v_unused_5882_; 
v_unused_5882_ = lean_ctor_get(v_snd_5769_, 1);
lean_dec(v_unused_5882_);
v___x_5782_ = v_snd_5769_;
v_isShared_5783_ = v_isSharedCheck_5881_;
goto v_resetjp_5781_;
}
else
{
lean_inc(v_fst_5780_);
lean_dec(v_snd_5769_);
v___x_5782_ = lean_box(0);
v_isShared_5783_ = v_isSharedCheck_5881_;
goto v_resetjp_5781_;
}
v_resetjp_5781_:
{
lean_object* v_fst_5784_; lean_object* v___x_5786_; uint8_t v_isShared_5787_; uint8_t v_isSharedCheck_5879_; 
v_fst_5784_ = lean_ctor_get(v_snd_5770_, 0);
v_isSharedCheck_5879_ = !lean_is_exclusive(v_snd_5770_);
if (v_isSharedCheck_5879_ == 0)
{
lean_object* v_unused_5880_; 
v_unused_5880_ = lean_ctor_get(v_snd_5770_, 1);
lean_dec(v_unused_5880_);
v___x_5786_ = v_snd_5770_;
v_isShared_5787_ = v_isSharedCheck_5879_;
goto v_resetjp_5785_;
}
else
{
lean_inc(v_fst_5784_);
lean_dec(v_snd_5770_);
v___x_5786_ = lean_box(0);
v_isShared_5787_ = v_isSharedCheck_5879_;
goto v_resetjp_5785_;
}
v_resetjp_5785_:
{
lean_object* v_array_5788_; lean_object* v_start_5789_; lean_object* v_stop_5790_; uint8_t v___x_5791_; 
v_array_5788_ = lean_ctor_get(v_snd_5771_, 0);
v_start_5789_ = lean_ctor_get(v_snd_5771_, 1);
v_stop_5790_ = lean_ctor_get(v_snd_5771_, 2);
v___x_5791_ = lean_nat_dec_lt(v_start_5789_, v_stop_5790_);
if (v___x_5791_ == 0)
{
lean_object* v___x_5793_; 
if (v_isShared_5787_ == 0)
{
v___x_5793_ = v___x_5786_;
goto v_reusejp_5792_;
}
else
{
lean_object* v_reuseFailAlloc_5804_; 
v_reuseFailAlloc_5804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5804_, 0, v_fst_5784_);
lean_ctor_set(v_reuseFailAlloc_5804_, 1, v_snd_5771_);
v___x_5793_ = v_reuseFailAlloc_5804_;
goto v_reusejp_5792_;
}
v_reusejp_5792_:
{
lean_object* v___x_5795_; 
if (v_isShared_5783_ == 0)
{
lean_ctor_set(v___x_5782_, 1, v___x_5793_);
v___x_5795_ = v___x_5782_;
goto v_reusejp_5794_;
}
else
{
lean_object* v_reuseFailAlloc_5803_; 
v_reuseFailAlloc_5803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5803_, 0, v_fst_5780_);
lean_ctor_set(v_reuseFailAlloc_5803_, 1, v___x_5793_);
v___x_5795_ = v_reuseFailAlloc_5803_;
goto v_reusejp_5794_;
}
v_reusejp_5794_:
{
lean_object* v___x_5797_; 
if (v_isShared_5779_ == 0)
{
lean_ctor_set(v___x_5778_, 1, v___x_5795_);
v___x_5797_ = v___x_5778_;
goto v_reusejp_5796_;
}
else
{
lean_object* v_reuseFailAlloc_5802_; 
v_reuseFailAlloc_5802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5802_, 0, v_fst_5776_);
lean_ctor_set(v_reuseFailAlloc_5802_, 1, v___x_5795_);
v___x_5797_ = v_reuseFailAlloc_5802_;
goto v_reusejp_5796_;
}
v_reusejp_5796_:
{
lean_object* v___x_5799_; 
if (v_isShared_5775_ == 0)
{
lean_ctor_set(v___x_5774_, 1, v___x_5797_);
v___x_5799_ = v___x_5774_;
goto v_reusejp_5798_;
}
else
{
lean_object* v_reuseFailAlloc_5801_; 
v_reuseFailAlloc_5801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5801_, 0, v_fst_5772_);
lean_ctor_set(v_reuseFailAlloc_5801_, 1, v___x_5797_);
v___x_5799_ = v_reuseFailAlloc_5801_;
goto v_reusejp_5798_;
}
v_reusejp_5798_:
{
lean_object* v___x_5800_; 
v___x_5800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5800_, 0, v___x_5799_);
return v___x_5800_;
}
}
}
}
}
else
{
lean_object* v___x_5806_; uint8_t v_isShared_5807_; uint8_t v_isSharedCheck_5875_; 
lean_inc(v_stop_5790_);
lean_inc(v_start_5789_);
lean_inc_ref(v_array_5788_);
v_isSharedCheck_5875_ = !lean_is_exclusive(v_snd_5771_);
if (v_isSharedCheck_5875_ == 0)
{
lean_object* v_unused_5876_; lean_object* v_unused_5877_; lean_object* v_unused_5878_; 
v_unused_5876_ = lean_ctor_get(v_snd_5771_, 2);
lean_dec(v_unused_5876_);
v_unused_5877_ = lean_ctor_get(v_snd_5771_, 1);
lean_dec(v_unused_5877_);
v_unused_5878_ = lean_ctor_get(v_snd_5771_, 0);
lean_dec(v_unused_5878_);
v___x_5806_ = v_snd_5771_;
v_isShared_5807_ = v_isSharedCheck_5875_;
goto v_resetjp_5805_;
}
else
{
lean_dec(v_snd_5771_);
v___x_5806_ = lean_box(0);
v_isShared_5807_ = v_isSharedCheck_5875_;
goto v_resetjp_5805_;
}
v_resetjp_5805_:
{
lean_object* v_array_5808_; lean_object* v_start_5809_; lean_object* v_stop_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; lean_object* v___x_5813_; lean_object* v___x_5815_; 
v_array_5808_ = lean_ctor_get(v_fst_5784_, 0);
v_start_5809_ = lean_ctor_get(v_fst_5784_, 1);
v_stop_5810_ = lean_ctor_get(v_fst_5784_, 2);
v___x_5811_ = lean_array_fget(v_array_5788_, v_start_5789_);
v___x_5812_ = lean_unsigned_to_nat(1u);
v___x_5813_ = lean_nat_add(v_start_5789_, v___x_5812_);
lean_dec(v_start_5789_);
if (v_isShared_5807_ == 0)
{
lean_ctor_set(v___x_5806_, 1, v___x_5813_);
v___x_5815_ = v___x_5806_;
goto v_reusejp_5814_;
}
else
{
lean_object* v_reuseFailAlloc_5874_; 
v_reuseFailAlloc_5874_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5874_, 0, v_array_5788_);
lean_ctor_set(v_reuseFailAlloc_5874_, 1, v___x_5813_);
lean_ctor_set(v_reuseFailAlloc_5874_, 2, v_stop_5790_);
v___x_5815_ = v_reuseFailAlloc_5874_;
goto v_reusejp_5814_;
}
v_reusejp_5814_:
{
uint8_t v___x_5816_; 
v___x_5816_ = lean_nat_dec_lt(v_start_5809_, v_stop_5810_);
if (v___x_5816_ == 0)
{
lean_object* v___x_5818_; 
lean_dec(v___x_5811_);
if (v_isShared_5787_ == 0)
{
lean_ctor_set(v___x_5786_, 1, v___x_5815_);
v___x_5818_ = v___x_5786_;
goto v_reusejp_5817_;
}
else
{
lean_object* v_reuseFailAlloc_5829_; 
v_reuseFailAlloc_5829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5829_, 0, v_fst_5784_);
lean_ctor_set(v_reuseFailAlloc_5829_, 1, v___x_5815_);
v___x_5818_ = v_reuseFailAlloc_5829_;
goto v_reusejp_5817_;
}
v_reusejp_5817_:
{
lean_object* v___x_5820_; 
if (v_isShared_5783_ == 0)
{
lean_ctor_set(v___x_5782_, 1, v___x_5818_);
v___x_5820_ = v___x_5782_;
goto v_reusejp_5819_;
}
else
{
lean_object* v_reuseFailAlloc_5828_; 
v_reuseFailAlloc_5828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5828_, 0, v_fst_5780_);
lean_ctor_set(v_reuseFailAlloc_5828_, 1, v___x_5818_);
v___x_5820_ = v_reuseFailAlloc_5828_;
goto v_reusejp_5819_;
}
v_reusejp_5819_:
{
lean_object* v___x_5822_; 
if (v_isShared_5779_ == 0)
{
lean_ctor_set(v___x_5778_, 1, v___x_5820_);
v___x_5822_ = v___x_5778_;
goto v_reusejp_5821_;
}
else
{
lean_object* v_reuseFailAlloc_5827_; 
v_reuseFailAlloc_5827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5827_, 0, v_fst_5776_);
lean_ctor_set(v_reuseFailAlloc_5827_, 1, v___x_5820_);
v___x_5822_ = v_reuseFailAlloc_5827_;
goto v_reusejp_5821_;
}
v_reusejp_5821_:
{
lean_object* v___x_5824_; 
if (v_isShared_5775_ == 0)
{
lean_ctor_set(v___x_5774_, 1, v___x_5822_);
v___x_5824_ = v___x_5774_;
goto v_reusejp_5823_;
}
else
{
lean_object* v_reuseFailAlloc_5826_; 
v_reuseFailAlloc_5826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5826_, 0, v_fst_5772_);
lean_ctor_set(v_reuseFailAlloc_5826_, 1, v___x_5822_);
v___x_5824_ = v_reuseFailAlloc_5826_;
goto v_reusejp_5823_;
}
v_reusejp_5823_:
{
lean_object* v___x_5825_; 
v___x_5825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5825_, 0, v___x_5824_);
return v___x_5825_;
}
}
}
}
}
else
{
lean_object* v___x_5831_; uint8_t v_isShared_5832_; uint8_t v_isSharedCheck_5870_; 
lean_inc(v_stop_5810_);
lean_inc(v_start_5809_);
lean_inc_ref(v_array_5808_);
lean_del_object(v___x_5786_);
lean_del_object(v___x_5782_);
lean_del_object(v___x_5778_);
lean_del_object(v___x_5774_);
v_isSharedCheck_5870_ = !lean_is_exclusive(v_fst_5784_);
if (v_isSharedCheck_5870_ == 0)
{
lean_object* v_unused_5871_; lean_object* v_unused_5872_; lean_object* v_unused_5873_; 
v_unused_5871_ = lean_ctor_get(v_fst_5784_, 2);
lean_dec(v_unused_5871_);
v_unused_5872_ = lean_ctor_get(v_fst_5784_, 1);
lean_dec(v_unused_5872_);
v_unused_5873_ = lean_ctor_get(v_fst_5784_, 0);
lean_dec(v_unused_5873_);
v___x_5831_ = v_fst_5784_;
v_isShared_5832_ = v_isSharedCheck_5870_;
goto v_resetjp_5830_;
}
else
{
lean_dec(v_fst_5784_);
v___x_5831_ = lean_box(0);
v_isShared_5832_ = v_isSharedCheck_5870_;
goto v_resetjp_5830_;
}
v_resetjp_5830_:
{
lean_object* v___x_5833_; lean_object* v___x_5834_; lean_object* v___x_5836_; 
v___x_5833_ = lean_array_fget(v_array_5808_, v_start_5809_);
v___x_5834_ = lean_nat_add(v_start_5809_, v___x_5812_);
lean_dec(v_start_5809_);
if (v_isShared_5832_ == 0)
{
lean_ctor_set(v___x_5831_, 1, v___x_5834_);
v___x_5836_ = v___x_5831_;
goto v_reusejp_5835_;
}
else
{
lean_object* v_reuseFailAlloc_5869_; 
v_reuseFailAlloc_5869_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5869_, 0, v_array_5808_);
lean_ctor_set(v_reuseFailAlloc_5869_, 1, v___x_5834_);
lean_ctor_set(v_reuseFailAlloc_5869_, 2, v_stop_5810_);
v___x_5836_ = v_reuseFailAlloc_5869_;
goto v_reusejp_5835_;
}
v_reusejp_5835_:
{
if (v_addEqualities_5732_ == 0)
{
lean_dec(v___x_5833_);
goto v___jp_5837_;
}
else
{
if (lean_obj_tag(v___x_5811_) == 0)
{
lean_object* v_a_5840_; lean_object* v___x_5841_; 
v_a_5840_ = lean_array_uget_borrowed(v_as_5734_, v_i_5736_);
lean_inc(v_a_5840_);
v___x_5841_ = l_Lean_Meta_mkEqHEq(v___x_5833_, v_a_5840_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_);
if (lean_obj_tag(v___x_5841_) == 0)
{
lean_object* v_a_5842_; lean_object* v___x_5843_; 
v_a_5842_ = lean_ctor_get(v___x_5841_, 0);
lean_inc(v_a_5842_);
lean_dec_ref_known(v___x_5841_, 1);
lean_inc(v_a_5840_);
v___x_5843_ = l_Lean_Meta_isProof(v_a_5840_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_);
if (lean_obj_tag(v___x_5843_) == 0)
{
lean_object* v_a_5844_; uint8_t v___x_5851_; 
v_a_5844_ = lean_ctor_get(v___x_5843_, 0);
lean_inc(v_a_5844_);
lean_dec_ref_known(v___x_5843_, 1);
v___x_5851_ = lean_unbox(v_a_5844_);
lean_dec(v_a_5844_);
if (v___x_5851_ == 0)
{
goto v___jp_5848_;
}
else
{
if (v_addProofEqualities_5733_ == 0)
{
lean_dec(v_a_5842_);
goto v___jp_5845_;
}
else
{
uint8_t v___x_5852_; 
v___x_5852_ = l_Lean_Expr_isHEq(v_a_5842_);
if (v___x_5852_ == 0)
{
goto v___jp_5848_;
}
else
{
lean_dec(v_a_5842_);
goto v___jp_5845_;
}
}
}
v___jp_5845_:
{
lean_object* v___x_5846_; lean_object* v___x_5847_; 
v___x_5846_ = lean_box(0);
v___x_5847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7___lam__0(v_fst_5772_, v_fst_5776_, v_fst_5780_, v___x_5836_, v___x_5815_, v___x_5811_, v___x_5846_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_);
v___y_5744_ = v___x_5847_;
goto v___jp_5743_;
}
v___jp_5848_:
{
lean_object* v___x_5849_; lean_object* v___x_5850_; 
v___x_5849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5849_, 0, v_a_5842_);
v___x_5850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7___lam__0(v_fst_5772_, v_fst_5776_, v_fst_5780_, v___x_5836_, v___x_5815_, v___x_5811_, v___x_5849_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_);
v___y_5744_ = v___x_5850_;
goto v___jp_5743_;
}
}
else
{
lean_object* v_a_5853_; lean_object* v___x_5855_; uint8_t v_isShared_5856_; uint8_t v_isSharedCheck_5860_; 
lean_dec(v_a_5842_);
lean_dec_ref(v___x_5836_);
lean_dec_ref(v___x_5815_);
lean_dec(v_fst_5780_);
lean_dec(v_fst_5776_);
lean_dec(v_fst_5772_);
v_a_5853_ = lean_ctor_get(v___x_5843_, 0);
v_isSharedCheck_5860_ = !lean_is_exclusive(v___x_5843_);
if (v_isSharedCheck_5860_ == 0)
{
v___x_5855_ = v___x_5843_;
v_isShared_5856_ = v_isSharedCheck_5860_;
goto v_resetjp_5854_;
}
else
{
lean_inc(v_a_5853_);
lean_dec(v___x_5843_);
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
lean_dec_ref(v___x_5836_);
lean_dec_ref(v___x_5815_);
lean_dec(v_fst_5780_);
lean_dec(v_fst_5776_);
lean_dec(v_fst_5772_);
v_a_5861_ = lean_ctor_get(v___x_5841_, 0);
v_isSharedCheck_5868_ = !lean_is_exclusive(v___x_5841_);
if (v_isSharedCheck_5868_ == 0)
{
v___x_5863_ = v___x_5841_;
v_isShared_5864_ = v_isSharedCheck_5868_;
goto v_resetjp_5862_;
}
else
{
lean_inc(v_a_5861_);
lean_dec(v___x_5841_);
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
else
{
lean_dec(v___x_5833_);
goto v___jp_5837_;
}
}
v___jp_5837_:
{
lean_object* v___x_5838_; lean_object* v___x_5839_; 
v___x_5838_ = lean_box(0);
v___x_5839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7___lam__0(v_fst_5772_, v_fst_5776_, v_fst_5780_, v___x_5836_, v___x_5815_, v___x_5811_, v___x_5838_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_);
v___y_5744_ = v___x_5839_;
goto v___jp_5743_;
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_5743_:
{
if (lean_obj_tag(v___y_5744_) == 0)
{
lean_object* v_a_5745_; lean_object* v___x_5747_; uint8_t v_isShared_5748_; uint8_t v_isSharedCheck_5757_; 
v_a_5745_ = lean_ctor_get(v___y_5744_, 0);
v_isSharedCheck_5757_ = !lean_is_exclusive(v___y_5744_);
if (v_isSharedCheck_5757_ == 0)
{
v___x_5747_ = v___y_5744_;
v_isShared_5748_ = v_isSharedCheck_5757_;
goto v_resetjp_5746_;
}
else
{
lean_inc(v_a_5745_);
lean_dec(v___y_5744_);
v___x_5747_ = lean_box(0);
v_isShared_5748_ = v_isSharedCheck_5757_;
goto v_resetjp_5746_;
}
v_resetjp_5746_:
{
if (lean_obj_tag(v_a_5745_) == 0)
{
lean_object* v_a_5749_; lean_object* v___x_5751_; 
v_a_5749_ = lean_ctor_get(v_a_5745_, 0);
lean_inc(v_a_5749_);
lean_dec_ref_known(v_a_5745_, 1);
if (v_isShared_5748_ == 0)
{
lean_ctor_set(v___x_5747_, 0, v_a_5749_);
v___x_5751_ = v___x_5747_;
goto v_reusejp_5750_;
}
else
{
lean_object* v_reuseFailAlloc_5752_; 
v_reuseFailAlloc_5752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5752_, 0, v_a_5749_);
v___x_5751_ = v_reuseFailAlloc_5752_;
goto v_reusejp_5750_;
}
v_reusejp_5750_:
{
return v___x_5751_;
}
}
else
{
lean_object* v_a_5753_; size_t v___x_5754_; size_t v___x_5755_; 
lean_del_object(v___x_5747_);
v_a_5753_ = lean_ctor_get(v_a_5745_, 0);
lean_inc(v_a_5753_);
lean_dec_ref_known(v_a_5745_, 1);
v___x_5754_ = ((size_t)1ULL);
v___x_5755_ = lean_usize_add(v_i_5736_, v___x_5754_);
v_i_5736_ = v___x_5755_;
v_b_5737_ = v_a_5753_;
goto _start;
}
}
}
else
{
lean_object* v_a_5758_; lean_object* v___x_5760_; uint8_t v_isShared_5761_; uint8_t v_isSharedCheck_5765_; 
v_a_5758_ = lean_ctor_get(v___y_5744_, 0);
v_isSharedCheck_5765_ = !lean_is_exclusive(v___y_5744_);
if (v_isSharedCheck_5765_ == 0)
{
v___x_5760_ = v___y_5744_;
v_isShared_5761_ = v_isSharedCheck_5765_;
goto v_resetjp_5759_;
}
else
{
lean_inc(v_a_5758_);
lean_dec(v___y_5744_);
v___x_5760_ = lean_box(0);
v_isShared_5761_ = v_isSharedCheck_5765_;
goto v_resetjp_5759_;
}
v_resetjp_5759_:
{
lean_object* v___x_5763_; 
if (v_isShared_5761_ == 0)
{
v___x_5763_ = v___x_5760_;
goto v_reusejp_5762_;
}
else
{
lean_object* v_reuseFailAlloc_5764_; 
v_reuseFailAlloc_5764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5764_, 0, v_a_5758_);
v___x_5763_ = v_reuseFailAlloc_5764_;
goto v_reusejp_5762_;
}
v_reusejp_5762_:
{
return v___x_5763_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7___boxed(lean_object* v_addEqualities_5887_, lean_object* v_addProofEqualities_5888_, lean_object* v_as_5889_, lean_object* v_sz_5890_, lean_object* v_i_5891_, lean_object* v_b_5892_, lean_object* v___y_5893_, lean_object* v___y_5894_, lean_object* v___y_5895_, lean_object* v___y_5896_, lean_object* v___y_5897_){
_start:
{
uint8_t v_addEqualities_boxed_5898_; uint8_t v_addProofEqualities_boxed_5899_; size_t v_sz_boxed_5900_; size_t v_i_boxed_5901_; lean_object* v_res_5902_; 
v_addEqualities_boxed_5898_ = lean_unbox(v_addEqualities_5887_);
v_addProofEqualities_boxed_5899_ = lean_unbox(v_addProofEqualities_5888_);
v_sz_boxed_5900_ = lean_unbox_usize(v_sz_5890_);
lean_dec(v_sz_5890_);
v_i_boxed_5901_ = lean_unbox_usize(v_i_5891_);
lean_dec(v_i_5891_);
v_res_5902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(v_addEqualities_boxed_5898_, v_addProofEqualities_boxed_5899_, v_as_5889_, v_sz_boxed_5900_, v_i_boxed_5901_, v_b_5892_, v___y_5893_, v___y_5894_, v___y_5895_, v___y_5896_);
lean_dec(v___y_5896_);
lean_dec_ref(v___y_5895_);
lean_dec(v___y_5894_);
lean_dec_ref(v___y_5893_);
lean_dec_ref(v_as_5889_);
return v_res_5902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(lean_object* v_onMotive_5903_, lean_object* v_toMatcherInfo_5904_, lean_object* v_a_5905_, uint8_t v_addEqualities_5906_, uint8_t v_addProofEqualities_5907_, size_t v___x_5908_, lean_object* v_discrs_5909_, lean_object* v_motiveArgs_5910_, lean_object* v_motiveBody_5911_, lean_object* v___y_5912_, lean_object* v___y_5913_, lean_object* v___y_5914_, lean_object* v___y_5915_){
_start:
{
lean_object* v___x_6009_; lean_object* v___x_6010_; uint8_t v___x_6011_; 
v___x_6009_ = lean_array_get_size(v_motiveArgs_5910_);
v___x_6010_ = lean_array_get_size(v_discrs_5909_);
v___x_6011_ = lean_nat_dec_eq(v___x_6009_, v___x_6010_);
if (v___x_6011_ == 0)
{
lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v_a_6020_; lean_object* v___x_6022_; uint8_t v_isShared_6023_; uint8_t v_isSharedCheck_6027_; 
lean_dec_ref(v_motiveBody_5911_);
lean_dec_ref(v_motiveArgs_5910_);
lean_dec_ref(v_a_5905_);
lean_dec_ref(v_toMatcherInfo_5904_);
lean_dec_ref(v_onMotive_5903_);
v___x_6012_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_6013_ = l_Nat_reprFast(v___x_6010_);
v___x_6014_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_6014_, 0, v___x_6013_);
v___x_6015_ = l_Lean_MessageData_ofFormat(v___x_6014_);
v___x_6016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6016_, 0, v___x_6012_);
lean_ctor_set(v___x_6016_, 1, v___x_6015_);
v___x_6017_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_6018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6018_, 0, v___x_6016_);
lean_ctor_set(v___x_6018_, 1, v___x_6017_);
v___x_6019_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_6018_, v___y_5912_, v___y_5913_, v___y_5914_, v___y_5915_);
v_a_6020_ = lean_ctor_get(v___x_6019_, 0);
v_isSharedCheck_6027_ = !lean_is_exclusive(v___x_6019_);
if (v_isSharedCheck_6027_ == 0)
{
v___x_6022_ = v___x_6019_;
v_isShared_6023_ = v_isSharedCheck_6027_;
goto v_resetjp_6021_;
}
else
{
lean_inc(v_a_6020_);
lean_dec(v___x_6019_);
v___x_6022_ = lean_box(0);
v_isShared_6023_ = v_isSharedCheck_6027_;
goto v_resetjp_6021_;
}
v_resetjp_6021_:
{
lean_object* v___x_6025_; 
if (v_isShared_6023_ == 0)
{
v___x_6025_ = v___x_6022_;
goto v_reusejp_6024_;
}
else
{
lean_object* v_reuseFailAlloc_6026_; 
v_reuseFailAlloc_6026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6026_, 0, v_a_6020_);
v___x_6025_ = v_reuseFailAlloc_6026_;
goto v_reusejp_6024_;
}
v_reusejp_6024_:
{
return v___x_6025_;
}
}
}
else
{
goto v___jp_5917_;
}
v___jp_5917_:
{
lean_object* v___x_5918_; 
lean_inc(v___y_5915_);
lean_inc_ref(v___y_5914_);
lean_inc(v___y_5913_);
lean_inc_ref(v___y_5912_);
lean_inc_ref(v_motiveArgs_5910_);
v___x_5918_ = lean_apply_7(v_onMotive_5903_, v_motiveArgs_5910_, v_motiveBody_5911_, v___y_5912_, v___y_5913_, v___y_5914_, v___y_5915_, lean_box(0));
if (lean_obj_tag(v___x_5918_) == 0)
{
lean_object* v_a_5919_; lean_object* v_discrInfos_5920_; lean_object* v___x_5921_; lean_object* v_addHEqualities_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; size_t v_sz_5931_; lean_object* v___x_5932_; 
v_a_5919_ = lean_ctor_get(v___x_5918_, 0);
lean_inc(v_a_5919_);
lean_dec_ref_known(v___x_5918_, 1);
v_discrInfos_5920_ = lean_ctor_get(v_toMatcherInfo_5904_, 4);
lean_inc_ref(v_discrInfos_5920_);
lean_dec_ref(v_toMatcherInfo_5904_);
v___x_5921_ = lean_unsigned_to_nat(0u);
v_addHEqualities_5922_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__18___closed__0));
v___x_5923_ = lean_array_get_size(v_a_5905_);
v___x_5924_ = l_Array_toSubarray___redArg(v_a_5905_, v___x_5921_, v___x_5923_);
v___x_5925_ = lean_array_get_size(v_discrInfos_5920_);
v___x_5926_ = l_Array_toSubarray___redArg(v_discrInfos_5920_, v___x_5921_, v___x_5925_);
v___x_5927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5927_, 0, v___x_5924_);
lean_ctor_set(v___x_5927_, 1, v___x_5926_);
v___x_5928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5928_, 0, v_addHEqualities_5922_);
lean_ctor_set(v___x_5928_, 1, v___x_5927_);
v___x_5929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5929_, 0, v_addHEqualities_5922_);
lean_ctor_set(v___x_5929_, 1, v___x_5928_);
v___x_5930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5930_, 0, v_a_5919_);
lean_ctor_set(v___x_5930_, 1, v___x_5929_);
v_sz_5931_ = lean_array_size(v_motiveArgs_5910_);
v___x_5932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(v_addEqualities_5906_, v_addProofEqualities_5907_, v_motiveArgs_5910_, v_sz_5931_, v___x_5908_, v___x_5930_, v___y_5912_, v___y_5913_, v___y_5914_, v___y_5915_);
if (lean_obj_tag(v___x_5932_) == 0)
{
lean_object* v_a_5933_; lean_object* v_snd_5934_; lean_object* v_snd_5935_; lean_object* v_fst_5936_; lean_object* v___x_5938_; uint8_t v_isShared_5939_; uint8_t v_isSharedCheck_5991_; 
v_a_5933_ = lean_ctor_get(v___x_5932_, 0);
lean_inc(v_a_5933_);
lean_dec_ref_known(v___x_5932_, 1);
v_snd_5934_ = lean_ctor_get(v_a_5933_, 1);
lean_inc(v_snd_5934_);
v_snd_5935_ = lean_ctor_get(v_snd_5934_, 1);
lean_inc(v_snd_5935_);
v_fst_5936_ = lean_ctor_get(v_a_5933_, 0);
v_isSharedCheck_5991_ = !lean_is_exclusive(v_a_5933_);
if (v_isSharedCheck_5991_ == 0)
{
lean_object* v_unused_5992_; 
v_unused_5992_ = lean_ctor_get(v_a_5933_, 1);
lean_dec(v_unused_5992_);
v___x_5938_ = v_a_5933_;
v_isShared_5939_ = v_isSharedCheck_5991_;
goto v_resetjp_5937_;
}
else
{
lean_inc(v_fst_5936_);
lean_dec(v_a_5933_);
v___x_5938_ = lean_box(0);
v_isShared_5939_ = v_isSharedCheck_5991_;
goto v_resetjp_5937_;
}
v_resetjp_5937_:
{
lean_object* v_fst_5940_; lean_object* v___x_5942_; uint8_t v_isShared_5943_; uint8_t v_isSharedCheck_5989_; 
v_fst_5940_ = lean_ctor_get(v_snd_5934_, 0);
v_isSharedCheck_5989_ = !lean_is_exclusive(v_snd_5934_);
if (v_isSharedCheck_5989_ == 0)
{
lean_object* v_unused_5990_; 
v_unused_5990_ = lean_ctor_get(v_snd_5934_, 1);
lean_dec(v_unused_5990_);
v___x_5942_ = v_snd_5934_;
v_isShared_5943_ = v_isSharedCheck_5989_;
goto v_resetjp_5941_;
}
else
{
lean_inc(v_fst_5940_);
lean_dec(v_snd_5934_);
v___x_5942_ = lean_box(0);
v_isShared_5943_ = v_isSharedCheck_5989_;
goto v_resetjp_5941_;
}
v_resetjp_5941_:
{
lean_object* v_fst_5944_; lean_object* v___x_5946_; uint8_t v_isShared_5947_; uint8_t v_isSharedCheck_5987_; 
v_fst_5944_ = lean_ctor_get(v_snd_5935_, 0);
v_isSharedCheck_5987_ = !lean_is_exclusive(v_snd_5935_);
if (v_isSharedCheck_5987_ == 0)
{
lean_object* v_unused_5988_; 
v_unused_5988_ = lean_ctor_get(v_snd_5935_, 1);
lean_dec(v_unused_5988_);
v___x_5946_ = v_snd_5935_;
v_isShared_5947_ = v_isSharedCheck_5987_;
goto v_resetjp_5945_;
}
else
{
lean_inc(v_fst_5944_);
lean_dec(v_snd_5935_);
v___x_5946_ = lean_box(0);
v_isShared_5947_ = v_isSharedCheck_5987_;
goto v_resetjp_5945_;
}
v_resetjp_5945_:
{
uint8_t v___x_5948_; uint8_t v___x_5949_; uint8_t v___x_5950_; lean_object* v___x_5951_; 
v___x_5948_ = 0;
v___x_5949_ = 1;
v___x_5950_ = 1;
lean_inc(v_fst_5936_);
v___x_5951_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_5910_, v_fst_5936_, v___x_5948_, v___x_5949_, v___x_5948_, v___x_5949_, v___x_5950_, v___y_5912_, v___y_5913_, v___y_5914_, v___y_5915_);
lean_dec_ref(v_motiveArgs_5910_);
if (lean_obj_tag(v___x_5951_) == 0)
{
lean_object* v_a_5952_; lean_object* v___x_5953_; 
v_a_5952_ = lean_ctor_get(v___x_5951_, 0);
lean_inc(v_a_5952_);
lean_dec_ref_known(v___x_5951_, 1);
v___x_5953_ = l_Lean_Meta_getLevel(v_fst_5936_, v___y_5912_, v___y_5913_, v___y_5914_, v___y_5915_);
if (lean_obj_tag(v___x_5953_) == 0)
{
lean_object* v_a_5954_; lean_object* v___x_5956_; uint8_t v_isShared_5957_; uint8_t v_isSharedCheck_5970_; 
v_a_5954_ = lean_ctor_get(v___x_5953_, 0);
v_isSharedCheck_5970_ = !lean_is_exclusive(v___x_5953_);
if (v_isSharedCheck_5970_ == 0)
{
v___x_5956_ = v___x_5953_;
v_isShared_5957_ = v_isSharedCheck_5970_;
goto v_resetjp_5955_;
}
else
{
lean_inc(v_a_5954_);
lean_dec(v___x_5953_);
v___x_5956_ = lean_box(0);
v_isShared_5957_ = v_isSharedCheck_5970_;
goto v_resetjp_5955_;
}
v_resetjp_5955_:
{
lean_object* v___x_5959_; 
if (v_isShared_5947_ == 0)
{
lean_ctor_set(v___x_5946_, 1, v_fst_5944_);
lean_ctor_set(v___x_5946_, 0, v_fst_5940_);
v___x_5959_ = v___x_5946_;
goto v_reusejp_5958_;
}
else
{
lean_object* v_reuseFailAlloc_5969_; 
v_reuseFailAlloc_5969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5969_, 0, v_fst_5940_);
lean_ctor_set(v_reuseFailAlloc_5969_, 1, v_fst_5944_);
v___x_5959_ = v_reuseFailAlloc_5969_;
goto v_reusejp_5958_;
}
v_reusejp_5958_:
{
lean_object* v___x_5961_; 
if (v_isShared_5943_ == 0)
{
lean_ctor_set(v___x_5942_, 1, v___x_5959_);
lean_ctor_set(v___x_5942_, 0, v_a_5954_);
v___x_5961_ = v___x_5942_;
goto v_reusejp_5960_;
}
else
{
lean_object* v_reuseFailAlloc_5968_; 
v_reuseFailAlloc_5968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5968_, 0, v_a_5954_);
lean_ctor_set(v_reuseFailAlloc_5968_, 1, v___x_5959_);
v___x_5961_ = v_reuseFailAlloc_5968_;
goto v_reusejp_5960_;
}
v_reusejp_5960_:
{
lean_object* v___x_5963_; 
if (v_isShared_5939_ == 0)
{
lean_ctor_set(v___x_5938_, 1, v___x_5961_);
lean_ctor_set(v___x_5938_, 0, v_a_5952_);
v___x_5963_ = v___x_5938_;
goto v_reusejp_5962_;
}
else
{
lean_object* v_reuseFailAlloc_5967_; 
v_reuseFailAlloc_5967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5967_, 0, v_a_5952_);
lean_ctor_set(v_reuseFailAlloc_5967_, 1, v___x_5961_);
v___x_5963_ = v_reuseFailAlloc_5967_;
goto v_reusejp_5962_;
}
v_reusejp_5962_:
{
lean_object* v___x_5965_; 
if (v_isShared_5957_ == 0)
{
lean_ctor_set(v___x_5956_, 0, v___x_5963_);
v___x_5965_ = v___x_5956_;
goto v_reusejp_5964_;
}
else
{
lean_object* v_reuseFailAlloc_5966_; 
v_reuseFailAlloc_5966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5966_, 0, v___x_5963_);
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
else
{
lean_object* v_a_5971_; lean_object* v___x_5973_; uint8_t v_isShared_5974_; uint8_t v_isSharedCheck_5978_; 
lean_dec(v_a_5952_);
lean_del_object(v___x_5946_);
lean_dec(v_fst_5944_);
lean_del_object(v___x_5942_);
lean_dec(v_fst_5940_);
lean_del_object(v___x_5938_);
v_a_5971_ = lean_ctor_get(v___x_5953_, 0);
v_isSharedCheck_5978_ = !lean_is_exclusive(v___x_5953_);
if (v_isSharedCheck_5978_ == 0)
{
v___x_5973_ = v___x_5953_;
v_isShared_5974_ = v_isSharedCheck_5978_;
goto v_resetjp_5972_;
}
else
{
lean_inc(v_a_5971_);
lean_dec(v___x_5953_);
v___x_5973_ = lean_box(0);
v_isShared_5974_ = v_isSharedCheck_5978_;
goto v_resetjp_5972_;
}
v_resetjp_5972_:
{
lean_object* v___x_5976_; 
if (v_isShared_5974_ == 0)
{
v___x_5976_ = v___x_5973_;
goto v_reusejp_5975_;
}
else
{
lean_object* v_reuseFailAlloc_5977_; 
v_reuseFailAlloc_5977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5977_, 0, v_a_5971_);
v___x_5976_ = v_reuseFailAlloc_5977_;
goto v_reusejp_5975_;
}
v_reusejp_5975_:
{
return v___x_5976_;
}
}
}
}
else
{
lean_object* v_a_5979_; lean_object* v___x_5981_; uint8_t v_isShared_5982_; uint8_t v_isSharedCheck_5986_; 
lean_del_object(v___x_5946_);
lean_dec(v_fst_5944_);
lean_del_object(v___x_5942_);
lean_dec(v_fst_5940_);
lean_del_object(v___x_5938_);
lean_dec(v_fst_5936_);
v_a_5979_ = lean_ctor_get(v___x_5951_, 0);
v_isSharedCheck_5986_ = !lean_is_exclusive(v___x_5951_);
if (v_isSharedCheck_5986_ == 0)
{
v___x_5981_ = v___x_5951_;
v_isShared_5982_ = v_isSharedCheck_5986_;
goto v_resetjp_5980_;
}
else
{
lean_inc(v_a_5979_);
lean_dec(v___x_5951_);
v___x_5981_ = lean_box(0);
v_isShared_5982_ = v_isSharedCheck_5986_;
goto v_resetjp_5980_;
}
v_resetjp_5980_:
{
lean_object* v___x_5984_; 
if (v_isShared_5982_ == 0)
{
v___x_5984_ = v___x_5981_;
goto v_reusejp_5983_;
}
else
{
lean_object* v_reuseFailAlloc_5985_; 
v_reuseFailAlloc_5985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5985_, 0, v_a_5979_);
v___x_5984_ = v_reuseFailAlloc_5985_;
goto v_reusejp_5983_;
}
v_reusejp_5983_:
{
return v___x_5984_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5993_; lean_object* v___x_5995_; uint8_t v_isShared_5996_; uint8_t v_isSharedCheck_6000_; 
lean_dec_ref(v_motiveArgs_5910_);
v_a_5993_ = lean_ctor_get(v___x_5932_, 0);
v_isSharedCheck_6000_ = !lean_is_exclusive(v___x_5932_);
if (v_isSharedCheck_6000_ == 0)
{
v___x_5995_ = v___x_5932_;
v_isShared_5996_ = v_isSharedCheck_6000_;
goto v_resetjp_5994_;
}
else
{
lean_inc(v_a_5993_);
lean_dec(v___x_5932_);
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
else
{
lean_object* v_a_6001_; lean_object* v___x_6003_; uint8_t v_isShared_6004_; uint8_t v_isSharedCheck_6008_; 
lean_dec_ref(v_motiveArgs_5910_);
lean_dec_ref(v_a_5905_);
lean_dec_ref(v_toMatcherInfo_5904_);
v_a_6001_ = lean_ctor_get(v___x_5918_, 0);
v_isSharedCheck_6008_ = !lean_is_exclusive(v___x_5918_);
if (v_isSharedCheck_6008_ == 0)
{
v___x_6003_ = v___x_5918_;
v_isShared_6004_ = v_isSharedCheck_6008_;
goto v_resetjp_6002_;
}
else
{
lean_inc(v_a_6001_);
lean_dec(v___x_5918_);
v___x_6003_ = lean_box(0);
v_isShared_6004_ = v_isSharedCheck_6008_;
goto v_resetjp_6002_;
}
v_resetjp_6002_:
{
lean_object* v___x_6006_; 
if (v_isShared_6004_ == 0)
{
v___x_6006_ = v___x_6003_;
goto v_reusejp_6005_;
}
else
{
lean_object* v_reuseFailAlloc_6007_; 
v_reuseFailAlloc_6007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6007_, 0, v_a_6001_);
v___x_6006_ = v_reuseFailAlloc_6007_;
goto v_reusejp_6005_;
}
v_reusejp_6005_:
{
return v___x_6006_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed(lean_object* v_onMotive_6028_, lean_object* v_toMatcherInfo_6029_, lean_object* v_a_6030_, lean_object* v_addEqualities_6031_, lean_object* v_addProofEqualities_6032_, lean_object* v___x_6033_, lean_object* v_discrs_6034_, lean_object* v_motiveArgs_6035_, lean_object* v_motiveBody_6036_, lean_object* v___y_6037_, lean_object* v___y_6038_, lean_object* v___y_6039_, lean_object* v___y_6040_, lean_object* v___y_6041_){
_start:
{
uint8_t v_addEqualities_boxed_6042_; uint8_t v_addProofEqualities_boxed_6043_; size_t v___x_34702__boxed_6044_; lean_object* v_res_6045_; 
v_addEqualities_boxed_6042_ = lean_unbox(v_addEqualities_6031_);
v_addProofEqualities_boxed_6043_ = lean_unbox(v_addProofEqualities_6032_);
v___x_34702__boxed_6044_ = lean_unbox_usize(v___x_6033_);
lean_dec(v___x_6033_);
v_res_6045_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(v_onMotive_6028_, v_toMatcherInfo_6029_, v_a_6030_, v_addEqualities_boxed_6042_, v_addProofEqualities_boxed_6043_, v___x_34702__boxed_6044_, v_discrs_6034_, v_motiveArgs_6035_, v_motiveBody_6036_, v___y_6037_, v___y_6038_, v___y_6039_, v___y_6040_);
lean_dec(v___y_6040_);
lean_dec_ref(v___y_6039_);
lean_dec(v___y_6038_);
lean_dec_ref(v___y_6037_);
lean_dec_ref(v_discrs_6034_);
return v_res_6045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(lean_object* v_as_6046_, size_t v_sz_6047_, size_t v_i_6048_, lean_object* v_b_6049_, lean_object* v___y_6050_, lean_object* v___y_6051_, lean_object* v___y_6052_, lean_object* v___y_6053_){
_start:
{
lean_object* v_a_6056_; uint8_t v___x_6060_; 
v___x_6060_ = lean_usize_dec_lt(v_i_6048_, v_sz_6047_);
if (v___x_6060_ == 0)
{
lean_object* v___x_6061_; 
v___x_6061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6061_, 0, v_b_6049_);
return v___x_6061_;
}
else
{
lean_object* v_snd_6062_; lean_object* v_snd_6063_; lean_object* v_fst_6064_; lean_object* v___x_6066_; uint8_t v_isShared_6067_; uint8_t v_isSharedCheck_6124_; 
v_snd_6062_ = lean_ctor_get(v_b_6049_, 1);
lean_inc(v_snd_6062_);
v_snd_6063_ = lean_ctor_get(v_snd_6062_, 1);
lean_inc(v_snd_6063_);
v_fst_6064_ = lean_ctor_get(v_b_6049_, 0);
v_isSharedCheck_6124_ = !lean_is_exclusive(v_b_6049_);
if (v_isSharedCheck_6124_ == 0)
{
lean_object* v_unused_6125_; 
v_unused_6125_ = lean_ctor_get(v_b_6049_, 1);
lean_dec(v_unused_6125_);
v___x_6066_ = v_b_6049_;
v_isShared_6067_ = v_isSharedCheck_6124_;
goto v_resetjp_6065_;
}
else
{
lean_inc(v_fst_6064_);
lean_dec(v_b_6049_);
v___x_6066_ = lean_box(0);
v_isShared_6067_ = v_isSharedCheck_6124_;
goto v_resetjp_6065_;
}
v_resetjp_6065_:
{
lean_object* v_fst_6068_; lean_object* v___x_6070_; uint8_t v_isShared_6071_; uint8_t v_isSharedCheck_6122_; 
v_fst_6068_ = lean_ctor_get(v_snd_6062_, 0);
v_isSharedCheck_6122_ = !lean_is_exclusive(v_snd_6062_);
if (v_isSharedCheck_6122_ == 0)
{
lean_object* v_unused_6123_; 
v_unused_6123_ = lean_ctor_get(v_snd_6062_, 1);
lean_dec(v_unused_6123_);
v___x_6070_ = v_snd_6062_;
v_isShared_6071_ = v_isSharedCheck_6122_;
goto v_resetjp_6069_;
}
else
{
lean_inc(v_fst_6068_);
lean_dec(v_snd_6062_);
v___x_6070_ = lean_box(0);
v_isShared_6071_ = v_isSharedCheck_6122_;
goto v_resetjp_6069_;
}
v_resetjp_6069_:
{
lean_object* v_array_6072_; lean_object* v_start_6073_; lean_object* v_stop_6074_; uint8_t v___x_6075_; 
v_array_6072_ = lean_ctor_get(v_snd_6063_, 0);
v_start_6073_ = lean_ctor_get(v_snd_6063_, 1);
v_stop_6074_ = lean_ctor_get(v_snd_6063_, 2);
v___x_6075_ = lean_nat_dec_lt(v_start_6073_, v_stop_6074_);
if (v___x_6075_ == 0)
{
lean_object* v___x_6077_; 
if (v_isShared_6071_ == 0)
{
v___x_6077_ = v___x_6070_;
goto v_reusejp_6076_;
}
else
{
lean_object* v_reuseFailAlloc_6082_; 
v_reuseFailAlloc_6082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6082_, 0, v_fst_6068_);
lean_ctor_set(v_reuseFailAlloc_6082_, 1, v_snd_6063_);
v___x_6077_ = v_reuseFailAlloc_6082_;
goto v_reusejp_6076_;
}
v_reusejp_6076_:
{
lean_object* v___x_6079_; 
if (v_isShared_6067_ == 0)
{
lean_ctor_set(v___x_6066_, 1, v___x_6077_);
v___x_6079_ = v___x_6066_;
goto v_reusejp_6078_;
}
else
{
lean_object* v_reuseFailAlloc_6081_; 
v_reuseFailAlloc_6081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6081_, 0, v_fst_6064_);
lean_ctor_set(v_reuseFailAlloc_6081_, 1, v___x_6077_);
v___x_6079_ = v_reuseFailAlloc_6081_;
goto v_reusejp_6078_;
}
v_reusejp_6078_:
{
lean_object* v___x_6080_; 
v___x_6080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6080_, 0, v___x_6079_);
return v___x_6080_;
}
}
}
else
{
lean_object* v___x_6084_; uint8_t v_isShared_6085_; uint8_t v_isSharedCheck_6118_; 
lean_inc(v_stop_6074_);
lean_inc(v_start_6073_);
lean_inc_ref(v_array_6072_);
v_isSharedCheck_6118_ = !lean_is_exclusive(v_snd_6063_);
if (v_isSharedCheck_6118_ == 0)
{
lean_object* v_unused_6119_; lean_object* v_unused_6120_; lean_object* v_unused_6121_; 
v_unused_6119_ = lean_ctor_get(v_snd_6063_, 2);
lean_dec(v_unused_6119_);
v_unused_6120_ = lean_ctor_get(v_snd_6063_, 1);
lean_dec(v_unused_6120_);
v_unused_6121_ = lean_ctor_get(v_snd_6063_, 0);
lean_dec(v_unused_6121_);
v___x_6084_ = v_snd_6063_;
v_isShared_6085_ = v_isSharedCheck_6118_;
goto v_resetjp_6083_;
}
else
{
lean_dec(v_snd_6063_);
v___x_6084_ = lean_box(0);
v_isShared_6085_ = v_isSharedCheck_6118_;
goto v_resetjp_6083_;
}
v_resetjp_6083_:
{
lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6090_; 
v___x_6086_ = lean_array_fget(v_array_6072_, v_start_6073_);
v___x_6087_ = lean_unsigned_to_nat(1u);
v___x_6088_ = lean_nat_add(v_start_6073_, v___x_6087_);
lean_dec(v_start_6073_);
if (v_isShared_6085_ == 0)
{
lean_ctor_set(v___x_6084_, 1, v___x_6088_);
v___x_6090_ = v___x_6084_;
goto v_reusejp_6089_;
}
else
{
lean_object* v_reuseFailAlloc_6117_; 
v_reuseFailAlloc_6117_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6117_, 0, v_array_6072_);
lean_ctor_set(v_reuseFailAlloc_6117_, 1, v___x_6088_);
lean_ctor_set(v_reuseFailAlloc_6117_, 2, v_stop_6074_);
v___x_6090_ = v_reuseFailAlloc_6117_;
goto v_reusejp_6089_;
}
v_reusejp_6089_:
{
lean_object* v___y_6092_; 
if (lean_obj_tag(v___x_6086_) == 0)
{
lean_object* v___x_6110_; lean_object* v___x_6111_; 
lean_del_object(v___x_6070_);
lean_del_object(v___x_6066_);
v___x_6110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6110_, 0, v_fst_6068_);
lean_ctor_set(v___x_6110_, 1, v___x_6090_);
v___x_6111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6111_, 0, v_fst_6064_);
lean_ctor_set(v___x_6111_, 1, v___x_6110_);
v_a_6056_ = v___x_6111_;
goto v___jp_6055_;
}
else
{
lean_object* v_val_6112_; lean_object* v_a_6113_; uint8_t v___x_6114_; 
v_val_6112_ = lean_ctor_get(v___x_6086_, 0);
lean_inc(v_val_6112_);
lean_dec_ref_known(v___x_6086_, 1);
v_a_6113_ = lean_array_uget_borrowed(v_as_6046_, v_i_6048_);
v___x_6114_ = lean_unbox(v_val_6112_);
lean_dec(v_val_6112_);
if (v___x_6114_ == 0)
{
lean_object* v___x_6115_; 
lean_inc(v_a_6113_);
v___x_6115_ = l_Lean_Meta_mkEqRefl(v_a_6113_, v___y_6050_, v___y_6051_, v___y_6052_, v___y_6053_);
v___y_6092_ = v___x_6115_;
goto v___jp_6091_;
}
else
{
lean_object* v___x_6116_; 
lean_inc(v_a_6113_);
v___x_6116_ = l_Lean_Meta_mkHEqRefl(v_a_6113_, v___y_6050_, v___y_6051_, v___y_6052_, v___y_6053_);
v___y_6092_ = v___x_6116_;
goto v___jp_6091_;
}
}
v___jp_6091_:
{
if (lean_obj_tag(v___y_6092_) == 0)
{
lean_object* v_a_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6097_; 
v_a_6093_ = lean_ctor_get(v___y_6092_, 0);
lean_inc(v_a_6093_);
lean_dec_ref_known(v___y_6092_, 1);
v___x_6094_ = lean_array_push(v_fst_6064_, v_a_6093_);
v___x_6095_ = lean_nat_add(v_fst_6068_, v___x_6087_);
lean_dec(v_fst_6068_);
if (v_isShared_6071_ == 0)
{
lean_ctor_set(v___x_6070_, 1, v___x_6090_);
lean_ctor_set(v___x_6070_, 0, v___x_6095_);
v___x_6097_ = v___x_6070_;
goto v_reusejp_6096_;
}
else
{
lean_object* v_reuseFailAlloc_6101_; 
v_reuseFailAlloc_6101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6101_, 0, v___x_6095_);
lean_ctor_set(v_reuseFailAlloc_6101_, 1, v___x_6090_);
v___x_6097_ = v_reuseFailAlloc_6101_;
goto v_reusejp_6096_;
}
v_reusejp_6096_:
{
lean_object* v___x_6099_; 
if (v_isShared_6067_ == 0)
{
lean_ctor_set(v___x_6066_, 1, v___x_6097_);
lean_ctor_set(v___x_6066_, 0, v___x_6094_);
v___x_6099_ = v___x_6066_;
goto v_reusejp_6098_;
}
else
{
lean_object* v_reuseFailAlloc_6100_; 
v_reuseFailAlloc_6100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6100_, 0, v___x_6094_);
lean_ctor_set(v_reuseFailAlloc_6100_, 1, v___x_6097_);
v___x_6099_ = v_reuseFailAlloc_6100_;
goto v_reusejp_6098_;
}
v_reusejp_6098_:
{
v_a_6056_ = v___x_6099_;
goto v___jp_6055_;
}
}
}
else
{
lean_object* v_a_6102_; lean_object* v___x_6104_; uint8_t v_isShared_6105_; uint8_t v_isSharedCheck_6109_; 
lean_dec_ref(v___x_6090_);
lean_del_object(v___x_6070_);
lean_dec(v_fst_6068_);
lean_del_object(v___x_6066_);
lean_dec(v_fst_6064_);
v_a_6102_ = lean_ctor_get(v___y_6092_, 0);
v_isSharedCheck_6109_ = !lean_is_exclusive(v___y_6092_);
if (v_isSharedCheck_6109_ == 0)
{
v___x_6104_ = v___y_6092_;
v_isShared_6105_ = v_isSharedCheck_6109_;
goto v_resetjp_6103_;
}
else
{
lean_inc(v_a_6102_);
lean_dec(v___y_6092_);
v___x_6104_ = lean_box(0);
v_isShared_6105_ = v_isSharedCheck_6109_;
goto v_resetjp_6103_;
}
v_resetjp_6103_:
{
lean_object* v___x_6107_; 
if (v_isShared_6105_ == 0)
{
v___x_6107_ = v___x_6104_;
goto v_reusejp_6106_;
}
else
{
lean_object* v_reuseFailAlloc_6108_; 
v_reuseFailAlloc_6108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6108_, 0, v_a_6102_);
v___x_6107_ = v_reuseFailAlloc_6108_;
goto v_reusejp_6106_;
}
v_reusejp_6106_:
{
return v___x_6107_;
}
}
}
}
}
}
}
}
}
}
v___jp_6055_:
{
size_t v___x_6057_; size_t v___x_6058_; 
v___x_6057_ = ((size_t)1ULL);
v___x_6058_ = lean_usize_add(v_i_6048_, v___x_6057_);
v_i_6048_ = v___x_6058_;
v_b_6049_ = v_a_6056_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8___boxed(lean_object* v_as_6126_, lean_object* v_sz_6127_, lean_object* v_i_6128_, lean_object* v_b_6129_, lean_object* v___y_6130_, lean_object* v___y_6131_, lean_object* v___y_6132_, lean_object* v___y_6133_, lean_object* v___y_6134_){
_start:
{
size_t v_sz_boxed_6135_; size_t v_i_boxed_6136_; lean_object* v_res_6137_; 
v_sz_boxed_6135_ = lean_unbox_usize(v_sz_6127_);
lean_dec(v_sz_6127_);
v_i_boxed_6136_ = lean_unbox_usize(v_i_6128_);
lean_dec(v_i_6128_);
v_res_6137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(v_as_6126_, v_sz_boxed_6135_, v_i_boxed_6136_, v_b_6129_, v___y_6130_, v___y_6131_, v___y_6132_, v___y_6133_);
lean_dec(v___y_6133_);
lean_dec_ref(v___y_6132_);
lean_dec(v___y_6131_);
lean_dec_ref(v___y_6130_);
lean_dec_ref(v_as_6126_);
return v_res_6137_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(lean_object* v___x_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_, lean_object* v___y_6141_, lean_object* v___y_6142_){
_start:
{
lean_object* v___x_6144_; 
v___x_6144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6144_, 0, v___x_6138_);
return v___x_6144_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed(lean_object* v___x_6145_, lean_object* v___y_6146_, lean_object* v___y_6147_, lean_object* v___y_6148_, lean_object* v___y_6149_, lean_object* v___y_6150_){
_start:
{
lean_object* v_res_6151_; 
v_res_6151_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(v___x_6145_, v___y_6146_, v___y_6147_, v___y_6148_, v___y_6149_);
lean_dec(v___y_6149_);
lean_dec_ref(v___y_6148_);
lean_dec(v___y_6147_);
lean_dec_ref(v___y_6146_);
return v_res_6151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(size_t v_sz_6152_, size_t v_i_6153_, lean_object* v_bs_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_, lean_object* v___y_6157_){
_start:
{
uint8_t v___x_6159_; 
v___x_6159_ = lean_usize_dec_lt(v_i_6153_, v_sz_6152_);
if (v___x_6159_ == 0)
{
lean_object* v___x_6160_; 
v___x_6160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6160_, 0, v_bs_6154_);
return v___x_6160_;
}
else
{
lean_object* v_v_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; 
v_v_6161_ = lean_array_uget_borrowed(v_bs_6154_, v_i_6153_);
v___x_6162_ = l_Lean_Expr_fvarId_x21(v_v_6161_);
v___x_6163_ = l_Lean_FVarId_getUserName___redArg(v___x_6162_, v___y_6155_, v___y_6156_, v___y_6157_);
if (lean_obj_tag(v___x_6163_) == 0)
{
lean_object* v_a_6164_; lean_object* v___x_6165_; lean_object* v_bs_x27_6166_; size_t v___x_6167_; size_t v___x_6168_; lean_object* v___x_6169_; 
v_a_6164_ = lean_ctor_get(v___x_6163_, 0);
lean_inc(v_a_6164_);
lean_dec_ref_known(v___x_6163_, 1);
v___x_6165_ = lean_unsigned_to_nat(0u);
v_bs_x27_6166_ = lean_array_uset(v_bs_6154_, v_i_6153_, v___x_6165_);
v___x_6167_ = ((size_t)1ULL);
v___x_6168_ = lean_usize_add(v_i_6153_, v___x_6167_);
v___x_6169_ = lean_array_uset(v_bs_x27_6166_, v_i_6153_, v_a_6164_);
v_i_6153_ = v___x_6168_;
v_bs_6154_ = v___x_6169_;
goto _start;
}
else
{
lean_object* v_a_6171_; lean_object* v___x_6173_; uint8_t v_isShared_6174_; uint8_t v_isSharedCheck_6178_; 
lean_dec_ref(v_bs_6154_);
v_a_6171_ = lean_ctor_get(v___x_6163_, 0);
v_isSharedCheck_6178_ = !lean_is_exclusive(v___x_6163_);
if (v_isSharedCheck_6178_ == 0)
{
v___x_6173_ = v___x_6163_;
v_isShared_6174_ = v_isSharedCheck_6178_;
goto v_resetjp_6172_;
}
else
{
lean_inc(v_a_6171_);
lean_dec(v___x_6163_);
v___x_6173_ = lean_box(0);
v_isShared_6174_ = v_isSharedCheck_6178_;
goto v_resetjp_6172_;
}
v_resetjp_6172_:
{
lean_object* v___x_6176_; 
if (v_isShared_6174_ == 0)
{
v___x_6176_ = v___x_6173_;
goto v_reusejp_6175_;
}
else
{
lean_object* v_reuseFailAlloc_6177_; 
v_reuseFailAlloc_6177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6177_, 0, v_a_6171_);
v___x_6176_ = v_reuseFailAlloc_6177_;
goto v_reusejp_6175_;
}
v_reusejp_6175_:
{
return v___x_6176_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg___boxed(lean_object* v_sz_6179_, lean_object* v_i_6180_, lean_object* v_bs_6181_, lean_object* v___y_6182_, lean_object* v___y_6183_, lean_object* v___y_6184_, lean_object* v___y_6185_){
_start:
{
size_t v_sz_boxed_6186_; size_t v_i_boxed_6187_; lean_object* v_res_6188_; 
v_sz_boxed_6186_ = lean_unbox_usize(v_sz_6179_);
lean_dec(v_sz_6179_);
v_i_boxed_6187_ = lean_unbox_usize(v_i_6180_);
lean_dec(v_i_6180_);
v_res_6188_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_boxed_6186_, v_i_boxed_6187_, v_bs_6181_, v___y_6182_, v___y_6183_, v___y_6184_);
lean_dec(v___y_6184_);
lean_dec_ref(v___y_6183_);
lean_dec_ref(v___y_6182_);
return v_res_6188_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(lean_object* v_xs_6189_, lean_object* v_x_6190_, lean_object* v___y_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_, lean_object* v___y_6194_){
_start:
{
size_t v_sz_6196_; size_t v___x_6197_; lean_object* v___x_6198_; 
v_sz_6196_ = lean_array_size(v_xs_6189_);
v___x_6197_ = ((size_t)0ULL);
v___x_6198_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_6196_, v___x_6197_, v_xs_6189_, v___y_6191_, v___y_6193_, v___y_6194_);
return v___x_6198_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3___boxed(lean_object* v_xs_6199_, lean_object* v_x_6200_, lean_object* v___y_6201_, lean_object* v___y_6202_, lean_object* v___y_6203_, lean_object* v___y_6204_, lean_object* v___y_6205_){
_start:
{
lean_object* v_res_6206_; 
v_res_6206_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(v_xs_6199_, v_x_6200_, v___y_6201_, v___y_6202_, v___y_6203_, v___y_6204_);
lean_dec(v___y_6204_);
lean_dec_ref(v___y_6203_);
lean_dec(v___y_6202_);
lean_dec_ref(v___y_6201_);
lean_dec_ref(v_x_6200_);
return v_res_6206_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(lean_object* v___x_6207_, lean_object* v___x_6208_, lean_object* v___f_6209_, uint8_t v___x_6210_, lean_object* v_fst_6211_, lean_object* v___x_6212_, lean_object* v___x_6213_, lean_object* v___x_6214_, lean_object* v___y_6215_, lean_object* v___y_6216_, lean_object* v___y_6217_, lean_object* v___y_6218_){
_start:
{
lean_object* v___x_6220_; 
v___x_6220_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v___x_6207_, v___x_6208_, v___f_6209_, v___x_6210_, v___x_6210_, v___y_6215_, v___y_6216_, v___y_6217_, v___y_6218_);
if (lean_obj_tag(v___x_6220_) == 0)
{
lean_object* v_a_6221_; lean_object* v___x_6223_; uint8_t v_isShared_6224_; uint8_t v_isSharedCheck_6233_; 
v_a_6221_ = lean_ctor_get(v___x_6220_, 0);
v_isSharedCheck_6233_ = !lean_is_exclusive(v___x_6220_);
if (v_isSharedCheck_6233_ == 0)
{
v___x_6223_ = v___x_6220_;
v_isShared_6224_ = v_isSharedCheck_6233_;
goto v_resetjp_6222_;
}
else
{
lean_inc(v_a_6221_);
lean_dec(v___x_6220_);
v___x_6223_ = lean_box(0);
v_isShared_6224_ = v_isSharedCheck_6233_;
goto v_resetjp_6222_;
}
v_resetjp_6222_:
{
lean_object* v___x_6225_; lean_object* v___x_6226_; lean_object* v___x_6227_; lean_object* v___x_6228_; lean_object* v___x_6229_; lean_object* v___x_6231_; 
v___x_6225_ = lean_array_push(v_fst_6211_, v_a_6221_);
v___x_6226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6226_, 0, v___x_6212_);
lean_ctor_set(v___x_6226_, 1, v___x_6213_);
v___x_6227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6227_, 0, v___x_6214_);
lean_ctor_set(v___x_6227_, 1, v___x_6226_);
v___x_6228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6228_, 0, v___x_6225_);
lean_ctor_set(v___x_6228_, 1, v___x_6227_);
v___x_6229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6229_, 0, v___x_6228_);
if (v_isShared_6224_ == 0)
{
lean_ctor_set(v___x_6223_, 0, v___x_6229_);
v___x_6231_ = v___x_6223_;
goto v_reusejp_6230_;
}
else
{
lean_object* v_reuseFailAlloc_6232_; 
v_reuseFailAlloc_6232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6232_, 0, v___x_6229_);
v___x_6231_ = v_reuseFailAlloc_6232_;
goto v_reusejp_6230_;
}
v_reusejp_6230_:
{
return v___x_6231_;
}
}
}
else
{
lean_object* v_a_6234_; lean_object* v___x_6236_; uint8_t v_isShared_6237_; uint8_t v_isSharedCheck_6241_; 
lean_dec_ref(v___x_6214_);
lean_dec_ref(v___x_6213_);
lean_dec_ref(v___x_6212_);
lean_dec(v_fst_6211_);
v_a_6234_ = lean_ctor_get(v___x_6220_, 0);
v_isSharedCheck_6241_ = !lean_is_exclusive(v___x_6220_);
if (v_isSharedCheck_6241_ == 0)
{
v___x_6236_ = v___x_6220_;
v_isShared_6237_ = v_isSharedCheck_6241_;
goto v_resetjp_6235_;
}
else
{
lean_inc(v_a_6234_);
lean_dec(v___x_6220_);
v___x_6236_ = lean_box(0);
v_isShared_6237_ = v_isSharedCheck_6241_;
goto v_resetjp_6235_;
}
v_resetjp_6235_:
{
lean_object* v___x_6239_; 
if (v_isShared_6237_ == 0)
{
v___x_6239_ = v___x_6236_;
goto v_reusejp_6238_;
}
else
{
lean_object* v_reuseFailAlloc_6240_; 
v_reuseFailAlloc_6240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6240_, 0, v_a_6234_);
v___x_6239_ = v_reuseFailAlloc_6240_;
goto v_reusejp_6238_;
}
v_reusejp_6238_:
{
return v___x_6239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed(lean_object* v___x_6242_, lean_object* v___x_6243_, lean_object* v___f_6244_, lean_object* v___x_6245_, lean_object* v_fst_6246_, lean_object* v___x_6247_, lean_object* v___x_6248_, lean_object* v___x_6249_, lean_object* v___y_6250_, lean_object* v___y_6251_, lean_object* v___y_6252_, lean_object* v___y_6253_, lean_object* v___y_6254_){
_start:
{
uint8_t v___x_35165__boxed_6255_; lean_object* v_res_6256_; 
v___x_35165__boxed_6255_ = lean_unbox(v___x_6245_);
v_res_6256_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(v___x_6242_, v___x_6243_, v___f_6244_, v___x_35165__boxed_6255_, v_fst_6246_, v___x_6247_, v___x_6248_, v___x_6249_, v___y_6250_, v___y_6251_, v___y_6252_, v___y_6253_);
lean_dec(v___y_6253_);
lean_dec_ref(v___y_6252_);
lean_dec(v___y_6251_);
lean_dec_ref(v___y_6250_);
return v_res_6256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(lean_object* v_fvars_6257_, lean_object* v_names_6258_, lean_object* v_k_6259_, lean_object* v___y_6260_, lean_object* v___y_6261_, lean_object* v___y_6262_, lean_object* v___y_6263_){
_start:
{
lean_object* v___x_6265_; 
v___x_6265_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_6257_, v_names_6258_, v_k_6259_, v___y_6260_, v___y_6261_, v___y_6262_, v___y_6263_);
if (lean_obj_tag(v___x_6265_) == 0)
{
lean_object* v_a_6266_; lean_object* v___x_6268_; uint8_t v_isShared_6269_; uint8_t v_isSharedCheck_6273_; 
v_a_6266_ = lean_ctor_get(v___x_6265_, 0);
v_isSharedCheck_6273_ = !lean_is_exclusive(v___x_6265_);
if (v_isSharedCheck_6273_ == 0)
{
v___x_6268_ = v___x_6265_;
v_isShared_6269_ = v_isSharedCheck_6273_;
goto v_resetjp_6267_;
}
else
{
lean_inc(v_a_6266_);
lean_dec(v___x_6265_);
v___x_6268_ = lean_box(0);
v_isShared_6269_ = v_isSharedCheck_6273_;
goto v_resetjp_6267_;
}
v_resetjp_6267_:
{
lean_object* v___x_6271_; 
if (v_isShared_6269_ == 0)
{
v___x_6271_ = v___x_6268_;
goto v_reusejp_6270_;
}
else
{
lean_object* v_reuseFailAlloc_6272_; 
v_reuseFailAlloc_6272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6272_, 0, v_a_6266_);
v___x_6271_ = v_reuseFailAlloc_6272_;
goto v_reusejp_6270_;
}
v_reusejp_6270_:
{
return v___x_6271_;
}
}
}
else
{
lean_object* v_a_6274_; lean_object* v___x_6276_; uint8_t v_isShared_6277_; uint8_t v_isSharedCheck_6281_; 
v_a_6274_ = lean_ctor_get(v___x_6265_, 0);
v_isSharedCheck_6281_ = !lean_is_exclusive(v___x_6265_);
if (v_isSharedCheck_6281_ == 0)
{
v___x_6276_ = v___x_6265_;
v_isShared_6277_ = v_isSharedCheck_6281_;
goto v_resetjp_6275_;
}
else
{
lean_inc(v_a_6274_);
lean_dec(v___x_6265_);
v___x_6276_ = lean_box(0);
v_isShared_6277_ = v_isSharedCheck_6281_;
goto v_resetjp_6275_;
}
v_resetjp_6275_:
{
lean_object* v___x_6279_; 
if (v_isShared_6277_ == 0)
{
v___x_6279_ = v___x_6276_;
goto v_reusejp_6278_;
}
else
{
lean_object* v_reuseFailAlloc_6280_; 
v_reuseFailAlloc_6280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6280_, 0, v_a_6274_);
v___x_6279_ = v_reuseFailAlloc_6280_;
goto v_reusejp_6278_;
}
v_reusejp_6278_:
{
return v___x_6279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg___boxed(lean_object* v_fvars_6282_, lean_object* v_names_6283_, lean_object* v_k_6284_, lean_object* v___y_6285_, lean_object* v___y_6286_, lean_object* v___y_6287_, lean_object* v___y_6288_, lean_object* v___y_6289_){
_start:
{
lean_object* v_res_6290_; 
v_res_6290_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_fvars_6282_, v_names_6283_, v_k_6284_, v___y_6285_, v___y_6286_, v___y_6287_, v___y_6288_);
lean_dec(v___y_6288_);
lean_dec_ref(v___y_6287_);
lean_dec(v___y_6286_);
lean_dec_ref(v___y_6285_);
lean_dec_ref(v_names_6283_);
lean_dec_ref(v_fvars_6282_);
return v_res_6290_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(lean_object* v___x_6291_, lean_object* v_xs_6292_, lean_object* v_remaining_x27_6293_, lean_object* v_ys4_6294_, lean_object* v_onAlt_6295_, lean_object* v_a_6296_, lean_object* v_altType_6297_, uint8_t v___x_6298_, uint8_t v___x_6299_, lean_object* v___y_6300_, lean_object* v___y_6301_, lean_object* v___y_6302_, lean_object* v___y_6303_){
_start:
{
lean_object* v___x_6305_; 
v___x_6305_ = l_Lean_Meta_instantiateLambda(v___x_6291_, v_xs_6292_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_);
if (lean_obj_tag(v___x_6305_) == 0)
{
lean_object* v_a_6306_; lean_object* v___x_6307_; lean_object* v___x_6308_; 
v_a_6306_ = lean_ctor_get(v___x_6305_, 0);
lean_inc(v_a_6306_);
lean_dec_ref_known(v___x_6305_, 1);
lean_inc_ref(v_ys4_6294_);
lean_inc_ref(v_remaining_x27_6293_);
lean_inc_ref_n(v_xs_6292_, 2);
v___x_6307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6307_, 0, v_xs_6292_);
lean_ctor_set(v___x_6307_, 1, v_xs_6292_);
lean_ctor_set(v___x_6307_, 2, v_remaining_x27_6293_);
lean_ctor_set(v___x_6307_, 3, v_remaining_x27_6293_);
lean_ctor_set(v___x_6307_, 4, v_ys4_6294_);
lean_inc(v___y_6303_);
lean_inc_ref(v___y_6302_);
lean_inc(v___y_6301_);
lean_inc_ref(v___y_6300_);
v___x_6308_ = lean_apply_9(v_onAlt_6295_, v_a_6296_, v_altType_6297_, v___x_6307_, v_a_6306_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, lean_box(0));
if (lean_obj_tag(v___x_6308_) == 0)
{
lean_object* v_a_6309_; lean_object* v___x_6310_; uint8_t v___x_6311_; lean_object* v___x_6312_; 
v_a_6309_ = lean_ctor_get(v___x_6308_, 0);
lean_inc(v_a_6309_);
lean_dec_ref_known(v___x_6308_, 1);
v___x_6310_ = l_Array_append___redArg(v_xs_6292_, v_ys4_6294_);
lean_dec_ref(v_ys4_6294_);
v___x_6311_ = 1;
v___x_6312_ = l_Lean_Meta_mkLambdaFVars(v___x_6310_, v_a_6309_, v___x_6298_, v___x_6299_, v___x_6298_, v___x_6299_, v___x_6311_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_);
lean_dec(v___y_6303_);
lean_dec_ref(v___y_6302_);
lean_dec(v___y_6301_);
lean_dec_ref(v___y_6300_);
lean_dec_ref(v___x_6310_);
return v___x_6312_;
}
else
{
lean_dec(v___y_6303_);
lean_dec_ref(v___y_6302_);
lean_dec(v___y_6301_);
lean_dec_ref(v___y_6300_);
lean_dec_ref(v_ys4_6294_);
lean_dec_ref(v_xs_6292_);
return v___x_6308_;
}
}
else
{
lean_dec(v___y_6303_);
lean_dec_ref(v___y_6302_);
lean_dec(v___y_6301_);
lean_dec_ref(v___y_6300_);
lean_dec_ref(v_altType_6297_);
lean_dec(v_a_6296_);
lean_dec_ref(v_onAlt_6295_);
lean_dec_ref(v_ys4_6294_);
lean_dec_ref(v_remaining_x27_6293_);
lean_dec_ref(v_xs_6292_);
return v___x_6305_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed(lean_object* v___x_6313_, lean_object* v_xs_6314_, lean_object* v_remaining_x27_6315_, lean_object* v_ys4_6316_, lean_object* v_onAlt_6317_, lean_object* v_a_6318_, lean_object* v_altType_6319_, lean_object* v___x_6320_, lean_object* v___x_6321_, lean_object* v___y_6322_, lean_object* v___y_6323_, lean_object* v___y_6324_, lean_object* v___y_6325_, lean_object* v___y_6326_){
_start:
{
uint8_t v___x_35292__boxed_6327_; uint8_t v___x_35293__boxed_6328_; lean_object* v_res_6329_; 
v___x_35292__boxed_6327_ = lean_unbox(v___x_6320_);
v___x_35293__boxed_6328_ = lean_unbox(v___x_6321_);
v_res_6329_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(v___x_6313_, v_xs_6314_, v_remaining_x27_6315_, v_ys4_6316_, v_onAlt_6317_, v_a_6318_, v_altType_6319_, v___x_35292__boxed_6327_, v___x_35293__boxed_6328_, v___y_6322_, v___y_6323_, v___y_6324_, v___y_6325_);
return v_res_6329_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(lean_object* v___x_6330_, lean_object* v___f_6331_, uint8_t v___x_6332_, lean_object* v_xs_6333_, lean_object* v_remaining_x27_6334_, lean_object* v_onAlt_6335_, lean_object* v_a_6336_, uint8_t v___x_6337_, lean_object* v_ys4_6338_, lean_object* v_altType_6339_, lean_object* v___y_6340_, lean_object* v___y_6341_, lean_object* v___y_6342_, lean_object* v___y_6343_){
_start:
{
lean_object* v___x_6345_; 
lean_inc_ref(v___x_6330_);
v___x_6345_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v___x_6330_, v___f_6331_, v___x_6332_, v___y_6340_, v___y_6341_, v___y_6342_, v___y_6343_);
if (lean_obj_tag(v___x_6345_) == 0)
{
lean_object* v_a_6346_; lean_object* v___x_6347_; lean_object* v___x_6348_; lean_object* v___f_6349_; lean_object* v___x_6350_; 
v_a_6346_ = lean_ctor_get(v___x_6345_, 0);
lean_inc(v_a_6346_);
lean_dec_ref_known(v___x_6345_, 1);
v___x_6347_ = lean_box(v___x_6332_);
v___x_6348_ = lean_box(v___x_6337_);
lean_inc_ref(v_xs_6333_);
v___f_6349_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_6349_, 0, v___x_6330_);
lean_closure_set(v___f_6349_, 1, v_xs_6333_);
lean_closure_set(v___f_6349_, 2, v_remaining_x27_6334_);
lean_closure_set(v___f_6349_, 3, v_ys4_6338_);
lean_closure_set(v___f_6349_, 4, v_onAlt_6335_);
lean_closure_set(v___f_6349_, 5, v_a_6336_);
lean_closure_set(v___f_6349_, 6, v_altType_6339_);
lean_closure_set(v___f_6349_, 7, v___x_6347_);
lean_closure_set(v___f_6349_, 8, v___x_6348_);
v___x_6350_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_xs_6333_, v_a_6346_, v___f_6349_, v___y_6340_, v___y_6341_, v___y_6342_, v___y_6343_);
lean_dec(v_a_6346_);
lean_dec_ref(v_xs_6333_);
return v___x_6350_;
}
else
{
lean_object* v_a_6351_; lean_object* v___x_6353_; uint8_t v_isShared_6354_; uint8_t v_isSharedCheck_6358_; 
lean_dec_ref(v_altType_6339_);
lean_dec_ref(v_ys4_6338_);
lean_dec(v_a_6336_);
lean_dec_ref(v_onAlt_6335_);
lean_dec_ref(v_remaining_x27_6334_);
lean_dec_ref(v_xs_6333_);
lean_dec_ref(v___x_6330_);
v_a_6351_ = lean_ctor_get(v___x_6345_, 0);
v_isSharedCheck_6358_ = !lean_is_exclusive(v___x_6345_);
if (v_isSharedCheck_6358_ == 0)
{
v___x_6353_ = v___x_6345_;
v_isShared_6354_ = v_isSharedCheck_6358_;
goto v_resetjp_6352_;
}
else
{
lean_inc(v_a_6351_);
lean_dec(v___x_6345_);
v___x_6353_ = lean_box(0);
v_isShared_6354_ = v_isSharedCheck_6358_;
goto v_resetjp_6352_;
}
v_resetjp_6352_:
{
lean_object* v___x_6356_; 
if (v_isShared_6354_ == 0)
{
v___x_6356_ = v___x_6353_;
goto v_reusejp_6355_;
}
else
{
lean_object* v_reuseFailAlloc_6357_; 
v_reuseFailAlloc_6357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6357_, 0, v_a_6351_);
v___x_6356_ = v_reuseFailAlloc_6357_;
goto v_reusejp_6355_;
}
v_reusejp_6355_:
{
return v___x_6356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed(lean_object* v___x_6359_, lean_object* v___f_6360_, lean_object* v___x_6361_, lean_object* v_xs_6362_, lean_object* v_remaining_x27_6363_, lean_object* v_onAlt_6364_, lean_object* v_a_6365_, lean_object* v___x_6366_, lean_object* v_ys4_6367_, lean_object* v_altType_6368_, lean_object* v___y_6369_, lean_object* v___y_6370_, lean_object* v___y_6371_, lean_object* v___y_6372_, lean_object* v___y_6373_){
_start:
{
uint8_t v___x_35335__boxed_6374_; uint8_t v___x_35336__boxed_6375_; lean_object* v_res_6376_; 
v___x_35335__boxed_6374_ = lean_unbox(v___x_6361_);
v___x_35336__boxed_6375_ = lean_unbox(v___x_6366_);
v_res_6376_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(v___x_6359_, v___f_6360_, v___x_35335__boxed_6374_, v_xs_6362_, v_remaining_x27_6363_, v_onAlt_6364_, v_a_6365_, v___x_35336__boxed_6375_, v_ys4_6367_, v_altType_6368_, v___y_6369_, v___y_6370_, v___y_6371_, v___y_6372_);
lean_dec(v___y_6372_);
lean_dec_ref(v___y_6371_);
lean_dec(v___y_6370_);
lean_dec_ref(v___y_6369_);
return v_res_6376_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(lean_object* v___x_6377_, lean_object* v___f_6378_, uint8_t v___x_6379_, lean_object* v_remaining_x27_6380_, lean_object* v_onAlt_6381_, lean_object* v_a_6382_, uint8_t v___x_6383_, lean_object* v_extraEqualities_6384_, lean_object* v_xs_6385_, lean_object* v_altType_6386_, lean_object* v___y_6387_, lean_object* v___y_6388_, lean_object* v___y_6389_, lean_object* v___y_6390_){
_start:
{
lean_object* v___x_6392_; lean_object* v___x_6393_; lean_object* v___f_6394_; lean_object* v___x_6395_; lean_object* v___x_6396_; 
v___x_6392_ = lean_box(v___x_6379_);
v___x_6393_ = lean_box(v___x_6383_);
v___f_6394_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed), 15, 8);
lean_closure_set(v___f_6394_, 0, v___x_6377_);
lean_closure_set(v___f_6394_, 1, v___f_6378_);
lean_closure_set(v___f_6394_, 2, v___x_6392_);
lean_closure_set(v___f_6394_, 3, v_xs_6385_);
lean_closure_set(v___f_6394_, 4, v_remaining_x27_6380_);
lean_closure_set(v___f_6394_, 5, v_onAlt_6381_);
lean_closure_set(v___f_6394_, 6, v_a_6382_);
lean_closure_set(v___f_6394_, 7, v___x_6393_);
v___x_6395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6395_, 0, v_extraEqualities_6384_);
v___x_6396_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_6386_, v___x_6395_, v___f_6394_, v___x_6379_, v___x_6379_, v___y_6387_, v___y_6388_, v___y_6389_, v___y_6390_);
return v___x_6396_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed(lean_object* v___x_6397_, lean_object* v___f_6398_, lean_object* v___x_6399_, lean_object* v_remaining_x27_6400_, lean_object* v_onAlt_6401_, lean_object* v_a_6402_, lean_object* v___x_6403_, lean_object* v_extraEqualities_6404_, lean_object* v_xs_6405_, lean_object* v_altType_6406_, lean_object* v___y_6407_, lean_object* v___y_6408_, lean_object* v___y_6409_, lean_object* v___y_6410_, lean_object* v___y_6411_){
_start:
{
uint8_t v___x_35390__boxed_6412_; uint8_t v___x_35391__boxed_6413_; lean_object* v_res_6414_; 
v___x_35390__boxed_6412_ = lean_unbox(v___x_6399_);
v___x_35391__boxed_6413_ = lean_unbox(v___x_6403_);
v_res_6414_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(v___x_6397_, v___f_6398_, v___x_35390__boxed_6412_, v_remaining_x27_6400_, v_onAlt_6401_, v_a_6402_, v___x_35391__boxed_6413_, v_extraEqualities_6404_, v_xs_6405_, v_altType_6406_, v___y_6407_, v___y_6408_, v___y_6409_, v___y_6410_);
lean_dec(v___y_6410_);
lean_dec_ref(v___y_6409_);
lean_dec(v___y_6408_);
lean_dec_ref(v___y_6407_);
return v_res_6414_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(lean_object* v_upperBound_6416_, lean_object* v_onAlt_6417_, lean_object* v_extraEqualities_6418_, lean_object* v_a_6419_, lean_object* v_b_6420_, lean_object* v___y_6421_, lean_object* v___y_6422_, lean_object* v___y_6423_, lean_object* v___y_6424_){
_start:
{
lean_object* v___y_6427_; uint8_t v___x_6450_; 
v___x_6450_ = lean_nat_dec_lt(v_a_6419_, v_upperBound_6416_);
if (v___x_6450_ == 0)
{
lean_object* v___x_6451_; 
lean_dec(v_a_6419_);
lean_dec(v_extraEqualities_6418_);
lean_dec_ref(v_onAlt_6417_);
v___x_6451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6451_, 0, v_b_6420_);
return v___x_6451_;
}
else
{
lean_object* v_snd_6452_; lean_object* v_snd_6453_; lean_object* v_snd_6454_; lean_object* v_fst_6455_; lean_object* v___x_6457_; uint8_t v_isShared_6458_; uint8_t v_isSharedCheck_6562_; 
v_snd_6452_ = lean_ctor_get(v_b_6420_, 1);
lean_inc(v_snd_6452_);
v_snd_6453_ = lean_ctor_get(v_snd_6452_, 1);
lean_inc(v_snd_6453_);
v_snd_6454_ = lean_ctor_get(v_snd_6453_, 1);
lean_inc(v_snd_6454_);
v_fst_6455_ = lean_ctor_get(v_b_6420_, 0);
v_isSharedCheck_6562_ = !lean_is_exclusive(v_b_6420_);
if (v_isSharedCheck_6562_ == 0)
{
lean_object* v_unused_6563_; 
v_unused_6563_ = lean_ctor_get(v_b_6420_, 1);
lean_dec(v_unused_6563_);
v___x_6457_ = v_b_6420_;
v_isShared_6458_ = v_isSharedCheck_6562_;
goto v_resetjp_6456_;
}
else
{
lean_inc(v_fst_6455_);
lean_dec(v_b_6420_);
v___x_6457_ = lean_box(0);
v_isShared_6458_ = v_isSharedCheck_6562_;
goto v_resetjp_6456_;
}
v_resetjp_6456_:
{
lean_object* v_fst_6459_; lean_object* v___x_6461_; uint8_t v_isShared_6462_; uint8_t v_isSharedCheck_6560_; 
v_fst_6459_ = lean_ctor_get(v_snd_6452_, 0);
v_isSharedCheck_6560_ = !lean_is_exclusive(v_snd_6452_);
if (v_isSharedCheck_6560_ == 0)
{
lean_object* v_unused_6561_; 
v_unused_6561_ = lean_ctor_get(v_snd_6452_, 1);
lean_dec(v_unused_6561_);
v___x_6461_ = v_snd_6452_;
v_isShared_6462_ = v_isSharedCheck_6560_;
goto v_resetjp_6460_;
}
else
{
lean_inc(v_fst_6459_);
lean_dec(v_snd_6452_);
v___x_6461_ = lean_box(0);
v_isShared_6462_ = v_isSharedCheck_6560_;
goto v_resetjp_6460_;
}
v_resetjp_6460_:
{
lean_object* v_fst_6463_; lean_object* v___x_6465_; uint8_t v_isShared_6466_; uint8_t v_isSharedCheck_6558_; 
v_fst_6463_ = lean_ctor_get(v_snd_6453_, 0);
v_isSharedCheck_6558_ = !lean_is_exclusive(v_snd_6453_);
if (v_isSharedCheck_6558_ == 0)
{
lean_object* v_unused_6559_; 
v_unused_6559_ = lean_ctor_get(v_snd_6453_, 1);
lean_dec(v_unused_6559_);
v___x_6465_ = v_snd_6453_;
v_isShared_6466_ = v_isSharedCheck_6558_;
goto v_resetjp_6464_;
}
else
{
lean_inc(v_fst_6463_);
lean_dec(v_snd_6453_);
v___x_6465_ = lean_box(0);
v_isShared_6466_ = v_isSharedCheck_6558_;
goto v_resetjp_6464_;
}
v_resetjp_6464_:
{
lean_object* v_array_6467_; lean_object* v_start_6468_; lean_object* v_stop_6469_; uint8_t v___x_6470_; 
v_array_6467_ = lean_ctor_get(v_snd_6454_, 0);
v_start_6468_ = lean_ctor_get(v_snd_6454_, 1);
v_stop_6469_ = lean_ctor_get(v_snd_6454_, 2);
v___x_6470_ = lean_nat_dec_lt(v_start_6468_, v_stop_6469_);
if (v___x_6470_ == 0)
{
lean_object* v___x_6472_; 
if (v_isShared_6466_ == 0)
{
v___x_6472_ = v___x_6465_;
goto v_reusejp_6471_;
}
else
{
lean_object* v_reuseFailAlloc_6481_; 
v_reuseFailAlloc_6481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6481_, 0, v_fst_6463_);
lean_ctor_set(v_reuseFailAlloc_6481_, 1, v_snd_6454_);
v___x_6472_ = v_reuseFailAlloc_6481_;
goto v_reusejp_6471_;
}
v_reusejp_6471_:
{
lean_object* v___x_6474_; 
if (v_isShared_6462_ == 0)
{
lean_ctor_set(v___x_6461_, 1, v___x_6472_);
v___x_6474_ = v___x_6461_;
goto v_reusejp_6473_;
}
else
{
lean_object* v_reuseFailAlloc_6480_; 
v_reuseFailAlloc_6480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6480_, 0, v_fst_6459_);
lean_ctor_set(v_reuseFailAlloc_6480_, 1, v___x_6472_);
v___x_6474_ = v_reuseFailAlloc_6480_;
goto v_reusejp_6473_;
}
v_reusejp_6473_:
{
lean_object* v___x_6476_; 
if (v_isShared_6458_ == 0)
{
lean_ctor_set(v___x_6457_, 1, v___x_6474_);
v___x_6476_ = v___x_6457_;
goto v_reusejp_6475_;
}
else
{
lean_object* v_reuseFailAlloc_6479_; 
v_reuseFailAlloc_6479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6479_, 0, v_fst_6455_);
lean_ctor_set(v_reuseFailAlloc_6479_, 1, v___x_6474_);
v___x_6476_ = v_reuseFailAlloc_6479_;
goto v_reusejp_6475_;
}
v_reusejp_6475_:
{
lean_object* v___x_6477_; lean_object* v___f_6478_; 
v___x_6477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6477_, 0, v___x_6476_);
v___f_6478_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6478_, 0, v___x_6477_);
v___y_6427_ = v___f_6478_;
goto v___jp_6426_;
}
}
}
}
else
{
lean_object* v___x_6483_; uint8_t v_isShared_6484_; uint8_t v_isSharedCheck_6554_; 
lean_inc(v_stop_6469_);
lean_inc(v_start_6468_);
lean_inc_ref(v_array_6467_);
v_isSharedCheck_6554_ = !lean_is_exclusive(v_snd_6454_);
if (v_isSharedCheck_6554_ == 0)
{
lean_object* v_unused_6555_; lean_object* v_unused_6556_; lean_object* v_unused_6557_; 
v_unused_6555_ = lean_ctor_get(v_snd_6454_, 2);
lean_dec(v_unused_6555_);
v_unused_6556_ = lean_ctor_get(v_snd_6454_, 1);
lean_dec(v_unused_6556_);
v_unused_6557_ = lean_ctor_get(v_snd_6454_, 0);
lean_dec(v_unused_6557_);
v___x_6483_ = v_snd_6454_;
v_isShared_6484_ = v_isSharedCheck_6554_;
goto v_resetjp_6482_;
}
else
{
lean_dec(v_snd_6454_);
v___x_6483_ = lean_box(0);
v_isShared_6484_ = v_isSharedCheck_6554_;
goto v_resetjp_6482_;
}
v_resetjp_6482_:
{
lean_object* v_array_6485_; lean_object* v_start_6486_; lean_object* v_stop_6487_; lean_object* v___x_6488_; lean_object* v___x_6489_; lean_object* v___x_6490_; lean_object* v___x_6492_; 
v_array_6485_ = lean_ctor_get(v_fst_6463_, 0);
v_start_6486_ = lean_ctor_get(v_fst_6463_, 1);
v_stop_6487_ = lean_ctor_get(v_fst_6463_, 2);
v___x_6488_ = lean_array_fget(v_array_6467_, v_start_6468_);
v___x_6489_ = lean_unsigned_to_nat(1u);
v___x_6490_ = lean_nat_add(v_start_6468_, v___x_6489_);
lean_dec(v_start_6468_);
if (v_isShared_6484_ == 0)
{
lean_ctor_set(v___x_6483_, 1, v___x_6490_);
v___x_6492_ = v___x_6483_;
goto v_reusejp_6491_;
}
else
{
lean_object* v_reuseFailAlloc_6553_; 
v_reuseFailAlloc_6553_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6553_, 0, v_array_6467_);
lean_ctor_set(v_reuseFailAlloc_6553_, 1, v___x_6490_);
lean_ctor_set(v_reuseFailAlloc_6553_, 2, v_stop_6469_);
v___x_6492_ = v_reuseFailAlloc_6553_;
goto v_reusejp_6491_;
}
v_reusejp_6491_:
{
uint8_t v___x_6493_; 
v___x_6493_ = lean_nat_dec_lt(v_start_6486_, v_stop_6487_);
if (v___x_6493_ == 0)
{
lean_object* v___x_6495_; 
lean_dec(v___x_6488_);
if (v_isShared_6466_ == 0)
{
lean_ctor_set(v___x_6465_, 1, v___x_6492_);
v___x_6495_ = v___x_6465_;
goto v_reusejp_6494_;
}
else
{
lean_object* v_reuseFailAlloc_6504_; 
v_reuseFailAlloc_6504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6504_, 0, v_fst_6463_);
lean_ctor_set(v_reuseFailAlloc_6504_, 1, v___x_6492_);
v___x_6495_ = v_reuseFailAlloc_6504_;
goto v_reusejp_6494_;
}
v_reusejp_6494_:
{
lean_object* v___x_6497_; 
if (v_isShared_6462_ == 0)
{
lean_ctor_set(v___x_6461_, 1, v___x_6495_);
v___x_6497_ = v___x_6461_;
goto v_reusejp_6496_;
}
else
{
lean_object* v_reuseFailAlloc_6503_; 
v_reuseFailAlloc_6503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6503_, 0, v_fst_6459_);
lean_ctor_set(v_reuseFailAlloc_6503_, 1, v___x_6495_);
v___x_6497_ = v_reuseFailAlloc_6503_;
goto v_reusejp_6496_;
}
v_reusejp_6496_:
{
lean_object* v___x_6499_; 
if (v_isShared_6458_ == 0)
{
lean_ctor_set(v___x_6457_, 1, v___x_6497_);
v___x_6499_ = v___x_6457_;
goto v_reusejp_6498_;
}
else
{
lean_object* v_reuseFailAlloc_6502_; 
v_reuseFailAlloc_6502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6502_, 0, v_fst_6455_);
lean_ctor_set(v_reuseFailAlloc_6502_, 1, v___x_6497_);
v___x_6499_ = v_reuseFailAlloc_6502_;
goto v_reusejp_6498_;
}
v_reusejp_6498_:
{
lean_object* v___x_6500_; lean_object* v___f_6501_; 
v___x_6500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6500_, 0, v___x_6499_);
v___f_6501_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6501_, 0, v___x_6500_);
v___y_6427_ = v___f_6501_;
goto v___jp_6426_;
}
}
}
}
else
{
lean_object* v___x_6506_; uint8_t v_isShared_6507_; uint8_t v_isSharedCheck_6549_; 
lean_inc(v_stop_6487_);
lean_inc(v_start_6486_);
lean_inc_ref(v_array_6485_);
v_isSharedCheck_6549_ = !lean_is_exclusive(v_fst_6463_);
if (v_isSharedCheck_6549_ == 0)
{
lean_object* v_unused_6550_; lean_object* v_unused_6551_; lean_object* v_unused_6552_; 
v_unused_6550_ = lean_ctor_get(v_fst_6463_, 2);
lean_dec(v_unused_6550_);
v_unused_6551_ = lean_ctor_get(v_fst_6463_, 1);
lean_dec(v_unused_6551_);
v_unused_6552_ = lean_ctor_get(v_fst_6463_, 0);
lean_dec(v_unused_6552_);
v___x_6506_ = v_fst_6463_;
v_isShared_6507_ = v_isSharedCheck_6549_;
goto v_resetjp_6505_;
}
else
{
lean_dec(v_fst_6463_);
v___x_6506_ = lean_box(0);
v_isShared_6507_ = v_isSharedCheck_6549_;
goto v_resetjp_6505_;
}
v_resetjp_6505_:
{
lean_object* v_array_6508_; lean_object* v_start_6509_; lean_object* v_stop_6510_; lean_object* v___x_6511_; lean_object* v___x_6512_; lean_object* v___x_6514_; 
v_array_6508_ = lean_ctor_get(v_fst_6459_, 0);
v_start_6509_ = lean_ctor_get(v_fst_6459_, 1);
v_stop_6510_ = lean_ctor_get(v_fst_6459_, 2);
v___x_6511_ = lean_array_fget(v_array_6485_, v_start_6486_);
v___x_6512_ = lean_nat_add(v_start_6486_, v___x_6489_);
lean_dec(v_start_6486_);
if (v_isShared_6507_ == 0)
{
lean_ctor_set(v___x_6506_, 1, v___x_6512_);
v___x_6514_ = v___x_6506_;
goto v_reusejp_6513_;
}
else
{
lean_object* v_reuseFailAlloc_6548_; 
v_reuseFailAlloc_6548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6548_, 0, v_array_6485_);
lean_ctor_set(v_reuseFailAlloc_6548_, 1, v___x_6512_);
lean_ctor_set(v_reuseFailAlloc_6548_, 2, v_stop_6487_);
v___x_6514_ = v_reuseFailAlloc_6548_;
goto v_reusejp_6513_;
}
v_reusejp_6513_:
{
uint8_t v___x_6515_; 
v___x_6515_ = lean_nat_dec_lt(v_start_6509_, v_stop_6510_);
if (v___x_6515_ == 0)
{
lean_object* v___x_6517_; 
lean_dec(v___x_6511_);
lean_dec(v___x_6488_);
if (v_isShared_6466_ == 0)
{
lean_ctor_set(v___x_6465_, 1, v___x_6492_);
lean_ctor_set(v___x_6465_, 0, v___x_6514_);
v___x_6517_ = v___x_6465_;
goto v_reusejp_6516_;
}
else
{
lean_object* v_reuseFailAlloc_6526_; 
v_reuseFailAlloc_6526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6526_, 0, v___x_6514_);
lean_ctor_set(v_reuseFailAlloc_6526_, 1, v___x_6492_);
v___x_6517_ = v_reuseFailAlloc_6526_;
goto v_reusejp_6516_;
}
v_reusejp_6516_:
{
lean_object* v___x_6519_; 
if (v_isShared_6462_ == 0)
{
lean_ctor_set(v___x_6461_, 1, v___x_6517_);
v___x_6519_ = v___x_6461_;
goto v_reusejp_6518_;
}
else
{
lean_object* v_reuseFailAlloc_6525_; 
v_reuseFailAlloc_6525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6525_, 0, v_fst_6459_);
lean_ctor_set(v_reuseFailAlloc_6525_, 1, v___x_6517_);
v___x_6519_ = v_reuseFailAlloc_6525_;
goto v_reusejp_6518_;
}
v_reusejp_6518_:
{
lean_object* v___x_6521_; 
if (v_isShared_6458_ == 0)
{
lean_ctor_set(v___x_6457_, 1, v___x_6519_);
v___x_6521_ = v___x_6457_;
goto v_reusejp_6520_;
}
else
{
lean_object* v_reuseFailAlloc_6524_; 
v_reuseFailAlloc_6524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6524_, 0, v_fst_6455_);
lean_ctor_set(v_reuseFailAlloc_6524_, 1, v___x_6519_);
v___x_6521_ = v_reuseFailAlloc_6524_;
goto v_reusejp_6520_;
}
v_reusejp_6520_:
{
lean_object* v___x_6522_; lean_object* v___f_6523_; 
v___x_6522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6522_, 0, v___x_6521_);
v___f_6523_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6523_, 0, v___x_6522_);
v___y_6427_ = v___f_6523_;
goto v___jp_6426_;
}
}
}
}
else
{
lean_object* v___x_6528_; uint8_t v_isShared_6529_; uint8_t v_isSharedCheck_6544_; 
lean_inc(v_stop_6510_);
lean_inc(v_start_6509_);
lean_inc_ref(v_array_6508_);
lean_del_object(v___x_6465_);
lean_del_object(v___x_6461_);
lean_del_object(v___x_6457_);
v_isSharedCheck_6544_ = !lean_is_exclusive(v_fst_6459_);
if (v_isSharedCheck_6544_ == 0)
{
lean_object* v_unused_6545_; lean_object* v_unused_6546_; lean_object* v_unused_6547_; 
v_unused_6545_ = lean_ctor_get(v_fst_6459_, 2);
lean_dec(v_unused_6545_);
v_unused_6546_ = lean_ctor_get(v_fst_6459_, 1);
lean_dec(v_unused_6546_);
v_unused_6547_ = lean_ctor_get(v_fst_6459_, 0);
lean_dec(v_unused_6547_);
v___x_6528_ = v_fst_6459_;
v_isShared_6529_ = v_isSharedCheck_6544_;
goto v_resetjp_6527_;
}
else
{
lean_dec(v_fst_6459_);
v___x_6528_ = lean_box(0);
v_isShared_6529_ = v_isSharedCheck_6544_;
goto v_resetjp_6527_;
}
v_resetjp_6527_:
{
lean_object* v___f_6530_; uint8_t v___x_6531_; lean_object* v_remaining_x27_6532_; lean_object* v___x_6533_; lean_object* v___x_6534_; lean_object* v___x_6535_; lean_object* v___f_6536_; lean_object* v___x_6537_; lean_object* v___x_6539_; 
v___f_6530_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___closed__0));
v___x_6531_ = 0;
v_remaining_x27_6532_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_6533_ = lean_array_fget_borrowed(v_array_6508_, v_start_6509_);
v___x_6534_ = lean_box(v___x_6531_);
v___x_6535_ = lean_box(v___x_6515_);
lean_inc(v_extraEqualities_6418_);
lean_inc(v_a_6419_);
lean_inc_ref(v_onAlt_6417_);
lean_inc(v___x_6533_);
v___f_6536_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed), 15, 8);
lean_closure_set(v___f_6536_, 0, v___x_6533_);
lean_closure_set(v___f_6536_, 1, v___f_6530_);
lean_closure_set(v___f_6536_, 2, v___x_6534_);
lean_closure_set(v___f_6536_, 3, v_remaining_x27_6532_);
lean_closure_set(v___f_6536_, 4, v_onAlt_6417_);
lean_closure_set(v___f_6536_, 5, v_a_6419_);
lean_closure_set(v___f_6536_, 6, v___x_6535_);
lean_closure_set(v___f_6536_, 7, v_extraEqualities_6418_);
v___x_6537_ = lean_nat_add(v_start_6509_, v___x_6489_);
lean_dec(v_start_6509_);
if (v_isShared_6529_ == 0)
{
lean_ctor_set(v___x_6528_, 1, v___x_6537_);
v___x_6539_ = v___x_6528_;
goto v_reusejp_6538_;
}
else
{
lean_object* v_reuseFailAlloc_6543_; 
v_reuseFailAlloc_6543_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6543_, 0, v_array_6508_);
lean_ctor_set(v_reuseFailAlloc_6543_, 1, v___x_6537_);
lean_ctor_set(v_reuseFailAlloc_6543_, 2, v_stop_6510_);
v___x_6539_ = v_reuseFailAlloc_6543_;
goto v_reusejp_6538_;
}
v_reusejp_6538_:
{
lean_object* v___x_6540_; lean_object* v___x_6541_; lean_object* v___f_6542_; 
v___x_6540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6540_, 0, v___x_6511_);
v___x_6541_ = lean_box(v___x_6531_);
v___f_6542_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed), 13, 8);
lean_closure_set(v___f_6542_, 0, v___x_6488_);
lean_closure_set(v___f_6542_, 1, v___x_6540_);
lean_closure_set(v___f_6542_, 2, v___f_6536_);
lean_closure_set(v___f_6542_, 3, v___x_6541_);
lean_closure_set(v___f_6542_, 4, v_fst_6455_);
lean_closure_set(v___f_6542_, 5, v___x_6514_);
lean_closure_set(v___f_6542_, 6, v___x_6492_);
lean_closure_set(v___f_6542_, 7, v___x_6539_);
v___y_6427_ = v___f_6542_;
goto v___jp_6426_;
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_6426_:
{
lean_object* v___x_6428_; 
lean_inc(v___y_6424_);
lean_inc_ref(v___y_6423_);
lean_inc(v___y_6422_);
lean_inc_ref(v___y_6421_);
v___x_6428_ = lean_apply_5(v___y_6427_, v___y_6421_, v___y_6422_, v___y_6423_, v___y_6424_, lean_box(0));
if (lean_obj_tag(v___x_6428_) == 0)
{
lean_object* v_a_6429_; lean_object* v___x_6431_; uint8_t v_isShared_6432_; uint8_t v_isSharedCheck_6441_; 
v_a_6429_ = lean_ctor_get(v___x_6428_, 0);
v_isSharedCheck_6441_ = !lean_is_exclusive(v___x_6428_);
if (v_isSharedCheck_6441_ == 0)
{
v___x_6431_ = v___x_6428_;
v_isShared_6432_ = v_isSharedCheck_6441_;
goto v_resetjp_6430_;
}
else
{
lean_inc(v_a_6429_);
lean_dec(v___x_6428_);
v___x_6431_ = lean_box(0);
v_isShared_6432_ = v_isSharedCheck_6441_;
goto v_resetjp_6430_;
}
v_resetjp_6430_:
{
if (lean_obj_tag(v_a_6429_) == 0)
{
lean_object* v_a_6433_; lean_object* v___x_6435_; 
lean_dec(v_a_6419_);
lean_dec(v_extraEqualities_6418_);
lean_dec_ref(v_onAlt_6417_);
v_a_6433_ = lean_ctor_get(v_a_6429_, 0);
lean_inc(v_a_6433_);
lean_dec_ref_known(v_a_6429_, 1);
if (v_isShared_6432_ == 0)
{
lean_ctor_set(v___x_6431_, 0, v_a_6433_);
v___x_6435_ = v___x_6431_;
goto v_reusejp_6434_;
}
else
{
lean_object* v_reuseFailAlloc_6436_; 
v_reuseFailAlloc_6436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6436_, 0, v_a_6433_);
v___x_6435_ = v_reuseFailAlloc_6436_;
goto v_reusejp_6434_;
}
v_reusejp_6434_:
{
return v___x_6435_;
}
}
else
{
lean_object* v_a_6437_; lean_object* v___x_6438_; lean_object* v___x_6439_; 
lean_del_object(v___x_6431_);
v_a_6437_ = lean_ctor_get(v_a_6429_, 0);
lean_inc(v_a_6437_);
lean_dec_ref_known(v_a_6429_, 1);
v___x_6438_ = lean_unsigned_to_nat(1u);
v___x_6439_ = lean_nat_add(v_a_6419_, v___x_6438_);
lean_dec(v_a_6419_);
v_a_6419_ = v___x_6439_;
v_b_6420_ = v_a_6437_;
goto _start;
}
}
}
else
{
lean_object* v_a_6442_; lean_object* v___x_6444_; uint8_t v_isShared_6445_; uint8_t v_isSharedCheck_6449_; 
lean_dec(v_a_6419_);
lean_dec(v_extraEqualities_6418_);
lean_dec_ref(v_onAlt_6417_);
v_a_6442_ = lean_ctor_get(v___x_6428_, 0);
v_isSharedCheck_6449_ = !lean_is_exclusive(v___x_6428_);
if (v_isSharedCheck_6449_ == 0)
{
v___x_6444_ = v___x_6428_;
v_isShared_6445_ = v_isSharedCheck_6449_;
goto v_resetjp_6443_;
}
else
{
lean_inc(v_a_6442_);
lean_dec(v___x_6428_);
v___x_6444_ = lean_box(0);
v_isShared_6445_ = v_isSharedCheck_6449_;
goto v_resetjp_6443_;
}
v_resetjp_6443_:
{
lean_object* v___x_6447_; 
if (v_isShared_6445_ == 0)
{
v___x_6447_ = v___x_6444_;
goto v_reusejp_6446_;
}
else
{
lean_object* v_reuseFailAlloc_6448_; 
v_reuseFailAlloc_6448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6448_, 0, v_a_6442_);
v___x_6447_ = v_reuseFailAlloc_6448_;
goto v_reusejp_6446_;
}
v_reusejp_6446_:
{
return v___x_6447_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___boxed(lean_object* v_upperBound_6564_, lean_object* v_onAlt_6565_, lean_object* v_extraEqualities_6566_, lean_object* v_a_6567_, lean_object* v_b_6568_, lean_object* v___y_6569_, lean_object* v___y_6570_, lean_object* v___y_6571_, lean_object* v___y_6572_, lean_object* v___y_6573_){
_start:
{
lean_object* v_res_6574_; 
v_res_6574_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v_upperBound_6564_, v_onAlt_6565_, v_extraEqualities_6566_, v_a_6567_, v_b_6568_, v___y_6569_, v___y_6570_, v___y_6571_, v___y_6572_);
lean_dec(v___y_6572_);
lean_dec_ref(v___y_6571_);
lean_dec(v___y_6570_);
lean_dec_ref(v___y_6569_);
lean_dec(v_upperBound_6564_);
return v_res_6574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(lean_object* v_onParams_6575_, size_t v_sz_6576_, size_t v_i_6577_, lean_object* v_bs_6578_, lean_object* v___y_6579_, lean_object* v___y_6580_, lean_object* v___y_6581_, lean_object* v___y_6582_){
_start:
{
uint8_t v___x_6584_; 
v___x_6584_ = lean_usize_dec_lt(v_i_6577_, v_sz_6576_);
if (v___x_6584_ == 0)
{
lean_object* v___x_6585_; 
lean_dec_ref(v_onParams_6575_);
v___x_6585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6585_, 0, v_bs_6578_);
return v___x_6585_;
}
else
{
lean_object* v_v_6586_; lean_object* v___x_6587_; 
v_v_6586_ = lean_array_uget_borrowed(v_bs_6578_, v_i_6577_);
lean_inc_ref(v_onParams_6575_);
lean_inc(v___y_6582_);
lean_inc_ref(v___y_6581_);
lean_inc(v___y_6580_);
lean_inc_ref(v___y_6579_);
lean_inc(v_v_6586_);
v___x_6587_ = lean_apply_6(v_onParams_6575_, v_v_6586_, v___y_6579_, v___y_6580_, v___y_6581_, v___y_6582_, lean_box(0));
if (lean_obj_tag(v___x_6587_) == 0)
{
lean_object* v_a_6588_; lean_object* v___x_6589_; lean_object* v_bs_x27_6590_; size_t v___x_6591_; size_t v___x_6592_; lean_object* v___x_6593_; 
v_a_6588_ = lean_ctor_get(v___x_6587_, 0);
lean_inc(v_a_6588_);
lean_dec_ref_known(v___x_6587_, 1);
v___x_6589_ = lean_unsigned_to_nat(0u);
v_bs_x27_6590_ = lean_array_uset(v_bs_6578_, v_i_6577_, v___x_6589_);
v___x_6591_ = ((size_t)1ULL);
v___x_6592_ = lean_usize_add(v_i_6577_, v___x_6591_);
v___x_6593_ = lean_array_uset(v_bs_x27_6590_, v_i_6577_, v_a_6588_);
v_i_6577_ = v___x_6592_;
v_bs_6578_ = v___x_6593_;
goto _start;
}
else
{
lean_object* v_a_6595_; lean_object* v___x_6597_; uint8_t v_isShared_6598_; uint8_t v_isSharedCheck_6602_; 
lean_dec_ref(v_bs_6578_);
lean_dec_ref(v_onParams_6575_);
v_a_6595_ = lean_ctor_get(v___x_6587_, 0);
v_isSharedCheck_6602_ = !lean_is_exclusive(v___x_6587_);
if (v_isSharedCheck_6602_ == 0)
{
v___x_6597_ = v___x_6587_;
v_isShared_6598_ = v_isSharedCheck_6602_;
goto v_resetjp_6596_;
}
else
{
lean_inc(v_a_6595_);
lean_dec(v___x_6587_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6___boxed(lean_object* v_onParams_6603_, lean_object* v_sz_6604_, lean_object* v_i_6605_, lean_object* v_bs_6606_, lean_object* v___y_6607_, lean_object* v___y_6608_, lean_object* v___y_6609_, lean_object* v___y_6610_, lean_object* v___y_6611_){
_start:
{
size_t v_sz_boxed_6612_; size_t v_i_boxed_6613_; lean_object* v_res_6614_; 
v_sz_boxed_6612_ = lean_unbox_usize(v_sz_6604_);
lean_dec(v_sz_6604_);
v_i_boxed_6613_ = lean_unbox_usize(v_i_6605_);
lean_dec(v_i_6605_);
v_res_6614_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6603_, v_sz_boxed_6612_, v_i_boxed_6613_, v_bs_6606_, v___y_6607_, v___y_6608_, v___y_6609_, v___y_6610_);
lean_dec(v___y_6610_);
lean_dec_ref(v___y_6609_);
lean_dec(v___y_6608_);
lean_dec_ref(v___y_6607_);
return v_res_6614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(lean_object* v_declName_6615_, lean_object* v___y_6616_){
_start:
{
lean_object* v___x_6618_; lean_object* v_env_6619_; lean_object* v___x_6620_; lean_object* v___x_6621_; 
v___x_6618_ = lean_st_ref_get(v___y_6616_);
v_env_6619_ = lean_ctor_get(v___x_6618_, 0);
lean_inc_ref(v_env_6619_);
lean_dec(v___x_6618_);
v___x_6620_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_6619_, v_declName_6615_);
v___x_6621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6621_, 0, v___x_6620_);
return v___x_6621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg___boxed(lean_object* v_declName_6622_, lean_object* v___y_6623_, lean_object* v___y_6624_){
_start:
{
lean_object* v_res_6625_; 
v_res_6625_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_declName_6622_, v___y_6623_);
lean_dec(v___y_6623_);
return v_res_6625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(lean_object* v_matcherApp_6628_, uint8_t v_useSplitter_6629_, uint8_t v_addEqualities_6630_, uint8_t v_addProofEqualities_6631_, lean_object* v_onParams_6632_, lean_object* v_onMotive_6633_, lean_object* v_onAlt_6634_, lean_object* v_onRemaining_6635_, lean_object* v___y_6636_, lean_object* v___y_6637_, lean_object* v___y_6638_, lean_object* v___y_6639_){
_start:
{
lean_object* v___x_6641_; lean_object* v_env_6642_; lean_object* v_toMatcherInfo_6643_; lean_object* v_matcherName_6644_; lean_object* v_matcherLevels_6645_; lean_object* v_params_6646_; lean_object* v_motive_6647_; lean_object* v_discrs_6648_; lean_object* v_alts_6649_; lean_object* v_remaining_6650_; lean_object* v___y_6652_; lean_object* v___y_6653_; lean_object* v___y_6654_; lean_object* v___y_6655_; lean_object* v___y_6656_; lean_object* v___y_6657_; lean_object* v___y_6658_; lean_object* v___y_6659_; lean_object* v___y_6660_; lean_object* v___y_6661_; lean_object* v___y_6662_; lean_object* v___y_6663_; lean_object* v___y_6664_; uint8_t v_isCasesOn_6749_; lean_object* v___y_6751_; lean_object* v___y_6752_; lean_object* v___y_6753_; lean_object* v___y_6754_; size_t v___y_6755_; lean_object* v___y_6756_; lean_object* v___y_6757_; lean_object* v_matcherLevels_6758_; lean_object* v___y_6759_; lean_object* v___y_6760_; lean_object* v___y_6761_; lean_object* v___y_6762_; lean_object* v_numDiscrEqs_6956_; lean_object* v___y_6957_; lean_object* v___y_6958_; lean_object* v___y_6959_; lean_object* v___y_6960_; 
v___x_6641_ = lean_st_ref_get(v___y_6639_);
v_env_6642_ = lean_ctor_get(v___x_6641_, 0);
lean_inc_ref(v_env_6642_);
lean_dec(v___x_6641_);
v_toMatcherInfo_6643_ = lean_ctor_get(v_matcherApp_6628_, 0);
lean_inc_ref(v_toMatcherInfo_6643_);
v_matcherName_6644_ = lean_ctor_get(v_matcherApp_6628_, 1);
lean_inc_n(v_matcherName_6644_, 2);
v_matcherLevels_6645_ = lean_ctor_get(v_matcherApp_6628_, 2);
v_params_6646_ = lean_ctor_get(v_matcherApp_6628_, 3);
v_motive_6647_ = lean_ctor_get(v_matcherApp_6628_, 4);
v_discrs_6648_ = lean_ctor_get(v_matcherApp_6628_, 5);
v_alts_6649_ = lean_ctor_get(v_matcherApp_6628_, 6);
lean_inc_ref(v_alts_6649_);
v_remaining_6650_ = lean_ctor_get(v_matcherApp_6628_, 7);
lean_inc_ref(v_remaining_6650_);
v_isCasesOn_6749_ = l_Lean_isCasesOnRecursor(v_env_6642_, v_matcherName_6644_);
if (v_isCasesOn_6749_ == 0)
{
lean_object* v___x_7011_; lean_object* v_a_7012_; 
lean_inc(v_matcherName_6644_);
v___x_7011_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_matcherName_6644_, v___y_6639_);
v_a_7012_ = lean_ctor_get(v___x_7011_, 0);
lean_inc(v_a_7012_);
lean_dec_ref(v___x_7011_);
if (lean_obj_tag(v_a_7012_) == 0)
{
lean_object* v___x_7013_; lean_object* v___x_7014_; lean_object* v___x_7015_; lean_object* v___x_7016_; lean_object* v___x_7017_; lean_object* v___x_7018_; lean_object* v_a_7019_; lean_object* v___x_7021_; uint8_t v_isShared_7022_; uint8_t v_isSharedCheck_7026_; 
lean_dec_ref(v_remaining_6650_);
lean_dec_ref(v_alts_6649_);
lean_dec_ref(v_toMatcherInfo_6643_);
lean_dec_ref(v_onRemaining_6635_);
lean_dec_ref(v_onAlt_6634_);
lean_dec_ref(v_onMotive_6633_);
lean_dec_ref(v_onParams_6632_);
lean_dec_ref(v_matcherApp_6628_);
v___x_7013_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__1);
v___x_7014_ = l_Lean_MessageData_ofName(v_matcherName_6644_);
v___x_7015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7015_, 0, v___x_7013_);
lean_ctor_set(v___x_7015_, 1, v___x_7014_);
v___x_7016_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__65___closed__3);
v___x_7017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7017_, 0, v___x_7015_);
lean_ctor_set(v___x_7017_, 1, v___x_7016_);
v___x_7018_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_7017_, v___y_6636_, v___y_6637_, v___y_6638_, v___y_6639_);
v_a_7019_ = lean_ctor_get(v___x_7018_, 0);
v_isSharedCheck_7026_ = !lean_is_exclusive(v___x_7018_);
if (v_isSharedCheck_7026_ == 0)
{
v___x_7021_ = v___x_7018_;
v_isShared_7022_ = v_isSharedCheck_7026_;
goto v_resetjp_7020_;
}
else
{
lean_inc(v_a_7019_);
lean_dec(v___x_7018_);
v___x_7021_ = lean_box(0);
v_isShared_7022_ = v_isSharedCheck_7026_;
goto v_resetjp_7020_;
}
v_resetjp_7020_:
{
lean_object* v___x_7024_; 
if (v_isShared_7022_ == 0)
{
v___x_7024_ = v___x_7021_;
goto v_reusejp_7023_;
}
else
{
lean_object* v_reuseFailAlloc_7025_; 
v_reuseFailAlloc_7025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7025_, 0, v_a_7019_);
v___x_7024_ = v_reuseFailAlloc_7025_;
goto v_reusejp_7023_;
}
v_reusejp_7023_:
{
return v___x_7024_;
}
}
}
else
{
lean_object* v_val_7027_; lean_object* v___x_7028_; 
v_val_7027_ = lean_ctor_get(v_a_7012_, 0);
lean_inc(v_val_7027_);
lean_dec_ref_known(v_a_7012_, 1);
v___x_7028_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_7027_);
lean_dec(v_val_7027_);
v_numDiscrEqs_6956_ = v___x_7028_;
v___y_6957_ = v___y_6636_;
v___y_6958_ = v___y_6637_;
v___y_6959_ = v___y_6638_;
v___y_6960_ = v___y_6639_;
goto v___jp_6955_;
}
}
else
{
lean_object* v___x_7029_; 
v___x_7029_ = lean_unsigned_to_nat(0u);
v_numDiscrEqs_6956_ = v___x_7029_;
v___y_6957_ = v___y_6636_;
v___y_6958_ = v___y_6637_;
v___y_6959_ = v___y_6638_;
v___y_6960_ = v___y_6639_;
goto v___jp_6955_;
}
v___jp_6651_:
{
lean_object* v___x_6665_; lean_object* v___x_6666_; lean_object* v_aux_6667_; lean_object* v_aux_6668_; lean_object* v_aux_6669_; lean_object* v___x_6670_; lean_object* v___x_6671_; lean_object* v___x_6672_; lean_object* v___f_6673_; uint8_t v___x_6674_; lean_object* v___x_6675_; lean_object* v___x_6676_; lean_object* v___x_6677_; 
lean_inc_ref(v___y_6655_);
v___x_6665_ = lean_array_to_list(v___y_6655_);
lean_inc(v_matcherName_6644_);
v___x_6666_ = l_Lean_mkConst(v_matcherName_6644_, v___x_6665_);
v_aux_6667_ = l_Lean_mkAppN(v___x_6666_, v___y_6654_);
lean_inc_ref(v___y_6661_);
v_aux_6668_ = l_Lean_Expr_app___override(v_aux_6667_, v___y_6661_);
v_aux_6669_ = l_Lean_mkAppN(v_aux_6668_, v___y_6660_);
v___x_6670_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__1);
lean_inc_ref_n(v_aux_6669_, 2);
v___x_6671_ = l_Lean_indentExpr(v_aux_6669_);
v___x_6672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6672_, 0, v___x_6670_);
lean_ctor_set(v___x_6672_, 1, v___x_6671_);
v___f_6673_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34), 2, 1);
lean_closure_set(v___f_6673_, 0, v___x_6672_);
v___x_6674_ = 0;
v___x_6675_ = lean_box(v___x_6674_);
v___x_6676_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6676_, 0, v_aux_6669_);
lean_closure_set(v___x_6676_, 1, v___x_6675_);
v___x_6677_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6676_, v___f_6673_, v___y_6663_, v___y_6658_, v___y_6656_, v___y_6659_);
if (lean_obj_tag(v___x_6677_) == 0)
{
lean_object* v___x_6678_; lean_object* v___x_6679_; 
lean_dec_ref_known(v___x_6677_, 1);
v___x_6678_ = lean_array_get_size(v_alts_6649_);
v___x_6679_ = l_Lean_Meta_inferArgumentTypesN(v___x_6678_, v_aux_6669_, v___y_6663_, v___y_6658_, v___y_6656_, v___y_6659_);
if (lean_obj_tag(v___x_6679_) == 0)
{
lean_object* v_a_6680_; lean_object* v___x_6681_; lean_object* v___x_6682_; lean_object* v___x_6683_; lean_object* v___x_6684_; lean_object* v___x_6685_; lean_object* v___x_6686_; lean_object* v___x_6687_; lean_object* v___x_6688_; lean_object* v___x_6689_; lean_object* v___x_6690_; 
v_a_6680_ = lean_ctor_get(v___x_6679_, 0);
lean_inc(v_a_6680_);
lean_dec_ref_known(v___x_6679_, 1);
v___x_6681_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_6628_);
v___x_6682_ = lean_array_get_size(v___x_6681_);
v___x_6683_ = lean_array_get_size(v_a_6680_);
lean_inc_n(v___y_6664_, 3);
v___x_6684_ = l_Array_toSubarray___redArg(v_alts_6649_, v___y_6664_, v___x_6678_);
v___x_6685_ = l_Array_toSubarray___redArg(v___x_6681_, v___y_6664_, v___x_6682_);
v___x_6686_ = l_Array_toSubarray___redArg(v_a_6680_, v___y_6664_, v___x_6683_);
v___x_6687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6687_, 0, v___x_6685_);
lean_ctor_set(v___x_6687_, 1, v___x_6686_);
v___x_6688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6688_, 0, v___x_6684_);
lean_ctor_set(v___x_6688_, 1, v___x_6687_);
lean_inc_ref(v___y_6662_);
v___x_6689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6689_, 0, v___y_6662_);
lean_ctor_set(v___x_6689_, 1, v___x_6688_);
v___x_6690_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v___x_6678_, v_onAlt_6634_, v___y_6652_, v___y_6664_, v___x_6689_, v___y_6663_, v___y_6658_, v___y_6656_, v___y_6659_);
if (lean_obj_tag(v___x_6690_) == 0)
{
lean_object* v_a_6691_; lean_object* v_fst_6692_; lean_object* v___x_6693_; 
v_a_6691_ = lean_ctor_get(v___x_6690_, 0);
lean_inc(v_a_6691_);
lean_dec_ref_known(v___x_6690_, 1);
v_fst_6692_ = lean_ctor_get(v_a_6691_, 0);
lean_inc(v_fst_6692_);
lean_dec(v_a_6691_);
lean_inc(v___y_6659_);
lean_inc_ref(v___y_6656_);
lean_inc(v___y_6658_);
lean_inc_ref(v___y_6663_);
v___x_6693_ = lean_apply_6(v_onRemaining_6635_, v_remaining_6650_, v___y_6663_, v___y_6658_, v___y_6656_, v___y_6659_, lean_box(0));
if (lean_obj_tag(v___x_6693_) == 0)
{
lean_object* v_a_6694_; lean_object* v___x_6696_; uint8_t v_isShared_6697_; uint8_t v_isSharedCheck_6716_; 
v_a_6694_ = lean_ctor_get(v___x_6693_, 0);
v_isSharedCheck_6716_ = !lean_is_exclusive(v___x_6693_);
if (v_isSharedCheck_6716_ == 0)
{
v___x_6696_ = v___x_6693_;
v_isShared_6697_ = v_isSharedCheck_6716_;
goto v_resetjp_6695_;
}
else
{
lean_inc(v_a_6694_);
lean_dec(v___x_6693_);
v___x_6696_ = lean_box(0);
v_isShared_6697_ = v_isSharedCheck_6716_;
goto v_resetjp_6695_;
}
v_resetjp_6695_:
{
lean_object* v_numParams_6698_; lean_object* v_numDiscrs_6699_; lean_object* v_altInfos_6700_; lean_object* v_uElimPos_x3f_6701_; lean_object* v_overlaps_6702_; lean_object* v___x_6704_; uint8_t v_isShared_6705_; uint8_t v_isSharedCheck_6714_; 
v_numParams_6698_ = lean_ctor_get(v_toMatcherInfo_6643_, 0);
v_numDiscrs_6699_ = lean_ctor_get(v_toMatcherInfo_6643_, 1);
v_altInfos_6700_ = lean_ctor_get(v_toMatcherInfo_6643_, 2);
v_uElimPos_x3f_6701_ = lean_ctor_get(v_toMatcherInfo_6643_, 3);
v_overlaps_6702_ = lean_ctor_get(v_toMatcherInfo_6643_, 5);
v_isSharedCheck_6714_ = !lean_is_exclusive(v_toMatcherInfo_6643_);
if (v_isSharedCheck_6714_ == 0)
{
lean_object* v_unused_6715_; 
v_unused_6715_ = lean_ctor_get(v_toMatcherInfo_6643_, 4);
lean_dec(v_unused_6715_);
v___x_6704_ = v_toMatcherInfo_6643_;
v_isShared_6705_ = v_isSharedCheck_6714_;
goto v_resetjp_6703_;
}
else
{
lean_inc(v_overlaps_6702_);
lean_inc(v_uElimPos_x3f_6701_);
lean_inc(v_altInfos_6700_);
lean_inc(v_numDiscrs_6699_);
lean_inc(v_numParams_6698_);
lean_dec(v_toMatcherInfo_6643_);
v___x_6704_ = lean_box(0);
v_isShared_6705_ = v_isSharedCheck_6714_;
goto v_resetjp_6703_;
}
v_resetjp_6703_:
{
lean_object* v_remaining_x27_6706_; lean_object* v___x_6708_; 
v_remaining_x27_6706_ = l_Array_append___redArg(v___y_6657_, v_a_6694_);
lean_dec(v_a_6694_);
if (v_isShared_6705_ == 0)
{
lean_ctor_set(v___x_6704_, 4, v___y_6653_);
v___x_6708_ = v___x_6704_;
goto v_reusejp_6707_;
}
else
{
lean_object* v_reuseFailAlloc_6713_; 
v_reuseFailAlloc_6713_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6713_, 0, v_numParams_6698_);
lean_ctor_set(v_reuseFailAlloc_6713_, 1, v_numDiscrs_6699_);
lean_ctor_set(v_reuseFailAlloc_6713_, 2, v_altInfos_6700_);
lean_ctor_set(v_reuseFailAlloc_6713_, 3, v_uElimPos_x3f_6701_);
lean_ctor_set(v_reuseFailAlloc_6713_, 4, v___y_6653_);
lean_ctor_set(v_reuseFailAlloc_6713_, 5, v_overlaps_6702_);
v___x_6708_ = v_reuseFailAlloc_6713_;
goto v_reusejp_6707_;
}
v_reusejp_6707_:
{
lean_object* v___x_6709_; lean_object* v___x_6711_; 
v___x_6709_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6709_, 0, v___x_6708_);
lean_ctor_set(v___x_6709_, 1, v_matcherName_6644_);
lean_ctor_set(v___x_6709_, 2, v___y_6655_);
lean_ctor_set(v___x_6709_, 3, v___y_6654_);
lean_ctor_set(v___x_6709_, 4, v___y_6661_);
lean_ctor_set(v___x_6709_, 5, v___y_6660_);
lean_ctor_set(v___x_6709_, 6, v_fst_6692_);
lean_ctor_set(v___x_6709_, 7, v_remaining_x27_6706_);
if (v_isShared_6697_ == 0)
{
lean_ctor_set(v___x_6696_, 0, v___x_6709_);
v___x_6711_ = v___x_6696_;
goto v_reusejp_6710_;
}
else
{
lean_object* v_reuseFailAlloc_6712_; 
v_reuseFailAlloc_6712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6712_, 0, v___x_6709_);
v___x_6711_ = v_reuseFailAlloc_6712_;
goto v_reusejp_6710_;
}
v_reusejp_6710_:
{
return v___x_6711_;
}
}
}
}
}
else
{
lean_object* v_a_6717_; lean_object* v___x_6719_; uint8_t v_isShared_6720_; uint8_t v_isSharedCheck_6724_; 
lean_dec(v_fst_6692_);
lean_dec_ref(v___y_6661_);
lean_dec_ref(v___y_6660_);
lean_dec(v___y_6657_);
lean_dec_ref(v___y_6655_);
lean_dec_ref(v___y_6654_);
lean_dec_ref(v___y_6653_);
lean_dec(v_matcherName_6644_);
lean_dec_ref(v_toMatcherInfo_6643_);
v_a_6717_ = lean_ctor_get(v___x_6693_, 0);
v_isSharedCheck_6724_ = !lean_is_exclusive(v___x_6693_);
if (v_isSharedCheck_6724_ == 0)
{
v___x_6719_ = v___x_6693_;
v_isShared_6720_ = v_isSharedCheck_6724_;
goto v_resetjp_6718_;
}
else
{
lean_inc(v_a_6717_);
lean_dec(v___x_6693_);
v___x_6719_ = lean_box(0);
v_isShared_6720_ = v_isSharedCheck_6724_;
goto v_resetjp_6718_;
}
v_resetjp_6718_:
{
lean_object* v___x_6722_; 
if (v_isShared_6720_ == 0)
{
v___x_6722_ = v___x_6719_;
goto v_reusejp_6721_;
}
else
{
lean_object* v_reuseFailAlloc_6723_; 
v_reuseFailAlloc_6723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6723_, 0, v_a_6717_);
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
else
{
lean_object* v_a_6725_; lean_object* v___x_6727_; uint8_t v_isShared_6728_; uint8_t v_isSharedCheck_6732_; 
lean_dec_ref(v___y_6661_);
lean_dec_ref(v___y_6660_);
lean_dec(v___y_6657_);
lean_dec_ref(v___y_6655_);
lean_dec_ref(v___y_6654_);
lean_dec_ref(v___y_6653_);
lean_dec_ref(v_remaining_6650_);
lean_dec(v_matcherName_6644_);
lean_dec_ref(v_toMatcherInfo_6643_);
lean_dec_ref(v_onRemaining_6635_);
v_a_6725_ = lean_ctor_get(v___x_6690_, 0);
v_isSharedCheck_6732_ = !lean_is_exclusive(v___x_6690_);
if (v_isSharedCheck_6732_ == 0)
{
v___x_6727_ = v___x_6690_;
v_isShared_6728_ = v_isSharedCheck_6732_;
goto v_resetjp_6726_;
}
else
{
lean_inc(v_a_6725_);
lean_dec(v___x_6690_);
v___x_6727_ = lean_box(0);
v_isShared_6728_ = v_isSharedCheck_6732_;
goto v_resetjp_6726_;
}
v_resetjp_6726_:
{
lean_object* v___x_6730_; 
if (v_isShared_6728_ == 0)
{
v___x_6730_ = v___x_6727_;
goto v_reusejp_6729_;
}
else
{
lean_object* v_reuseFailAlloc_6731_; 
v_reuseFailAlloc_6731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6731_, 0, v_a_6725_);
v___x_6730_ = v_reuseFailAlloc_6731_;
goto v_reusejp_6729_;
}
v_reusejp_6729_:
{
return v___x_6730_;
}
}
}
}
else
{
lean_object* v_a_6733_; lean_object* v___x_6735_; uint8_t v_isShared_6736_; uint8_t v_isSharedCheck_6740_; 
lean_dec(v___y_6664_);
lean_dec_ref(v___y_6661_);
lean_dec_ref(v___y_6660_);
lean_dec(v___y_6657_);
lean_dec_ref(v___y_6655_);
lean_dec_ref(v___y_6654_);
lean_dec_ref(v___y_6653_);
lean_dec(v___y_6652_);
lean_dec_ref(v_remaining_6650_);
lean_dec_ref(v_alts_6649_);
lean_dec(v_matcherName_6644_);
lean_dec_ref(v_toMatcherInfo_6643_);
lean_dec_ref(v_onRemaining_6635_);
lean_dec_ref(v_onAlt_6634_);
lean_dec_ref(v_matcherApp_6628_);
v_a_6733_ = lean_ctor_get(v___x_6679_, 0);
v_isSharedCheck_6740_ = !lean_is_exclusive(v___x_6679_);
if (v_isSharedCheck_6740_ == 0)
{
v___x_6735_ = v___x_6679_;
v_isShared_6736_ = v_isSharedCheck_6740_;
goto v_resetjp_6734_;
}
else
{
lean_inc(v_a_6733_);
lean_dec(v___x_6679_);
v___x_6735_ = lean_box(0);
v_isShared_6736_ = v_isSharedCheck_6740_;
goto v_resetjp_6734_;
}
v_resetjp_6734_:
{
lean_object* v___x_6738_; 
if (v_isShared_6736_ == 0)
{
v___x_6738_ = v___x_6735_;
goto v_reusejp_6737_;
}
else
{
lean_object* v_reuseFailAlloc_6739_; 
v_reuseFailAlloc_6739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6739_, 0, v_a_6733_);
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
else
{
lean_object* v_a_6741_; lean_object* v___x_6743_; uint8_t v_isShared_6744_; uint8_t v_isSharedCheck_6748_; 
lean_dec_ref(v_aux_6669_);
lean_dec(v___y_6664_);
lean_dec_ref(v___y_6661_);
lean_dec_ref(v___y_6660_);
lean_dec(v___y_6657_);
lean_dec_ref(v___y_6655_);
lean_dec_ref(v___y_6654_);
lean_dec_ref(v___y_6653_);
lean_dec(v___y_6652_);
lean_dec_ref(v_remaining_6650_);
lean_dec_ref(v_alts_6649_);
lean_dec(v_matcherName_6644_);
lean_dec_ref(v_toMatcherInfo_6643_);
lean_dec_ref(v_onRemaining_6635_);
lean_dec_ref(v_onAlt_6634_);
lean_dec_ref(v_matcherApp_6628_);
v_a_6741_ = lean_ctor_get(v___x_6677_, 0);
v_isSharedCheck_6748_ = !lean_is_exclusive(v___x_6677_);
if (v_isSharedCheck_6748_ == 0)
{
v___x_6743_ = v___x_6677_;
v_isShared_6744_ = v_isSharedCheck_6748_;
goto v_resetjp_6742_;
}
else
{
lean_inc(v_a_6741_);
lean_dec(v___x_6677_);
v___x_6743_ = lean_box(0);
v_isShared_6744_ = v_isSharedCheck_6748_;
goto v_resetjp_6742_;
}
v_resetjp_6742_:
{
lean_object* v___x_6746_; 
if (v_isShared_6744_ == 0)
{
v___x_6746_ = v___x_6743_;
goto v_reusejp_6745_;
}
else
{
lean_object* v_reuseFailAlloc_6747_; 
v_reuseFailAlloc_6747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6747_, 0, v_a_6741_);
v___x_6746_ = v_reuseFailAlloc_6747_;
goto v_reusejp_6745_;
}
v_reusejp_6745_:
{
return v___x_6746_;
}
}
}
}
v___jp_6750_:
{
lean_object* v___x_6763_; lean_object* v_remaining_x27_6764_; lean_object* v___x_6765_; lean_object* v___x_6766_; lean_object* v___x_6767_; lean_object* v___x_6768_; lean_object* v___x_6769_; lean_object* v___x_6770_; size_t v_sz_6771_; lean_object* v___x_6772_; 
v___x_6763_ = lean_unsigned_to_nat(0u);
v_remaining_x27_6764_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_6765_ = l_Array_reverse___redArg(v___y_6757_);
v___x_6766_ = lean_array_get_size(v___x_6765_);
v___x_6767_ = l_Array_toSubarray___redArg(v___x_6765_, v___x_6763_, v___x_6766_);
lean_inc_ref(v___y_6752_);
v___x_6768_ = l_Array_reverse___redArg(v___y_6752_);
v___x_6769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6769_, 0, v___x_6763_);
lean_ctor_set(v___x_6769_, 1, v___x_6767_);
v___x_6770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6770_, 0, v_remaining_x27_6764_);
lean_ctor_set(v___x_6770_, 1, v___x_6769_);
v_sz_6771_ = lean_array_size(v___x_6768_);
v___x_6772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(v___x_6768_, v_sz_6771_, v___y_6755_, v___x_6770_, v___y_6759_, v___y_6760_, v___y_6761_, v___y_6762_);
lean_dec_ref(v___x_6768_);
if (lean_obj_tag(v___x_6772_) == 0)
{
lean_object* v_a_6773_; lean_object* v_snd_6774_; 
v_a_6773_ = lean_ctor_get(v___x_6772_, 0);
lean_inc(v_a_6773_);
lean_dec_ref_known(v___x_6772_, 1);
v_snd_6774_ = lean_ctor_get(v_a_6773_, 1);
lean_inc(v_snd_6774_);
if (v_useSplitter_6629_ == 0)
{
lean_object* v_fst_6775_; lean_object* v_fst_6776_; 
lean_dec(v___y_6756_);
v_fst_6775_ = lean_ctor_get(v_a_6773_, 0);
lean_inc(v_fst_6775_);
lean_dec(v_a_6773_);
v_fst_6776_ = lean_ctor_get(v_snd_6774_, 0);
lean_inc(v_fst_6776_);
lean_dec(v_snd_6774_);
v___y_6652_ = v_fst_6776_;
v___y_6653_ = v___y_6751_;
v___y_6654_ = v___y_6754_;
v___y_6655_ = v_matcherLevels_6758_;
v___y_6656_ = v___y_6761_;
v___y_6657_ = v_fst_6775_;
v___y_6658_ = v___y_6760_;
v___y_6659_ = v___y_6762_;
v___y_6660_ = v___y_6752_;
v___y_6661_ = v___y_6753_;
v___y_6662_ = v_remaining_x27_6764_;
v___y_6663_ = v___y_6759_;
v___y_6664_ = v___x_6763_;
goto v___jp_6651_;
}
else
{
if (v_isCasesOn_6749_ == 0)
{
lean_object* v___x_6778_; uint8_t v_isShared_6779_; uint8_t v_isSharedCheck_6936_; 
v_isSharedCheck_6936_ = !lean_is_exclusive(v_matcherApp_6628_);
if (v_isSharedCheck_6936_ == 0)
{
lean_object* v_unused_6937_; lean_object* v_unused_6938_; lean_object* v_unused_6939_; lean_object* v_unused_6940_; lean_object* v_unused_6941_; lean_object* v_unused_6942_; lean_object* v_unused_6943_; lean_object* v_unused_6944_; 
v_unused_6937_ = lean_ctor_get(v_matcherApp_6628_, 7);
lean_dec(v_unused_6937_);
v_unused_6938_ = lean_ctor_get(v_matcherApp_6628_, 6);
lean_dec(v_unused_6938_);
v_unused_6939_ = lean_ctor_get(v_matcherApp_6628_, 5);
lean_dec(v_unused_6939_);
v_unused_6940_ = lean_ctor_get(v_matcherApp_6628_, 4);
lean_dec(v_unused_6940_);
v_unused_6941_ = lean_ctor_get(v_matcherApp_6628_, 3);
lean_dec(v_unused_6941_);
v_unused_6942_ = lean_ctor_get(v_matcherApp_6628_, 2);
lean_dec(v_unused_6942_);
v_unused_6943_ = lean_ctor_get(v_matcherApp_6628_, 1);
lean_dec(v_unused_6943_);
v_unused_6944_ = lean_ctor_get(v_matcherApp_6628_, 0);
lean_dec(v_unused_6944_);
v___x_6778_ = v_matcherApp_6628_;
v_isShared_6779_ = v_isSharedCheck_6936_;
goto v_resetjp_6777_;
}
else
{
lean_dec(v_matcherApp_6628_);
v___x_6778_ = lean_box(0);
v_isShared_6779_ = v_isSharedCheck_6936_;
goto v_resetjp_6777_;
}
v_resetjp_6777_:
{
lean_object* v_fst_6780_; lean_object* v___x_6782_; uint8_t v_isShared_6783_; uint8_t v_isSharedCheck_6934_; 
v_fst_6780_ = lean_ctor_get(v_a_6773_, 0);
v_isSharedCheck_6934_ = !lean_is_exclusive(v_a_6773_);
if (v_isSharedCheck_6934_ == 0)
{
lean_object* v_unused_6935_; 
v_unused_6935_ = lean_ctor_get(v_a_6773_, 1);
lean_dec(v_unused_6935_);
v___x_6782_ = v_a_6773_;
v_isShared_6783_ = v_isSharedCheck_6934_;
goto v_resetjp_6781_;
}
else
{
lean_inc(v_fst_6780_);
lean_dec(v_a_6773_);
v___x_6782_ = lean_box(0);
v_isShared_6783_ = v_isSharedCheck_6934_;
goto v_resetjp_6781_;
}
v_resetjp_6781_:
{
lean_object* v_fst_6784_; lean_object* v___x_6786_; uint8_t v_isShared_6787_; uint8_t v_isSharedCheck_6932_; 
v_fst_6784_ = lean_ctor_get(v_snd_6774_, 0);
v_isSharedCheck_6932_ = !lean_is_exclusive(v_snd_6774_);
if (v_isSharedCheck_6932_ == 0)
{
lean_object* v_unused_6933_; 
v_unused_6933_ = lean_ctor_get(v_snd_6774_, 1);
lean_dec(v_unused_6933_);
v___x_6786_ = v_snd_6774_;
v_isShared_6787_ = v_isSharedCheck_6932_;
goto v_resetjp_6785_;
}
else
{
lean_inc(v_fst_6784_);
lean_dec(v_snd_6774_);
v___x_6786_ = lean_box(0);
v_isShared_6787_ = v_isSharedCheck_6932_;
goto v_resetjp_6785_;
}
v_resetjp_6785_:
{
lean_object* v___x_6788_; lean_object* v___x_6789_; lean_object* v_aux1_6790_; lean_object* v_aux1_6791_; lean_object* v_aux1_6792_; lean_object* v___x_6793_; lean_object* v___x_6794_; lean_object* v___x_6795_; lean_object* v___x_6796_; lean_object* v___x_6797_; lean_object* v___f_6798_; uint8_t v___x_6799_; lean_object* v___x_6800_; lean_object* v___x_6801_; lean_object* v___x_6802_; 
lean_inc_ref(v_matcherLevels_6758_);
v___x_6788_ = lean_array_to_list(v_matcherLevels_6758_);
lean_inc(v___x_6788_);
lean_inc(v_matcherName_6644_);
v___x_6789_ = l_Lean_mkConst(v_matcherName_6644_, v___x_6788_);
v_aux1_6790_ = l_Lean_mkAppN(v___x_6789_, v___y_6754_);
lean_inc_ref(v___y_6753_);
v_aux1_6791_ = l_Lean_Expr_app___override(v_aux1_6790_, v___y_6753_);
v_aux1_6792_ = l_Lean_mkAppN(v_aux1_6791_, v___y_6752_);
v___x_6793_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__3);
lean_inc_ref_n(v_aux1_6792_, 2);
v___x_6794_ = l_Lean_indentExpr(v_aux1_6792_);
v___x_6795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6795_, 0, v___x_6793_);
lean_ctor_set(v___x_6795_, 1, v___x_6794_);
v___x_6796_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__57___closed__5);
v___x_6797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6797_, 0, v___x_6795_);
lean_ctor_set(v___x_6797_, 1, v___x_6796_);
v___f_6798_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34), 2, 1);
lean_closure_set(v___f_6798_, 0, v___x_6797_);
v___x_6799_ = 0;
v___x_6800_ = lean_box(v___x_6799_);
v___x_6801_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6801_, 0, v_aux1_6792_);
lean_closure_set(v___x_6801_, 1, v___x_6800_);
v___x_6802_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6801_, v___f_6798_, v___y_6759_, v___y_6760_, v___y_6761_, v___y_6762_);
if (lean_obj_tag(v___x_6802_) == 0)
{
lean_object* v___x_6803_; lean_object* v___x_6804_; 
lean_dec_ref_known(v___x_6802_, 1);
v___x_6803_ = lean_array_get_size(v_alts_6649_);
v___x_6804_ = l_Lean_Meta_inferArgumentTypesN(v___x_6803_, v_aux1_6792_, v___y_6759_, v___y_6760_, v___y_6761_, v___y_6762_);
if (lean_obj_tag(v___x_6804_) == 0)
{
lean_object* v_a_6805_; lean_object* v___x_6806_; 
v_a_6805_ = lean_ctor_get(v___x_6804_, 0);
lean_inc(v_a_6805_);
lean_dec_ref_known(v___x_6804_, 1);
lean_inc(v___y_6762_);
lean_inc_ref(v___y_6761_);
lean_inc(v___y_6760_);
lean_inc_ref(v___y_6759_);
v___x_6806_ = lean_get_match_equations_for(v_matcherName_6644_, v___y_6759_, v___y_6760_, v___y_6761_, v___y_6762_);
if (lean_obj_tag(v___x_6806_) == 0)
{
lean_object* v_a_6807_; lean_object* v_splitterName_6808_; lean_object* v_splitterMatchInfo_6809_; lean_object* v___x_6810_; lean_object* v_aux2_6811_; lean_object* v_aux2_6812_; lean_object* v_aux2_6813_; lean_object* v___x_6814_; lean_object* v___x_6815_; lean_object* v___x_6816_; lean_object* v___x_6817_; lean_object* v___f_6818_; lean_object* v___x_6819_; lean_object* v___x_6820_; lean_object* v___x_6821_; 
v_a_6807_ = lean_ctor_get(v___x_6806_, 0);
lean_inc(v_a_6807_);
lean_dec_ref_known(v___x_6806_, 1);
v_splitterName_6808_ = lean_ctor_get(v_a_6807_, 1);
lean_inc_n(v_splitterName_6808_, 2);
v_splitterMatchInfo_6809_ = lean_ctor_get(v_a_6807_, 2);
lean_inc_ref(v_splitterMatchInfo_6809_);
lean_dec(v_a_6807_);
v___x_6810_ = l_Lean_mkConst(v_splitterName_6808_, v___x_6788_);
v_aux2_6811_ = l_Lean_mkAppN(v___x_6810_, v___y_6754_);
lean_inc_ref(v___y_6753_);
v_aux2_6812_ = l_Lean_Expr_app___override(v_aux2_6811_, v___y_6753_);
v_aux2_6813_ = l_Lean_mkAppN(v_aux2_6812_, v___y_6752_);
v___x_6814_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1);
lean_inc_ref_n(v_aux2_6813_, 2);
v___x_6815_ = l_Lean_indentExpr(v_aux2_6813_);
v___x_6816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6816_, 0, v___x_6814_);
lean_ctor_set(v___x_6816_, 1, v___x_6815_);
v___x_6817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6817_, 0, v___x_6816_);
lean_ctor_set(v___x_6817_, 1, v___x_6796_);
v___f_6818_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34), 2, 1);
lean_closure_set(v___f_6818_, 0, v___x_6817_);
v___x_6819_ = lean_box(v___x_6799_);
v___x_6820_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6820_, 0, v_aux2_6813_);
lean_closure_set(v___x_6820_, 1, v___x_6819_);
v___x_6821_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6820_, v___f_6818_, v___y_6759_, v___y_6760_, v___y_6761_, v___y_6762_);
if (lean_obj_tag(v___x_6821_) == 0)
{
lean_object* v___x_6822_; 
lean_dec_ref_known(v___x_6821_, 1);
v___x_6822_ = l_Lean_Meta_inferArgumentTypesN(v___x_6803_, v_aux2_6813_, v___y_6759_, v___y_6760_, v___y_6761_, v___y_6762_);
if (lean_obj_tag(v___x_6822_) == 0)
{
lean_object* v_a_6823_; lean_object* v_numParams_6824_; lean_object* v_numDiscrs_6825_; lean_object* v_altInfos_6826_; lean_object* v_uElimPos_x3f_6827_; lean_object* v_overlaps_6828_; lean_object* v_altInfos_6829_; lean_object* v___x_6831_; uint8_t v_isShared_6832_; uint8_t v_isSharedCheck_6886_; 
v_a_6823_ = lean_ctor_get(v___x_6822_, 0);
lean_inc(v_a_6823_);
lean_dec_ref_known(v___x_6822_, 1);
v_numParams_6824_ = lean_ctor_get(v_toMatcherInfo_6643_, 0);
lean_inc(v_numParams_6824_);
v_numDiscrs_6825_ = lean_ctor_get(v_toMatcherInfo_6643_, 1);
lean_inc(v_numDiscrs_6825_);
v_altInfos_6826_ = lean_ctor_get(v_toMatcherInfo_6643_, 2);
lean_inc_ref(v_altInfos_6826_);
v_uElimPos_x3f_6827_ = lean_ctor_get(v_toMatcherInfo_6643_, 3);
lean_inc(v_uElimPos_x3f_6827_);
v_overlaps_6828_ = lean_ctor_get(v_toMatcherInfo_6643_, 5);
lean_inc_ref(v_overlaps_6828_);
lean_dec_ref(v_toMatcherInfo_6643_);
v_altInfos_6829_ = lean_ctor_get(v_splitterMatchInfo_6809_, 2);
v_isSharedCheck_6886_ = !lean_is_exclusive(v_splitterMatchInfo_6809_);
if (v_isSharedCheck_6886_ == 0)
{
lean_object* v_unused_6887_; lean_object* v_unused_6888_; lean_object* v_unused_6889_; lean_object* v_unused_6890_; lean_object* v_unused_6891_; 
v_unused_6887_ = lean_ctor_get(v_splitterMatchInfo_6809_, 5);
lean_dec(v_unused_6887_);
v_unused_6888_ = lean_ctor_get(v_splitterMatchInfo_6809_, 4);
lean_dec(v_unused_6888_);
v_unused_6889_ = lean_ctor_get(v_splitterMatchInfo_6809_, 3);
lean_dec(v_unused_6889_);
v_unused_6890_ = lean_ctor_get(v_splitterMatchInfo_6809_, 1);
lean_dec(v_unused_6890_);
v_unused_6891_ = lean_ctor_get(v_splitterMatchInfo_6809_, 0);
lean_dec(v_unused_6891_);
v___x_6831_ = v_splitterMatchInfo_6809_;
v_isShared_6832_ = v_isSharedCheck_6886_;
goto v_resetjp_6830_;
}
else
{
lean_inc(v_altInfos_6829_);
lean_dec(v_splitterMatchInfo_6809_);
v___x_6831_ = lean_box(0);
v_isShared_6832_ = v_isSharedCheck_6886_;
goto v_resetjp_6830_;
}
v_resetjp_6830_:
{
lean_object* v___x_6833_; lean_object* v___x_6834_; lean_object* v___x_6835_; lean_object* v___x_6836_; lean_object* v___x_6837_; lean_object* v___x_6838_; lean_object* v___x_6839_; lean_object* v___x_6840_; lean_object* v___x_6841_; lean_object* v___x_6843_; 
v___x_6833_ = lean_array_get_size(v_altInfos_6826_);
v___x_6834_ = lean_array_get_size(v_altInfos_6829_);
v___x_6835_ = lean_array_get_size(v_a_6805_);
v___x_6836_ = lean_array_get_size(v_a_6823_);
v___x_6837_ = l_Array_toSubarray___redArg(v_alts_6649_, v___x_6763_, v___x_6803_);
lean_inc_ref(v_altInfos_6826_);
v___x_6838_ = l_Array_toSubarray___redArg(v_altInfos_6826_, v___x_6763_, v___x_6833_);
v___x_6839_ = l_Array_toSubarray___redArg(v_altInfos_6829_, v___x_6763_, v___x_6834_);
v___x_6840_ = l_Array_toSubarray___redArg(v_a_6805_, v___x_6763_, v___x_6835_);
v___x_6841_ = l_Array_toSubarray___redArg(v_a_6823_, v___x_6763_, v___x_6836_);
if (v_isShared_6787_ == 0)
{
lean_ctor_set(v___x_6786_, 1, v___x_6841_);
lean_ctor_set(v___x_6786_, 0, v___x_6840_);
v___x_6843_ = v___x_6786_;
goto v_reusejp_6842_;
}
else
{
lean_object* v_reuseFailAlloc_6885_; 
v_reuseFailAlloc_6885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6885_, 0, v___x_6840_);
lean_ctor_set(v_reuseFailAlloc_6885_, 1, v___x_6841_);
v___x_6843_ = v_reuseFailAlloc_6885_;
goto v_reusejp_6842_;
}
v_reusejp_6842_:
{
lean_object* v___x_6845_; 
if (v_isShared_6783_ == 0)
{
lean_ctor_set(v___x_6782_, 1, v___x_6843_);
lean_ctor_set(v___x_6782_, 0, v___x_6839_);
v___x_6845_ = v___x_6782_;
goto v_reusejp_6844_;
}
else
{
lean_object* v_reuseFailAlloc_6884_; 
v_reuseFailAlloc_6884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6884_, 0, v___x_6839_);
lean_ctor_set(v_reuseFailAlloc_6884_, 1, v___x_6843_);
v___x_6845_ = v_reuseFailAlloc_6884_;
goto v_reusejp_6844_;
}
v_reusejp_6844_:
{
lean_object* v___x_6846_; lean_object* v___x_6847_; lean_object* v___x_6848_; lean_object* v___x_6849_; 
v___x_6846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6846_, 0, v___x_6838_);
lean_ctor_set(v___x_6846_, 1, v___x_6845_);
v___x_6847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6847_, 0, v___x_6837_);
lean_ctor_set(v___x_6847_, 1, v___x_6846_);
v___x_6848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6848_, 0, v_remaining_x27_6764_);
lean_ctor_set(v___x_6848_, 1, v___x_6847_);
v___x_6849_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v___x_6803_, v_onAlt_6634_, v_useSplitter_6629_, v_fst_6784_, v___y_6756_, v___x_6763_, v___x_6848_, v___y_6759_, v___y_6760_, v___y_6761_, v___y_6762_);
if (lean_obj_tag(v___x_6849_) == 0)
{
lean_object* v_a_6850_; lean_object* v_fst_6851_; lean_object* v___x_6852_; 
v_a_6850_ = lean_ctor_get(v___x_6849_, 0);
lean_inc(v_a_6850_);
lean_dec_ref_known(v___x_6849_, 1);
v_fst_6851_ = lean_ctor_get(v_a_6850_, 0);
lean_inc(v_fst_6851_);
lean_dec(v_a_6850_);
lean_inc(v___y_6762_);
lean_inc_ref(v___y_6761_);
lean_inc(v___y_6760_);
lean_inc_ref(v___y_6759_);
v___x_6852_ = lean_apply_6(v_onRemaining_6635_, v_remaining_6650_, v___y_6759_, v___y_6760_, v___y_6761_, v___y_6762_, lean_box(0));
if (lean_obj_tag(v___x_6852_) == 0)
{
lean_object* v_a_6853_; lean_object* v___x_6855_; uint8_t v_isShared_6856_; uint8_t v_isSharedCheck_6867_; 
v_a_6853_ = lean_ctor_get(v___x_6852_, 0);
v_isSharedCheck_6867_ = !lean_is_exclusive(v___x_6852_);
if (v_isSharedCheck_6867_ == 0)
{
v___x_6855_ = v___x_6852_;
v_isShared_6856_ = v_isSharedCheck_6867_;
goto v_resetjp_6854_;
}
else
{
lean_inc(v_a_6853_);
lean_dec(v___x_6852_);
v___x_6855_ = lean_box(0);
v_isShared_6856_ = v_isSharedCheck_6867_;
goto v_resetjp_6854_;
}
v_resetjp_6854_:
{
lean_object* v_remaining_x27_6857_; lean_object* v___x_6859_; 
v_remaining_x27_6857_ = l_Array_append___redArg(v_fst_6780_, v_a_6853_);
lean_dec(v_a_6853_);
if (v_isShared_6832_ == 0)
{
lean_ctor_set(v___x_6831_, 5, v_overlaps_6828_);
lean_ctor_set(v___x_6831_, 4, v___y_6751_);
lean_ctor_set(v___x_6831_, 3, v_uElimPos_x3f_6827_);
lean_ctor_set(v___x_6831_, 2, v_altInfos_6826_);
lean_ctor_set(v___x_6831_, 1, v_numDiscrs_6825_);
lean_ctor_set(v___x_6831_, 0, v_numParams_6824_);
v___x_6859_ = v___x_6831_;
goto v_reusejp_6858_;
}
else
{
lean_object* v_reuseFailAlloc_6866_; 
v_reuseFailAlloc_6866_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6866_, 0, v_numParams_6824_);
lean_ctor_set(v_reuseFailAlloc_6866_, 1, v_numDiscrs_6825_);
lean_ctor_set(v_reuseFailAlloc_6866_, 2, v_altInfos_6826_);
lean_ctor_set(v_reuseFailAlloc_6866_, 3, v_uElimPos_x3f_6827_);
lean_ctor_set(v_reuseFailAlloc_6866_, 4, v___y_6751_);
lean_ctor_set(v_reuseFailAlloc_6866_, 5, v_overlaps_6828_);
v___x_6859_ = v_reuseFailAlloc_6866_;
goto v_reusejp_6858_;
}
v_reusejp_6858_:
{
lean_object* v___x_6861_; 
if (v_isShared_6779_ == 0)
{
lean_ctor_set(v___x_6778_, 7, v_remaining_x27_6857_);
lean_ctor_set(v___x_6778_, 6, v_fst_6851_);
lean_ctor_set(v___x_6778_, 5, v___y_6752_);
lean_ctor_set(v___x_6778_, 4, v___y_6753_);
lean_ctor_set(v___x_6778_, 3, v___y_6754_);
lean_ctor_set(v___x_6778_, 2, v_matcherLevels_6758_);
lean_ctor_set(v___x_6778_, 1, v_splitterName_6808_);
lean_ctor_set(v___x_6778_, 0, v___x_6859_);
v___x_6861_ = v___x_6778_;
goto v_reusejp_6860_;
}
else
{
lean_object* v_reuseFailAlloc_6865_; 
v_reuseFailAlloc_6865_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_6865_, 0, v___x_6859_);
lean_ctor_set(v_reuseFailAlloc_6865_, 1, v_splitterName_6808_);
lean_ctor_set(v_reuseFailAlloc_6865_, 2, v_matcherLevels_6758_);
lean_ctor_set(v_reuseFailAlloc_6865_, 3, v___y_6754_);
lean_ctor_set(v_reuseFailAlloc_6865_, 4, v___y_6753_);
lean_ctor_set(v_reuseFailAlloc_6865_, 5, v___y_6752_);
lean_ctor_set(v_reuseFailAlloc_6865_, 6, v_fst_6851_);
lean_ctor_set(v_reuseFailAlloc_6865_, 7, v_remaining_x27_6857_);
v___x_6861_ = v_reuseFailAlloc_6865_;
goto v_reusejp_6860_;
}
v_reusejp_6860_:
{
lean_object* v___x_6863_; 
if (v_isShared_6856_ == 0)
{
lean_ctor_set(v___x_6855_, 0, v___x_6861_);
v___x_6863_ = v___x_6855_;
goto v_reusejp_6862_;
}
else
{
lean_object* v_reuseFailAlloc_6864_; 
v_reuseFailAlloc_6864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6864_, 0, v___x_6861_);
v___x_6863_ = v_reuseFailAlloc_6864_;
goto v_reusejp_6862_;
}
v_reusejp_6862_:
{
return v___x_6863_;
}
}
}
}
}
else
{
lean_object* v_a_6868_; lean_object* v___x_6870_; uint8_t v_isShared_6871_; uint8_t v_isSharedCheck_6875_; 
lean_dec(v_fst_6851_);
lean_del_object(v___x_6831_);
lean_dec_ref(v_overlaps_6828_);
lean_dec(v_uElimPos_x3f_6827_);
lean_dec_ref(v_altInfos_6826_);
lean_dec(v_numDiscrs_6825_);
lean_dec(v_numParams_6824_);
lean_dec(v_splitterName_6808_);
lean_dec(v_fst_6780_);
lean_del_object(v___x_6778_);
lean_dec_ref(v_matcherLevels_6758_);
lean_dec_ref(v___y_6754_);
lean_dec_ref(v___y_6753_);
lean_dec_ref(v___y_6752_);
lean_dec_ref(v___y_6751_);
v_a_6868_ = lean_ctor_get(v___x_6852_, 0);
v_isSharedCheck_6875_ = !lean_is_exclusive(v___x_6852_);
if (v_isSharedCheck_6875_ == 0)
{
v___x_6870_ = v___x_6852_;
v_isShared_6871_ = v_isSharedCheck_6875_;
goto v_resetjp_6869_;
}
else
{
lean_inc(v_a_6868_);
lean_dec(v___x_6852_);
v___x_6870_ = lean_box(0);
v_isShared_6871_ = v_isSharedCheck_6875_;
goto v_resetjp_6869_;
}
v_resetjp_6869_:
{
lean_object* v___x_6873_; 
if (v_isShared_6871_ == 0)
{
v___x_6873_ = v___x_6870_;
goto v_reusejp_6872_;
}
else
{
lean_object* v_reuseFailAlloc_6874_; 
v_reuseFailAlloc_6874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6874_, 0, v_a_6868_);
v___x_6873_ = v_reuseFailAlloc_6874_;
goto v_reusejp_6872_;
}
v_reusejp_6872_:
{
return v___x_6873_;
}
}
}
}
else
{
lean_object* v_a_6876_; lean_object* v___x_6878_; uint8_t v_isShared_6879_; uint8_t v_isSharedCheck_6883_; 
lean_del_object(v___x_6831_);
lean_dec_ref(v_overlaps_6828_);
lean_dec(v_uElimPos_x3f_6827_);
lean_dec_ref(v_altInfos_6826_);
lean_dec(v_numDiscrs_6825_);
lean_dec(v_numParams_6824_);
lean_dec(v_splitterName_6808_);
lean_dec(v_fst_6780_);
lean_del_object(v___x_6778_);
lean_dec_ref(v_matcherLevels_6758_);
lean_dec_ref(v___y_6754_);
lean_dec_ref(v___y_6753_);
lean_dec_ref(v___y_6752_);
lean_dec_ref(v___y_6751_);
lean_dec_ref(v_remaining_6650_);
lean_dec_ref(v_onRemaining_6635_);
v_a_6876_ = lean_ctor_get(v___x_6849_, 0);
v_isSharedCheck_6883_ = !lean_is_exclusive(v___x_6849_);
if (v_isSharedCheck_6883_ == 0)
{
v___x_6878_ = v___x_6849_;
v_isShared_6879_ = v_isSharedCheck_6883_;
goto v_resetjp_6877_;
}
else
{
lean_inc(v_a_6876_);
lean_dec(v___x_6849_);
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
}
}
}
else
{
lean_object* v_a_6892_; lean_object* v___x_6894_; uint8_t v_isShared_6895_; uint8_t v_isSharedCheck_6899_; 
lean_dec_ref(v_splitterMatchInfo_6809_);
lean_dec(v_splitterName_6808_);
lean_dec(v_a_6805_);
lean_del_object(v___x_6786_);
lean_dec(v_fst_6784_);
lean_del_object(v___x_6782_);
lean_dec(v_fst_6780_);
lean_del_object(v___x_6778_);
lean_dec_ref(v_matcherLevels_6758_);
lean_dec(v___y_6756_);
lean_dec_ref(v___y_6754_);
lean_dec_ref(v___y_6753_);
lean_dec_ref(v___y_6752_);
lean_dec_ref(v___y_6751_);
lean_dec_ref(v_remaining_6650_);
lean_dec_ref(v_alts_6649_);
lean_dec_ref(v_toMatcherInfo_6643_);
lean_dec_ref(v_onRemaining_6635_);
lean_dec_ref(v_onAlt_6634_);
v_a_6892_ = lean_ctor_get(v___x_6822_, 0);
v_isSharedCheck_6899_ = !lean_is_exclusive(v___x_6822_);
if (v_isSharedCheck_6899_ == 0)
{
v___x_6894_ = v___x_6822_;
v_isShared_6895_ = v_isSharedCheck_6899_;
goto v_resetjp_6893_;
}
else
{
lean_inc(v_a_6892_);
lean_dec(v___x_6822_);
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
else
{
lean_object* v_a_6900_; lean_object* v___x_6902_; uint8_t v_isShared_6903_; uint8_t v_isSharedCheck_6907_; 
lean_dec_ref(v_aux2_6813_);
lean_dec_ref(v_splitterMatchInfo_6809_);
lean_dec(v_splitterName_6808_);
lean_dec(v_a_6805_);
lean_del_object(v___x_6786_);
lean_dec(v_fst_6784_);
lean_del_object(v___x_6782_);
lean_dec(v_fst_6780_);
lean_del_object(v___x_6778_);
lean_dec_ref(v_matcherLevels_6758_);
lean_dec(v___y_6756_);
lean_dec_ref(v___y_6754_);
lean_dec_ref(v___y_6753_);
lean_dec_ref(v___y_6752_);
lean_dec_ref(v___y_6751_);
lean_dec_ref(v_remaining_6650_);
lean_dec_ref(v_alts_6649_);
lean_dec_ref(v_toMatcherInfo_6643_);
lean_dec_ref(v_onRemaining_6635_);
lean_dec_ref(v_onAlt_6634_);
v_a_6900_ = lean_ctor_get(v___x_6821_, 0);
v_isSharedCheck_6907_ = !lean_is_exclusive(v___x_6821_);
if (v_isSharedCheck_6907_ == 0)
{
v___x_6902_ = v___x_6821_;
v_isShared_6903_ = v_isSharedCheck_6907_;
goto v_resetjp_6901_;
}
else
{
lean_inc(v_a_6900_);
lean_dec(v___x_6821_);
v___x_6902_ = lean_box(0);
v_isShared_6903_ = v_isSharedCheck_6907_;
goto v_resetjp_6901_;
}
v_resetjp_6901_:
{
lean_object* v___x_6905_; 
if (v_isShared_6903_ == 0)
{
v___x_6905_ = v___x_6902_;
goto v_reusejp_6904_;
}
else
{
lean_object* v_reuseFailAlloc_6906_; 
v_reuseFailAlloc_6906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6906_, 0, v_a_6900_);
v___x_6905_ = v_reuseFailAlloc_6906_;
goto v_reusejp_6904_;
}
v_reusejp_6904_:
{
return v___x_6905_;
}
}
}
}
else
{
lean_object* v_a_6908_; lean_object* v___x_6910_; uint8_t v_isShared_6911_; uint8_t v_isSharedCheck_6915_; 
lean_dec(v_a_6805_);
lean_dec(v___x_6788_);
lean_del_object(v___x_6786_);
lean_dec(v_fst_6784_);
lean_del_object(v___x_6782_);
lean_dec(v_fst_6780_);
lean_del_object(v___x_6778_);
lean_dec_ref(v_matcherLevels_6758_);
lean_dec(v___y_6756_);
lean_dec_ref(v___y_6754_);
lean_dec_ref(v___y_6753_);
lean_dec_ref(v___y_6752_);
lean_dec_ref(v___y_6751_);
lean_dec_ref(v_remaining_6650_);
lean_dec_ref(v_alts_6649_);
lean_dec_ref(v_toMatcherInfo_6643_);
lean_dec_ref(v_onRemaining_6635_);
lean_dec_ref(v_onAlt_6634_);
v_a_6908_ = lean_ctor_get(v___x_6806_, 0);
v_isSharedCheck_6915_ = !lean_is_exclusive(v___x_6806_);
if (v_isSharedCheck_6915_ == 0)
{
v___x_6910_ = v___x_6806_;
v_isShared_6911_ = v_isSharedCheck_6915_;
goto v_resetjp_6909_;
}
else
{
lean_inc(v_a_6908_);
lean_dec(v___x_6806_);
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
}
else
{
lean_object* v_a_6916_; lean_object* v___x_6918_; uint8_t v_isShared_6919_; uint8_t v_isSharedCheck_6923_; 
lean_dec(v___x_6788_);
lean_del_object(v___x_6786_);
lean_dec(v_fst_6784_);
lean_del_object(v___x_6782_);
lean_dec(v_fst_6780_);
lean_del_object(v___x_6778_);
lean_dec_ref(v_matcherLevels_6758_);
lean_dec(v___y_6756_);
lean_dec_ref(v___y_6754_);
lean_dec_ref(v___y_6753_);
lean_dec_ref(v___y_6752_);
lean_dec_ref(v___y_6751_);
lean_dec_ref(v_remaining_6650_);
lean_dec_ref(v_alts_6649_);
lean_dec(v_matcherName_6644_);
lean_dec_ref(v_toMatcherInfo_6643_);
lean_dec_ref(v_onRemaining_6635_);
lean_dec_ref(v_onAlt_6634_);
v_a_6916_ = lean_ctor_get(v___x_6804_, 0);
v_isSharedCheck_6923_ = !lean_is_exclusive(v___x_6804_);
if (v_isSharedCheck_6923_ == 0)
{
v___x_6918_ = v___x_6804_;
v_isShared_6919_ = v_isSharedCheck_6923_;
goto v_resetjp_6917_;
}
else
{
lean_inc(v_a_6916_);
lean_dec(v___x_6804_);
v___x_6918_ = lean_box(0);
v_isShared_6919_ = v_isSharedCheck_6923_;
goto v_resetjp_6917_;
}
v_resetjp_6917_:
{
lean_object* v___x_6921_; 
if (v_isShared_6919_ == 0)
{
v___x_6921_ = v___x_6918_;
goto v_reusejp_6920_;
}
else
{
lean_object* v_reuseFailAlloc_6922_; 
v_reuseFailAlloc_6922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6922_, 0, v_a_6916_);
v___x_6921_ = v_reuseFailAlloc_6922_;
goto v_reusejp_6920_;
}
v_reusejp_6920_:
{
return v___x_6921_;
}
}
}
}
else
{
lean_object* v_a_6924_; lean_object* v___x_6926_; uint8_t v_isShared_6927_; uint8_t v_isSharedCheck_6931_; 
lean_dec_ref(v_aux1_6792_);
lean_dec(v___x_6788_);
lean_del_object(v___x_6786_);
lean_dec(v_fst_6784_);
lean_del_object(v___x_6782_);
lean_dec(v_fst_6780_);
lean_del_object(v___x_6778_);
lean_dec_ref(v_matcherLevels_6758_);
lean_dec(v___y_6756_);
lean_dec_ref(v___y_6754_);
lean_dec_ref(v___y_6753_);
lean_dec_ref(v___y_6752_);
lean_dec_ref(v___y_6751_);
lean_dec_ref(v_remaining_6650_);
lean_dec_ref(v_alts_6649_);
lean_dec(v_matcherName_6644_);
lean_dec_ref(v_toMatcherInfo_6643_);
lean_dec_ref(v_onRemaining_6635_);
lean_dec_ref(v_onAlt_6634_);
v_a_6924_ = lean_ctor_get(v___x_6802_, 0);
v_isSharedCheck_6931_ = !lean_is_exclusive(v___x_6802_);
if (v_isSharedCheck_6931_ == 0)
{
v___x_6926_ = v___x_6802_;
v_isShared_6927_ = v_isSharedCheck_6931_;
goto v_resetjp_6925_;
}
else
{
lean_inc(v_a_6924_);
lean_dec(v___x_6802_);
v___x_6926_ = lean_box(0);
v_isShared_6927_ = v_isSharedCheck_6931_;
goto v_resetjp_6925_;
}
v_resetjp_6925_:
{
lean_object* v___x_6929_; 
if (v_isShared_6927_ == 0)
{
v___x_6929_ = v___x_6926_;
goto v_reusejp_6928_;
}
else
{
lean_object* v_reuseFailAlloc_6930_; 
v_reuseFailAlloc_6930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6930_, 0, v_a_6924_);
v___x_6929_ = v_reuseFailAlloc_6930_;
goto v_reusejp_6928_;
}
v_reusejp_6928_:
{
return v___x_6929_;
}
}
}
}
}
}
}
else
{
lean_object* v_fst_6945_; lean_object* v_fst_6946_; 
lean_dec(v___y_6756_);
v_fst_6945_ = lean_ctor_get(v_a_6773_, 0);
lean_inc(v_fst_6945_);
lean_dec(v_a_6773_);
v_fst_6946_ = lean_ctor_get(v_snd_6774_, 0);
lean_inc(v_fst_6946_);
lean_dec(v_snd_6774_);
v___y_6652_ = v_fst_6946_;
v___y_6653_ = v___y_6751_;
v___y_6654_ = v___y_6754_;
v___y_6655_ = v_matcherLevels_6758_;
v___y_6656_ = v___y_6761_;
v___y_6657_ = v_fst_6945_;
v___y_6658_ = v___y_6760_;
v___y_6659_ = v___y_6762_;
v___y_6660_ = v___y_6752_;
v___y_6661_ = v___y_6753_;
v___y_6662_ = v_remaining_x27_6764_;
v___y_6663_ = v___y_6759_;
v___y_6664_ = v___x_6763_;
goto v___jp_6651_;
}
}
}
else
{
lean_object* v_a_6947_; lean_object* v___x_6949_; uint8_t v_isShared_6950_; uint8_t v_isSharedCheck_6954_; 
lean_dec_ref(v_matcherLevels_6758_);
lean_dec(v___y_6756_);
lean_dec_ref(v___y_6754_);
lean_dec_ref(v___y_6753_);
lean_dec_ref(v___y_6752_);
lean_dec_ref(v___y_6751_);
lean_dec_ref(v_remaining_6650_);
lean_dec_ref(v_alts_6649_);
lean_dec(v_matcherName_6644_);
lean_dec_ref(v_toMatcherInfo_6643_);
lean_dec_ref(v_onRemaining_6635_);
lean_dec_ref(v_onAlt_6634_);
lean_dec_ref(v_matcherApp_6628_);
v_a_6947_ = lean_ctor_get(v___x_6772_, 0);
v_isSharedCheck_6954_ = !lean_is_exclusive(v___x_6772_);
if (v_isSharedCheck_6954_ == 0)
{
v___x_6949_ = v___x_6772_;
v_isShared_6950_ = v_isSharedCheck_6954_;
goto v_resetjp_6948_;
}
else
{
lean_inc(v_a_6947_);
lean_dec(v___x_6772_);
v___x_6949_ = lean_box(0);
v_isShared_6950_ = v_isSharedCheck_6954_;
goto v_resetjp_6948_;
}
v_resetjp_6948_:
{
lean_object* v___x_6952_; 
if (v_isShared_6950_ == 0)
{
v___x_6952_ = v___x_6949_;
goto v_reusejp_6951_;
}
else
{
lean_object* v_reuseFailAlloc_6953_; 
v_reuseFailAlloc_6953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6953_, 0, v_a_6947_);
v___x_6952_ = v_reuseFailAlloc_6953_;
goto v_reusejp_6951_;
}
v_reusejp_6951_:
{
return v___x_6952_;
}
}
}
}
v___jp_6955_:
{
size_t v_sz_6961_; size_t v___x_6962_; lean_object* v___x_6963_; 
v_sz_6961_ = lean_array_size(v_params_6646_);
v___x_6962_ = ((size_t)0ULL);
lean_inc_ref(v_params_6646_);
lean_inc_ref(v_onParams_6632_);
v___x_6963_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6632_, v_sz_6961_, v___x_6962_, v_params_6646_, v___y_6957_, v___y_6958_, v___y_6959_, v___y_6960_);
if (lean_obj_tag(v___x_6963_) == 0)
{
lean_object* v_a_6964_; size_t v_sz_6965_; lean_object* v___x_6966_; 
v_a_6964_ = lean_ctor_get(v___x_6963_, 0);
lean_inc(v_a_6964_);
lean_dec_ref_known(v___x_6963_, 1);
v_sz_6965_ = lean_array_size(v_discrs_6648_);
lean_inc_ref(v_discrs_6648_);
v___x_6966_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6632_, v_sz_6965_, v___x_6962_, v_discrs_6648_, v___y_6957_, v___y_6958_, v___y_6959_, v___y_6960_);
if (lean_obj_tag(v___x_6966_) == 0)
{
lean_object* v_a_6967_; lean_object* v___x_6968_; lean_object* v___x_6969_; lean_object* v___x_6970_; lean_object* v___f_6971_; uint8_t v___x_6972_; lean_object* v___x_6973_; 
v_a_6967_ = lean_ctor_get(v___x_6966_, 0);
lean_inc_n(v_a_6967_, 2);
lean_dec_ref_known(v___x_6966_, 1);
v___x_6968_ = lean_box(v_addEqualities_6630_);
v___x_6969_ = lean_box(v_addProofEqualities_6631_);
v___x_6970_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed__const__1));
lean_inc_ref(v_discrs_6648_);
lean_inc_ref(v_toMatcherInfo_6643_);
v___f_6971_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed), 14, 7);
lean_closure_set(v___f_6971_, 0, v_onMotive_6633_);
lean_closure_set(v___f_6971_, 1, v_toMatcherInfo_6643_);
lean_closure_set(v___f_6971_, 2, v_a_6967_);
lean_closure_set(v___f_6971_, 3, v___x_6968_);
lean_closure_set(v___f_6971_, 4, v___x_6969_);
lean_closure_set(v___f_6971_, 5, v___x_6970_);
lean_closure_set(v___f_6971_, 6, v_discrs_6648_);
v___x_6972_ = 0;
lean_inc_ref(v_motive_6647_);
v___x_6973_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_6647_, v___f_6971_, v___x_6972_, v___y_6957_, v___y_6958_, v___y_6959_, v___y_6960_);
if (lean_obj_tag(v___x_6973_) == 0)
{
lean_object* v_a_6974_; lean_object* v_snd_6975_; lean_object* v_snd_6976_; lean_object* v_uElimPos_x3f_6977_; 
v_a_6974_ = lean_ctor_get(v___x_6973_, 0);
lean_inc(v_a_6974_);
lean_dec_ref_known(v___x_6973_, 1);
v_snd_6975_ = lean_ctor_get(v_a_6974_, 1);
v_snd_6976_ = lean_ctor_get(v_snd_6975_, 1);
lean_inc(v_snd_6976_);
v_uElimPos_x3f_6977_ = lean_ctor_get(v_toMatcherInfo_6643_, 3);
if (lean_obj_tag(v_uElimPos_x3f_6977_) == 0)
{
lean_object* v_fst_6978_; lean_object* v_fst_6979_; lean_object* v_snd_6980_; 
v_fst_6978_ = lean_ctor_get(v_a_6974_, 0);
lean_inc(v_fst_6978_);
lean_dec(v_a_6974_);
v_fst_6979_ = lean_ctor_get(v_snd_6976_, 0);
lean_inc(v_fst_6979_);
v_snd_6980_ = lean_ctor_get(v_snd_6976_, 1);
lean_inc(v_snd_6980_);
lean_dec(v_snd_6976_);
lean_inc_ref(v_matcherLevels_6645_);
v___y_6751_ = v_snd_6980_;
v___y_6752_ = v_a_6967_;
v___y_6753_ = v_fst_6978_;
v___y_6754_ = v_a_6964_;
v___y_6755_ = v___x_6962_;
v___y_6756_ = v_numDiscrEqs_6956_;
v___y_6757_ = v_fst_6979_;
v_matcherLevels_6758_ = v_matcherLevels_6645_;
v___y_6759_ = v___y_6957_;
v___y_6760_ = v___y_6958_;
v___y_6761_ = v___y_6959_;
v___y_6762_ = v___y_6960_;
goto v___jp_6750_;
}
else
{
lean_object* v_fst_6981_; lean_object* v_fst_6982_; lean_object* v_fst_6983_; lean_object* v_snd_6984_; lean_object* v_val_6985_; lean_object* v___x_6986_; 
lean_inc(v_snd_6975_);
v_fst_6981_ = lean_ctor_get(v_a_6974_, 0);
lean_inc(v_fst_6981_);
lean_dec(v_a_6974_);
v_fst_6982_ = lean_ctor_get(v_snd_6975_, 0);
lean_inc(v_fst_6982_);
lean_dec(v_snd_6975_);
v_fst_6983_ = lean_ctor_get(v_snd_6976_, 0);
lean_inc(v_fst_6983_);
v_snd_6984_ = lean_ctor_get(v_snd_6976_, 1);
lean_inc(v_snd_6984_);
lean_dec(v_snd_6976_);
v_val_6985_ = lean_ctor_get(v_uElimPos_x3f_6977_, 0);
lean_inc_ref(v_matcherLevels_6645_);
v___x_6986_ = lean_array_set(v_matcherLevels_6645_, v_val_6985_, v_fst_6982_);
v___y_6751_ = v_snd_6984_;
v___y_6752_ = v_a_6967_;
v___y_6753_ = v_fst_6981_;
v___y_6754_ = v_a_6964_;
v___y_6755_ = v___x_6962_;
v___y_6756_ = v_numDiscrEqs_6956_;
v___y_6757_ = v_fst_6983_;
v_matcherLevels_6758_ = v___x_6986_;
v___y_6759_ = v___y_6957_;
v___y_6760_ = v___y_6958_;
v___y_6761_ = v___y_6959_;
v___y_6762_ = v___y_6960_;
goto v___jp_6750_;
}
}
else
{
lean_object* v_a_6987_; lean_object* v___x_6989_; uint8_t v_isShared_6990_; uint8_t v_isSharedCheck_6994_; 
lean_dec(v_a_6967_);
lean_dec(v_a_6964_);
lean_dec(v_numDiscrEqs_6956_);
lean_dec_ref(v_remaining_6650_);
lean_dec_ref(v_alts_6649_);
lean_dec(v_matcherName_6644_);
lean_dec_ref(v_toMatcherInfo_6643_);
lean_dec_ref(v_onRemaining_6635_);
lean_dec_ref(v_onAlt_6634_);
lean_dec_ref(v_matcherApp_6628_);
v_a_6987_ = lean_ctor_get(v___x_6973_, 0);
v_isSharedCheck_6994_ = !lean_is_exclusive(v___x_6973_);
if (v_isSharedCheck_6994_ == 0)
{
v___x_6989_ = v___x_6973_;
v_isShared_6990_ = v_isSharedCheck_6994_;
goto v_resetjp_6988_;
}
else
{
lean_inc(v_a_6987_);
lean_dec(v___x_6973_);
v___x_6989_ = lean_box(0);
v_isShared_6990_ = v_isSharedCheck_6994_;
goto v_resetjp_6988_;
}
v_resetjp_6988_:
{
lean_object* v___x_6992_; 
if (v_isShared_6990_ == 0)
{
v___x_6992_ = v___x_6989_;
goto v_reusejp_6991_;
}
else
{
lean_object* v_reuseFailAlloc_6993_; 
v_reuseFailAlloc_6993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6993_, 0, v_a_6987_);
v___x_6992_ = v_reuseFailAlloc_6993_;
goto v_reusejp_6991_;
}
v_reusejp_6991_:
{
return v___x_6992_;
}
}
}
}
else
{
lean_object* v_a_6995_; lean_object* v___x_6997_; uint8_t v_isShared_6998_; uint8_t v_isSharedCheck_7002_; 
lean_dec(v_a_6964_);
lean_dec(v_numDiscrEqs_6956_);
lean_dec_ref(v_remaining_6650_);
lean_dec_ref(v_alts_6649_);
lean_dec(v_matcherName_6644_);
lean_dec_ref(v_toMatcherInfo_6643_);
lean_dec_ref(v_onRemaining_6635_);
lean_dec_ref(v_onAlt_6634_);
lean_dec_ref(v_onMotive_6633_);
lean_dec_ref(v_matcherApp_6628_);
v_a_6995_ = lean_ctor_get(v___x_6966_, 0);
v_isSharedCheck_7002_ = !lean_is_exclusive(v___x_6966_);
if (v_isSharedCheck_7002_ == 0)
{
v___x_6997_ = v___x_6966_;
v_isShared_6998_ = v_isSharedCheck_7002_;
goto v_resetjp_6996_;
}
else
{
lean_inc(v_a_6995_);
lean_dec(v___x_6966_);
v___x_6997_ = lean_box(0);
v_isShared_6998_ = v_isSharedCheck_7002_;
goto v_resetjp_6996_;
}
v_resetjp_6996_:
{
lean_object* v___x_7000_; 
if (v_isShared_6998_ == 0)
{
v___x_7000_ = v___x_6997_;
goto v_reusejp_6999_;
}
else
{
lean_object* v_reuseFailAlloc_7001_; 
v_reuseFailAlloc_7001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7001_, 0, v_a_6995_);
v___x_7000_ = v_reuseFailAlloc_7001_;
goto v_reusejp_6999_;
}
v_reusejp_6999_:
{
return v___x_7000_;
}
}
}
}
else
{
lean_object* v_a_7003_; lean_object* v___x_7005_; uint8_t v_isShared_7006_; uint8_t v_isSharedCheck_7010_; 
lean_dec(v_numDiscrEqs_6956_);
lean_dec_ref(v_remaining_6650_);
lean_dec_ref(v_alts_6649_);
lean_dec(v_matcherName_6644_);
lean_dec_ref(v_toMatcherInfo_6643_);
lean_dec_ref(v_onRemaining_6635_);
lean_dec_ref(v_onAlt_6634_);
lean_dec_ref(v_onMotive_6633_);
lean_dec_ref(v_onParams_6632_);
lean_dec_ref(v_matcherApp_6628_);
v_a_7003_ = lean_ctor_get(v___x_6963_, 0);
v_isSharedCheck_7010_ = !lean_is_exclusive(v___x_6963_);
if (v_isSharedCheck_7010_ == 0)
{
v___x_7005_ = v___x_6963_;
v_isShared_7006_ = v_isSharedCheck_7010_;
goto v_resetjp_7004_;
}
else
{
lean_inc(v_a_7003_);
lean_dec(v___x_6963_);
v___x_7005_ = lean_box(0);
v_isShared_7006_ = v_isSharedCheck_7010_;
goto v_resetjp_7004_;
}
v_resetjp_7004_:
{
lean_object* v___x_7008_; 
if (v_isShared_7006_ == 0)
{
v___x_7008_ = v___x_7005_;
goto v_reusejp_7007_;
}
else
{
lean_object* v_reuseFailAlloc_7009_; 
v_reuseFailAlloc_7009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7009_, 0, v_a_7003_);
v___x_7008_ = v_reuseFailAlloc_7009_;
goto v_reusejp_7007_;
}
v_reusejp_7007_:
{
return v___x_7008_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed(lean_object* v_matcherApp_7030_, lean_object* v_useSplitter_7031_, lean_object* v_addEqualities_7032_, lean_object* v_addProofEqualities_7033_, lean_object* v_onParams_7034_, lean_object* v_onMotive_7035_, lean_object* v_onAlt_7036_, lean_object* v_onRemaining_7037_, lean_object* v___y_7038_, lean_object* v___y_7039_, lean_object* v___y_7040_, lean_object* v___y_7041_, lean_object* v___y_7042_){
_start:
{
uint8_t v_useSplitter_boxed_7043_; uint8_t v_addEqualities_boxed_7044_; uint8_t v_addProofEqualities_boxed_7045_; lean_object* v_res_7046_; 
v_useSplitter_boxed_7043_ = lean_unbox(v_useSplitter_7031_);
v_addEqualities_boxed_7044_ = lean_unbox(v_addEqualities_7032_);
v_addProofEqualities_boxed_7045_ = lean_unbox(v_addProofEqualities_7033_);
v_res_7046_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(v_matcherApp_7030_, v_useSplitter_boxed_7043_, v_addEqualities_boxed_7044_, v_addProofEqualities_boxed_7045_, v_onParams_7034_, v_onMotive_7035_, v_onAlt_7036_, v_onRemaining_7037_, v___y_7038_, v___y_7039_, v___y_7040_, v___y_7041_);
lean_dec(v___y_7041_);
lean_dec_ref(v___y_7040_);
lean_dec(v___y_7039_);
lean_dec_ref(v___y_7038_);
return v_res_7046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType(lean_object* v_matcherApp_7052_, lean_object* v_a_7053_, lean_object* v_a_7054_, lean_object* v_a_7055_, lean_object* v_a_7056_){
_start:
{
lean_object* v_toMatcherInfo_7058_; lean_object* v_matcherName_7059_; lean_object* v_matcherLevels_7060_; lean_object* v_params_7061_; lean_object* v_alts_7062_; lean_object* v_remaining_7063_; lean_object* v___f_7064_; lean_object* v___f_7065_; lean_object* v_nExtra_7066_; uint8_t v___x_7067_; lean_object* v___f_7068_; uint8_t v___x_7069_; lean_object* v___x_7070_; lean_object* v___x_7071_; lean_object* v___f_7072_; lean_object* v___x_7073_; 
v_toMatcherInfo_7058_ = lean_ctor_get(v_matcherApp_7052_, 0);
v_matcherName_7059_ = lean_ctor_get(v_matcherApp_7052_, 1);
v_matcherLevels_7060_ = lean_ctor_get(v_matcherApp_7052_, 2);
v_params_7061_ = lean_ctor_get(v_matcherApp_7052_, 3);
v_alts_7062_ = lean_ctor_get(v_matcherApp_7052_, 6);
v_remaining_7063_ = lean_ctor_get(v_matcherApp_7052_, 7);
v___f_7064_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__0));
v___f_7065_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__1));
v_nExtra_7066_ = lean_array_get_size(v_remaining_7063_);
v___x_7067_ = 1;
v___f_7068_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__2));
v___x_7069_ = 0;
v___x_7070_ = lean_box(v___x_7069_);
v___x_7071_ = lean_box(v___x_7067_);
lean_inc_ref(v_matcherLevels_7060_);
lean_inc_ref(v_params_7061_);
lean_inc(v_matcherName_7059_);
lean_inc_ref(v_toMatcherInfo_7058_);
lean_inc_ref(v_alts_7062_);
v___f_7072_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed), 15, 8);
lean_closure_set(v___f_7072_, 0, v_nExtra_7066_);
lean_closure_set(v___f_7072_, 1, v___x_7070_);
lean_closure_set(v___f_7072_, 2, v___x_7071_);
lean_closure_set(v___f_7072_, 3, v_alts_7062_);
lean_closure_set(v___f_7072_, 4, v_toMatcherInfo_7058_);
lean_closure_set(v___f_7072_, 5, v_matcherName_7059_);
lean_closure_set(v___f_7072_, 6, v_params_7061_);
lean_closure_set(v___f_7072_, 7, v_matcherLevels_7060_);
v___x_7073_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(v_matcherApp_7052_, v___x_7067_, v___x_7069_, v___x_7069_, v___f_7064_, v___f_7072_, v___f_7068_, v___f_7065_, v_a_7053_, v_a_7054_, v_a_7055_, v_a_7056_);
return v___x_7073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___boxed(lean_object* v_matcherApp_7074_, lean_object* v_a_7075_, lean_object* v_a_7076_, lean_object* v_a_7077_, lean_object* v_a_7078_, lean_object* v_a_7079_){
_start:
{
lean_object* v_res_7080_; 
v_res_7080_ = l_Lean_Meta_MatcherApp_inferMatchType(v_matcherApp_7074_, v_a_7075_, v_a_7076_, v_a_7077_, v_a_7078_);
lean_dec(v_a_7078_);
lean_dec_ref(v_a_7077_);
lean_dec(v_a_7076_);
lean_dec_ref(v_a_7075_);
return v_res_7080_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(lean_object* v_a_7081_, lean_object* v_termAlt_7082_, lean_object* v_inst_7083_, lean_object* v_R_7084_, lean_object* v_a_7085_, lean_object* v_b_7086_, lean_object* v_c_7087_, lean_object* v___y_7088_, lean_object* v___y_7089_, lean_object* v___y_7090_, lean_object* v___y_7091_){
_start:
{
lean_object* v___x_7093_; 
v___x_7093_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_7081_, v_termAlt_7082_, v_a_7085_, v_b_7086_, v___y_7088_, v___y_7089_, v___y_7090_, v___y_7091_);
return v___x_7093_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___boxed(lean_object* v_a_7094_, lean_object* v_termAlt_7095_, lean_object* v_inst_7096_, lean_object* v_R_7097_, lean_object* v_a_7098_, lean_object* v_b_7099_, lean_object* v_c_7100_, lean_object* v___y_7101_, lean_object* v___y_7102_, lean_object* v___y_7103_, lean_object* v___y_7104_, lean_object* v___y_7105_){
_start:
{
lean_object* v_res_7106_; 
v_res_7106_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(v_a_7094_, v_termAlt_7095_, v_inst_7096_, v_R_7097_, v_a_7098_, v_b_7099_, v_c_7100_, v___y_7101_, v___y_7102_, v___y_7103_, v___y_7104_);
lean_dec(v___y_7104_);
lean_dec_ref(v___y_7103_);
lean_dec(v___y_7102_);
lean_dec_ref(v___y_7101_);
return v_res_7106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(lean_object* v_00_u03b1_7107_, lean_object* v_fvars_7108_, lean_object* v_names_7109_, lean_object* v_k_7110_, lean_object* v___y_7111_, lean_object* v___y_7112_, lean_object* v___y_7113_, lean_object* v___y_7114_){
_start:
{
lean_object* v___x_7116_; 
v___x_7116_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_fvars_7108_, v_names_7109_, v_k_7110_, v___y_7111_, v___y_7112_, v___y_7113_, v___y_7114_);
return v___x_7116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___boxed(lean_object* v_00_u03b1_7117_, lean_object* v_fvars_7118_, lean_object* v_names_7119_, lean_object* v_k_7120_, lean_object* v___y_7121_, lean_object* v___y_7122_, lean_object* v___y_7123_, lean_object* v___y_7124_, lean_object* v___y_7125_){
_start:
{
lean_object* v_res_7126_; 
v_res_7126_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(v_00_u03b1_7117_, v_fvars_7118_, v_names_7119_, v_k_7120_, v___y_7121_, v___y_7122_, v___y_7123_, v___y_7124_);
lean_dec(v___y_7124_);
lean_dec_ref(v___y_7123_);
lean_dec(v___y_7122_);
lean_dec_ref(v___y_7121_);
lean_dec_ref(v_names_7119_);
lean_dec_ref(v_fvars_7118_);
return v_res_7126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(lean_object* v_00_u03b1_7127_, lean_object* v_origAltType_7128_, lean_object* v_altInfo_7129_, lean_object* v_k_7130_, lean_object* v___y_7131_, lean_object* v___y_7132_, lean_object* v___y_7133_, lean_object* v___y_7134_){
_start:
{
lean_object* v___x_7136_; 
v___x_7136_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v_origAltType_7128_, v_altInfo_7129_, v_k_7130_, v___y_7131_, v___y_7132_, v___y_7133_, v___y_7134_);
return v___x_7136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___boxed(lean_object* v_00_u03b1_7137_, lean_object* v_origAltType_7138_, lean_object* v_altInfo_7139_, lean_object* v_k_7140_, lean_object* v___y_7141_, lean_object* v___y_7142_, lean_object* v___y_7143_, lean_object* v___y_7144_, lean_object* v___y_7145_){
_start:
{
lean_object* v_res_7146_; 
v_res_7146_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(v_00_u03b1_7137_, v_origAltType_7138_, v_altInfo_7139_, v_k_7140_, v___y_7141_, v___y_7142_, v___y_7143_, v___y_7144_);
lean_dec(v___y_7144_);
lean_dec_ref(v___y_7143_);
lean_dec(v___y_7142_);
lean_dec_ref(v___y_7141_);
return v_res_7146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(lean_object* v_declName_7147_, lean_object* v___y_7148_, lean_object* v___y_7149_, lean_object* v___y_7150_, lean_object* v___y_7151_){
_start:
{
lean_object* v___x_7153_; 
v___x_7153_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_declName_7147_, v___y_7151_);
return v___x_7153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___boxed(lean_object* v_declName_7154_, lean_object* v___y_7155_, lean_object* v___y_7156_, lean_object* v___y_7157_, lean_object* v___y_7158_, lean_object* v___y_7159_){
_start:
{
lean_object* v_res_7160_; 
v_res_7160_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(v_declName_7154_, v___y_7155_, v___y_7156_, v___y_7157_, v___y_7158_);
lean_dec(v___y_7158_);
lean_dec_ref(v___y_7157_);
lean_dec(v___y_7156_);
lean_dec_ref(v___y_7155_);
return v_res_7160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(size_t v_sz_7161_, size_t v_i_7162_, lean_object* v_bs_7163_, lean_object* v___y_7164_, lean_object* v___y_7165_, lean_object* v___y_7166_, lean_object* v___y_7167_){
_start:
{
lean_object* v___x_7169_; 
v___x_7169_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_7161_, v_i_7162_, v_bs_7163_, v___y_7164_, v___y_7166_, v___y_7167_);
return v___x_7169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___boxed(lean_object* v_sz_7170_, lean_object* v_i_7171_, lean_object* v_bs_7172_, lean_object* v___y_7173_, lean_object* v___y_7174_, lean_object* v___y_7175_, lean_object* v___y_7176_, lean_object* v___y_7177_){
_start:
{
size_t v_sz_boxed_7178_; size_t v_i_boxed_7179_; lean_object* v_res_7180_; 
v_sz_boxed_7178_ = lean_unbox_usize(v_sz_7170_);
lean_dec(v_sz_7170_);
v_i_boxed_7179_ = lean_unbox_usize(v_i_7171_);
lean_dec(v_i_7171_);
v_res_7180_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(v_sz_boxed_7178_, v_i_boxed_7179_, v_bs_7172_, v___y_7173_, v___y_7174_, v___y_7175_, v___y_7176_);
lean_dec(v___y_7176_);
lean_dec_ref(v___y_7175_);
lean_dec(v___y_7174_);
lean_dec_ref(v___y_7173_);
return v_res_7180_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(lean_object* v_upperBound_7181_, lean_object* v_onAlt_7182_, lean_object* v_extraEqualities_7183_, lean_object* v_inst_7184_, lean_object* v_R_7185_, lean_object* v_a_7186_, lean_object* v_b_7187_, lean_object* v_c_7188_, lean_object* v___y_7189_, lean_object* v___y_7190_, lean_object* v___y_7191_, lean_object* v___y_7192_){
_start:
{
lean_object* v___x_7194_; 
v___x_7194_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v_upperBound_7181_, v_onAlt_7182_, v_extraEqualities_7183_, v_a_7186_, v_b_7187_, v___y_7189_, v___y_7190_, v___y_7191_, v___y_7192_);
return v___x_7194_;
}
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(lean_object* v_upperBound_7209_, lean_object* v_onAlt_7210_, uint8_t v_useSplitter_7211_, lean_object* v_extraEqualities_7212_, lean_object* v_numDiscrEqs_7213_, lean_object* v_inst_7214_, lean_object* v_R_7215_, lean_object* v_a_7216_, lean_object* v_b_7217_, lean_object* v_c_7218_, lean_object* v___y_7219_, lean_object* v___y_7220_, lean_object* v___y_7221_, lean_object* v___y_7222_){
_start:
{
lean_object* v___x_7224_; 
v___x_7224_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v_upperBound_7209_, v_onAlt_7210_, v_useSplitter_7211_, v_extraEqualities_7212_, v_numDiscrEqs_7213_, v_a_7216_, v_b_7217_, v___y_7219_, v___y_7220_, v___y_7221_, v___y_7222_);
return v___x_7224_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___boxed(lean_object* v_upperBound_7225_, lean_object* v_onAlt_7226_, lean_object* v_useSplitter_7227_, lean_object* v_extraEqualities_7228_, lean_object* v_numDiscrEqs_7229_, lean_object* v_inst_7230_, lean_object* v_R_7231_, lean_object* v_a_7232_, lean_object* v_b_7233_, lean_object* v_c_7234_, lean_object* v___y_7235_, lean_object* v___y_7236_, lean_object* v___y_7237_, lean_object* v___y_7238_, lean_object* v___y_7239_){
_start:
{
uint8_t v_useSplitter_boxed_7240_; lean_object* v_res_7241_; 
v_useSplitter_boxed_7240_ = lean_unbox(v_useSplitter_7227_);
v_res_7241_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(v_upperBound_7225_, v_onAlt_7226_, v_useSplitter_boxed_7240_, v_extraEqualities_7228_, v_numDiscrEqs_7229_, v_inst_7230_, v_R_7231_, v_a_7232_, v_b_7233_, v_c_7234_, v___y_7235_, v___y_7236_, v___y_7237_, v___y_7238_);
lean_dec(v___y_7238_);
lean_dec_ref(v___y_7237_);
lean_dec(v___y_7236_);
lean_dec_ref(v___y_7235_);
lean_dec(v_upperBound_7225_);
return v_res_7241_;
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
