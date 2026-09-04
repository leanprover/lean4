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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_4196__boxed_236_; uint8_t v_refined_boxed_237_; lean_object* v_res_238_; 
v___x_4196__boxed_236_ = lean_unbox(v___x_224_);
v_refined_boxed_237_ = lean_unbox(v_refined_226_);
v_res_238_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(v_alt_223_, v___x_4196__boxed_236_, v_xs_225_, v_refined_boxed_237_, v___x_227_, v_unrefinedArgType_228_, v_x_229_, v_x_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
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
v_options_250_ = lean_ctor_get(v___y_242_, 1);
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
v_ref_267_ = lean_ctor_get(v___y_264_, 4);
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
uint8_t v___x_4421__boxed_375_; uint8_t v_refined_boxed_376_; lean_object* v_res_377_; 
v___x_4421__boxed_375_ = lean_unbox(v___x_362_);
v_refined_boxed_376_ = lean_unbox(v_refined_363_);
v_res_377_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(v___x_4421__boxed_375_, v_refined_boxed_376_, v___x_364_, v_unrefinedArgType_365_, v_binderType_366_, v_numParams_367_, v_xs_368_, v_alt_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
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
uint8_t v_val_12139__boxed_1646_; lean_object* v_res_1647_; 
v_val_12139__boxed_1646_ = lean_unbox(v_val_1639_);
v_res_1647_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__4(v_val_12139__boxed_1646_, v_a_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6(lean_object* v_heq_1706_, lean_object* v_fst_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Lean_mkArrow(v_heq_1706_, v_fst_1707_, v___y_1710_, v___y_1711_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed(lean_object* v_heq_1714_, lean_object* v_fst_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__6(v_heq_1714_, v_fst_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7(lean_object* v_heq_1724_, lean_object* v_fst_1725_, lean_object* v_fst_1726_, lean_object* v___x_1727_, lean_object* v___x_1728_, lean_object* v_toPure_1729_, lean_object* v_motiveBody_x27_1730_){
_start:
{
uint8_t v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1731_ = l_Lean_Expr_isHEq(v_heq_1724_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7___boxed(lean_object* v_heq_1743_, lean_object* v_fst_1744_, lean_object* v_fst_1745_, lean_object* v___x_1746_, lean_object* v___x_1747_, lean_object* v_toPure_1748_, lean_object* v_motiveBody_x27_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__7(v_heq_1743_, v_fst_1744_, v_fst_1745_, v___x_1746_, v___x_1747_, v_toPure_1748_, v_motiveBody_x27_1749_);
lean_dec_ref(v_heq_1743_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8(lean_object* v_fst_1751_, lean_object* v_fst_1752_, lean_object* v_fst_1753_, lean_object* v___x_1754_, lean_object* v___x_1755_, lean_object* v_toPure_1756_, lean_object* v_inst_1757_, lean_object* v_toBind_1758_, lean_object* v_heq_1759_){
_start:
{
lean_object* v___f_1760_; lean_object* v___f_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_inc_ref(v_heq_1759_);
v___f_1760_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed), 7, 2);
lean_closure_set(v___f_1760_, 0, v_heq_1759_);
lean_closure_set(v___f_1760_, 1, v_fst_1751_);
v___f_1761_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7___boxed), 7, 6);
lean_closure_set(v___f_1761_, 0, v_heq_1759_);
lean_closure_set(v___f_1761_, 1, v_fst_1752_);
lean_closure_set(v___f_1761_, 2, v_fst_1753_);
lean_closure_set(v___f_1761_, 3, v___x_1754_);
lean_closure_set(v___f_1761_, 4, v___x_1755_);
lean_closure_set(v___f_1761_, 5, v_toPure_1756_);
v___x_1762_ = lean_apply_2(v_inst_1757_, lean_box(0), v___f_1760_);
v___x_1763_ = lean_apply_4(v_toBind_1758_, lean_box(0), lean_box(0), v___x_1762_, v___f_1761_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9(lean_object* v___x_1764_, lean_object* v_a_1765_, lean_object* v_inst_1766_, lean_object* v_toBind_1767_, lean_object* v___f_1768_, lean_object* v_fst_1769_, lean_object* v_fst_1770_, lean_object* v___x_1771_, lean_object* v___x_1772_, lean_object* v___x_1773_, lean_object* v_fst_1774_, lean_object* v_toPure_1775_, uint8_t v_____do__lift_1776_){
_start:
{
if (v_____do__lift_1776_ == 0)
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
lean_dec(v_toPure_1775_);
lean_dec(v_fst_1774_);
lean_dec_ref(v___x_1773_);
lean_dec_ref(v___x_1772_);
lean_dec(v___x_1771_);
lean_dec(v_fst_1770_);
lean_dec(v_fst_1769_);
v___x_1777_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEqHEq___boxed), 7, 2);
lean_closure_set(v___x_1777_, 0, v___x_1764_);
lean_closure_set(v___x_1777_, 1, v_a_1765_);
v___x_1778_ = lean_apply_2(v_inst_1766_, lean_box(0), v___x_1777_);
v___x_1779_ = lean_apply_4(v_toBind_1767_, lean_box(0), lean_box(0), v___x_1778_, v___f_1768_);
return v___x_1779_;
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
lean_dec(v___f_1768_);
lean_dec(v_toBind_1767_);
lean_dec(v_inst_1766_);
lean_dec_ref(v_a_1765_);
lean_dec_ref(v___x_1764_);
v___x_1780_ = lean_box(0);
v___x_1781_ = lean_array_push(v_fst_1769_, v___x_1780_);
v___x_1782_ = lean_array_push(v_fst_1770_, v___x_1771_);
v___x_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1772_);
lean_ctor_set(v___x_1783_, 1, v___x_1773_);
v___x_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1782_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
v___x_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1781_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
v___x_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1786_, 0, v_fst_1774_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
v___x_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
v___x_1788_ = lean_apply_2(v_toPure_1775_, lean_box(0), v___x_1787_);
return v___x_1788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9___boxed(lean_object* v___x_1789_, lean_object* v_a_1790_, lean_object* v_inst_1791_, lean_object* v_toBind_1792_, lean_object* v___f_1793_, lean_object* v_fst_1794_, lean_object* v_fst_1795_, lean_object* v___x_1796_, lean_object* v___x_1797_, lean_object* v___x_1798_, lean_object* v_fst_1799_, lean_object* v_toPure_1800_, lean_object* v_____do__lift_1801_){
_start:
{
uint8_t v_____do__lift_12330__boxed_1802_; lean_object* v_res_1803_; 
v_____do__lift_12330__boxed_1802_ = lean_unbox(v_____do__lift_1801_);
v_res_1803_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__9(v___x_1789_, v_a_1790_, v_inst_1791_, v_toBind_1792_, v___f_1793_, v_fst_1794_, v_fst_1795_, v___x_1796_, v___x_1797_, v___x_1798_, v_fst_1799_, v_toPure_1800_, v_____do__lift_12330__boxed_1802_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10(lean_object* v_toPure_1804_, uint8_t v_addEqualities_1805_, lean_object* v_inst_1806_, lean_object* v_toBind_1807_, lean_object* v_a_1808_, lean_object* v_x_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v_snd_1811_; lean_object* v_snd_1812_; lean_object* v_snd_1813_; lean_object* v_snd_1814_; lean_object* v_fst_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1921_; 
v_snd_1811_ = lean_ctor_get(v___y_1810_, 1);
lean_inc(v_snd_1811_);
v_snd_1812_ = lean_ctor_get(v_snd_1811_, 1);
lean_inc(v_snd_1812_);
v_snd_1813_ = lean_ctor_get(v_snd_1812_, 1);
lean_inc(v_snd_1813_);
v_snd_1814_ = lean_ctor_get(v_snd_1813_, 1);
lean_inc(v_snd_1814_);
v_fst_1815_ = lean_ctor_get(v___y_1810_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___y_1810_);
if (v_isSharedCheck_1921_ == 0)
{
lean_object* v_unused_1922_; 
v_unused_1922_ = lean_ctor_get(v___y_1810_, 1);
lean_dec(v_unused_1922_);
v___x_1817_ = v___y_1810_;
v_isShared_1818_ = v_isSharedCheck_1921_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_fst_1815_);
lean_dec(v___y_1810_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1921_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v_fst_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1919_; 
v_fst_1819_ = lean_ctor_get(v_snd_1811_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v_snd_1811_);
if (v_isSharedCheck_1919_ == 0)
{
lean_object* v_unused_1920_; 
v_unused_1920_ = lean_ctor_get(v_snd_1811_, 1);
lean_dec(v_unused_1920_);
v___x_1821_ = v_snd_1811_;
v_isShared_1822_ = v_isSharedCheck_1919_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_fst_1819_);
lean_dec(v_snd_1811_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1919_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v_fst_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1917_; 
v_fst_1823_ = lean_ctor_get(v_snd_1812_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_snd_1812_);
if (v_isSharedCheck_1917_ == 0)
{
lean_object* v_unused_1918_; 
v_unused_1918_ = lean_ctor_get(v_snd_1812_, 1);
lean_dec(v_unused_1918_);
v___x_1825_ = v_snd_1812_;
v_isShared_1826_ = v_isSharedCheck_1917_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_fst_1823_);
lean_dec(v_snd_1812_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1917_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v_fst_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1915_; 
v_fst_1827_ = lean_ctor_get(v_snd_1813_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v_snd_1813_);
if (v_isSharedCheck_1915_ == 0)
{
lean_object* v_unused_1916_; 
v_unused_1916_ = lean_ctor_get(v_snd_1813_, 1);
lean_dec(v_unused_1916_);
v___x_1829_ = v_snd_1813_;
v_isShared_1830_ = v_isSharedCheck_1915_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_fst_1827_);
lean_dec(v_snd_1813_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1915_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v_array_1831_; lean_object* v_start_1832_; lean_object* v_stop_1833_; uint8_t v___x_1834_; 
v_array_1831_ = lean_ctor_get(v_snd_1814_, 0);
v_start_1832_ = lean_ctor_get(v_snd_1814_, 1);
v_stop_1833_ = lean_ctor_get(v_snd_1814_, 2);
v___x_1834_ = lean_nat_dec_lt(v_start_1832_, v_stop_1833_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1836_; 
lean_dec_ref(v_a_1808_);
lean_dec(v_toBind_1807_);
lean_dec(v_inst_1806_);
if (v_isShared_1830_ == 0)
{
v___x_1836_ = v___x_1829_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_fst_1827_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_snd_1814_);
v___x_1836_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
lean_object* v___x_1838_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 1, v___x_1836_);
v___x_1838_ = v___x_1825_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_fst_1823_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
lean_object* v___x_1840_; 
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 1, v___x_1838_);
v___x_1840_ = v___x_1821_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_fst_1819_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v___x_1842_; 
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 1, v___x_1840_);
v___x_1842_ = v___x_1817_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_fst_1815_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
v___x_1844_ = lean_apply_2(v_toPure_1804_, lean_box(0), v___x_1843_);
return v___x_1844_;
}
}
}
}
}
else
{
lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1911_; 
lean_inc(v_stop_1833_);
lean_inc(v_start_1832_);
lean_inc_ref(v_array_1831_);
v_isSharedCheck_1911_ = !lean_is_exclusive(v_snd_1814_);
if (v_isSharedCheck_1911_ == 0)
{
lean_object* v_unused_1912_; lean_object* v_unused_1913_; lean_object* v_unused_1914_; 
v_unused_1912_ = lean_ctor_get(v_snd_1814_, 2);
lean_dec(v_unused_1912_);
v_unused_1913_ = lean_ctor_get(v_snd_1814_, 1);
lean_dec(v_unused_1913_);
v_unused_1914_ = lean_ctor_get(v_snd_1814_, 0);
lean_dec(v_unused_1914_);
v___x_1850_ = v_snd_1814_;
v_isShared_1851_ = v_isSharedCheck_1911_;
goto v_resetjp_1849_;
}
else
{
lean_dec(v_snd_1814_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1911_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v_array_1852_; lean_object* v_start_1853_; lean_object* v_stop_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1859_; 
v_array_1852_ = lean_ctor_get(v_fst_1827_, 0);
v_start_1853_ = lean_ctor_get(v_fst_1827_, 1);
v_stop_1854_ = lean_ctor_get(v_fst_1827_, 2);
v___x_1855_ = lean_array_fget(v_array_1831_, v_start_1832_);
v___x_1856_ = lean_unsigned_to_nat(1u);
v___x_1857_ = lean_nat_add(v_start_1832_, v___x_1856_);
lean_dec(v_start_1832_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 1, v___x_1857_);
v___x_1859_ = v___x_1850_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_array_1831_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v___x_1857_);
lean_ctor_set(v_reuseFailAlloc_1910_, 2, v_stop_1833_);
v___x_1859_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
uint8_t v___x_1860_; 
v___x_1860_ = lean_nat_dec_lt(v_start_1853_, v_stop_1854_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1862_; 
lean_dec(v___x_1855_);
lean_dec_ref(v_a_1808_);
lean_dec(v_toBind_1807_);
lean_dec(v_inst_1806_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 1, v___x_1859_);
v___x_1862_ = v___x_1829_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_fst_1827_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v___x_1859_);
v___x_1862_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
lean_object* v___x_1864_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 1, v___x_1862_);
v___x_1864_ = v___x_1825_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_fst_1823_);
lean_ctor_set(v_reuseFailAlloc_1873_, 1, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1866_; 
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 1, v___x_1864_);
v___x_1866_ = v___x_1821_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_fst_1819_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
lean_object* v___x_1868_; 
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 1, v___x_1866_);
v___x_1868_ = v___x_1817_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_fst_1815_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v___x_1866_);
v___x_1868_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
v___x_1870_ = lean_apply_2(v_toPure_1804_, lean_box(0), v___x_1869_);
return v___x_1870_;
}
}
}
}
}
else
{
lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1906_; 
lean_inc(v_stop_1854_);
lean_inc(v_start_1853_);
lean_inc_ref(v_array_1852_);
v_isSharedCheck_1906_ = !lean_is_exclusive(v_fst_1827_);
if (v_isSharedCheck_1906_ == 0)
{
lean_object* v_unused_1907_; lean_object* v_unused_1908_; lean_object* v_unused_1909_; 
v_unused_1907_ = lean_ctor_get(v_fst_1827_, 2);
lean_dec(v_unused_1907_);
v_unused_1908_ = lean_ctor_get(v_fst_1827_, 1);
lean_dec(v_unused_1908_);
v_unused_1909_ = lean_ctor_get(v_fst_1827_, 0);
lean_dec(v_unused_1909_);
v___x_1876_ = v_fst_1827_;
v_isShared_1877_ = v_isSharedCheck_1906_;
goto v_resetjp_1875_;
}
else
{
lean_dec(v_fst_1827_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1906_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1881_; 
v___x_1878_ = lean_array_fget(v_array_1852_, v_start_1853_);
v___x_1879_ = lean_nat_add(v_start_1853_, v___x_1856_);
lean_dec(v_start_1853_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 1, v___x_1879_);
v___x_1881_ = v___x_1876_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_array_1852_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v___x_1879_);
lean_ctor_set(v_reuseFailAlloc_1905_, 2, v_stop_1854_);
v___x_1881_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
if (v_addEqualities_1805_ == 0)
{
lean_dec(v___x_1878_);
lean_dec_ref(v_a_1808_);
lean_dec(v_toBind_1807_);
lean_dec(v_inst_1806_);
goto v___jp_1882_;
}
else
{
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v___f_1900_; lean_object* v___f_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
lean_del_object(v___x_1829_);
lean_del_object(v___x_1825_);
lean_del_object(v___x_1821_);
lean_del_object(v___x_1817_);
lean_inc_n(v_toBind_1807_, 2);
lean_inc_n(v_inst_1806_, 2);
lean_inc(v_toPure_1804_);
lean_inc_ref(v___x_1859_);
lean_inc_ref(v___x_1881_);
lean_inc(v_fst_1823_);
lean_inc(v_fst_1819_);
lean_inc(v_fst_1815_);
v___f_1900_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__8), 9, 8);
lean_closure_set(v___f_1900_, 0, v_fst_1815_);
lean_closure_set(v___f_1900_, 1, v_fst_1819_);
lean_closure_set(v___f_1900_, 2, v_fst_1823_);
lean_closure_set(v___f_1900_, 3, v___x_1881_);
lean_closure_set(v___f_1900_, 4, v___x_1859_);
lean_closure_set(v___f_1900_, 5, v_toPure_1804_);
lean_closure_set(v___f_1900_, 6, v_inst_1806_);
lean_closure_set(v___f_1900_, 7, v_toBind_1807_);
lean_inc_ref(v_a_1808_);
v___f_1901_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9___boxed), 13, 12);
lean_closure_set(v___f_1901_, 0, v___x_1878_);
lean_closure_set(v___f_1901_, 1, v_a_1808_);
lean_closure_set(v___f_1901_, 2, v_inst_1806_);
lean_closure_set(v___f_1901_, 3, v_toBind_1807_);
lean_closure_set(v___f_1901_, 4, v___f_1900_);
lean_closure_set(v___f_1901_, 5, v_fst_1819_);
lean_closure_set(v___f_1901_, 6, v_fst_1823_);
lean_closure_set(v___f_1901_, 7, v___x_1855_);
lean_closure_set(v___f_1901_, 8, v___x_1881_);
lean_closure_set(v___f_1901_, 9, v___x_1859_);
lean_closure_set(v___f_1901_, 10, v_fst_1815_);
lean_closure_set(v___f_1901_, 11, v_toPure_1804_);
v___x_1902_ = lean_alloc_closure((void*)(l_Lean_Meta_isProof___boxed), 6, 1);
lean_closure_set(v___x_1902_, 0, v_a_1808_);
v___x_1903_ = lean_apply_2(v_inst_1806_, lean_box(0), v___x_1902_);
v___x_1904_ = lean_apply_4(v_toBind_1807_, lean_box(0), lean_box(0), v___x_1903_, v___f_1901_);
return v___x_1904_;
}
else
{
lean_dec(v___x_1878_);
lean_dec_ref(v_a_1808_);
lean_dec(v_toBind_1807_);
lean_dec(v_inst_1806_);
goto v___jp_1882_;
}
}
v___jp_1882_:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1883_ = lean_box(0);
v___x_1884_ = lean_array_push(v_fst_1819_, v___x_1883_);
v___x_1885_ = lean_array_push(v_fst_1823_, v___x_1855_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 1, v___x_1859_);
lean_ctor_set(v___x_1829_, 0, v___x_1881_);
v___x_1887_ = v___x_1829_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1881_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v___x_1859_);
v___x_1887_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
lean_object* v___x_1889_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 1, v___x_1887_);
lean_ctor_set(v___x_1825_, 0, v___x_1885_);
v___x_1889_ = v___x_1825_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v___x_1887_);
v___x_1889_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
lean_object* v___x_1891_; 
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 1, v___x_1889_);
lean_ctor_set(v___x_1821_, 0, v___x_1884_);
v___x_1891_ = v___x_1821_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1884_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v___x_1889_);
v___x_1891_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
lean_object* v___x_1893_; 
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 1, v___x_1891_);
v___x_1893_ = v___x_1817_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_fst_1815_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
v___x_1895_ = lean_apply_2(v_toPure_1804_, lean_box(0), v___x_1894_);
return v___x_1895_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10___boxed(lean_object* v_toPure_1923_, lean_object* v_addEqualities_1924_, lean_object* v_inst_1925_, lean_object* v_toBind_1926_, lean_object* v_a_1927_, lean_object* v_x_1928_, lean_object* v___y_1929_){
_start:
{
uint8_t v_addEqualities_boxed_1930_; lean_object* v_res_1931_; 
v_addEqualities_boxed_1930_ = lean_unbox(v_addEqualities_1924_);
v_res_1931_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__10(v_toPure_1923_, v_addEqualities_boxed_1930_, v_inst_1925_, v_toBind_1926_, v_a_1927_, v_x_1928_, v___y_1929_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11(lean_object* v_toPure_1932_, lean_object* v_____do__lift_1933_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = lean_apply_2(v_toPure_1932_, lean_box(0), v_____do__lift_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12(lean_object* v_toPure_1935_, lean_object* v_____do__lift_1936_){
_start:
{
lean_object* v___x_1937_; 
v___x_1937_ = lean_apply_2(v_toPure_1935_, lean_box(0), v_____do__lift_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__13(lean_object* v_fst_1938_, lean_object* v_fst_1939_, lean_object* v_____do__lift_1940_, lean_object* v_toPure_1941_, lean_object* v_____do__lift_1942_){
_start:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1943_, 0, v_fst_1938_);
lean_ctor_set(v___x_1943_, 1, v_fst_1939_);
v___x_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1944_, 0, v_____do__lift_1942_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
v___x_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1945_, 0, v_____do__lift_1940_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
v___x_1946_ = lean_apply_2(v_toPure_1941_, lean_box(0), v___x_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__14(lean_object* v_fst_1947_, lean_object* v_fst_1948_, lean_object* v_toPure_1949_, lean_object* v_fst_1950_, lean_object* v_inst_1951_, lean_object* v_toBind_1952_, lean_object* v_____do__lift_1953_){
_start:
{
lean_object* v___f_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___f_1954_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__13), 5, 4);
lean_closure_set(v___f_1954_, 0, v_fst_1947_);
lean_closure_set(v___f_1954_, 1, v_fst_1948_);
lean_closure_set(v___f_1954_, 2, v_____do__lift_1953_);
lean_closure_set(v___f_1954_, 3, v_toPure_1949_);
v___x_1955_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1955_, 0, v_fst_1950_);
v___x_1956_ = lean_apply_2(v_inst_1951_, lean_box(0), v___x_1955_);
v___x_1957_ = lean_apply_4(v_toBind_1952_, lean_box(0), lean_box(0), v___x_1956_, v___f_1954_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__15(lean_object* v_toPure_1958_, lean_object* v_inst_1959_, lean_object* v_toBind_1960_, lean_object* v_motiveArgs_1961_, lean_object* v_____s_1962_){
_start:
{
lean_object* v_snd_1963_; lean_object* v_snd_1964_; lean_object* v_fst_1965_; lean_object* v_fst_1966_; lean_object* v_fst_1967_; lean_object* v___f_1968_; uint8_t v___x_1969_; uint8_t v___x_1970_; uint8_t v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v_snd_1963_ = lean_ctor_get(v_____s_1962_, 1);
lean_inc(v_snd_1963_);
v_snd_1964_ = lean_ctor_get(v_snd_1963_, 1);
lean_inc(v_snd_1964_);
v_fst_1965_ = lean_ctor_get(v_____s_1962_, 0);
lean_inc_n(v_fst_1965_, 2);
lean_dec_ref(v_____s_1962_);
v_fst_1966_ = lean_ctor_get(v_snd_1963_, 0);
lean_inc(v_fst_1966_);
lean_dec(v_snd_1963_);
v_fst_1967_ = lean_ctor_get(v_snd_1964_, 0);
lean_inc(v_fst_1967_);
lean_dec(v_snd_1964_);
lean_inc(v_toBind_1960_);
lean_inc(v_inst_1959_);
v___f_1968_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14), 7, 6);
lean_closure_set(v___f_1968_, 0, v_fst_1966_);
lean_closure_set(v___f_1968_, 1, v_fst_1967_);
lean_closure_set(v___f_1968_, 2, v_toPure_1958_);
lean_closure_set(v___f_1968_, 3, v_fst_1965_);
lean_closure_set(v___f_1968_, 4, v_inst_1959_);
lean_closure_set(v___f_1968_, 5, v_toBind_1960_);
v___x_1969_ = 0;
v___x_1970_ = 1;
v___x_1971_ = 1;
v___x_1972_ = lean_box(v___x_1969_);
v___x_1973_ = lean_box(v___x_1970_);
v___x_1974_ = lean_box(v___x_1969_);
v___x_1975_ = lean_box(v___x_1970_);
v___x_1976_ = lean_box(v___x_1971_);
v___x_1977_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1977_, 0, v_motiveArgs_1961_);
lean_closure_set(v___x_1977_, 1, v_fst_1965_);
lean_closure_set(v___x_1977_, 2, v___x_1972_);
lean_closure_set(v___x_1977_, 3, v___x_1973_);
lean_closure_set(v___x_1977_, 4, v___x_1974_);
lean_closure_set(v___x_1977_, 5, v___x_1975_);
lean_closure_set(v___x_1977_, 6, v___x_1976_);
v___x_1978_ = lean_apply_2(v_inst_1959_, lean_box(0), v___x_1977_);
v___x_1979_ = lean_apply_4(v_toBind_1960_, lean_box(0), lean_box(0), v___x_1978_, v___f_1968_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__16(lean_object* v_toMatcherInfo_1982_, lean_object* v_discrs_x27_1983_, lean_object* v_motiveArgs_1984_, lean_object* v_inst_1985_, lean_object* v___f_1986_, lean_object* v_toBind_1987_, lean_object* v___f_1988_, lean_object* v_motiveBody_x27_1989_){
_start:
{
lean_object* v_discrInfos_1990_; lean_object* v___x_1991_; lean_object* v_addHEqualities_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; size_t v_sz_2001_; size_t v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v_discrInfos_1990_ = lean_ctor_get(v_toMatcherInfo_1982_, 4);
lean_inc_ref(v_discrInfos_1990_);
lean_dec_ref(v_toMatcherInfo_1982_);
v___x_1991_ = lean_unsigned_to_nat(0u);
v_addHEqualities_1992_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___closed__0));
v___x_1993_ = lean_array_get_size(v_discrs_x27_1983_);
v___x_1994_ = l_Array_toSubarray___redArg(v_discrs_x27_1983_, v___x_1991_, v___x_1993_);
v___x_1995_ = lean_array_get_size(v_discrInfos_1990_);
v___x_1996_ = l_Array_toSubarray___redArg(v_discrInfos_1990_, v___x_1991_, v___x_1995_);
v___x_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1994_);
lean_ctor_set(v___x_1997_, 1, v___x_1996_);
v___x_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1998_, 0, v_addHEqualities_1992_);
lean_ctor_set(v___x_1998_, 1, v___x_1997_);
v___x_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1999_, 0, v_addHEqualities_1992_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
v___x_2000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2000_, 0, v_motiveBody_x27_1989_);
lean_ctor_set(v___x_2000_, 1, v___x_1999_);
v_sz_2001_ = lean_array_size(v_motiveArgs_1984_);
v___x_2002_ = ((size_t)0ULL);
v___x_2003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1985_, v_motiveArgs_1984_, v___f_1986_, v_sz_2001_, v___x_2002_, v___x_2000_);
v___x_2004_ = lean_apply_4(v_toBind_1987_, lean_box(0), lean_box(0), v___x_2003_, v___f_1988_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__17(lean_object* v_onMotive_2005_, lean_object* v_motiveArgs_2006_, lean_object* v_motiveBody_2007_, lean_object* v_toBind_2008_, lean_object* v___f_2009_, lean_object* v_____r_2010_){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = lean_apply_2(v_onMotive_2005_, v_motiveArgs_2006_, v_motiveBody_2007_);
v___x_2012_ = lean_apply_4(v_toBind_2008_, lean_box(0), lean_box(0), v___x_2011_, v___f_2009_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__18(lean_object* v___f_2013_, lean_object* v_____r_2014_){
_start:
{
lean_object* v___x_2015_; 
v___x_2015_ = lean_apply_1(v___f_2013_, v_____r_2014_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19(lean_object* v_toPure_2016_, lean_object* v_inst_2017_, lean_object* v_toBind_2018_, lean_object* v_toMatcherInfo_2019_, lean_object* v_discrs_x27_2020_, lean_object* v_inst_2021_, lean_object* v___f_2022_, lean_object* v_onMotive_2023_, lean_object* v_discrs_2024_, lean_object* v_inst_2025_, lean_object* v_motiveArgs_2026_, lean_object* v_motiveBody_2027_){
_start:
{
lean_object* v___f_2028_; lean_object* v___f_2029_; lean_object* v___f_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
lean_inc_ref_n(v_motiveArgs_2026_, 3);
lean_inc_n(v_toBind_2018_, 3);
v___f_2028_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__15), 5, 4);
lean_closure_set(v___f_2028_, 0, v_toPure_2016_);
lean_closure_set(v___f_2028_, 1, v_inst_2017_);
lean_closure_set(v___f_2028_, 2, v_toBind_2018_);
lean_closure_set(v___f_2028_, 3, v_motiveArgs_2026_);
lean_inc_ref(v_inst_2021_);
v___f_2029_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16), 8, 7);
lean_closure_set(v___f_2029_, 0, v_toMatcherInfo_2019_);
lean_closure_set(v___f_2029_, 1, v_discrs_x27_2020_);
lean_closure_set(v___f_2029_, 2, v_motiveArgs_2026_);
lean_closure_set(v___f_2029_, 3, v_inst_2021_);
lean_closure_set(v___f_2029_, 4, v___f_2022_);
lean_closure_set(v___f_2029_, 5, v_toBind_2018_);
lean_closure_set(v___f_2029_, 6, v___f_2028_);
lean_inc_ref(v___f_2029_);
lean_inc_ref(v_motiveBody_2027_);
lean_inc(v_onMotive_2023_);
v___f_2030_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__17), 6, 5);
lean_closure_set(v___f_2030_, 0, v_onMotive_2023_);
lean_closure_set(v___f_2030_, 1, v_motiveArgs_2026_);
lean_closure_set(v___f_2030_, 2, v_motiveBody_2027_);
lean_closure_set(v___f_2030_, 3, v_toBind_2018_);
lean_closure_set(v___f_2030_, 4, v___f_2029_);
v___x_2031_ = lean_array_get_size(v_motiveArgs_2026_);
v___x_2032_ = lean_array_get_size(v_discrs_2024_);
v___x_2033_ = lean_nat_dec_eq(v___x_2031_, v___x_2032_);
if (v___x_2033_ == 0)
{
lean_object* v___f_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
lean_dec_ref(v___f_2029_);
lean_dec_ref(v_motiveBody_2027_);
lean_dec_ref(v_motiveArgs_2026_);
lean_dec(v_onMotive_2023_);
v___f_2034_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__18), 2, 1);
lean_closure_set(v___f_2034_, 0, v___f_2030_);
v___x_2035_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_2036_ = l_Nat_reprFast(v___x_2032_);
v___x_2037_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
v___x_2038_ = l_Lean_MessageData_ofFormat(v___x_2037_);
v___x_2039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2035_);
lean_ctor_set(v___x_2039_, 1, v___x_2038_);
v___x_2040_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_2041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2039_);
lean_ctor_set(v___x_2041_, 1, v___x_2040_);
v___x_2042_ = l_Lean_throwError___redArg(v_inst_2021_, v_inst_2025_, v___x_2041_);
v___x_2043_ = lean_apply_4(v_toBind_2018_, lean_box(0), lean_box(0), v___x_2042_, v___f_2034_);
return v___x_2043_;
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
lean_dec_ref(v___f_2030_);
lean_dec_ref(v_inst_2025_);
lean_dec_ref(v_inst_2021_);
v___x_2044_ = lean_box(0);
v___x_2045_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__17(v_onMotive_2023_, v_motiveArgs_2026_, v_motiveBody_2027_, v_toBind_2018_, v___f_2029_, v___x_2044_);
return v___x_2045_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19___boxed(lean_object* v_toPure_2046_, lean_object* v_inst_2047_, lean_object* v_toBind_2048_, lean_object* v_toMatcherInfo_2049_, lean_object* v_discrs_x27_2050_, lean_object* v_inst_2051_, lean_object* v___f_2052_, lean_object* v_onMotive_2053_, lean_object* v_discrs_2054_, lean_object* v_inst_2055_, lean_object* v_motiveArgs_2056_, lean_object* v_motiveBody_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__19(v_toPure_2046_, v_inst_2047_, v_toBind_2048_, v_toMatcherInfo_2049_, v_discrs_x27_2050_, v_inst_2051_, v___f_2052_, v_onMotive_2053_, v_discrs_2054_, v_inst_2055_, v_motiveArgs_2056_, v_motiveBody_2057_);
lean_dec_ref(v_discrs_2054_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20(lean_object* v_fst_2059_, lean_object* v_numParams_2060_, lean_object* v_numDiscrs_2061_, lean_object* v_altInfos_2062_, lean_object* v_uElimPos_x3f_2063_, lean_object* v_snd_2064_, lean_object* v_overlaps_2065_, lean_object* v_matcherName_2066_, lean_object* v_matcherLevels_2067_, lean_object* v_params_x27_2068_, lean_object* v_fst_2069_, lean_object* v_discrs_x27_2070_, lean_object* v_fst_2071_, lean_object* v_toPure_2072_, lean_object* v_____do__lift_2073_){
_start:
{
lean_object* v_remaining_x27_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v_remaining_x27_2074_ = l_Array_append___redArg(v_fst_2059_, v_____do__lift_2073_);
v___x_2075_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2075_, 0, v_numParams_2060_);
lean_ctor_set(v___x_2075_, 1, v_numDiscrs_2061_);
lean_ctor_set(v___x_2075_, 2, v_altInfos_2062_);
lean_ctor_set(v___x_2075_, 3, v_uElimPos_x3f_2063_);
lean_ctor_set(v___x_2075_, 4, v_snd_2064_);
lean_ctor_set(v___x_2075_, 5, v_overlaps_2065_);
v___x_2076_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
lean_ctor_set(v___x_2076_, 1, v_matcherName_2066_);
lean_ctor_set(v___x_2076_, 2, v_matcherLevels_2067_);
lean_ctor_set(v___x_2076_, 3, v_params_x27_2068_);
lean_ctor_set(v___x_2076_, 4, v_fst_2069_);
lean_ctor_set(v___x_2076_, 5, v_discrs_x27_2070_);
lean_ctor_set(v___x_2076_, 6, v_fst_2071_);
lean_ctor_set(v___x_2076_, 7, v_remaining_x27_2074_);
v___x_2077_ = lean_apply_2(v_toPure_2072_, lean_box(0), v___x_2076_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20___boxed(lean_object* v_fst_2078_, lean_object* v_numParams_2079_, lean_object* v_numDiscrs_2080_, lean_object* v_altInfos_2081_, lean_object* v_uElimPos_x3f_2082_, lean_object* v_snd_2083_, lean_object* v_overlaps_2084_, lean_object* v_matcherName_2085_, lean_object* v_matcherLevels_2086_, lean_object* v_params_x27_2087_, lean_object* v_fst_2088_, lean_object* v_discrs_x27_2089_, lean_object* v_fst_2090_, lean_object* v_toPure_2091_, lean_object* v_____do__lift_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__20(v_fst_2078_, v_numParams_2079_, v_numDiscrs_2080_, v_altInfos_2081_, v_uElimPos_x3f_2082_, v_snd_2083_, v_overlaps_2084_, v_matcherName_2085_, v_matcherLevels_2086_, v_params_x27_2087_, v_fst_2088_, v_discrs_x27_2089_, v_fst_2090_, v_toPure_2091_, v_____do__lift_2092_);
lean_dec_ref(v_____do__lift_2092_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21(lean_object* v_fst_2094_, lean_object* v_numParams_2095_, lean_object* v_numDiscrs_2096_, lean_object* v_altInfos_2097_, lean_object* v_uElimPos_x3f_2098_, lean_object* v_snd_2099_, lean_object* v_overlaps_2100_, lean_object* v_matcherName_2101_, lean_object* v_matcherLevels_2102_, lean_object* v_params_x27_2103_, lean_object* v_fst_2104_, lean_object* v_discrs_x27_2105_, lean_object* v_toPure_2106_, lean_object* v_onRemaining_2107_, lean_object* v_remaining_2108_, lean_object* v_toBind_2109_, lean_object* v_____s_2110_){
_start:
{
lean_object* v_fst_2111_; lean_object* v___f_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v_fst_2111_ = lean_ctor_get(v_____s_2110_, 0);
lean_inc(v_fst_2111_);
lean_dec_ref(v_____s_2110_);
v___f_2112_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__20___boxed), 15, 14);
lean_closure_set(v___f_2112_, 0, v_fst_2094_);
lean_closure_set(v___f_2112_, 1, v_numParams_2095_);
lean_closure_set(v___f_2112_, 2, v_numDiscrs_2096_);
lean_closure_set(v___f_2112_, 3, v_altInfos_2097_);
lean_closure_set(v___f_2112_, 4, v_uElimPos_x3f_2098_);
lean_closure_set(v___f_2112_, 5, v_snd_2099_);
lean_closure_set(v___f_2112_, 6, v_overlaps_2100_);
lean_closure_set(v___f_2112_, 7, v_matcherName_2101_);
lean_closure_set(v___f_2112_, 8, v_matcherLevels_2102_);
lean_closure_set(v___f_2112_, 9, v_params_x27_2103_);
lean_closure_set(v___f_2112_, 10, v_fst_2104_);
lean_closure_set(v___f_2112_, 11, v_discrs_x27_2105_);
lean_closure_set(v___f_2112_, 12, v_fst_2111_);
lean_closure_set(v___f_2112_, 13, v_toPure_2106_);
v___x_2113_ = lean_apply_1(v_onRemaining_2107_, v_remaining_2108_);
v___x_2114_ = lean_apply_4(v_toBind_2109_, lean_box(0), lean_box(0), v___x_2113_, v___f_2112_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed(lean_object** _args){
lean_object* v_fst_2115_ = _args[0];
lean_object* v_numParams_2116_ = _args[1];
lean_object* v_numDiscrs_2117_ = _args[2];
lean_object* v_altInfos_2118_ = _args[3];
lean_object* v_uElimPos_x3f_2119_ = _args[4];
lean_object* v_snd_2120_ = _args[5];
lean_object* v_overlaps_2121_ = _args[6];
lean_object* v_matcherName_2122_ = _args[7];
lean_object* v_matcherLevels_2123_ = _args[8];
lean_object* v_params_x27_2124_ = _args[9];
lean_object* v_fst_2125_ = _args[10];
lean_object* v_discrs_x27_2126_ = _args[11];
lean_object* v_toPure_2127_ = _args[12];
lean_object* v_onRemaining_2128_ = _args[13];
lean_object* v_remaining_2129_ = _args[14];
lean_object* v_toBind_2130_ = _args[15];
lean_object* v_____s_2131_ = _args[16];
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__21(v_fst_2115_, v_numParams_2116_, v_numDiscrs_2117_, v_altInfos_2118_, v_uElimPos_x3f_2119_, v_snd_2120_, v_overlaps_2121_, v_matcherName_2122_, v_matcherLevels_2123_, v_params_x27_2124_, v_fst_2125_, v_discrs_x27_2126_, v_toPure_2127_, v_onRemaining_2128_, v_remaining_2129_, v_toBind_2130_, v_____s_2131_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22(lean_object* v_toPure_2133_, lean_object* v_next_2134_, lean_object* v_G_2135_, lean_object* v_____do__lift_2136_){
_start:
{
if (lean_obj_tag(v_____do__lift_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2138_; 
lean_dec(v_G_2135_);
v_a_2137_ = lean_ctor_get(v_____do__lift_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v_____do__lift_2136_, 1);
v___x_2138_ = lean_apply_2(v_toPure_2133_, lean_box(0), v_a_2137_);
return v___x_2138_;
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
lean_dec(v_toPure_2133_);
v_a_2139_ = lean_ctor_get(v_____do__lift_2136_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v_____do__lift_2136_, 1);
v___x_2140_ = lean_unsigned_to_nat(1u);
v___x_2141_ = lean_nat_add(v_next_2134_, v___x_2140_);
v___x_2142_ = lean_apply_4(v_G_2135_, v___x_2141_, v_a_2139_, lean_box(0), lean_box(0));
return v___x_2142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22___boxed(lean_object* v_toPure_2143_, lean_object* v_next_2144_, lean_object* v_G_2145_, lean_object* v_____do__lift_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__22(v_toPure_2143_, v_next_2144_, v_G_2145_, v_____do__lift_2146_);
lean_dec(v_next_2144_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23(lean_object* v_xs_2148_, lean_object* v_ys4_2149_, uint8_t v___x_2150_, uint8_t v___x_2151_, lean_object* v_inst_2152_, lean_object* v_alt_x27_2153_){
_start:
{
lean_object* v___x_2154_; uint8_t v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2154_ = l_Array_append___redArg(v_xs_2148_, v_ys4_2149_);
v___x_2155_ = 1;
v___x_2156_ = lean_box(v___x_2150_);
v___x_2157_ = lean_box(v___x_2151_);
v___x_2158_ = lean_box(v___x_2150_);
v___x_2159_ = lean_box(v___x_2151_);
v___x_2160_ = lean_box(v___x_2155_);
v___x_2161_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_2161_, 0, v___x_2154_);
lean_closure_set(v___x_2161_, 1, v_alt_x27_2153_);
lean_closure_set(v___x_2161_, 2, v___x_2156_);
lean_closure_set(v___x_2161_, 3, v___x_2157_);
lean_closure_set(v___x_2161_, 4, v___x_2158_);
lean_closure_set(v___x_2161_, 5, v___x_2159_);
lean_closure_set(v___x_2161_, 6, v___x_2160_);
v___x_2162_ = lean_apply_2(v_inst_2152_, lean_box(0), v___x_2161_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed(lean_object* v_xs_2163_, lean_object* v_ys4_2164_, lean_object* v___x_2165_, lean_object* v___x_2166_, lean_object* v_inst_2167_, lean_object* v_alt_x27_2168_){
_start:
{
uint8_t v___x_12783__boxed_2169_; uint8_t v___x_12784__boxed_2170_; lean_object* v_res_2171_; 
v___x_12783__boxed_2169_ = lean_unbox(v___x_2165_);
v___x_12784__boxed_2170_ = lean_unbox(v___x_2166_);
v_res_2171_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__23(v_xs_2163_, v_ys4_2164_, v___x_12783__boxed_2169_, v___x_12784__boxed_2170_, v_inst_2167_, v_alt_x27_2168_);
lean_dec_ref(v_ys4_2164_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__24(lean_object* v_xs_2172_, lean_object* v_remaining_x27_2173_, lean_object* v_ys4_2174_, lean_object* v_onAlt_2175_, lean_object* v_next_2176_, lean_object* v_altType_2177_, lean_object* v_toBind_2178_, lean_object* v___f_2179_, lean_object* v_alt_2180_){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
lean_inc_ref(v_remaining_x27_2173_);
lean_inc_ref(v_xs_2172_);
v___x_2181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2181_, 0, v_xs_2172_);
lean_ctor_set(v___x_2181_, 1, v_xs_2172_);
lean_ctor_set(v___x_2181_, 2, v_remaining_x27_2173_);
lean_ctor_set(v___x_2181_, 3, v_remaining_x27_2173_);
lean_ctor_set(v___x_2181_, 4, v_ys4_2174_);
v___x_2182_ = lean_apply_4(v_onAlt_2175_, v_next_2176_, v_altType_2177_, v___x_2181_, v_alt_2180_);
v___x_2183_ = lean_apply_4(v_toBind_2178_, lean_box(0), lean_box(0), v___x_2182_, v___f_2179_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25(lean_object* v___x_2184_, lean_object* v_xs_2185_, lean_object* v_inst_2186_, lean_object* v_toBind_2187_, lean_object* v___f_2188_, lean_object* v_inst_2189_, lean_object* v_inst_2190_, lean_object* v_names_2191_){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
lean_inc_ref(v_xs_2185_);
v___x_2192_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLambda___boxed), 7, 2);
lean_closure_set(v___x_2192_, 0, v___x_2184_);
lean_closure_set(v___x_2192_, 1, v_xs_2185_);
v___x_2193_ = lean_apply_2(v_inst_2186_, lean_box(0), v___x_2192_);
v___x_2194_ = lean_apply_4(v_toBind_2187_, lean_box(0), lean_box(0), v___x_2193_, v___f_2188_);
v___x_2195_ = l_Lean_Meta_MatcherApp_withUserNames___redArg(v_inst_2189_, v_inst_2190_, v_xs_2185_, v_names_2191_, v___x_2194_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26(lean_object* v_xs_2196_, uint8_t v___x_2197_, uint8_t v___x_2198_, lean_object* v_inst_2199_, lean_object* v_remaining_x27_2200_, lean_object* v_onAlt_2201_, lean_object* v_next_2202_, lean_object* v_toBind_2203_, lean_object* v___x_2204_, lean_object* v_inst_2205_, lean_object* v_inst_2206_, lean_object* v___f_2207_, lean_object* v_ys4_2208_, lean_object* v_altType_2209_){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___f_2212_; lean_object* v___f_2213_; lean_object* v___f_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2210_ = lean_box(v___x_2197_);
v___x_2211_ = lean_box(v___x_2198_);
lean_inc(v_inst_2199_);
lean_inc_ref(v_ys4_2208_);
lean_inc_ref_n(v_xs_2196_, 2);
v___f_2212_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed), 6, 5);
lean_closure_set(v___f_2212_, 0, v_xs_2196_);
lean_closure_set(v___f_2212_, 1, v_ys4_2208_);
lean_closure_set(v___f_2212_, 2, v___x_2210_);
lean_closure_set(v___f_2212_, 3, v___x_2211_);
lean_closure_set(v___f_2212_, 4, v_inst_2199_);
lean_inc_n(v_toBind_2203_, 2);
v___f_2213_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__24), 9, 8);
lean_closure_set(v___f_2213_, 0, v_xs_2196_);
lean_closure_set(v___f_2213_, 1, v_remaining_x27_2200_);
lean_closure_set(v___f_2213_, 2, v_ys4_2208_);
lean_closure_set(v___f_2213_, 3, v_onAlt_2201_);
lean_closure_set(v___f_2213_, 4, v_next_2202_);
lean_closure_set(v___f_2213_, 5, v_altType_2209_);
lean_closure_set(v___f_2213_, 6, v_toBind_2203_);
lean_closure_set(v___f_2213_, 7, v___f_2212_);
lean_inc_ref(v_inst_2206_);
lean_inc_ref(v_inst_2205_);
lean_inc_ref(v___x_2204_);
v___f_2214_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__25), 8, 7);
lean_closure_set(v___f_2214_, 0, v___x_2204_);
lean_closure_set(v___f_2214_, 1, v_xs_2196_);
lean_closure_set(v___f_2214_, 2, v_inst_2199_);
lean_closure_set(v___f_2214_, 3, v_toBind_2203_);
lean_closure_set(v___f_2214_, 4, v___f_2213_);
lean_closure_set(v___f_2214_, 5, v_inst_2205_);
lean_closure_set(v___f_2214_, 6, v_inst_2206_);
v___x_2215_ = l_Lean_Meta_lambdaTelescope___redArg(v_inst_2205_, v_inst_2206_, v___x_2204_, v___f_2207_, v___x_2197_);
v___x_2216_ = lean_apply_4(v_toBind_2203_, lean_box(0), lean_box(0), v___x_2215_, v___f_2214_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed(lean_object* v_xs_2217_, lean_object* v___x_2218_, lean_object* v___x_2219_, lean_object* v_inst_2220_, lean_object* v_remaining_x27_2221_, lean_object* v_onAlt_2222_, lean_object* v_next_2223_, lean_object* v_toBind_2224_, lean_object* v___x_2225_, lean_object* v_inst_2226_, lean_object* v_inst_2227_, lean_object* v___f_2228_, lean_object* v_ys4_2229_, lean_object* v_altType_2230_){
_start:
{
uint8_t v___x_12836__boxed_2231_; uint8_t v___x_12837__boxed_2232_; lean_object* v_res_2233_; 
v___x_12836__boxed_2231_ = lean_unbox(v___x_2218_);
v___x_12837__boxed_2232_ = lean_unbox(v___x_2219_);
v_res_2233_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__26(v_xs_2217_, v___x_12836__boxed_2231_, v___x_12837__boxed_2232_, v_inst_2220_, v_remaining_x27_2221_, v_onAlt_2222_, v_next_2223_, v_toBind_2224_, v___x_2225_, v_inst_2226_, v_inst_2227_, v___f_2228_, v_ys4_2229_, v_altType_2230_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27(uint8_t v___x_2234_, uint8_t v___x_2235_, lean_object* v_inst_2236_, lean_object* v_remaining_x27_2237_, lean_object* v_onAlt_2238_, lean_object* v_next_2239_, lean_object* v_toBind_2240_, lean_object* v___x_2241_, lean_object* v_inst_2242_, lean_object* v_inst_2243_, lean_object* v___f_2244_, lean_object* v_fst_2245_, lean_object* v_xs_2246_, lean_object* v_altType_2247_){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___f_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2248_ = lean_box(v___x_2234_);
v___x_2249_ = lean_box(v___x_2235_);
lean_inc_ref(v_inst_2243_);
lean_inc_ref(v_inst_2242_);
v___f_2250_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed), 14, 12);
lean_closure_set(v___f_2250_, 0, v_xs_2246_);
lean_closure_set(v___f_2250_, 1, v___x_2248_);
lean_closure_set(v___f_2250_, 2, v___x_2249_);
lean_closure_set(v___f_2250_, 3, v_inst_2236_);
lean_closure_set(v___f_2250_, 4, v_remaining_x27_2237_);
lean_closure_set(v___f_2250_, 5, v_onAlt_2238_);
lean_closure_set(v___f_2250_, 6, v_next_2239_);
lean_closure_set(v___f_2250_, 7, v_toBind_2240_);
lean_closure_set(v___f_2250_, 8, v___x_2241_);
lean_closure_set(v___f_2250_, 9, v_inst_2242_);
lean_closure_set(v___f_2250_, 10, v_inst_2243_);
lean_closure_set(v___f_2250_, 11, v___f_2244_);
v___x_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2251_, 0, v_fst_2245_);
v___x_2252_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2242_, v_inst_2243_, v_altType_2247_, v___x_2251_, v___f_2250_, v___x_2234_, v___x_2234_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed(lean_object* v___x_2253_, lean_object* v___x_2254_, lean_object* v_inst_2255_, lean_object* v_remaining_x27_2256_, lean_object* v_onAlt_2257_, lean_object* v_next_2258_, lean_object* v_toBind_2259_, lean_object* v___x_2260_, lean_object* v_inst_2261_, lean_object* v_inst_2262_, lean_object* v___f_2263_, lean_object* v_fst_2264_, lean_object* v_xs_2265_, lean_object* v_altType_2266_){
_start:
{
uint8_t v___x_12871__boxed_2267_; uint8_t v___x_12872__boxed_2268_; lean_object* v_res_2269_; 
v___x_12871__boxed_2267_ = lean_unbox(v___x_2253_);
v___x_12872__boxed_2268_ = lean_unbox(v___x_2254_);
v_res_2269_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__27(v___x_12871__boxed_2267_, v___x_12872__boxed_2268_, v_inst_2255_, v_remaining_x27_2256_, v_onAlt_2257_, v_next_2258_, v_toBind_2259_, v___x_2260_, v_inst_2261_, v_inst_2262_, v___f_2263_, v_fst_2264_, v_xs_2265_, v_altType_2266_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__28(lean_object* v_fst_2270_, lean_object* v___x_2271_, lean_object* v___x_2272_, lean_object* v___x_2273_, lean_object* v_toPure_2274_, lean_object* v_alt_x27_2275_){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2276_ = lean_array_push(v_fst_2270_, v_alt_x27_2275_);
v___x_2277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2271_);
lean_ctor_set(v___x_2277_, 1, v___x_2272_);
v___x_2278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2273_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
v___x_2279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2276_);
lean_ctor_set(v___x_2279_, 1, v___x_2278_);
v___x_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
v___x_2281_ = lean_apply_2(v_toPure_2274_, lean_box(0), v___x_2280_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29(lean_object* v___x_2282_, lean_object* v_toPure_2283_, lean_object* v_toBind_2284_, lean_object* v___f_2285_, uint8_t v___x_2286_, uint8_t v___x_2287_, lean_object* v_inst_2288_, lean_object* v_remaining_x27_2289_, lean_object* v_onAlt_2290_, lean_object* v_inst_2291_, lean_object* v_inst_2292_, lean_object* v___f_2293_, lean_object* v_fst_2294_, lean_object* v_next_2295_, lean_object* v_acc_2296_, lean_object* v_h_2297_, lean_object* v_G_2298_){
_start:
{
uint8_t v___x_2299_; 
v___x_2299_ = lean_nat_dec_lt(v_next_2295_, v___x_2282_);
if (v___x_2299_ == 0)
{
lean_object* v___x_2300_; 
lean_dec(v_G_2298_);
lean_dec(v_next_2295_);
lean_dec(v_fst_2294_);
lean_dec(v___f_2293_);
lean_dec_ref(v_inst_2292_);
lean_dec_ref(v_inst_2291_);
lean_dec(v_onAlt_2290_);
lean_dec_ref(v_remaining_x27_2289_);
lean_dec(v_inst_2288_);
lean_dec(v___f_2285_);
lean_dec(v_toBind_2284_);
v___x_2300_ = lean_apply_2(v_toPure_2283_, lean_box(0), v_acc_2296_);
return v___x_2300_;
}
else
{
lean_object* v_snd_2301_; lean_object* v_snd_2302_; lean_object* v_snd_2303_; lean_object* v_fst_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2414_; 
v_snd_2301_ = lean_ctor_get(v_acc_2296_, 1);
lean_inc(v_snd_2301_);
v_snd_2302_ = lean_ctor_get(v_snd_2301_, 1);
lean_inc(v_snd_2302_);
v_snd_2303_ = lean_ctor_get(v_snd_2302_, 1);
lean_inc(v_snd_2303_);
v_fst_2304_ = lean_ctor_get(v_acc_2296_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v_acc_2296_);
if (v_isSharedCheck_2414_ == 0)
{
lean_object* v_unused_2415_; 
v_unused_2415_ = lean_ctor_get(v_acc_2296_, 1);
lean_dec(v_unused_2415_);
v___x_2306_ = v_acc_2296_;
v_isShared_2307_ = v_isSharedCheck_2414_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_fst_2304_);
lean_dec(v_acc_2296_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2414_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v_fst_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2412_; 
v_fst_2308_ = lean_ctor_get(v_snd_2301_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v_snd_2301_);
if (v_isSharedCheck_2412_ == 0)
{
lean_object* v_unused_2413_; 
v_unused_2413_ = lean_ctor_get(v_snd_2301_, 1);
lean_dec(v_unused_2413_);
v___x_2310_ = v_snd_2301_;
v_isShared_2311_ = v_isSharedCheck_2412_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_fst_2308_);
lean_dec(v_snd_2301_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2412_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v_fst_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2410_; 
v_fst_2312_ = lean_ctor_get(v_snd_2302_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v_snd_2302_);
if (v_isSharedCheck_2410_ == 0)
{
lean_object* v_unused_2411_; 
v_unused_2411_ = lean_ctor_get(v_snd_2302_, 1);
lean_dec(v_unused_2411_);
v___x_2314_ = v_snd_2302_;
v_isShared_2315_ = v_isSharedCheck_2410_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_fst_2312_);
lean_dec(v_snd_2302_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2410_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v_array_2316_; lean_object* v_start_2317_; lean_object* v_stop_2318_; lean_object* v___f_2319_; lean_object* v___y_2321_; uint8_t v___x_2324_; 
v_array_2316_ = lean_ctor_get(v_snd_2303_, 0);
v_start_2317_ = lean_ctor_get(v_snd_2303_, 1);
v_stop_2318_ = lean_ctor_get(v_snd_2303_, 2);
lean_inc(v_next_2295_);
lean_inc(v_toPure_2283_);
v___f_2319_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__22___boxed), 4, 3);
lean_closure_set(v___f_2319_, 0, v_toPure_2283_);
lean_closure_set(v___f_2319_, 1, v_next_2295_);
lean_closure_set(v___f_2319_, 2, v_G_2298_);
v___x_2324_ = lean_nat_dec_lt(v_start_2317_, v_stop_2318_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2326_; 
lean_dec(v_next_2295_);
lean_dec(v_fst_2294_);
lean_dec(v___f_2293_);
lean_dec_ref(v_inst_2292_);
lean_dec_ref(v_inst_2291_);
lean_dec(v_onAlt_2290_);
lean_dec_ref(v_remaining_x27_2289_);
lean_dec(v_inst_2288_);
if (v_isShared_2315_ == 0)
{
v___x_2326_ = v___x_2314_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_fst_2312_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_snd_2303_);
v___x_2326_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
lean_object* v___x_2328_; 
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 1, v___x_2326_);
v___x_2328_ = v___x_2310_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_fst_2308_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v___x_2326_);
v___x_2328_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
lean_object* v___x_2330_; 
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 1, v___x_2328_);
v___x_2330_ = v___x_2306_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_fst_2304_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v___x_2328_);
v___x_2330_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2330_);
v___x_2332_ = lean_apply_2(v_toPure_2283_, lean_box(0), v___x_2331_);
v___y_2321_ = v___x_2332_;
goto v___jp_2320_;
}
}
}
}
else
{
lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2406_; 
lean_inc(v_stop_2318_);
lean_inc(v_start_2317_);
lean_inc_ref(v_array_2316_);
v_isSharedCheck_2406_ = !lean_is_exclusive(v_snd_2303_);
if (v_isSharedCheck_2406_ == 0)
{
lean_object* v_unused_2407_; lean_object* v_unused_2408_; lean_object* v_unused_2409_; 
v_unused_2407_ = lean_ctor_get(v_snd_2303_, 2);
lean_dec(v_unused_2407_);
v_unused_2408_ = lean_ctor_get(v_snd_2303_, 1);
lean_dec(v_unused_2408_);
v_unused_2409_ = lean_ctor_get(v_snd_2303_, 0);
lean_dec(v_unused_2409_);
v___x_2337_ = v_snd_2303_;
v_isShared_2338_ = v_isSharedCheck_2406_;
goto v_resetjp_2336_;
}
else
{
lean_dec(v_snd_2303_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2406_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v_array_2339_; lean_object* v_start_2340_; lean_object* v_stop_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2346_; 
v_array_2339_ = lean_ctor_get(v_fst_2312_, 0);
v_start_2340_ = lean_ctor_get(v_fst_2312_, 1);
v_stop_2341_ = lean_ctor_get(v_fst_2312_, 2);
v___x_2342_ = lean_array_fget(v_array_2316_, v_start_2317_);
v___x_2343_ = lean_unsigned_to_nat(1u);
v___x_2344_ = lean_nat_add(v_start_2317_, v___x_2343_);
lean_dec(v_start_2317_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 1, v___x_2344_);
v___x_2346_ = v___x_2337_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_array_2316_);
lean_ctor_set(v_reuseFailAlloc_2405_, 1, v___x_2344_);
lean_ctor_set(v_reuseFailAlloc_2405_, 2, v_stop_2318_);
v___x_2346_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
uint8_t v___x_2347_; 
v___x_2347_ = lean_nat_dec_lt(v_start_2340_, v_stop_2341_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2349_; 
lean_dec(v___x_2342_);
lean_dec(v_next_2295_);
lean_dec(v_fst_2294_);
lean_dec(v___f_2293_);
lean_dec_ref(v_inst_2292_);
lean_dec_ref(v_inst_2291_);
lean_dec(v_onAlt_2290_);
lean_dec_ref(v_remaining_x27_2289_);
lean_dec(v_inst_2288_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 1, v___x_2346_);
v___x_2349_ = v___x_2314_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_fst_2312_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v___x_2346_);
v___x_2349_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
lean_object* v___x_2351_; 
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 1, v___x_2349_);
v___x_2351_ = v___x_2310_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_fst_2308_);
lean_ctor_set(v_reuseFailAlloc_2357_, 1, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
lean_object* v___x_2353_; 
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 1, v___x_2351_);
v___x_2353_ = v___x_2306_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_fst_2304_);
lean_ctor_set(v_reuseFailAlloc_2356_, 1, v___x_2351_);
v___x_2353_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
v___x_2355_ = lean_apply_2(v_toPure_2283_, lean_box(0), v___x_2354_);
v___y_2321_ = v___x_2355_;
goto v___jp_2320_;
}
}
}
}
else
{
lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2401_; 
lean_inc(v_stop_2341_);
lean_inc(v_start_2340_);
lean_inc_ref(v_array_2339_);
v_isSharedCheck_2401_ = !lean_is_exclusive(v_fst_2312_);
if (v_isSharedCheck_2401_ == 0)
{
lean_object* v_unused_2402_; lean_object* v_unused_2403_; lean_object* v_unused_2404_; 
v_unused_2402_ = lean_ctor_get(v_fst_2312_, 2);
lean_dec(v_unused_2402_);
v_unused_2403_ = lean_ctor_get(v_fst_2312_, 1);
lean_dec(v_unused_2403_);
v_unused_2404_ = lean_ctor_get(v_fst_2312_, 0);
lean_dec(v_unused_2404_);
v___x_2360_ = v_fst_2312_;
v_isShared_2361_ = v_isSharedCheck_2401_;
goto v_resetjp_2359_;
}
else
{
lean_dec(v_fst_2312_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2401_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v_array_2362_; lean_object* v_start_2363_; lean_object* v_stop_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2368_; 
v_array_2362_ = lean_ctor_get(v_fst_2308_, 0);
v_start_2363_ = lean_ctor_get(v_fst_2308_, 1);
v_stop_2364_ = lean_ctor_get(v_fst_2308_, 2);
v___x_2365_ = lean_array_fget(v_array_2339_, v_start_2340_);
v___x_2366_ = lean_nat_add(v_start_2340_, v___x_2343_);
lean_dec(v_start_2340_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 1, v___x_2366_);
v___x_2368_ = v___x_2360_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_array_2339_);
lean_ctor_set(v_reuseFailAlloc_2400_, 1, v___x_2366_);
lean_ctor_set(v_reuseFailAlloc_2400_, 2, v_stop_2341_);
v___x_2368_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
uint8_t v___x_2369_; 
v___x_2369_ = lean_nat_dec_lt(v_start_2363_, v_stop_2364_);
if (v___x_2369_ == 0)
{
lean_object* v___x_2371_; 
lean_dec(v___x_2365_);
lean_dec(v___x_2342_);
lean_dec(v_next_2295_);
lean_dec(v_fst_2294_);
lean_dec(v___f_2293_);
lean_dec_ref(v_inst_2292_);
lean_dec_ref(v_inst_2291_);
lean_dec(v_onAlt_2290_);
lean_dec_ref(v_remaining_x27_2289_);
lean_dec(v_inst_2288_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 1, v___x_2346_);
lean_ctor_set(v___x_2314_, 0, v___x_2368_);
v___x_2371_ = v___x_2314_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2368_);
lean_ctor_set(v_reuseFailAlloc_2380_, 1, v___x_2346_);
v___x_2371_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
lean_object* v___x_2373_; 
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 1, v___x_2371_);
v___x_2373_ = v___x_2310_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_fst_2308_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v___x_2371_);
v___x_2373_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
lean_object* v___x_2375_; 
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 1, v___x_2373_);
v___x_2375_ = v___x_2306_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_fst_2304_);
lean_ctor_set(v_reuseFailAlloc_2378_, 1, v___x_2373_);
v___x_2375_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
v___x_2377_ = lean_apply_2(v_toPure_2283_, lean_box(0), v___x_2376_);
v___y_2321_ = v___x_2377_;
goto v___jp_2320_;
}
}
}
}
else
{
lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2396_; 
lean_inc(v_stop_2364_);
lean_inc(v_start_2363_);
lean_inc_ref(v_array_2362_);
lean_del_object(v___x_2314_);
lean_del_object(v___x_2310_);
lean_del_object(v___x_2306_);
v_isSharedCheck_2396_ = !lean_is_exclusive(v_fst_2308_);
if (v_isSharedCheck_2396_ == 0)
{
lean_object* v_unused_2397_; lean_object* v_unused_2398_; lean_object* v_unused_2399_; 
v_unused_2397_ = lean_ctor_get(v_fst_2308_, 2);
lean_dec(v_unused_2397_);
v_unused_2398_ = lean_ctor_get(v_fst_2308_, 1);
lean_dec(v_unused_2398_);
v_unused_2399_ = lean_ctor_get(v_fst_2308_, 0);
lean_dec(v_unused_2399_);
v___x_2382_ = v_fst_2308_;
v_isShared_2383_ = v_isSharedCheck_2396_;
goto v_resetjp_2381_;
}
else
{
lean_dec(v_fst_2308_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2396_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___f_2387_; lean_object* v___x_2388_; lean_object* v___x_2390_; 
v___x_2384_ = lean_array_fget_borrowed(v_array_2362_, v_start_2363_);
v___x_2385_ = lean_box(v___x_2286_);
v___x_2386_ = lean_box(v___x_2287_);
lean_inc_ref(v_inst_2292_);
lean_inc_ref(v_inst_2291_);
lean_inc(v___x_2384_);
lean_inc(v_toBind_2284_);
v___f_2387_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed), 14, 12);
lean_closure_set(v___f_2387_, 0, v___x_2385_);
lean_closure_set(v___f_2387_, 1, v___x_2386_);
lean_closure_set(v___f_2387_, 2, v_inst_2288_);
lean_closure_set(v___f_2387_, 3, v_remaining_x27_2289_);
lean_closure_set(v___f_2387_, 4, v_onAlt_2290_);
lean_closure_set(v___f_2387_, 5, v_next_2295_);
lean_closure_set(v___f_2387_, 6, v_toBind_2284_);
lean_closure_set(v___f_2387_, 7, v___x_2384_);
lean_closure_set(v___f_2387_, 8, v_inst_2291_);
lean_closure_set(v___f_2387_, 9, v_inst_2292_);
lean_closure_set(v___f_2387_, 10, v___f_2293_);
lean_closure_set(v___f_2387_, 11, v_fst_2294_);
v___x_2388_ = lean_nat_add(v_start_2363_, v___x_2343_);
lean_dec(v_start_2363_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 1, v___x_2388_);
v___x_2390_ = v___x_2382_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_array_2362_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v___x_2388_);
lean_ctor_set(v_reuseFailAlloc_2395_, 2, v_stop_2364_);
v___x_2390_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
lean_object* v___f_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___f_2391_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__28), 6, 5);
lean_closure_set(v___f_2391_, 0, v_fst_2304_);
lean_closure_set(v___f_2391_, 1, v___x_2368_);
lean_closure_set(v___f_2391_, 2, v___x_2346_);
lean_closure_set(v___f_2391_, 3, v___x_2390_);
lean_closure_set(v___f_2391_, 4, v_toPure_2283_);
v___x_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2365_);
v___x_2393_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2291_, v_inst_2292_, v___x_2342_, v___x_2392_, v___f_2387_, v___x_2286_, v___x_2286_);
lean_inc(v_toBind_2284_);
v___x_2394_ = lean_apply_4(v_toBind_2284_, lean_box(0), lean_box(0), v___x_2393_, v___f_2391_);
v___y_2321_ = v___x_2394_;
goto v___jp_2320_;
}
}
}
}
}
}
}
}
}
v___jp_2320_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
lean_inc(v_toBind_2284_);
v___x_2322_ = lean_apply_4(v_toBind_2284_, lean_box(0), lean_box(0), v___y_2321_, v___f_2285_);
v___x_2323_ = lean_apply_4(v_toBind_2284_, lean_box(0), lean_box(0), v___x_2322_, v___f_2319_);
return v___x_2323_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29___boxed(lean_object** _args){
lean_object* v___x_2416_ = _args[0];
lean_object* v_toPure_2417_ = _args[1];
lean_object* v_toBind_2418_ = _args[2];
lean_object* v___f_2419_ = _args[3];
lean_object* v___x_2420_ = _args[4];
lean_object* v___x_2421_ = _args[5];
lean_object* v_inst_2422_ = _args[6];
lean_object* v_remaining_x27_2423_ = _args[7];
lean_object* v_onAlt_2424_ = _args[8];
lean_object* v_inst_2425_ = _args[9];
lean_object* v_inst_2426_ = _args[10];
lean_object* v___f_2427_ = _args[11];
lean_object* v_fst_2428_ = _args[12];
lean_object* v_next_2429_ = _args[13];
lean_object* v_acc_2430_ = _args[14];
lean_object* v_h_2431_ = _args[15];
lean_object* v_G_2432_ = _args[16];
_start:
{
uint8_t v___x_12922__boxed_2433_; uint8_t v___x_12923__boxed_2434_; lean_object* v_res_2435_; 
v___x_12922__boxed_2433_ = lean_unbox(v___x_2420_);
v___x_12923__boxed_2434_ = lean_unbox(v___x_2421_);
v_res_2435_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__29(v___x_2416_, v_toPure_2417_, v_toBind_2418_, v___f_2419_, v___x_12922__boxed_2433_, v___x_12923__boxed_2434_, v_inst_2422_, v_remaining_x27_2423_, v_onAlt_2424_, v_inst_2425_, v_inst_2426_, v___f_2427_, v_fst_2428_, v_next_2429_, v_acc_2430_, v_h_2431_, v_G_2432_);
lean_dec(v___x_2416_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__30(lean_object* v_matcherApp_2436_, lean_object* v_alts_2437_, lean_object* v___x_2438_, lean_object* v___x_2439_, lean_object* v_remaining_x27_2440_, lean_object* v___f_2441_, lean_object* v_toBind_2442_, lean_object* v___f_2443_, lean_object* v_altTypes_2444_){
_start:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2445_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_2436_);
v___x_2446_ = lean_array_get_size(v___x_2445_);
v___x_2447_ = lean_array_get_size(v_altTypes_2444_);
lean_inc_n(v___x_2438_, 3);
v___x_2448_ = l_Array_toSubarray___redArg(v_alts_2437_, v___x_2438_, v___x_2439_);
v___x_2449_ = l_Array_toSubarray___redArg(v___x_2445_, v___x_2438_, v___x_2446_);
v___x_2450_ = l_Array_toSubarray___redArg(v_altTypes_2444_, v___x_2438_, v___x_2447_);
v___x_2451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2449_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
v___x_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2448_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2453_, 0, v_remaining_x27_2440_);
lean_ctor_set(v___x_2453_, 1, v___x_2452_);
v___x_2454_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2441_, v___x_2438_, v___x_2453_, lean_box(0));
v___x_2455_ = lean_apply_4(v_toBind_2442_, lean_box(0), lean_box(0), v___x_2454_, v___f_2443_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31(lean_object* v_alts_2456_, lean_object* v_toPure_2457_, lean_object* v_toBind_2458_, lean_object* v___f_2459_, uint8_t v___x_2460_, uint8_t v___x_2461_, lean_object* v_inst_2462_, lean_object* v_remaining_x27_2463_, lean_object* v_onAlt_2464_, lean_object* v_inst_2465_, lean_object* v_inst_2466_, lean_object* v___f_2467_, lean_object* v_fst_2468_, lean_object* v_matcherApp_2469_, lean_object* v___x_2470_, lean_object* v___f_2471_, lean_object* v_aux_2472_, lean_object* v_____r_2473_){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___f_2477_; lean_object* v___f_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2474_ = lean_array_get_size(v_alts_2456_);
v___x_2475_ = lean_box(v___x_2460_);
v___x_2476_ = lean_box(v___x_2461_);
lean_inc_ref(v_remaining_x27_2463_);
lean_inc(v_inst_2462_);
lean_inc_n(v_toBind_2458_, 2);
v___f_2477_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__29___boxed), 17, 13);
lean_closure_set(v___f_2477_, 0, v___x_2474_);
lean_closure_set(v___f_2477_, 1, v_toPure_2457_);
lean_closure_set(v___f_2477_, 2, v_toBind_2458_);
lean_closure_set(v___f_2477_, 3, v___f_2459_);
lean_closure_set(v___f_2477_, 4, v___x_2475_);
lean_closure_set(v___f_2477_, 5, v___x_2476_);
lean_closure_set(v___f_2477_, 6, v_inst_2462_);
lean_closure_set(v___f_2477_, 7, v_remaining_x27_2463_);
lean_closure_set(v___f_2477_, 8, v_onAlt_2464_);
lean_closure_set(v___f_2477_, 9, v_inst_2465_);
lean_closure_set(v___f_2477_, 10, v_inst_2466_);
lean_closure_set(v___f_2477_, 11, v___f_2467_);
lean_closure_set(v___f_2477_, 12, v_fst_2468_);
v___f_2478_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__30), 9, 8);
lean_closure_set(v___f_2478_, 0, v_matcherApp_2469_);
lean_closure_set(v___f_2478_, 1, v_alts_2456_);
lean_closure_set(v___f_2478_, 2, v___x_2470_);
lean_closure_set(v___f_2478_, 3, v___x_2474_);
lean_closure_set(v___f_2478_, 4, v_remaining_x27_2463_);
lean_closure_set(v___f_2478_, 5, v___f_2477_);
lean_closure_set(v___f_2478_, 6, v_toBind_2458_);
lean_closure_set(v___f_2478_, 7, v___f_2471_);
v___x_2479_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_2479_, 0, v___x_2474_);
lean_closure_set(v___x_2479_, 1, v_aux_2472_);
v___x_2480_ = lean_apply_2(v_inst_2462_, lean_box(0), v___x_2479_);
v___x_2481_ = lean_apply_4(v_toBind_2458_, lean_box(0), lean_box(0), v___x_2480_, v___f_2478_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed(lean_object** _args){
lean_object* v_alts_2482_ = _args[0];
lean_object* v_toPure_2483_ = _args[1];
lean_object* v_toBind_2484_ = _args[2];
lean_object* v___f_2485_ = _args[3];
lean_object* v___x_2486_ = _args[4];
lean_object* v___x_2487_ = _args[5];
lean_object* v_inst_2488_ = _args[6];
lean_object* v_remaining_x27_2489_ = _args[7];
lean_object* v_onAlt_2490_ = _args[8];
lean_object* v_inst_2491_ = _args[9];
lean_object* v_inst_2492_ = _args[10];
lean_object* v___f_2493_ = _args[11];
lean_object* v_fst_2494_ = _args[12];
lean_object* v_matcherApp_2495_ = _args[13];
lean_object* v___x_2496_ = _args[14];
lean_object* v___f_2497_ = _args[15];
lean_object* v_aux_2498_ = _args[16];
lean_object* v_____r_2499_ = _args[17];
_start:
{
uint8_t v___x_13179__boxed_2500_; uint8_t v___x_13180__boxed_2501_; lean_object* v_res_2502_; 
v___x_13179__boxed_2500_ = lean_unbox(v___x_2486_);
v___x_13180__boxed_2501_ = lean_unbox(v___x_2487_);
v_res_2502_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__31(v_alts_2482_, v_toPure_2483_, v_toBind_2484_, v___f_2485_, v___x_13179__boxed_2500_, v___x_13180__boxed_2501_, v_inst_2488_, v_remaining_x27_2489_, v_onAlt_2490_, v_inst_2491_, v_inst_2492_, v___f_2493_, v_fst_2494_, v_matcherApp_2495_, v___x_2496_, v___f_2497_, v_aux_2498_, v_____r_2499_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__32(lean_object* v___x_2503_, lean_object* v_e_2504_){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2505_ = l_Lean_indentD(v_e_2504_);
v___x_2506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2503_);
lean_ctor_set(v___x_2506_, 1, v___x_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33(lean_object* v___x_2507_, lean_object* v___f_2508_, lean_object* v_runInBase_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = lean_apply_2(v_runInBase_2509_, lean_box(0), v___x_2507_);
v___x_2516_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2515_, v___f_2508_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed(lean_object* v___x_2517_, lean_object* v___f_2518_, lean_object* v_runInBase_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__33(v___x_2517_, v___f_2518_, v_runInBase_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35(lean_object* v_toPure_2526_, lean_object* v_next_2527_, lean_object* v_G_2528_, lean_object* v_____do__lift_2529_){
_start:
{
if (lean_obj_tag(v_____do__lift_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2531_; 
lean_dec(v_G_2528_);
v_a_2530_ = lean_ctor_get(v_____do__lift_2529_, 0);
lean_inc(v_a_2530_);
lean_dec_ref_known(v_____do__lift_2529_, 1);
v___x_2531_ = lean_apply_2(v_toPure_2526_, lean_box(0), v_a_2530_);
return v___x_2531_;
}
else
{
lean_object* v_a_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
lean_dec(v_toPure_2526_);
v_a_2532_ = lean_ctor_get(v_____do__lift_2529_, 0);
lean_inc(v_a_2532_);
lean_dec_ref_known(v_____do__lift_2529_, 1);
v___x_2533_ = lean_unsigned_to_nat(1u);
v___x_2534_ = lean_nat_add(v_next_2527_, v___x_2533_);
v___x_2535_ = lean_apply_4(v_G_2528_, v___x_2534_, v_a_2532_, lean_box(0), lean_box(0));
return v___x_2535_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed(lean_object* v_toPure_2536_, lean_object* v_next_2537_, lean_object* v_G_2538_, lean_object* v_____do__lift_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__35(v_toPure_2536_, v_next_2537_, v_G_2538_, v_____do__lift_2539_);
lean_dec(v_next_2537_);
return v_res_2540_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5(void){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2549_ = lean_box(0);
v___x_2550_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__4));
v___x_2551_ = l_Lean_mkConst(v___x_2550_, v___x_2549_);
return v___x_2551_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6(void){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2552_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5);
v___x_2553_ = lean_unsigned_to_nat(2u);
v___x_2554_ = lean_mk_empty_array_with_capacity(v___x_2553_);
v___x_2555_ = lean_array_push(v___x_2554_, v___x_2552_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34(lean_object* v___x_2556_, lean_object* v_toPure_2557_, lean_object* v_inst_2558_, lean_object* v_alt_x27_2559_){
_start:
{
uint8_t v_hasUnitThunk_2560_; 
v_hasUnitThunk_2560_ = lean_ctor_get_uint8(v___x_2556_, sizeof(void*)*2);
if (v_hasUnitThunk_2560_ == 0)
{
lean_object* v___x_2561_; 
lean_dec(v_inst_2558_);
v___x_2561_ = lean_apply_2(v_toPure_2557_, lean_box(0), v_alt_x27_2559_);
return v___x_2561_;
}
else
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
lean_dec(v_toPure_2557_);
v___x_2562_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__2));
v___x_2563_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6);
v___x_2564_ = lean_array_push(v___x_2563_, v_alt_x27_2559_);
v___x_2565_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___boxed), 7, 2);
lean_closure_set(v___x_2565_, 0, v___x_2562_);
lean_closure_set(v___x_2565_, 1, v___x_2564_);
v___x_2566_ = lean_apply_2(v_inst_2558_, lean_box(0), v___x_2565_);
return v___x_2566_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed(lean_object* v___x_2567_, lean_object* v_toPure_2568_, lean_object* v_inst_2569_, lean_object* v_alt_x27_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__34(v___x_2567_, v_toPure_2568_, v_inst_2569_, v_alt_x27_2570_);
lean_dec_ref(v___x_2567_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36(lean_object* v_ys_2572_, lean_object* v_ys2_2573_, lean_object* v_ys3_2574_, lean_object* v_ys4_2575_, uint8_t v___x_2576_, uint8_t v_useSplitter_2577_, lean_object* v_inst_2578_, lean_object* v_alt_x27_2579_){
_start:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; uint8_t v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2580_ = l_Array_append___redArg(v_ys_2572_, v_ys2_2573_);
v___x_2581_ = l_Array_append___redArg(v___x_2580_, v_ys3_2574_);
v___x_2582_ = l_Array_append___redArg(v___x_2581_, v_ys4_2575_);
v___x_2583_ = 1;
v___x_2584_ = lean_box(v___x_2576_);
v___x_2585_ = lean_box(v_useSplitter_2577_);
v___x_2586_ = lean_box(v___x_2576_);
v___x_2587_ = lean_box(v_useSplitter_2577_);
v___x_2588_ = lean_box(v___x_2583_);
v___x_2589_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_2589_, 0, v___x_2582_);
lean_closure_set(v___x_2589_, 1, v_alt_x27_2579_);
lean_closure_set(v___x_2589_, 2, v___x_2584_);
lean_closure_set(v___x_2589_, 3, v___x_2585_);
lean_closure_set(v___x_2589_, 4, v___x_2586_);
lean_closure_set(v___x_2589_, 5, v___x_2587_);
lean_closure_set(v___x_2589_, 6, v___x_2588_);
v___x_2590_ = lean_apply_2(v_inst_2578_, lean_box(0), v___x_2589_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed(lean_object* v_ys_2591_, lean_object* v_ys2_2592_, lean_object* v_ys3_2593_, lean_object* v_ys4_2594_, lean_object* v___x_2595_, lean_object* v_useSplitter_2596_, lean_object* v_inst_2597_, lean_object* v_alt_x27_2598_){
_start:
{
uint8_t v___x_13333__boxed_2599_; uint8_t v_useSplitter_boxed_2600_; lean_object* v_res_2601_; 
v___x_13333__boxed_2599_ = lean_unbox(v___x_2595_);
v_useSplitter_boxed_2600_ = lean_unbox(v_useSplitter_2596_);
v_res_2601_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__36(v_ys_2591_, v_ys2_2592_, v_ys3_2593_, v_ys4_2594_, v___x_13333__boxed_2599_, v_useSplitter_boxed_2600_, v_inst_2597_, v_alt_x27_2598_);
lean_dec_ref(v_ys4_2594_);
lean_dec_ref(v_ys3_2593_);
lean_dec_ref(v_ys2_2592_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__37(lean_object* v_args_2602_, lean_object* v_ys_2603_, lean_object* v_ys2_2604_, lean_object* v_ys3_2605_, lean_object* v_ys4_2606_, lean_object* v_onAlt_2607_, lean_object* v_next_2608_, lean_object* v_altType_2609_, lean_object* v_toBind_2610_, lean_object* v___f_2611_, lean_object* v_alt_2612_){
_start:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2613_, 0, v_args_2602_);
lean_ctor_set(v___x_2613_, 1, v_ys_2603_);
lean_ctor_set(v___x_2613_, 2, v_ys2_2604_);
lean_ctor_set(v___x_2613_, 3, v_ys3_2605_);
lean_ctor_set(v___x_2613_, 4, v_ys4_2606_);
v___x_2614_ = lean_apply_4(v_onAlt_2607_, v_next_2608_, v_altType_2609_, v___x_2613_, v_alt_2612_);
v___x_2615_ = lean_apply_4(v_toBind_2610_, lean_box(0), lean_box(0), v___x_2614_, v___f_2611_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38(lean_object* v_toMonadExceptOf_2616_, lean_object* v_ys_2617_, lean_object* v_ys2_2618_, lean_object* v_ys3_2619_, uint8_t v___x_2620_, uint8_t v_useSplitter_2621_, lean_object* v_inst_2622_, lean_object* v_args_2623_, lean_object* v_onAlt_2624_, lean_object* v_next_2625_, lean_object* v_toBind_2626_, lean_object* v___x_2627_, lean_object* v___f_2628_, lean_object* v_ys4_2629_, lean_object* v_altType_2630_){
_start:
{
lean_object* v_tryCatch_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___f_2634_; lean_object* v___f_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v_tryCatch_2631_ = lean_ctor_get(v_toMonadExceptOf_2616_, 1);
lean_inc(v_tryCatch_2631_);
lean_dec_ref(v_toMonadExceptOf_2616_);
v___x_2632_ = lean_box(v___x_2620_);
v___x_2633_ = lean_box(v_useSplitter_2621_);
lean_inc(v_inst_2622_);
lean_inc_ref(v_ys4_2629_);
lean_inc_ref_n(v_ys3_2619_, 2);
lean_inc_ref(v_ys2_2618_);
lean_inc_ref(v_ys_2617_);
v___f_2634_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed), 8, 7);
lean_closure_set(v___f_2634_, 0, v_ys_2617_);
lean_closure_set(v___f_2634_, 1, v_ys2_2618_);
lean_closure_set(v___f_2634_, 2, v_ys3_2619_);
lean_closure_set(v___f_2634_, 3, v_ys4_2629_);
lean_closure_set(v___f_2634_, 4, v___x_2632_);
lean_closure_set(v___f_2634_, 5, v___x_2633_);
lean_closure_set(v___f_2634_, 6, v_inst_2622_);
lean_inc(v_toBind_2626_);
lean_inc_ref(v_args_2623_);
v___f_2635_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37), 11, 10);
lean_closure_set(v___f_2635_, 0, v_args_2623_);
lean_closure_set(v___f_2635_, 1, v_ys_2617_);
lean_closure_set(v___f_2635_, 2, v_ys2_2618_);
lean_closure_set(v___f_2635_, 3, v_ys3_2619_);
lean_closure_set(v___f_2635_, 4, v_ys4_2629_);
lean_closure_set(v___f_2635_, 5, v_onAlt_2624_);
lean_closure_set(v___f_2635_, 6, v_next_2625_);
lean_closure_set(v___f_2635_, 7, v_altType_2630_);
lean_closure_set(v___f_2635_, 8, v_toBind_2626_);
lean_closure_set(v___f_2635_, 9, v___f_2634_);
v___x_2636_ = l_Array_append___redArg(v_args_2623_, v_ys3_2619_);
lean_dec_ref(v_ys3_2619_);
v___x_2637_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLambda___boxed), 7, 2);
lean_closure_set(v___x_2637_, 0, v___x_2627_);
lean_closure_set(v___x_2637_, 1, v___x_2636_);
v___x_2638_ = lean_apply_2(v_inst_2622_, lean_box(0), v___x_2637_);
v___x_2639_ = lean_apply_3(v_tryCatch_2631_, lean_box(0), v___x_2638_, v___f_2628_);
v___x_2640_ = lean_apply_4(v_toBind_2626_, lean_box(0), lean_box(0), v___x_2639_, v___f_2635_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed(lean_object* v_toMonadExceptOf_2641_, lean_object* v_ys_2642_, lean_object* v_ys2_2643_, lean_object* v_ys3_2644_, lean_object* v___x_2645_, lean_object* v_useSplitter_2646_, lean_object* v_inst_2647_, lean_object* v_args_2648_, lean_object* v_onAlt_2649_, lean_object* v_next_2650_, lean_object* v_toBind_2651_, lean_object* v___x_2652_, lean_object* v___f_2653_, lean_object* v_ys4_2654_, lean_object* v_altType_2655_){
_start:
{
uint8_t v___x_13369__boxed_2656_; uint8_t v_useSplitter_boxed_2657_; lean_object* v_res_2658_; 
v___x_13369__boxed_2656_ = lean_unbox(v___x_2645_);
v_useSplitter_boxed_2657_ = lean_unbox(v_useSplitter_2646_);
v_res_2658_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__38(v_toMonadExceptOf_2641_, v_ys_2642_, v_ys2_2643_, v_ys3_2644_, v___x_13369__boxed_2656_, v_useSplitter_boxed_2657_, v_inst_2647_, v_args_2648_, v_onAlt_2649_, v_next_2650_, v_toBind_2651_, v___x_2652_, v___f_2653_, v_ys4_2654_, v_altType_2655_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39(lean_object* v_toMonadExceptOf_2659_, lean_object* v_ys_2660_, lean_object* v_ys2_2661_, uint8_t v___x_2662_, uint8_t v_useSplitter_2663_, lean_object* v_inst_2664_, lean_object* v_args_2665_, lean_object* v_onAlt_2666_, lean_object* v_next_2667_, lean_object* v_toBind_2668_, lean_object* v___x_2669_, lean_object* v___f_2670_, lean_object* v_fst_2671_, lean_object* v_inst_2672_, lean_object* v_inst_2673_, lean_object* v_ys3_2674_, lean_object* v_altType_2675_){
_start:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___f_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2676_ = lean_box(v___x_2662_);
v___x_2677_ = lean_box(v_useSplitter_2663_);
v___f_2678_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed), 15, 13);
lean_closure_set(v___f_2678_, 0, v_toMonadExceptOf_2659_);
lean_closure_set(v___f_2678_, 1, v_ys_2660_);
lean_closure_set(v___f_2678_, 2, v_ys2_2661_);
lean_closure_set(v___f_2678_, 3, v_ys3_2674_);
lean_closure_set(v___f_2678_, 4, v___x_2676_);
lean_closure_set(v___f_2678_, 5, v___x_2677_);
lean_closure_set(v___f_2678_, 6, v_inst_2664_);
lean_closure_set(v___f_2678_, 7, v_args_2665_);
lean_closure_set(v___f_2678_, 8, v_onAlt_2666_);
lean_closure_set(v___f_2678_, 9, v_next_2667_);
lean_closure_set(v___f_2678_, 10, v_toBind_2668_);
lean_closure_set(v___f_2678_, 11, v___x_2669_);
lean_closure_set(v___f_2678_, 12, v___f_2670_);
v___x_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2679_, 0, v_fst_2671_);
v___x_2680_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2672_, v_inst_2673_, v_altType_2675_, v___x_2679_, v___f_2678_, v___x_2662_, v___x_2662_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39___boxed(lean_object** _args){
lean_object* v_toMonadExceptOf_2681_ = _args[0];
lean_object* v_ys_2682_ = _args[1];
lean_object* v_ys2_2683_ = _args[2];
lean_object* v___x_2684_ = _args[3];
lean_object* v_useSplitter_2685_ = _args[4];
lean_object* v_inst_2686_ = _args[5];
lean_object* v_args_2687_ = _args[6];
lean_object* v_onAlt_2688_ = _args[7];
lean_object* v_next_2689_ = _args[8];
lean_object* v_toBind_2690_ = _args[9];
lean_object* v___x_2691_ = _args[10];
lean_object* v___f_2692_ = _args[11];
lean_object* v_fst_2693_ = _args[12];
lean_object* v_inst_2694_ = _args[13];
lean_object* v_inst_2695_ = _args[14];
lean_object* v_ys3_2696_ = _args[15];
lean_object* v_altType_2697_ = _args[16];
_start:
{
uint8_t v___x_13399__boxed_2698_; uint8_t v_useSplitter_boxed_2699_; lean_object* v_res_2700_; 
v___x_13399__boxed_2698_ = lean_unbox(v___x_2684_);
v_useSplitter_boxed_2699_ = lean_unbox(v_useSplitter_2685_);
v_res_2700_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__39(v_toMonadExceptOf_2681_, v_ys_2682_, v_ys2_2683_, v___x_13399__boxed_2698_, v_useSplitter_boxed_2699_, v_inst_2686_, v_args_2687_, v_onAlt_2688_, v_next_2689_, v_toBind_2690_, v___x_2691_, v___f_2692_, v_fst_2693_, v_inst_2694_, v_inst_2695_, v_ys3_2696_, v_altType_2697_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40(lean_object* v_toMonadExceptOf_2701_, lean_object* v_ys_2702_, uint8_t v___x_2703_, uint8_t v_useSplitter_2704_, lean_object* v_inst_2705_, lean_object* v_args_2706_, lean_object* v_onAlt_2707_, lean_object* v_next_2708_, lean_object* v_toBind_2709_, lean_object* v___x_2710_, lean_object* v___f_2711_, lean_object* v_fst_2712_, lean_object* v_inst_2713_, lean_object* v_inst_2714_, lean_object* v_numDiscrEqs_2715_, lean_object* v_ys2_2716_, lean_object* v_altType_2717_){
_start:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___f_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2718_ = lean_box(v___x_2703_);
v___x_2719_ = lean_box(v_useSplitter_2704_);
lean_inc_ref(v_inst_2714_);
lean_inc_ref(v_inst_2713_);
v___f_2720_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__39___boxed), 17, 15);
lean_closure_set(v___f_2720_, 0, v_toMonadExceptOf_2701_);
lean_closure_set(v___f_2720_, 1, v_ys_2702_);
lean_closure_set(v___f_2720_, 2, v_ys2_2716_);
lean_closure_set(v___f_2720_, 3, v___x_2718_);
lean_closure_set(v___f_2720_, 4, v___x_2719_);
lean_closure_set(v___f_2720_, 5, v_inst_2705_);
lean_closure_set(v___f_2720_, 6, v_args_2706_);
lean_closure_set(v___f_2720_, 7, v_onAlt_2707_);
lean_closure_set(v___f_2720_, 8, v_next_2708_);
lean_closure_set(v___f_2720_, 9, v_toBind_2709_);
lean_closure_set(v___f_2720_, 10, v___x_2710_);
lean_closure_set(v___f_2720_, 11, v___f_2711_);
lean_closure_set(v___f_2720_, 12, v_fst_2712_);
lean_closure_set(v___f_2720_, 13, v_inst_2713_);
lean_closure_set(v___f_2720_, 14, v_inst_2714_);
v___x_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2721_, 0, v_numDiscrEqs_2715_);
v___x_2722_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2713_, v_inst_2714_, v_altType_2717_, v___x_2721_, v___f_2720_, v___x_2703_, v___x_2703_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed(lean_object** _args){
lean_object* v_toMonadExceptOf_2723_ = _args[0];
lean_object* v_ys_2724_ = _args[1];
lean_object* v___x_2725_ = _args[2];
lean_object* v_useSplitter_2726_ = _args[3];
lean_object* v_inst_2727_ = _args[4];
lean_object* v_args_2728_ = _args[5];
lean_object* v_onAlt_2729_ = _args[6];
lean_object* v_next_2730_ = _args[7];
lean_object* v_toBind_2731_ = _args[8];
lean_object* v___x_2732_ = _args[9];
lean_object* v___f_2733_ = _args[10];
lean_object* v_fst_2734_ = _args[11];
lean_object* v_inst_2735_ = _args[12];
lean_object* v_inst_2736_ = _args[13];
lean_object* v_numDiscrEqs_2737_ = _args[14];
lean_object* v_ys2_2738_ = _args[15];
lean_object* v_altType_2739_ = _args[16];
_start:
{
uint8_t v___x_13427__boxed_2740_; uint8_t v_useSplitter_boxed_2741_; lean_object* v_res_2742_; 
v___x_13427__boxed_2740_ = lean_unbox(v___x_2725_);
v_useSplitter_boxed_2741_ = lean_unbox(v_useSplitter_2726_);
v_res_2742_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__40(v_toMonadExceptOf_2723_, v_ys_2724_, v___x_13427__boxed_2740_, v_useSplitter_boxed_2741_, v_inst_2727_, v_args_2728_, v_onAlt_2729_, v_next_2730_, v_toBind_2731_, v___x_2732_, v___f_2733_, v_fst_2734_, v_inst_2735_, v_inst_2736_, v_numDiscrEqs_2737_, v_ys2_2738_, v_altType_2739_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41(lean_object* v___x_2743_, lean_object* v_inst_2744_, lean_object* v_inst_2745_, lean_object* v___f_2746_, uint8_t v___x_2747_, lean_object* v_toBind_2748_, lean_object* v___f_2749_, lean_object* v_altType_2750_){
_start:
{
lean_object* v_numOverlaps_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v_numOverlaps_2751_ = lean_ctor_get(v___x_2743_, 1);
lean_inc(v_numOverlaps_2751_);
v___x_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2752_, 0, v_numOverlaps_2751_);
v___x_2753_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2744_, v_inst_2745_, v_altType_2750_, v___x_2752_, v___f_2746_, v___x_2747_, v___x_2747_);
v___x_2754_ = lean_apply_4(v_toBind_2748_, lean_box(0), lean_box(0), v___x_2753_, v___f_2749_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed(lean_object* v___x_2755_, lean_object* v_inst_2756_, lean_object* v_inst_2757_, lean_object* v___f_2758_, lean_object* v___x_2759_, lean_object* v_toBind_2760_, lean_object* v___f_2761_, lean_object* v_altType_2762_){
_start:
{
uint8_t v___x_13459__boxed_2763_; lean_object* v_res_2764_; 
v___x_13459__boxed_2763_ = lean_unbox(v___x_2759_);
v_res_2764_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__41(v___x_2755_, v_inst_2756_, v_inst_2757_, v___f_2758_, v___x_13459__boxed_2763_, v_toBind_2760_, v___f_2761_, v_altType_2762_);
lean_dec_ref(v___x_2755_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__42(lean_object* v___f_2765_, lean_object* v_altType_2766_){
_start:
{
lean_object* v___x_2767_; 
v___x_2767_ = lean_apply_1(v___f_2765_, v_altType_2766_);
return v___x_2767_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2(void){
_start:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2772_ = lean_box(0);
v___x_2773_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__1));
v___x_2774_ = l_Lean_mkConst(v___x_2773_, v___x_2772_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44(lean_object* v___x_2775_, lean_object* v_toPure_2776_, lean_object* v_toBind_2777_, lean_object* v___f_2778_, lean_object* v___x_2779_, lean_object* v_inst_2780_, lean_object* v___f_2781_, lean_object* v_altType_2782_){
_start:
{
uint8_t v_hasUnitThunk_2783_; 
v_hasUnitThunk_2783_ = lean_ctor_get_uint8(v___x_2775_, sizeof(void*)*2);
if (v_hasUnitThunk_2783_ == 0)
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
lean_dec(v___f_2781_);
lean_dec(v_inst_2780_);
v___x_2784_ = lean_apply_2(v_toPure_2776_, lean_box(0), v_altType_2782_);
v___x_2785_ = lean_apply_4(v_toBind_2777_, lean_box(0), lean_box(0), v___x_2784_, v___f_2778_);
return v___x_2785_;
}
else
{
lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
lean_dec(v___f_2778_);
lean_dec(v_toPure_2776_);
v___x_2786_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2);
v___x_2787_ = lean_mk_empty_array_with_capacity(v___x_2779_);
v___x_2788_ = lean_array_push(v___x_2787_, v___x_2786_);
v___x_2789_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateForall___boxed), 7, 2);
lean_closure_set(v___x_2789_, 0, v_altType_2782_);
lean_closure_set(v___x_2789_, 1, v___x_2788_);
v___x_2790_ = lean_apply_2(v_inst_2780_, lean_box(0), v___x_2789_);
v___x_2791_ = lean_apply_4(v_toBind_2777_, lean_box(0), lean_box(0), v___x_2790_, v___f_2781_);
return v___x_2791_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed(lean_object* v___x_2792_, lean_object* v_toPure_2793_, lean_object* v_toBind_2794_, lean_object* v___f_2795_, lean_object* v___x_2796_, lean_object* v_inst_2797_, lean_object* v___f_2798_, lean_object* v_altType_2799_){
_start:
{
lean_object* v_res_2800_; 
v_res_2800_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__44(v___x_2792_, v_toPure_2793_, v_toBind_2794_, v___f_2795_, v___x_2796_, v_inst_2797_, v___f_2798_, v_altType_2799_);
lean_dec(v___x_2796_);
lean_dec_ref(v___x_2792_);
return v_res_2800_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3(void){
_start:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2804_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__2));
v___x_2805_ = lean_unsigned_to_nat(8u);
v___x_2806_ = lean_unsigned_to_nat(360u);
v___x_2807_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__1));
v___x_2808_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__0));
v___x_2809_ = l_mkPanicMessageWithDecl(v___x_2808_, v___x_2807_, v___x_2806_, v___x_2805_, v___x_2804_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43(lean_object* v___x_2810_, lean_object* v___x_2811_, lean_object* v_toMonadExceptOf_2812_, uint8_t v___x_2813_, uint8_t v_useSplitter_2814_, lean_object* v_inst_2815_, lean_object* v_onAlt_2816_, lean_object* v_next_2817_, lean_object* v_toBind_2818_, lean_object* v___x_2819_, lean_object* v___f_2820_, lean_object* v_fst_2821_, lean_object* v_inst_2822_, lean_object* v_inst_2823_, lean_object* v_numDiscrEqs_2824_, lean_object* v___f_2825_, lean_object* v___x_2826_, lean_object* v_toPure_2827_, lean_object* v___x_2828_, lean_object* v___x_2829_, lean_object* v_ys_2830_, lean_object* v_args_2831_){
_start:
{
lean_object* v_numFields_2832_; lean_object* v___x_2833_; uint8_t v___x_2834_; 
v_numFields_2832_ = lean_ctor_get(v___x_2810_, 0);
v___x_2833_ = lean_array_get_size(v_ys_2830_);
v___x_2834_ = lean_nat_dec_eq(v___x_2833_, v_numFields_2832_);
if (v___x_2834_ == 0)
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
lean_dec_ref(v_args_2831_);
lean_dec_ref(v_ys_2830_);
lean_dec_ref(v___x_2829_);
lean_dec(v___x_2828_);
lean_dec(v_toPure_2827_);
lean_dec_ref(v___x_2826_);
lean_dec(v___f_2825_);
lean_dec(v_numDiscrEqs_2824_);
lean_dec_ref(v_inst_2823_);
lean_dec_ref(v_inst_2822_);
lean_dec(v_fst_2821_);
lean_dec(v___f_2820_);
lean_dec_ref(v___x_2819_);
lean_dec(v_toBind_2818_);
lean_dec(v_next_2817_);
lean_dec(v_onAlt_2816_);
lean_dec(v_inst_2815_);
lean_dec_ref(v_toMonadExceptOf_2812_);
lean_dec_ref(v___x_2810_);
v___x_2835_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3);
v___x_2836_ = l_panic___redArg(v___x_2811_, v___x_2835_);
return v___x_2836_;
}
else
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___f_2839_; lean_object* v___x_2840_; lean_object* v___f_2841_; lean_object* v___f_2842_; lean_object* v___f_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2837_ = lean_box(v___x_2813_);
v___x_2838_ = lean_box(v_useSplitter_2814_);
lean_inc_ref(v_inst_2823_);
lean_inc_ref(v_inst_2822_);
lean_inc_n(v_toBind_2818_, 3);
lean_inc_n(v_inst_2815_, 2);
lean_inc_ref(v_ys_2830_);
v___f_2839_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed), 17, 15);
lean_closure_set(v___f_2839_, 0, v_toMonadExceptOf_2812_);
lean_closure_set(v___f_2839_, 1, v_ys_2830_);
lean_closure_set(v___f_2839_, 2, v___x_2837_);
lean_closure_set(v___f_2839_, 3, v___x_2838_);
lean_closure_set(v___f_2839_, 4, v_inst_2815_);
lean_closure_set(v___f_2839_, 5, v_args_2831_);
lean_closure_set(v___f_2839_, 6, v_onAlt_2816_);
lean_closure_set(v___f_2839_, 7, v_next_2817_);
lean_closure_set(v___f_2839_, 8, v_toBind_2818_);
lean_closure_set(v___f_2839_, 9, v___x_2819_);
lean_closure_set(v___f_2839_, 10, v___f_2820_);
lean_closure_set(v___f_2839_, 11, v_fst_2821_);
lean_closure_set(v___f_2839_, 12, v_inst_2822_);
lean_closure_set(v___f_2839_, 13, v_inst_2823_);
lean_closure_set(v___f_2839_, 14, v_numDiscrEqs_2824_);
v___x_2840_ = lean_box(v___x_2813_);
v___f_2841_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed), 8, 7);
lean_closure_set(v___f_2841_, 0, v___x_2810_);
lean_closure_set(v___f_2841_, 1, v_inst_2822_);
lean_closure_set(v___f_2841_, 2, v_inst_2823_);
lean_closure_set(v___f_2841_, 3, v___f_2839_);
lean_closure_set(v___f_2841_, 4, v___x_2840_);
lean_closure_set(v___f_2841_, 5, v_toBind_2818_);
lean_closure_set(v___f_2841_, 6, v___f_2825_);
v___f_2842_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__42), 2, 1);
lean_closure_set(v___f_2842_, 0, v___f_2841_);
lean_inc_ref(v___f_2842_);
v___f_2843_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed), 8, 7);
lean_closure_set(v___f_2843_, 0, v___x_2826_);
lean_closure_set(v___f_2843_, 1, v_toPure_2827_);
lean_closure_set(v___f_2843_, 2, v_toBind_2818_);
lean_closure_set(v___f_2843_, 3, v___f_2842_);
lean_closure_set(v___f_2843_, 4, v___x_2828_);
lean_closure_set(v___f_2843_, 5, v_inst_2815_);
lean_closure_set(v___f_2843_, 6, v___f_2842_);
v___x_2844_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateForall___boxed), 7, 2);
lean_closure_set(v___x_2844_, 0, v___x_2829_);
lean_closure_set(v___x_2844_, 1, v_ys_2830_);
v___x_2845_ = lean_apply_2(v_inst_2815_, lean_box(0), v___x_2844_);
v___x_2846_ = lean_apply_4(v_toBind_2818_, lean_box(0), lean_box(0), v___x_2845_, v___f_2843_);
return v___x_2846_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed(lean_object** _args){
lean_object* v___x_2847_ = _args[0];
lean_object* v___x_2848_ = _args[1];
lean_object* v_toMonadExceptOf_2849_ = _args[2];
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
lean_object* v_inst_2860_ = _args[13];
lean_object* v_numDiscrEqs_2861_ = _args[14];
lean_object* v___f_2862_ = _args[15];
lean_object* v___x_2863_ = _args[16];
lean_object* v_toPure_2864_ = _args[17];
lean_object* v___x_2865_ = _args[18];
lean_object* v___x_2866_ = _args[19];
lean_object* v_ys_2867_ = _args[20];
lean_object* v_args_2868_ = _args[21];
_start:
{
uint8_t v___x_13556__boxed_2869_; uint8_t v_useSplitter_boxed_2870_; lean_object* v_res_2871_; 
v___x_13556__boxed_2869_ = lean_unbox(v___x_2850_);
v_useSplitter_boxed_2870_ = lean_unbox(v_useSplitter_2851_);
v_res_2871_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__43(v___x_2847_, v___x_2848_, v_toMonadExceptOf_2849_, v___x_13556__boxed_2869_, v_useSplitter_boxed_2870_, v_inst_2852_, v_onAlt_2853_, v_next_2854_, v_toBind_2855_, v___x_2856_, v___f_2857_, v_fst_2858_, v_inst_2859_, v_inst_2860_, v_numDiscrEqs_2861_, v___f_2862_, v___x_2863_, v_toPure_2864_, v___x_2865_, v___x_2866_, v_ys_2867_, v_args_2868_);
lean_dec(v___x_2848_);
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
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1(void){
_start:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2889_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0));
v___x_2890_ = lean_unsigned_to_nat(6u);
v___x_2891_ = lean_unsigned_to_nat(358u);
v___x_2892_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__1));
v___x_2893_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__0));
v___x_2894_ = l_mkPanicMessageWithDecl(v___x_2893_, v___x_2892_, v___x_2891_, v___x_2890_, v___x_2889_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46(lean_object* v___x_2895_, lean_object* v_toPure_2896_, lean_object* v_toBind_2897_, lean_object* v___f_2898_, lean_object* v___x_2899_, lean_object* v___x_2900_, lean_object* v_inst_2901_, lean_object* v___x_2902_, lean_object* v_toMonadExceptOf_2903_, uint8_t v___x_2904_, uint8_t v_useSplitter_2905_, lean_object* v_onAlt_2906_, lean_object* v___f_2907_, lean_object* v_fst_2908_, lean_object* v_inst_2909_, lean_object* v_inst_2910_, lean_object* v_numDiscrEqs_2911_, lean_object* v_next_2912_, lean_object* v_acc_2913_, lean_object* v_h_2914_, lean_object* v_G_2915_){
_start:
{
uint8_t v___x_2916_; 
v___x_2916_ = lean_nat_dec_lt(v_next_2912_, v___x_2895_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; 
lean_dec(v_G_2915_);
lean_dec(v_next_2912_);
lean_dec(v_numDiscrEqs_2911_);
lean_dec_ref(v_inst_2910_);
lean_dec_ref(v_inst_2909_);
lean_dec(v_fst_2908_);
lean_dec(v___f_2907_);
lean_dec(v_onAlt_2906_);
lean_dec_ref(v_toMonadExceptOf_2903_);
lean_dec(v___x_2902_);
lean_dec(v_inst_2901_);
lean_dec(v___f_2898_);
lean_dec(v_toBind_2897_);
v___x_2917_ = lean_apply_2(v_toPure_2896_, lean_box(0), v_acc_2913_);
return v___x_2917_;
}
else
{
lean_object* v_snd_2918_; lean_object* v_snd_2919_; lean_object* v_snd_2920_; lean_object* v_snd_2921_; lean_object* v_snd_2922_; lean_object* v_fst_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_3133_; 
v_snd_2918_ = lean_ctor_get(v_acc_2913_, 1);
lean_inc(v_snd_2918_);
v_snd_2919_ = lean_ctor_get(v_snd_2918_, 1);
lean_inc(v_snd_2919_);
v_snd_2920_ = lean_ctor_get(v_snd_2919_, 1);
lean_inc(v_snd_2920_);
v_snd_2921_ = lean_ctor_get(v_snd_2920_, 1);
lean_inc(v_snd_2921_);
v_snd_2922_ = lean_ctor_get(v_snd_2921_, 1);
lean_inc(v_snd_2922_);
v_fst_2923_ = lean_ctor_get(v_acc_2913_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v_acc_2913_);
if (v_isSharedCheck_3133_ == 0)
{
lean_object* v_unused_3134_; 
v_unused_3134_ = lean_ctor_get(v_acc_2913_, 1);
lean_dec(v_unused_3134_);
v___x_2925_ = v_acc_2913_;
v_isShared_2926_ = v_isSharedCheck_3133_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_fst_2923_);
lean_dec(v_acc_2913_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_3133_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v_fst_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_3131_; 
v_fst_2927_ = lean_ctor_get(v_snd_2918_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v_snd_2918_);
if (v_isSharedCheck_3131_ == 0)
{
lean_object* v_unused_3132_; 
v_unused_3132_ = lean_ctor_get(v_snd_2918_, 1);
lean_dec(v_unused_3132_);
v___x_2929_ = v_snd_2918_;
v_isShared_2930_ = v_isSharedCheck_3131_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_fst_2927_);
lean_dec(v_snd_2918_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_3131_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v_fst_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_3129_; 
v_fst_2931_ = lean_ctor_get(v_snd_2919_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v_snd_2919_);
if (v_isSharedCheck_3129_ == 0)
{
lean_object* v_unused_3130_; 
v_unused_3130_ = lean_ctor_get(v_snd_2919_, 1);
lean_dec(v_unused_3130_);
v___x_2933_ = v_snd_2919_;
v_isShared_2934_ = v_isSharedCheck_3129_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_fst_2931_);
lean_dec(v_snd_2919_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_3129_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v_fst_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_3127_; 
v_fst_2935_ = lean_ctor_get(v_snd_2920_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v_snd_2920_);
if (v_isSharedCheck_3127_ == 0)
{
lean_object* v_unused_3128_; 
v_unused_3128_ = lean_ctor_get(v_snd_2920_, 1);
lean_dec(v_unused_3128_);
v___x_2937_ = v_snd_2920_;
v_isShared_2938_ = v_isSharedCheck_3127_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_fst_2935_);
lean_dec(v_snd_2920_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_3127_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v_fst_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_3125_; 
v_fst_2939_ = lean_ctor_get(v_snd_2921_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v_snd_2921_);
if (v_isSharedCheck_3125_ == 0)
{
lean_object* v_unused_3126_; 
v_unused_3126_ = lean_ctor_get(v_snd_2921_, 1);
lean_dec(v_unused_3126_);
v___x_2941_ = v_snd_2921_;
v_isShared_2942_ = v_isSharedCheck_3125_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_fst_2939_);
lean_dec(v_snd_2921_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_3125_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v_array_2943_; lean_object* v_start_2944_; lean_object* v_stop_2945_; lean_object* v___f_2946_; lean_object* v___y_2948_; uint8_t v___x_2951_; 
v_array_2943_ = lean_ctor_get(v_snd_2922_, 0);
v_start_2944_ = lean_ctor_get(v_snd_2922_, 1);
v_stop_2945_ = lean_ctor_get(v_snd_2922_, 2);
lean_inc(v_next_2912_);
lean_inc(v_toPure_2896_);
v___f_2946_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed), 4, 3);
lean_closure_set(v___f_2946_, 0, v_toPure_2896_);
lean_closure_set(v___f_2946_, 1, v_next_2912_);
lean_closure_set(v___f_2946_, 2, v_G_2915_);
v___x_2951_ = lean_nat_dec_lt(v_start_2944_, v_stop_2945_);
if (v___x_2951_ == 0)
{
lean_object* v___x_2953_; 
lean_dec(v_next_2912_);
lean_dec(v_numDiscrEqs_2911_);
lean_dec_ref(v_inst_2910_);
lean_dec_ref(v_inst_2909_);
lean_dec(v_fst_2908_);
lean_dec(v___f_2907_);
lean_dec(v_onAlt_2906_);
lean_dec_ref(v_toMonadExceptOf_2903_);
lean_dec(v___x_2902_);
lean_dec(v_inst_2901_);
if (v_isShared_2942_ == 0)
{
v___x_2953_ = v___x_2941_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_fst_2939_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v_snd_2922_);
v___x_2953_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
lean_object* v___x_2955_; 
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 1, v___x_2953_);
v___x_2955_ = v___x_2937_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_fst_2935_);
lean_ctor_set(v_reuseFailAlloc_2967_, 1, v___x_2953_);
v___x_2955_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
lean_object* v___x_2957_; 
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 1, v___x_2955_);
v___x_2957_ = v___x_2933_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_fst_2931_);
lean_ctor_set(v_reuseFailAlloc_2966_, 1, v___x_2955_);
v___x_2957_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
lean_object* v___x_2959_; 
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 1, v___x_2957_);
v___x_2959_ = v___x_2929_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_fst_2927_);
lean_ctor_set(v_reuseFailAlloc_2965_, 1, v___x_2957_);
v___x_2959_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
lean_object* v___x_2961_; 
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 1, v___x_2959_);
v___x_2961_ = v___x_2925_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_fst_2923_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v___x_2959_);
v___x_2961_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
v___x_2963_ = lean_apply_2(v_toPure_2896_, lean_box(0), v___x_2962_);
v___y_2948_ = v___x_2963_;
goto v___jp_2947_;
}
}
}
}
}
}
else
{
lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_3121_; 
lean_inc(v_stop_2945_);
lean_inc(v_start_2944_);
lean_inc_ref(v_array_2943_);
v_isSharedCheck_3121_ = !lean_is_exclusive(v_snd_2922_);
if (v_isSharedCheck_3121_ == 0)
{
lean_object* v_unused_3122_; lean_object* v_unused_3123_; lean_object* v_unused_3124_; 
v_unused_3122_ = lean_ctor_get(v_snd_2922_, 2);
lean_dec(v_unused_3122_);
v_unused_3123_ = lean_ctor_get(v_snd_2922_, 1);
lean_dec(v_unused_3123_);
v_unused_3124_ = lean_ctor_get(v_snd_2922_, 0);
lean_dec(v_unused_3124_);
v___x_2970_ = v_snd_2922_;
v_isShared_2971_ = v_isSharedCheck_3121_;
goto v_resetjp_2969_;
}
else
{
lean_dec(v_snd_2922_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_3121_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v_array_2972_; lean_object* v_start_2973_; lean_object* v_stop_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2979_; 
v_array_2972_ = lean_ctor_get(v_fst_2939_, 0);
v_start_2973_ = lean_ctor_get(v_fst_2939_, 1);
v_stop_2974_ = lean_ctor_get(v_fst_2939_, 2);
v___x_2975_ = lean_array_fget(v_array_2943_, v_start_2944_);
v___x_2976_ = lean_unsigned_to_nat(1u);
v___x_2977_ = lean_nat_add(v_start_2944_, v___x_2976_);
lean_dec(v_start_2944_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 1, v___x_2977_);
v___x_2979_ = v___x_2970_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_array_2943_);
lean_ctor_set(v_reuseFailAlloc_3120_, 1, v___x_2977_);
lean_ctor_set(v_reuseFailAlloc_3120_, 2, v_stop_2945_);
v___x_2979_ = v_reuseFailAlloc_3120_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
uint8_t v___x_2980_; 
v___x_2980_ = lean_nat_dec_lt(v_start_2973_, v_stop_2974_);
if (v___x_2980_ == 0)
{
lean_object* v___x_2982_; 
lean_dec(v___x_2975_);
lean_dec(v_next_2912_);
lean_dec(v_numDiscrEqs_2911_);
lean_dec_ref(v_inst_2910_);
lean_dec_ref(v_inst_2909_);
lean_dec(v_fst_2908_);
lean_dec(v___f_2907_);
lean_dec(v_onAlt_2906_);
lean_dec_ref(v_toMonadExceptOf_2903_);
lean_dec(v___x_2902_);
lean_dec(v_inst_2901_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 1, v___x_2979_);
v___x_2982_ = v___x_2941_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_fst_2939_);
lean_ctor_set(v_reuseFailAlloc_2997_, 1, v___x_2979_);
v___x_2982_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
lean_object* v___x_2984_; 
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 1, v___x_2982_);
v___x_2984_ = v___x_2937_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_fst_2935_);
lean_ctor_set(v_reuseFailAlloc_2996_, 1, v___x_2982_);
v___x_2984_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
lean_object* v___x_2986_; 
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 1, v___x_2984_);
v___x_2986_ = v___x_2933_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_fst_2931_);
lean_ctor_set(v_reuseFailAlloc_2995_, 1, v___x_2984_);
v___x_2986_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
lean_object* v___x_2988_; 
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 1, v___x_2986_);
v___x_2988_ = v___x_2929_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_fst_2927_);
lean_ctor_set(v_reuseFailAlloc_2994_, 1, v___x_2986_);
v___x_2988_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
lean_object* v___x_2990_; 
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 1, v___x_2988_);
v___x_2990_ = v___x_2925_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_fst_2923_);
lean_ctor_set(v_reuseFailAlloc_2993_, 1, v___x_2988_);
v___x_2990_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
v___x_2992_ = lean_apply_2(v_toPure_2896_, lean_box(0), v___x_2991_);
v___y_2948_ = v___x_2992_;
goto v___jp_2947_;
}
}
}
}
}
}
else
{
lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3116_; 
lean_inc(v_stop_2974_);
lean_inc(v_start_2973_);
lean_inc_ref(v_array_2972_);
v_isSharedCheck_3116_ = !lean_is_exclusive(v_fst_2939_);
if (v_isSharedCheck_3116_ == 0)
{
lean_object* v_unused_3117_; lean_object* v_unused_3118_; lean_object* v_unused_3119_; 
v_unused_3117_ = lean_ctor_get(v_fst_2939_, 2);
lean_dec(v_unused_3117_);
v_unused_3118_ = lean_ctor_get(v_fst_2939_, 1);
lean_dec(v_unused_3118_);
v_unused_3119_ = lean_ctor_get(v_fst_2939_, 0);
lean_dec(v_unused_3119_);
v___x_2999_ = v_fst_2939_;
v_isShared_3000_ = v_isSharedCheck_3116_;
goto v_resetjp_2998_;
}
else
{
lean_dec(v_fst_2939_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3116_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v_array_3001_; lean_object* v_start_3002_; lean_object* v_stop_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3007_; 
v_array_3001_ = lean_ctor_get(v_fst_2935_, 0);
v_start_3002_ = lean_ctor_get(v_fst_2935_, 1);
v_stop_3003_ = lean_ctor_get(v_fst_2935_, 2);
v___x_3004_ = lean_array_fget(v_array_2972_, v_start_2973_);
v___x_3005_ = lean_nat_add(v_start_2973_, v___x_2976_);
lean_dec(v_start_2973_);
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 1, v___x_3005_);
v___x_3007_ = v___x_2999_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_array_2972_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v___x_3005_);
lean_ctor_set(v_reuseFailAlloc_3115_, 2, v_stop_2974_);
v___x_3007_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
uint8_t v___x_3008_; 
v___x_3008_ = lean_nat_dec_lt(v_start_3002_, v_stop_3003_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3010_; 
lean_dec(v___x_3004_);
lean_dec(v___x_2975_);
lean_dec(v_next_2912_);
lean_dec(v_numDiscrEqs_2911_);
lean_dec_ref(v_inst_2910_);
lean_dec_ref(v_inst_2909_);
lean_dec(v_fst_2908_);
lean_dec(v___f_2907_);
lean_dec(v_onAlt_2906_);
lean_dec_ref(v_toMonadExceptOf_2903_);
lean_dec(v___x_2902_);
lean_dec(v_inst_2901_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 1, v___x_2979_);
lean_ctor_set(v___x_2941_, 0, v___x_3007_);
v___x_3010_ = v___x_2941_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_3007_);
lean_ctor_set(v_reuseFailAlloc_3025_, 1, v___x_2979_);
v___x_3010_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
lean_object* v___x_3012_; 
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 1, v___x_3010_);
v___x_3012_ = v___x_2937_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_fst_2935_);
lean_ctor_set(v_reuseFailAlloc_3024_, 1, v___x_3010_);
v___x_3012_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
lean_object* v___x_3014_; 
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 1, v___x_3012_);
v___x_3014_ = v___x_2933_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_fst_2931_);
lean_ctor_set(v_reuseFailAlloc_3023_, 1, v___x_3012_);
v___x_3014_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
lean_object* v___x_3016_; 
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 1, v___x_3014_);
v___x_3016_ = v___x_2929_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_fst_2927_);
lean_ctor_set(v_reuseFailAlloc_3022_, 1, v___x_3014_);
v___x_3016_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
lean_object* v___x_3018_; 
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 1, v___x_3016_);
v___x_3018_ = v___x_2925_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_fst_2923_);
lean_ctor_set(v_reuseFailAlloc_3021_, 1, v___x_3016_);
v___x_3018_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
v___x_3020_ = lean_apply_2(v_toPure_2896_, lean_box(0), v___x_3019_);
v___y_2948_ = v___x_3020_;
goto v___jp_2947_;
}
}
}
}
}
}
else
{
lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3111_; 
lean_inc(v_stop_3003_);
lean_inc(v_start_3002_);
lean_inc_ref(v_array_3001_);
v_isSharedCheck_3111_ = !lean_is_exclusive(v_fst_2935_);
if (v_isSharedCheck_3111_ == 0)
{
lean_object* v_unused_3112_; lean_object* v_unused_3113_; lean_object* v_unused_3114_; 
v_unused_3112_ = lean_ctor_get(v_fst_2935_, 2);
lean_dec(v_unused_3112_);
v_unused_3113_ = lean_ctor_get(v_fst_2935_, 1);
lean_dec(v_unused_3113_);
v_unused_3114_ = lean_ctor_get(v_fst_2935_, 0);
lean_dec(v_unused_3114_);
v___x_3027_ = v_fst_2935_;
v_isShared_3028_ = v_isSharedCheck_3111_;
goto v_resetjp_3026_;
}
else
{
lean_dec(v_fst_2935_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3111_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v_array_3029_; lean_object* v_start_3030_; lean_object* v_stop_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3035_; 
v_array_3029_ = lean_ctor_get(v_fst_2931_, 0);
v_start_3030_ = lean_ctor_get(v_fst_2931_, 1);
v_stop_3031_ = lean_ctor_get(v_fst_2931_, 2);
v___x_3032_ = lean_array_fget(v_array_3001_, v_start_3002_);
v___x_3033_ = lean_nat_add(v_start_3002_, v___x_2976_);
lean_dec(v_start_3002_);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 1, v___x_3033_);
v___x_3035_ = v___x_3027_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_array_3001_);
lean_ctor_set(v_reuseFailAlloc_3110_, 1, v___x_3033_);
lean_ctor_set(v_reuseFailAlloc_3110_, 2, v_stop_3003_);
v___x_3035_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
uint8_t v___x_3036_; 
v___x_3036_ = lean_nat_dec_lt(v_start_3030_, v_stop_3031_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3038_; 
lean_dec(v___x_3032_);
lean_dec(v___x_3004_);
lean_dec(v___x_2975_);
lean_dec(v_next_2912_);
lean_dec(v_numDiscrEqs_2911_);
lean_dec_ref(v_inst_2910_);
lean_dec_ref(v_inst_2909_);
lean_dec(v_fst_2908_);
lean_dec(v___f_2907_);
lean_dec(v_onAlt_2906_);
lean_dec_ref(v_toMonadExceptOf_2903_);
lean_dec(v___x_2902_);
lean_dec(v_inst_2901_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 1, v___x_2979_);
lean_ctor_set(v___x_2941_, 0, v___x_3007_);
v___x_3038_ = v___x_2941_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3007_);
lean_ctor_set(v_reuseFailAlloc_3053_, 1, v___x_2979_);
v___x_3038_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
lean_object* v___x_3040_; 
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 1, v___x_3038_);
lean_ctor_set(v___x_2937_, 0, v___x_3035_);
v___x_3040_ = v___x_2937_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3035_);
lean_ctor_set(v_reuseFailAlloc_3052_, 1, v___x_3038_);
v___x_3040_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_object* v___x_3042_; 
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 1, v___x_3040_);
v___x_3042_ = v___x_2933_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_fst_2931_);
lean_ctor_set(v_reuseFailAlloc_3051_, 1, v___x_3040_);
v___x_3042_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3044_; 
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 1, v___x_3042_);
v___x_3044_ = v___x_2929_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_fst_2927_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v___x_3042_);
v___x_3044_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
lean_object* v___x_3046_; 
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 1, v___x_3044_);
v___x_3046_ = v___x_2925_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_fst_2923_);
lean_ctor_set(v_reuseFailAlloc_3049_, 1, v___x_3044_);
v___x_3046_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3046_);
v___x_3048_ = lean_apply_2(v_toPure_2896_, lean_box(0), v___x_3047_);
v___y_2948_ = v___x_3048_;
goto v___jp_2947_;
}
}
}
}
}
}
else
{
lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3106_; 
lean_inc(v_stop_3031_);
lean_inc(v_start_3030_);
lean_inc_ref(v_array_3029_);
v_isSharedCheck_3106_ = !lean_is_exclusive(v_fst_2931_);
if (v_isSharedCheck_3106_ == 0)
{
lean_object* v_unused_3107_; lean_object* v_unused_3108_; lean_object* v_unused_3109_; 
v_unused_3107_ = lean_ctor_get(v_fst_2931_, 2);
lean_dec(v_unused_3107_);
v_unused_3108_ = lean_ctor_get(v_fst_2931_, 1);
lean_dec(v_unused_3108_);
v_unused_3109_ = lean_ctor_get(v_fst_2931_, 0);
lean_dec(v_unused_3109_);
v___x_3055_ = v_fst_2931_;
v_isShared_3056_ = v_isSharedCheck_3106_;
goto v_resetjp_3054_;
}
else
{
lean_dec(v_fst_2931_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3106_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v_array_3057_; lean_object* v_start_3058_; lean_object* v_stop_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3063_; 
v_array_3057_ = lean_ctor_get(v_fst_2927_, 0);
v_start_3058_ = lean_ctor_get(v_fst_2927_, 1);
v_stop_3059_ = lean_ctor_get(v_fst_2927_, 2);
v___x_3060_ = lean_array_fget(v_array_3029_, v_start_3030_);
v___x_3061_ = lean_nat_add(v_start_3030_, v___x_2976_);
lean_dec(v_start_3030_);
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 1, v___x_3061_);
v___x_3063_ = v___x_3055_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_array_3029_);
lean_ctor_set(v_reuseFailAlloc_3105_, 1, v___x_3061_);
lean_ctor_set(v_reuseFailAlloc_3105_, 2, v_stop_3031_);
v___x_3063_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
uint8_t v___x_3064_; 
v___x_3064_ = lean_nat_dec_lt(v_start_3058_, v_stop_3059_);
if (v___x_3064_ == 0)
{
lean_object* v___x_3066_; 
lean_dec(v___x_3060_);
lean_dec(v___x_3032_);
lean_dec(v___x_3004_);
lean_dec(v___x_2975_);
lean_dec(v_next_2912_);
lean_dec(v_numDiscrEqs_2911_);
lean_dec_ref(v_inst_2910_);
lean_dec_ref(v_inst_2909_);
lean_dec(v_fst_2908_);
lean_dec(v___f_2907_);
lean_dec(v_onAlt_2906_);
lean_dec_ref(v_toMonadExceptOf_2903_);
lean_dec(v___x_2902_);
lean_dec(v_inst_2901_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 1, v___x_2979_);
lean_ctor_set(v___x_2941_, 0, v___x_3007_);
v___x_3066_ = v___x_2941_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v___x_3007_);
lean_ctor_set(v_reuseFailAlloc_3081_, 1, v___x_2979_);
v___x_3066_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
lean_object* v___x_3068_; 
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 1, v___x_3066_);
lean_ctor_set(v___x_2937_, 0, v___x_3035_);
v___x_3068_ = v___x_2937_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3035_);
lean_ctor_set(v_reuseFailAlloc_3080_, 1, v___x_3066_);
v___x_3068_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
lean_object* v___x_3070_; 
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 1, v___x_3068_);
lean_ctor_set(v___x_2933_, 0, v___x_3063_);
v___x_3070_ = v___x_2933_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3063_);
lean_ctor_set(v_reuseFailAlloc_3079_, 1, v___x_3068_);
v___x_3070_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
lean_object* v___x_3072_; 
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 1, v___x_3070_);
v___x_3072_ = v___x_2929_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_fst_2927_);
lean_ctor_set(v_reuseFailAlloc_3078_, 1, v___x_3070_);
v___x_3072_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
lean_object* v___x_3074_; 
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 1, v___x_3072_);
v___x_3074_ = v___x_2925_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_fst_2923_);
lean_ctor_set(v_reuseFailAlloc_3077_, 1, v___x_3072_);
v___x_3074_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
v___x_3076_ = lean_apply_2(v_toPure_2896_, lean_box(0), v___x_3075_);
v___y_2948_ = v___x_3076_;
goto v___jp_2947_;
}
}
}
}
}
}
else
{
lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3101_; 
lean_inc(v_stop_3059_);
lean_inc(v_start_3058_);
lean_inc_ref(v_array_3057_);
lean_del_object(v___x_2941_);
lean_del_object(v___x_2937_);
lean_del_object(v___x_2933_);
lean_del_object(v___x_2929_);
lean_del_object(v___x_2925_);
v_isSharedCheck_3101_ = !lean_is_exclusive(v_fst_2927_);
if (v_isSharedCheck_3101_ == 0)
{
lean_object* v_unused_3102_; lean_object* v_unused_3103_; lean_object* v_unused_3104_; 
v_unused_3102_ = lean_ctor_get(v_fst_2927_, 2);
lean_dec(v_unused_3102_);
v_unused_3103_ = lean_ctor_get(v_fst_2927_, 1);
lean_dec(v_unused_3103_);
v_unused_3104_ = lean_ctor_get(v_fst_2927_, 0);
lean_dec(v_unused_3104_);
v___x_3083_ = v_fst_2927_;
v_isShared_3084_ = v_isSharedCheck_3101_;
goto v_resetjp_3082_;
}
else
{
lean_dec(v_fst_2927_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3101_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v_numOverlaps_3085_; uint8_t v___x_3086_; 
v_numOverlaps_3085_ = lean_ctor_get(v___x_3060_, 1);
v___x_3086_ = lean_nat_dec_eq(v_numOverlaps_3085_, v___x_2899_);
if (v___x_3086_ == 0)
{
lean_object* v___x_3087_; lean_object* v___x_3088_; 
lean_del_object(v___x_3083_);
lean_dec_ref(v___x_3063_);
lean_dec(v___x_3060_);
lean_dec(v_stop_3059_);
lean_dec(v_start_3058_);
lean_dec_ref(v_array_3057_);
lean_dec_ref(v___x_3035_);
lean_dec(v___x_3032_);
lean_dec_ref(v___x_3007_);
lean_dec(v___x_3004_);
lean_dec_ref(v___x_2979_);
lean_dec(v___x_2975_);
lean_dec(v_fst_2923_);
lean_dec(v_next_2912_);
lean_dec(v_numDiscrEqs_2911_);
lean_dec_ref(v_inst_2910_);
lean_dec_ref(v_inst_2909_);
lean_dec(v_fst_2908_);
lean_dec(v___f_2907_);
lean_dec(v_onAlt_2906_);
lean_dec_ref(v_toMonadExceptOf_2903_);
lean_dec(v___x_2902_);
lean_dec(v_inst_2901_);
lean_dec(v_toPure_2896_);
v___x_3087_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_3088_ = l_panic___redArg(v___x_2900_, v___x_3087_);
v___y_2948_ = v___x_3088_;
goto v___jp_2947_;
}
else
{
lean_object* v___f_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___f_3093_; lean_object* v___x_3094_; lean_object* v___x_3096_; 
lean_inc(v_inst_2901_);
lean_inc_n(v_toPure_2896_, 2);
lean_inc(v___x_3032_);
v___f_3089_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed), 4, 3);
lean_closure_set(v___f_3089_, 0, v___x_3032_);
lean_closure_set(v___f_3089_, 1, v_toPure_2896_);
lean_closure_set(v___f_3089_, 2, v_inst_2901_);
v___x_3090_ = lean_array_fget_borrowed(v_array_3057_, v_start_3058_);
v___x_3091_ = lean_box(v___x_2904_);
v___x_3092_ = lean_box(v_useSplitter_2905_);
lean_inc(v___x_3060_);
lean_inc_ref(v_inst_2910_);
lean_inc_ref(v_inst_2909_);
lean_inc(v___x_3090_);
lean_inc(v_toBind_2897_);
v___f_3093_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed), 22, 20);
lean_closure_set(v___f_3093_, 0, v___x_3032_);
lean_closure_set(v___f_3093_, 1, v___x_2902_);
lean_closure_set(v___f_3093_, 2, v_toMonadExceptOf_2903_);
lean_closure_set(v___f_3093_, 3, v___x_3091_);
lean_closure_set(v___f_3093_, 4, v___x_3092_);
lean_closure_set(v___f_3093_, 5, v_inst_2901_);
lean_closure_set(v___f_3093_, 6, v_onAlt_2906_);
lean_closure_set(v___f_3093_, 7, v_next_2912_);
lean_closure_set(v___f_3093_, 8, v_toBind_2897_);
lean_closure_set(v___f_3093_, 9, v___x_3090_);
lean_closure_set(v___f_3093_, 10, v___f_2907_);
lean_closure_set(v___f_3093_, 11, v_fst_2908_);
lean_closure_set(v___f_3093_, 12, v_inst_2909_);
lean_closure_set(v___f_3093_, 13, v_inst_2910_);
lean_closure_set(v___f_3093_, 14, v_numDiscrEqs_2911_);
lean_closure_set(v___f_3093_, 15, v___f_3089_);
lean_closure_set(v___f_3093_, 16, v___x_3060_);
lean_closure_set(v___f_3093_, 17, v_toPure_2896_);
lean_closure_set(v___f_3093_, 18, v___x_2976_);
lean_closure_set(v___f_3093_, 19, v___x_2975_);
v___x_3094_ = lean_nat_add(v_start_3058_, v___x_2976_);
lean_dec(v_start_3058_);
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 1, v___x_3094_);
v___x_3096_ = v___x_3083_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_array_3057_);
lean_ctor_set(v_reuseFailAlloc_3100_, 1, v___x_3094_);
lean_ctor_set(v_reuseFailAlloc_3100_, 2, v_stop_3059_);
v___x_3096_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
lean_object* v___f_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___f_3097_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__45), 8, 7);
lean_closure_set(v___f_3097_, 0, v_fst_2923_);
lean_closure_set(v___f_3097_, 1, v___x_3007_);
lean_closure_set(v___f_3097_, 2, v___x_2979_);
lean_closure_set(v___f_3097_, 3, v___x_3035_);
lean_closure_set(v___f_3097_, 4, v___x_3063_);
lean_closure_set(v___f_3097_, 5, v___x_3096_);
lean_closure_set(v___f_3097_, 6, v_toPure_2896_);
v___x_3098_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(v_inst_2910_, v_inst_2909_, v___x_3004_, v___x_3060_, v___f_3093_);
lean_inc(v_toBind_2897_);
v___x_3099_ = lean_apply_4(v_toBind_2897_, lean_box(0), lean_box(0), v___x_3098_, v___f_3097_);
v___y_2948_ = v___x_3099_;
goto v___jp_2947_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_2947_:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
lean_inc(v_toBind_2897_);
v___x_2949_ = lean_apply_4(v_toBind_2897_, lean_box(0), lean_box(0), v___y_2948_, v___f_2898_);
v___x_2950_ = lean_apply_4(v_toBind_2897_, lean_box(0), lean_box(0), v___x_2949_, v___f_2946_);
return v___x_2950_;
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
lean_object* v___x_3140_ = _args[5];
lean_object* v_inst_3141_ = _args[6];
lean_object* v___x_3142_ = _args[7];
lean_object* v_toMonadExceptOf_3143_ = _args[8];
lean_object* v___x_3144_ = _args[9];
lean_object* v_useSplitter_3145_ = _args[10];
lean_object* v_onAlt_3146_ = _args[11];
lean_object* v___f_3147_ = _args[12];
lean_object* v_fst_3148_ = _args[13];
lean_object* v_inst_3149_ = _args[14];
lean_object* v_inst_3150_ = _args[15];
lean_object* v_numDiscrEqs_3151_ = _args[16];
lean_object* v_next_3152_ = _args[17];
lean_object* v_acc_3153_ = _args[18];
lean_object* v_h_3154_ = _args[19];
lean_object* v_G_3155_ = _args[20];
_start:
{
uint8_t v___x_13675__boxed_3156_; uint8_t v_useSplitter_boxed_3157_; lean_object* v_res_3158_; 
v___x_13675__boxed_3156_ = lean_unbox(v___x_3144_);
v_useSplitter_boxed_3157_ = lean_unbox(v_useSplitter_3145_);
v_res_3158_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__46(v___x_3135_, v_toPure_3136_, v_toBind_3137_, v___f_3138_, v___x_3139_, v___x_3140_, v_inst_3141_, v___x_3142_, v_toMonadExceptOf_3143_, v___x_13675__boxed_3156_, v_useSplitter_boxed_3157_, v_onAlt_3146_, v___f_3147_, v_fst_3148_, v_inst_3149_, v_inst_3150_, v_numDiscrEqs_3151_, v_next_3152_, v_acc_3153_, v_h_3154_, v_G_3155_);
lean_dec(v___x_3140_);
lean_dec(v___x_3139_);
lean_dec(v___x_3135_);
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47(lean_object* v_fst_3159_, lean_object* v_numParams_3160_, lean_object* v_numDiscrs_3161_, lean_object* v_altInfos_3162_, lean_object* v_uElimPos_x3f_3163_, lean_object* v_snd_3164_, lean_object* v_overlaps_3165_, lean_object* v_splitterName_3166_, lean_object* v_matcherLevels_3167_, lean_object* v_params_x27_3168_, lean_object* v_fst_3169_, lean_object* v_discrs_x27_3170_, lean_object* v_fst_3171_, lean_object* v_toPure_3172_, lean_object* v_____do__lift_3173_){
_start:
{
lean_object* v_remaining_x27_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v_remaining_x27_3174_ = l_Array_append___redArg(v_fst_3159_, v_____do__lift_3173_);
v___x_3175_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3175_, 0, v_numParams_3160_);
lean_ctor_set(v___x_3175_, 1, v_numDiscrs_3161_);
lean_ctor_set(v___x_3175_, 2, v_altInfos_3162_);
lean_ctor_set(v___x_3175_, 3, v_uElimPos_x3f_3163_);
lean_ctor_set(v___x_3175_, 4, v_snd_3164_);
lean_ctor_set(v___x_3175_, 5, v_overlaps_3165_);
v___x_3176_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3175_);
lean_ctor_set(v___x_3176_, 1, v_splitterName_3166_);
lean_ctor_set(v___x_3176_, 2, v_matcherLevels_3167_);
lean_ctor_set(v___x_3176_, 3, v_params_x27_3168_);
lean_ctor_set(v___x_3176_, 4, v_fst_3169_);
lean_ctor_set(v___x_3176_, 5, v_discrs_x27_3170_);
lean_ctor_set(v___x_3176_, 6, v_fst_3171_);
lean_ctor_set(v___x_3176_, 7, v_remaining_x27_3174_);
v___x_3177_ = lean_apply_2(v_toPure_3172_, lean_box(0), v___x_3176_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47___boxed(lean_object* v_fst_3178_, lean_object* v_numParams_3179_, lean_object* v_numDiscrs_3180_, lean_object* v_altInfos_3181_, lean_object* v_uElimPos_x3f_3182_, lean_object* v_snd_3183_, lean_object* v_overlaps_3184_, lean_object* v_splitterName_3185_, lean_object* v_matcherLevels_3186_, lean_object* v_params_x27_3187_, lean_object* v_fst_3188_, lean_object* v_discrs_x27_3189_, lean_object* v_fst_3190_, lean_object* v_toPure_3191_, lean_object* v_____do__lift_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__47(v_fst_3178_, v_numParams_3179_, v_numDiscrs_3180_, v_altInfos_3181_, v_uElimPos_x3f_3182_, v_snd_3183_, v_overlaps_3184_, v_splitterName_3185_, v_matcherLevels_3186_, v_params_x27_3187_, v_fst_3188_, v_discrs_x27_3189_, v_fst_3190_, v_toPure_3191_, v_____do__lift_3192_);
lean_dec_ref(v_____do__lift_3192_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48(lean_object* v_fst_3194_, lean_object* v_numParams_3195_, lean_object* v_numDiscrs_3196_, lean_object* v_altInfos_3197_, lean_object* v_uElimPos_x3f_3198_, lean_object* v_snd_3199_, lean_object* v_overlaps_3200_, lean_object* v_splitterName_3201_, lean_object* v_matcherLevels_3202_, lean_object* v_params_x27_3203_, lean_object* v_fst_3204_, lean_object* v_discrs_x27_3205_, lean_object* v_toPure_3206_, lean_object* v_onRemaining_3207_, lean_object* v_remaining_3208_, lean_object* v_toBind_3209_, lean_object* v_____s_3210_){
_start:
{
lean_object* v_fst_3211_; lean_object* v___f_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v_fst_3211_ = lean_ctor_get(v_____s_3210_, 0);
lean_inc(v_fst_3211_);
lean_dec_ref(v_____s_3210_);
v___f_3212_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__47___boxed), 15, 14);
lean_closure_set(v___f_3212_, 0, v_fst_3194_);
lean_closure_set(v___f_3212_, 1, v_numParams_3195_);
lean_closure_set(v___f_3212_, 2, v_numDiscrs_3196_);
lean_closure_set(v___f_3212_, 3, v_altInfos_3197_);
lean_closure_set(v___f_3212_, 4, v_uElimPos_x3f_3198_);
lean_closure_set(v___f_3212_, 5, v_snd_3199_);
lean_closure_set(v___f_3212_, 6, v_overlaps_3200_);
lean_closure_set(v___f_3212_, 7, v_splitterName_3201_);
lean_closure_set(v___f_3212_, 8, v_matcherLevels_3202_);
lean_closure_set(v___f_3212_, 9, v_params_x27_3203_);
lean_closure_set(v___f_3212_, 10, v_fst_3204_);
lean_closure_set(v___f_3212_, 11, v_discrs_x27_3205_);
lean_closure_set(v___f_3212_, 12, v_fst_3211_);
lean_closure_set(v___f_3212_, 13, v_toPure_3206_);
v___x_3213_ = lean_apply_1(v_onRemaining_3207_, v_remaining_3208_);
v___x_3214_ = lean_apply_4(v_toBind_3209_, lean_box(0), lean_box(0), v___x_3213_, v___f_3212_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed(lean_object** _args){
lean_object* v_fst_3215_ = _args[0];
lean_object* v_numParams_3216_ = _args[1];
lean_object* v_numDiscrs_3217_ = _args[2];
lean_object* v_altInfos_3218_ = _args[3];
lean_object* v_uElimPos_x3f_3219_ = _args[4];
lean_object* v_snd_3220_ = _args[5];
lean_object* v_overlaps_3221_ = _args[6];
lean_object* v_splitterName_3222_ = _args[7];
lean_object* v_matcherLevels_3223_ = _args[8];
lean_object* v_params_x27_3224_ = _args[9];
lean_object* v_fst_3225_ = _args[10];
lean_object* v_discrs_x27_3226_ = _args[11];
lean_object* v_toPure_3227_ = _args[12];
lean_object* v_onRemaining_3228_ = _args[13];
lean_object* v_remaining_3229_ = _args[14];
lean_object* v_toBind_3230_ = _args[15];
lean_object* v_____s_3231_ = _args[16];
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__48(v_fst_3215_, v_numParams_3216_, v_numDiscrs_3217_, v_altInfos_3218_, v_uElimPos_x3f_3219_, v_snd_3220_, v_overlaps_3221_, v_splitterName_3222_, v_matcherLevels_3223_, v_params_x27_3224_, v_fst_3225_, v_discrs_x27_3226_, v_toPure_3227_, v_onRemaining_3228_, v_remaining_3229_, v_toBind_3230_, v_____s_3231_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49(lean_object* v_splitterMatchInfo_3233_, lean_object* v_fst_3234_, lean_object* v_numParams_3235_, lean_object* v_numDiscrs_3236_, lean_object* v_altInfos_3237_, lean_object* v_uElimPos_x3f_3238_, lean_object* v_snd_3239_, lean_object* v_overlaps_3240_, lean_object* v_splitterName_3241_, lean_object* v_matcherLevels_3242_, lean_object* v_params_x27_3243_, lean_object* v_fst_3244_, lean_object* v_discrs_x27_3245_, lean_object* v_toPure_3246_, lean_object* v_onRemaining_3247_, lean_object* v_remaining_3248_, lean_object* v_toBind_3249_, lean_object* v_origAltTypes_3250_, lean_object* v_alts_3251_, lean_object* v___x_3252_, lean_object* v___x_3253_, lean_object* v_remaining_x27_3254_, lean_object* v___f_3255_, lean_object* v_altTypes_3256_){
_start:
{
lean_object* v_altInfos_3257_; lean_object* v___f_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v_altInfos_3257_ = lean_ctor_get(v_splitterMatchInfo_3233_, 2);
lean_inc_ref(v_altInfos_3257_);
lean_dec_ref(v_splitterMatchInfo_3233_);
lean_inc(v_toBind_3249_);
lean_inc_ref(v_altInfos_3237_);
v___f_3258_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 17, 16);
lean_closure_set(v___f_3258_, 0, v_fst_3234_);
lean_closure_set(v___f_3258_, 1, v_numParams_3235_);
lean_closure_set(v___f_3258_, 2, v_numDiscrs_3236_);
lean_closure_set(v___f_3258_, 3, v_altInfos_3237_);
lean_closure_set(v___f_3258_, 4, v_uElimPos_x3f_3238_);
lean_closure_set(v___f_3258_, 5, v_snd_3239_);
lean_closure_set(v___f_3258_, 6, v_overlaps_3240_);
lean_closure_set(v___f_3258_, 7, v_splitterName_3241_);
lean_closure_set(v___f_3258_, 8, v_matcherLevels_3242_);
lean_closure_set(v___f_3258_, 9, v_params_x27_3243_);
lean_closure_set(v___f_3258_, 10, v_fst_3244_);
lean_closure_set(v___f_3258_, 11, v_discrs_x27_3245_);
lean_closure_set(v___f_3258_, 12, v_toPure_3246_);
lean_closure_set(v___f_3258_, 13, v_onRemaining_3247_);
lean_closure_set(v___f_3258_, 14, v_remaining_3248_);
lean_closure_set(v___f_3258_, 15, v_toBind_3249_);
v___x_3259_ = lean_array_get_size(v_altInfos_3237_);
v___x_3260_ = lean_array_get_size(v_altInfos_3257_);
v___x_3261_ = lean_array_get_size(v_origAltTypes_3250_);
v___x_3262_ = lean_array_get_size(v_altTypes_3256_);
lean_inc_n(v___x_3252_, 5);
v___x_3263_ = l_Array_toSubarray___redArg(v_alts_3251_, v___x_3252_, v___x_3253_);
v___x_3264_ = l_Array_toSubarray___redArg(v_altInfos_3237_, v___x_3252_, v___x_3259_);
v___x_3265_ = l_Array_toSubarray___redArg(v_altInfos_3257_, v___x_3252_, v___x_3260_);
v___x_3266_ = l_Array_toSubarray___redArg(v_origAltTypes_3250_, v___x_3252_, v___x_3261_);
v___x_3267_ = l_Array_toSubarray___redArg(v_altTypes_3256_, v___x_3252_, v___x_3262_);
v___x_3268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3266_);
lean_ctor_set(v___x_3268_, 1, v___x_3267_);
v___x_3269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3265_);
lean_ctor_set(v___x_3269_, 1, v___x_3268_);
v___x_3270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3264_);
lean_ctor_set(v___x_3270_, 1, v___x_3269_);
v___x_3271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3263_);
lean_ctor_set(v___x_3271_, 1, v___x_3270_);
v___x_3272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3272_, 0, v_remaining_x27_3254_);
lean_ctor_set(v___x_3272_, 1, v___x_3271_);
v___x_3273_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3255_, v___x_3252_, v___x_3272_, lean_box(0));
v___x_3274_ = lean_apply_4(v_toBind_3249_, lean_box(0), lean_box(0), v___x_3273_, v___f_3258_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed(lean_object** _args){
lean_object* v_splitterMatchInfo_3275_ = _args[0];
lean_object* v_fst_3276_ = _args[1];
lean_object* v_numParams_3277_ = _args[2];
lean_object* v_numDiscrs_3278_ = _args[3];
lean_object* v_altInfos_3279_ = _args[4];
lean_object* v_uElimPos_x3f_3280_ = _args[5];
lean_object* v_snd_3281_ = _args[6];
lean_object* v_overlaps_3282_ = _args[7];
lean_object* v_splitterName_3283_ = _args[8];
lean_object* v_matcherLevels_3284_ = _args[9];
lean_object* v_params_x27_3285_ = _args[10];
lean_object* v_fst_3286_ = _args[11];
lean_object* v_discrs_x27_3287_ = _args[12];
lean_object* v_toPure_3288_ = _args[13];
lean_object* v_onRemaining_3289_ = _args[14];
lean_object* v_remaining_3290_ = _args[15];
lean_object* v_toBind_3291_ = _args[16];
lean_object* v_origAltTypes_3292_ = _args[17];
lean_object* v_alts_3293_ = _args[18];
lean_object* v___x_3294_ = _args[19];
lean_object* v___x_3295_ = _args[20];
lean_object* v_remaining_x27_3296_ = _args[21];
lean_object* v___f_3297_ = _args[22];
lean_object* v_altTypes_3298_ = _args[23];
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__49(v_splitterMatchInfo_3275_, v_fst_3276_, v_numParams_3277_, v_numDiscrs_3278_, v_altInfos_3279_, v_uElimPos_x3f_3280_, v_snd_3281_, v_overlaps_3282_, v_splitterName_3283_, v_matcherLevels_3284_, v_params_x27_3285_, v_fst_3286_, v_discrs_x27_3287_, v_toPure_3288_, v_onRemaining_3289_, v_remaining_3290_, v_toBind_3291_, v_origAltTypes_3292_, v_alts_3293_, v___x_3294_, v___x_3295_, v_remaining_x27_3296_, v___f_3297_, v_altTypes_3298_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__50(lean_object* v___x_3300_, lean_object* v_aux2_3301_, lean_object* v_inst_3302_, lean_object* v_toBind_3303_, lean_object* v___f_3304_, lean_object* v_____r_3305_){
_start:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3306_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_3306_, 0, v___x_3300_);
lean_closure_set(v___x_3306_, 1, v_aux2_3301_);
v___x_3307_ = lean_apply_2(v_inst_3302_, lean_box(0), v___x_3306_);
v___x_3308_ = lean_apply_4(v_toBind_3303_, lean_box(0), lean_box(0), v___x_3307_, v___f_3304_);
return v___x_3308_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1(void){
_start:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3310_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__0));
v___x_3311_ = l_Lean_stringToMessageData(v___x_3310_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53(lean_object* v___x_3312_, lean_object* v_params_x27_3313_, lean_object* v_fst_3314_, lean_object* v_discrs_x27_3315_, lean_object* v_fst_3316_, lean_object* v_numParams_3317_, lean_object* v_numDiscrs_3318_, lean_object* v_altInfos_3319_, lean_object* v_uElimPos_x3f_3320_, lean_object* v_snd_3321_, lean_object* v_overlaps_3322_, lean_object* v_matcherLevels_3323_, lean_object* v_toPure_3324_, lean_object* v_onRemaining_3325_, lean_object* v_remaining_3326_, lean_object* v_toBind_3327_, lean_object* v_origAltTypes_3328_, lean_object* v_alts_3329_, lean_object* v___x_3330_, lean_object* v___x_3331_, lean_object* v_remaining_x27_3332_, lean_object* v___f_3333_, lean_object* v_inst_3334_, lean_object* v___x_3335_, uint8_t v___x_3336_, lean_object* v_liftWith_3337_, lean_object* v_restoreM_3338_, lean_object* v_matchEqns_3339_){
_start:
{
lean_object* v_splitterName_3340_; lean_object* v_splitterMatchInfo_3341_; lean_object* v___x_3342_; lean_object* v_aux2_3343_; lean_object* v_aux2_3344_; lean_object* v_aux2_3345_; lean_object* v___x_3346_; lean_object* v___f_3347_; lean_object* v___f_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___f_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___f_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v_splitterName_3340_ = lean_ctor_get(v_matchEqns_3339_, 1);
lean_inc_n(v_splitterName_3340_, 2);
v_splitterMatchInfo_3341_ = lean_ctor_get(v_matchEqns_3339_, 2);
lean_inc_ref(v_splitterMatchInfo_3341_);
lean_dec_ref(v_matchEqns_3339_);
v___x_3342_ = l_Lean_mkConst(v_splitterName_3340_, v___x_3312_);
v_aux2_3343_ = l_Lean_mkAppN(v___x_3342_, v_params_x27_3313_);
lean_inc_ref(v_fst_3314_);
v_aux2_3344_ = l_Lean_Expr_app___override(v_aux2_3343_, v_fst_3314_);
v_aux2_3345_ = l_Lean_mkAppN(v_aux2_3344_, v_discrs_x27_3315_);
lean_inc_ref_n(v_aux2_3345_, 2);
v___x_3346_ = l_Lean_indentExpr(v_aux2_3345_);
lean_inc(v___x_3331_);
lean_inc_n(v_toBind_3327_, 3);
v___f_3347_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed), 24, 23);
lean_closure_set(v___f_3347_, 0, v_splitterMatchInfo_3341_);
lean_closure_set(v___f_3347_, 1, v_fst_3316_);
lean_closure_set(v___f_3347_, 2, v_numParams_3317_);
lean_closure_set(v___f_3347_, 3, v_numDiscrs_3318_);
lean_closure_set(v___f_3347_, 4, v_altInfos_3319_);
lean_closure_set(v___f_3347_, 5, v_uElimPos_x3f_3320_);
lean_closure_set(v___f_3347_, 6, v_snd_3321_);
lean_closure_set(v___f_3347_, 7, v_overlaps_3322_);
lean_closure_set(v___f_3347_, 8, v_splitterName_3340_);
lean_closure_set(v___f_3347_, 9, v_matcherLevels_3323_);
lean_closure_set(v___f_3347_, 10, v_params_x27_3313_);
lean_closure_set(v___f_3347_, 11, v_fst_3314_);
lean_closure_set(v___f_3347_, 12, v_discrs_x27_3315_);
lean_closure_set(v___f_3347_, 13, v_toPure_3324_);
lean_closure_set(v___f_3347_, 14, v_onRemaining_3325_);
lean_closure_set(v___f_3347_, 15, v_remaining_3326_);
lean_closure_set(v___f_3347_, 16, v_toBind_3327_);
lean_closure_set(v___f_3347_, 17, v_origAltTypes_3328_);
lean_closure_set(v___f_3347_, 18, v_alts_3329_);
lean_closure_set(v___f_3347_, 19, v___x_3330_);
lean_closure_set(v___f_3347_, 20, v___x_3331_);
lean_closure_set(v___f_3347_, 21, v_remaining_x27_3332_);
lean_closure_set(v___f_3347_, 22, v___f_3333_);
lean_inc(v_inst_3334_);
v___f_3348_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__50), 6, 5);
lean_closure_set(v___f_3348_, 0, v___x_3331_);
lean_closure_set(v___f_3348_, 1, v_aux2_3345_);
lean_closure_set(v___f_3348_, 2, v_inst_3334_);
lean_closure_set(v___f_3348_, 3, v_toBind_3327_);
lean_closure_set(v___f_3348_, 4, v___f_3347_);
v___x_3349_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1);
v___x_3350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3349_);
lean_ctor_set(v___x_3350_, 1, v___x_3346_);
v___x_3351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3350_);
lean_ctor_set(v___x_3351_, 1, v___x_3335_);
v___f_3352_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3352_, 0, v___x_3351_);
v___x_3353_ = lean_box(v___x_3336_);
v___x_3354_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_3354_, 0, v_aux2_3345_);
lean_closure_set(v___x_3354_, 1, v___x_3353_);
v___x_3355_ = lean_apply_2(v_inst_3334_, lean_box(0), v___x_3354_);
v___f_3356_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3356_, 0, v___x_3355_);
lean_closure_set(v___f_3356_, 1, v___f_3352_);
v___x_3357_ = lean_apply_2(v_liftWith_3337_, lean_box(0), v___f_3356_);
v___x_3358_ = lean_apply_1(v_restoreM_3338_, lean_box(0));
v___x_3359_ = lean_apply_4(v_toBind_3327_, lean_box(0), lean_box(0), v___x_3357_, v___x_3358_);
v___x_3360_ = lean_apply_4(v_toBind_3327_, lean_box(0), lean_box(0), v___x_3359_, v___f_3348_);
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed(lean_object** _args){
lean_object* v___x_3361_ = _args[0];
lean_object* v_params_x27_3362_ = _args[1];
lean_object* v_fst_3363_ = _args[2];
lean_object* v_discrs_x27_3364_ = _args[3];
lean_object* v_fst_3365_ = _args[4];
lean_object* v_numParams_3366_ = _args[5];
lean_object* v_numDiscrs_3367_ = _args[6];
lean_object* v_altInfos_3368_ = _args[7];
lean_object* v_uElimPos_x3f_3369_ = _args[8];
lean_object* v_snd_3370_ = _args[9];
lean_object* v_overlaps_3371_ = _args[10];
lean_object* v_matcherLevels_3372_ = _args[11];
lean_object* v_toPure_3373_ = _args[12];
lean_object* v_onRemaining_3374_ = _args[13];
lean_object* v_remaining_3375_ = _args[14];
lean_object* v_toBind_3376_ = _args[15];
lean_object* v_origAltTypes_3377_ = _args[16];
lean_object* v_alts_3378_ = _args[17];
lean_object* v___x_3379_ = _args[18];
lean_object* v___x_3380_ = _args[19];
lean_object* v_remaining_x27_3381_ = _args[20];
lean_object* v___f_3382_ = _args[21];
lean_object* v_inst_3383_ = _args[22];
lean_object* v___x_3384_ = _args[23];
lean_object* v___x_3385_ = _args[24];
lean_object* v_liftWith_3386_ = _args[25];
lean_object* v_restoreM_3387_ = _args[26];
lean_object* v_matchEqns_3388_ = _args[27];
_start:
{
uint8_t v___x_14199__boxed_3389_; lean_object* v_res_3390_; 
v___x_14199__boxed_3389_ = lean_unbox(v___x_3385_);
v_res_3390_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__53(v___x_3361_, v_params_x27_3362_, v_fst_3363_, v_discrs_x27_3364_, v_fst_3365_, v_numParams_3366_, v_numDiscrs_3367_, v_altInfos_3368_, v_uElimPos_x3f_3369_, v_snd_3370_, v_overlaps_3371_, v_matcherLevels_3372_, v_toPure_3373_, v_onRemaining_3374_, v_remaining_3375_, v_toBind_3376_, v_origAltTypes_3377_, v_alts_3378_, v___x_3379_, v___x_3380_, v_remaining_x27_3381_, v___f_3382_, v_inst_3383_, v___x_3384_, v___x_14199__boxed_3389_, v_liftWith_3386_, v_restoreM_3387_, v_matchEqns_3388_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51(lean_object* v___x_3391_, lean_object* v_params_x27_3392_, lean_object* v_fst_3393_, lean_object* v_discrs_x27_3394_, lean_object* v_fst_3395_, lean_object* v_numParams_3396_, lean_object* v_numDiscrs_3397_, lean_object* v_altInfos_3398_, lean_object* v_uElimPos_x3f_3399_, lean_object* v_snd_3400_, lean_object* v_overlaps_3401_, lean_object* v_matcherLevels_3402_, lean_object* v_toPure_3403_, lean_object* v_onRemaining_3404_, lean_object* v_remaining_3405_, lean_object* v_toBind_3406_, lean_object* v_alts_3407_, lean_object* v___x_3408_, lean_object* v___x_3409_, lean_object* v_remaining_x27_3410_, lean_object* v___f_3411_, lean_object* v_inst_3412_, lean_object* v___x_3413_, uint8_t v___x_3414_, lean_object* v_liftWith_3415_, lean_object* v_restoreM_3416_, lean_object* v_matcherName_3417_, lean_object* v_origAltTypes_3418_){
_start:
{
lean_object* v___x_3419_; lean_object* v___f_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3419_ = lean_box(v___x_3414_);
lean_inc(v_inst_3412_);
lean_inc(v_toBind_3406_);
v___f_3420_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed), 28, 27);
lean_closure_set(v___f_3420_, 0, v___x_3391_);
lean_closure_set(v___f_3420_, 1, v_params_x27_3392_);
lean_closure_set(v___f_3420_, 2, v_fst_3393_);
lean_closure_set(v___f_3420_, 3, v_discrs_x27_3394_);
lean_closure_set(v___f_3420_, 4, v_fst_3395_);
lean_closure_set(v___f_3420_, 5, v_numParams_3396_);
lean_closure_set(v___f_3420_, 6, v_numDiscrs_3397_);
lean_closure_set(v___f_3420_, 7, v_altInfos_3398_);
lean_closure_set(v___f_3420_, 8, v_uElimPos_x3f_3399_);
lean_closure_set(v___f_3420_, 9, v_snd_3400_);
lean_closure_set(v___f_3420_, 10, v_overlaps_3401_);
lean_closure_set(v___f_3420_, 11, v_matcherLevels_3402_);
lean_closure_set(v___f_3420_, 12, v_toPure_3403_);
lean_closure_set(v___f_3420_, 13, v_onRemaining_3404_);
lean_closure_set(v___f_3420_, 14, v_remaining_3405_);
lean_closure_set(v___f_3420_, 15, v_toBind_3406_);
lean_closure_set(v___f_3420_, 16, v_origAltTypes_3418_);
lean_closure_set(v___f_3420_, 17, v_alts_3407_);
lean_closure_set(v___f_3420_, 18, v___x_3408_);
lean_closure_set(v___f_3420_, 19, v___x_3409_);
lean_closure_set(v___f_3420_, 20, v_remaining_x27_3410_);
lean_closure_set(v___f_3420_, 21, v___f_3411_);
lean_closure_set(v___f_3420_, 22, v_inst_3412_);
lean_closure_set(v___f_3420_, 23, v___x_3413_);
lean_closure_set(v___f_3420_, 24, v___x_3419_);
lean_closure_set(v___f_3420_, 25, v_liftWith_3415_);
lean_closure_set(v___f_3420_, 26, v_restoreM_3416_);
v___x_3421_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_getEquationsFor___boxed), 6, 1);
lean_closure_set(v___x_3421_, 0, v_matcherName_3417_);
v___x_3422_ = lean_apply_2(v_inst_3412_, lean_box(0), v___x_3421_);
v___x_3423_ = lean_apply_4(v_toBind_3406_, lean_box(0), lean_box(0), v___x_3422_, v___f_3420_);
return v___x_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed(lean_object** _args){
lean_object* v___x_3424_ = _args[0];
lean_object* v_params_x27_3425_ = _args[1];
lean_object* v_fst_3426_ = _args[2];
lean_object* v_discrs_x27_3427_ = _args[3];
lean_object* v_fst_3428_ = _args[4];
lean_object* v_numParams_3429_ = _args[5];
lean_object* v_numDiscrs_3430_ = _args[6];
lean_object* v_altInfos_3431_ = _args[7];
lean_object* v_uElimPos_x3f_3432_ = _args[8];
lean_object* v_snd_3433_ = _args[9];
lean_object* v_overlaps_3434_ = _args[10];
lean_object* v_matcherLevels_3435_ = _args[11];
lean_object* v_toPure_3436_ = _args[12];
lean_object* v_onRemaining_3437_ = _args[13];
lean_object* v_remaining_3438_ = _args[14];
lean_object* v_toBind_3439_ = _args[15];
lean_object* v_alts_3440_ = _args[16];
lean_object* v___x_3441_ = _args[17];
lean_object* v___x_3442_ = _args[18];
lean_object* v_remaining_x27_3443_ = _args[19];
lean_object* v___f_3444_ = _args[20];
lean_object* v_inst_3445_ = _args[21];
lean_object* v___x_3446_ = _args[22];
lean_object* v___x_3447_ = _args[23];
lean_object* v_liftWith_3448_ = _args[24];
lean_object* v_restoreM_3449_ = _args[25];
lean_object* v_matcherName_3450_ = _args[26];
lean_object* v_origAltTypes_3451_ = _args[27];
_start:
{
uint8_t v___x_14261__boxed_3452_; lean_object* v_res_3453_; 
v___x_14261__boxed_3452_ = lean_unbox(v___x_3447_);
v_res_3453_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__51(v___x_3424_, v_params_x27_3425_, v_fst_3426_, v_discrs_x27_3427_, v_fst_3428_, v_numParams_3429_, v_numDiscrs_3430_, v_altInfos_3431_, v_uElimPos_x3f_3432_, v_snd_3433_, v_overlaps_3434_, v_matcherLevels_3435_, v_toPure_3436_, v_onRemaining_3437_, v_remaining_3438_, v_toBind_3439_, v_alts_3440_, v___x_3441_, v___x_3442_, v_remaining_x27_3443_, v___f_3444_, v_inst_3445_, v___x_3446_, v___x_14261__boxed_3452_, v_liftWith_3448_, v_restoreM_3449_, v_matcherName_3450_, v_origAltTypes_3451_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52(lean_object* v_alts_3454_, lean_object* v_toPure_3455_, lean_object* v_toBind_3456_, lean_object* v___f_3457_, lean_object* v___x_3458_, lean_object* v___x_3459_, lean_object* v_inst_3460_, lean_object* v___x_3461_, lean_object* v_toMonadExceptOf_3462_, uint8_t v___x_3463_, uint8_t v_useSplitter_3464_, lean_object* v_onAlt_3465_, lean_object* v___f_3466_, lean_object* v_fst_3467_, lean_object* v_inst_3468_, lean_object* v_inst_3469_, lean_object* v_numDiscrEqs_3470_, lean_object* v___x_3471_, lean_object* v_params_x27_3472_, lean_object* v_fst_3473_, lean_object* v_discrs_x27_3474_, lean_object* v_fst_3475_, lean_object* v_numParams_3476_, lean_object* v_numDiscrs_3477_, lean_object* v_altInfos_3478_, lean_object* v_uElimPos_x3f_3479_, lean_object* v_snd_3480_, lean_object* v_overlaps_3481_, lean_object* v_matcherLevels_3482_, lean_object* v_onRemaining_3483_, lean_object* v_remaining_3484_, lean_object* v_remaining_x27_3485_, lean_object* v___x_3486_, uint8_t v___x_3487_, lean_object* v_liftWith_3488_, lean_object* v_restoreM_3489_, lean_object* v_matcherName_3490_, lean_object* v_aux1_3491_, lean_object* v_____r_3492_){
_start:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___f_3496_; lean_object* v___x_3497_; lean_object* v___f_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3493_ = lean_array_get_size(v_alts_3454_);
v___x_3494_ = lean_box(v___x_3463_);
v___x_3495_ = lean_box(v_useSplitter_3464_);
lean_inc_n(v_inst_3460_, 2);
lean_inc(v___x_3458_);
lean_inc_n(v_toBind_3456_, 2);
lean_inc(v_toPure_3455_);
v___f_3496_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46___boxed), 21, 17);
lean_closure_set(v___f_3496_, 0, v___x_3493_);
lean_closure_set(v___f_3496_, 1, v_toPure_3455_);
lean_closure_set(v___f_3496_, 2, v_toBind_3456_);
lean_closure_set(v___f_3496_, 3, v___f_3457_);
lean_closure_set(v___f_3496_, 4, v___x_3458_);
lean_closure_set(v___f_3496_, 5, v___x_3459_);
lean_closure_set(v___f_3496_, 6, v_inst_3460_);
lean_closure_set(v___f_3496_, 7, v___x_3461_);
lean_closure_set(v___f_3496_, 8, v_toMonadExceptOf_3462_);
lean_closure_set(v___f_3496_, 9, v___x_3494_);
lean_closure_set(v___f_3496_, 10, v___x_3495_);
lean_closure_set(v___f_3496_, 11, v_onAlt_3465_);
lean_closure_set(v___f_3496_, 12, v___f_3466_);
lean_closure_set(v___f_3496_, 13, v_fst_3467_);
lean_closure_set(v___f_3496_, 14, v_inst_3468_);
lean_closure_set(v___f_3496_, 15, v_inst_3469_);
lean_closure_set(v___f_3496_, 16, v_numDiscrEqs_3470_);
v___x_3497_ = lean_box(v___x_3487_);
v___f_3498_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed), 28, 27);
lean_closure_set(v___f_3498_, 0, v___x_3471_);
lean_closure_set(v___f_3498_, 1, v_params_x27_3472_);
lean_closure_set(v___f_3498_, 2, v_fst_3473_);
lean_closure_set(v___f_3498_, 3, v_discrs_x27_3474_);
lean_closure_set(v___f_3498_, 4, v_fst_3475_);
lean_closure_set(v___f_3498_, 5, v_numParams_3476_);
lean_closure_set(v___f_3498_, 6, v_numDiscrs_3477_);
lean_closure_set(v___f_3498_, 7, v_altInfos_3478_);
lean_closure_set(v___f_3498_, 8, v_uElimPos_x3f_3479_);
lean_closure_set(v___f_3498_, 9, v_snd_3480_);
lean_closure_set(v___f_3498_, 10, v_overlaps_3481_);
lean_closure_set(v___f_3498_, 11, v_matcherLevels_3482_);
lean_closure_set(v___f_3498_, 12, v_toPure_3455_);
lean_closure_set(v___f_3498_, 13, v_onRemaining_3483_);
lean_closure_set(v___f_3498_, 14, v_remaining_3484_);
lean_closure_set(v___f_3498_, 15, v_toBind_3456_);
lean_closure_set(v___f_3498_, 16, v_alts_3454_);
lean_closure_set(v___f_3498_, 17, v___x_3458_);
lean_closure_set(v___f_3498_, 18, v___x_3493_);
lean_closure_set(v___f_3498_, 19, v_remaining_x27_3485_);
lean_closure_set(v___f_3498_, 20, v___f_3496_);
lean_closure_set(v___f_3498_, 21, v_inst_3460_);
lean_closure_set(v___f_3498_, 22, v___x_3486_);
lean_closure_set(v___f_3498_, 23, v___x_3497_);
lean_closure_set(v___f_3498_, 24, v_liftWith_3488_);
lean_closure_set(v___f_3498_, 25, v_restoreM_3489_);
lean_closure_set(v___f_3498_, 26, v_matcherName_3490_);
v___x_3499_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_3499_, 0, v___x_3493_);
lean_closure_set(v___x_3499_, 1, v_aux1_3491_);
v___x_3500_ = lean_apply_2(v_inst_3460_, lean_box(0), v___x_3499_);
v___x_3501_ = lean_apply_4(v_toBind_3456_, lean_box(0), lean_box(0), v___x_3500_, v___f_3498_);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed(lean_object** _args){
lean_object* v_alts_3502_ = _args[0];
lean_object* v_toPure_3503_ = _args[1];
lean_object* v_toBind_3504_ = _args[2];
lean_object* v___f_3505_ = _args[3];
lean_object* v___x_3506_ = _args[4];
lean_object* v___x_3507_ = _args[5];
lean_object* v_inst_3508_ = _args[6];
lean_object* v___x_3509_ = _args[7];
lean_object* v_toMonadExceptOf_3510_ = _args[8];
lean_object* v___x_3511_ = _args[9];
lean_object* v_useSplitter_3512_ = _args[10];
lean_object* v_onAlt_3513_ = _args[11];
lean_object* v___f_3514_ = _args[12];
lean_object* v_fst_3515_ = _args[13];
lean_object* v_inst_3516_ = _args[14];
lean_object* v_inst_3517_ = _args[15];
lean_object* v_numDiscrEqs_3518_ = _args[16];
lean_object* v___x_3519_ = _args[17];
lean_object* v_params_x27_3520_ = _args[18];
lean_object* v_fst_3521_ = _args[19];
lean_object* v_discrs_x27_3522_ = _args[20];
lean_object* v_fst_3523_ = _args[21];
lean_object* v_numParams_3524_ = _args[22];
lean_object* v_numDiscrs_3525_ = _args[23];
lean_object* v_altInfos_3526_ = _args[24];
lean_object* v_uElimPos_x3f_3527_ = _args[25];
lean_object* v_snd_3528_ = _args[26];
lean_object* v_overlaps_3529_ = _args[27];
lean_object* v_matcherLevels_3530_ = _args[28];
lean_object* v_onRemaining_3531_ = _args[29];
lean_object* v_remaining_3532_ = _args[30];
lean_object* v_remaining_x27_3533_ = _args[31];
lean_object* v___x_3534_ = _args[32];
lean_object* v___x_3535_ = _args[33];
lean_object* v_liftWith_3536_ = _args[34];
lean_object* v_restoreM_3537_ = _args[35];
lean_object* v_matcherName_3538_ = _args[36];
lean_object* v_aux1_3539_ = _args[37];
lean_object* v_____r_3540_ = _args[38];
_start:
{
uint8_t v___x_14295__boxed_3541_; uint8_t v_useSplitter_boxed_3542_; uint8_t v___x_14303__boxed_3543_; lean_object* v_res_3544_; 
v___x_14295__boxed_3541_ = lean_unbox(v___x_3511_);
v_useSplitter_boxed_3542_ = lean_unbox(v_useSplitter_3512_);
v___x_14303__boxed_3543_ = lean_unbox(v___x_3535_);
v_res_3544_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__52(v_alts_3502_, v_toPure_3503_, v_toBind_3504_, v___f_3505_, v___x_3506_, v___x_3507_, v_inst_3508_, v___x_3509_, v_toMonadExceptOf_3510_, v___x_14295__boxed_3541_, v_useSplitter_boxed_3542_, v_onAlt_3513_, v___f_3514_, v_fst_3515_, v_inst_3516_, v_inst_3517_, v_numDiscrEqs_3518_, v___x_3519_, v_params_x27_3520_, v_fst_3521_, v_discrs_x27_3522_, v_fst_3523_, v_numParams_3524_, v_numDiscrs_3525_, v_altInfos_3526_, v_uElimPos_x3f_3527_, v_snd_3528_, v_overlaps_3529_, v_matcherLevels_3530_, v_onRemaining_3531_, v_remaining_3532_, v_remaining_x27_3533_, v___x_3534_, v___x_14303__boxed_3543_, v_liftWith_3536_, v_restoreM_3537_, v_matcherName_3538_, v_aux1_3539_, v_____r_3540_);
return v_res_3544_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1(void){
_start:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3546_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__0));
v___x_3547_ = l_Lean_stringToMessageData(v___x_3546_);
return v___x_3547_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3(void){
_start:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3549_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__2));
v___x_3550_ = l_Lean_stringToMessageData(v___x_3549_);
return v___x_3550_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5(void){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3552_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__4));
v___x_3553_ = l_Lean_stringToMessageData(v___x_3552_);
return v___x_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55(lean_object* v_numParams_3554_, lean_object* v_numDiscrs_3555_, lean_object* v_altInfos_3556_, lean_object* v_uElimPos_x3f_3557_, lean_object* v_snd_3558_, lean_object* v_overlaps_3559_, lean_object* v_matcherName_3560_, lean_object* v_matcherLevels_3561_, lean_object* v_params_x27_3562_, lean_object* v_fst_3563_, lean_object* v_discrs_x27_3564_, lean_object* v_toPure_3565_, lean_object* v_onRemaining_3566_, lean_object* v_remaining_3567_, lean_object* v_toBind_3568_, lean_object* v_inst_3569_, lean_object* v_alts_3570_, lean_object* v___f_3571_, uint8_t v___x_3572_, lean_object* v_inst_3573_, lean_object* v_remaining_x27_3574_, lean_object* v_onAlt_3575_, lean_object* v_inst_3576_, lean_object* v___f_3577_, lean_object* v_matcherApp_3578_, lean_object* v___x_3579_, uint8_t v_useSplitter_3580_, uint8_t v_isCasesOn_3581_, lean_object* v___f_3582_, lean_object* v___x_3583_, lean_object* v___x_3584_, lean_object* v_toMonadExceptOf_3585_, lean_object* v___f_3586_, lean_object* v_numDiscrEqs_3587_, lean_object* v_____s_3588_){
_start:
{
lean_object* v_snd_3589_; lean_object* v_fst_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3656_; 
v_snd_3589_ = lean_ctor_get(v_____s_3588_, 1);
v_fst_3590_ = lean_ctor_get(v_____s_3588_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v_____s_3588_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3592_ = v_____s_3588_;
v_isShared_3593_ = v_isSharedCheck_3656_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_snd_3589_);
lean_inc(v_fst_3590_);
lean_dec(v_____s_3588_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3656_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v_fst_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3654_; 
v_fst_3594_ = lean_ctor_get(v_snd_3589_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v_snd_3589_);
if (v_isSharedCheck_3654_ == 0)
{
lean_object* v_unused_3655_; 
v_unused_3655_ = lean_ctor_get(v_snd_3589_, 1);
lean_dec(v_unused_3655_);
v___x_3596_ = v_snd_3589_;
v_isShared_3597_ = v_isSharedCheck_3654_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_fst_3594_);
lean_dec(v_snd_3589_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3654_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___f_3598_; 
lean_inc(v_toBind_3568_);
lean_inc_ref(v_remaining_3567_);
lean_inc(v_onRemaining_3566_);
lean_inc(v_toPure_3565_);
lean_inc_ref(v_discrs_x27_3564_);
lean_inc_ref(v_fst_3563_);
lean_inc_ref(v_params_x27_3562_);
lean_inc_ref(v_matcherLevels_3561_);
lean_inc(v_matcherName_3560_);
lean_inc_ref(v_overlaps_3559_);
lean_inc_ref(v_snd_3558_);
lean_inc(v_uElimPos_x3f_3557_);
lean_inc_ref(v_altInfos_3556_);
lean_inc(v_numDiscrs_3555_);
lean_inc(v_numParams_3554_);
lean_inc(v_fst_3590_);
v___f_3598_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed), 17, 16);
lean_closure_set(v___f_3598_, 0, v_fst_3590_);
lean_closure_set(v___f_3598_, 1, v_numParams_3554_);
lean_closure_set(v___f_3598_, 2, v_numDiscrs_3555_);
lean_closure_set(v___f_3598_, 3, v_altInfos_3556_);
lean_closure_set(v___f_3598_, 4, v_uElimPos_x3f_3557_);
lean_closure_set(v___f_3598_, 5, v_snd_3558_);
lean_closure_set(v___f_3598_, 6, v_overlaps_3559_);
lean_closure_set(v___f_3598_, 7, v_matcherName_3560_);
lean_closure_set(v___f_3598_, 8, v_matcherLevels_3561_);
lean_closure_set(v___f_3598_, 9, v_params_x27_3562_);
lean_closure_set(v___f_3598_, 10, v_fst_3563_);
lean_closure_set(v___f_3598_, 11, v_discrs_x27_3564_);
lean_closure_set(v___f_3598_, 12, v_toPure_3565_);
lean_closure_set(v___f_3598_, 13, v_onRemaining_3566_);
lean_closure_set(v___f_3598_, 14, v_remaining_3567_);
lean_closure_set(v___f_3598_, 15, v_toBind_3568_);
if (v_useSplitter_3580_ == 0)
{
lean_del_object(v___x_3592_);
lean_dec(v_fst_3590_);
lean_dec(v_numDiscrEqs_3587_);
lean_dec(v___f_3586_);
lean_dec_ref(v_toMonadExceptOf_3585_);
lean_dec(v___x_3584_);
lean_dec(v___x_3583_);
lean_dec(v___f_3582_);
lean_dec_ref(v_remaining_3567_);
lean_dec(v_onRemaining_3566_);
lean_dec_ref(v_overlaps_3559_);
lean_dec_ref(v_snd_3558_);
lean_dec(v_uElimPos_x3f_3557_);
lean_dec_ref(v_altInfos_3556_);
lean_dec(v_numDiscrs_3555_);
lean_dec(v_numParams_3554_);
goto v___jp_3599_;
}
else
{
if (v_isCasesOn_3581_ == 0)
{
lean_object* v_liftWith_3626_; lean_object* v_restoreM_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v_aux1_3630_; lean_object* v_aux1_3631_; lean_object* v_aux1_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3636_; 
lean_dec_ref(v___f_3598_);
lean_del_object(v___x_3596_);
lean_dec_ref(v_matcherApp_3578_);
lean_dec(v___f_3577_);
lean_dec(v___f_3571_);
v_liftWith_3626_ = lean_ctor_get(v_inst_3569_, 0);
lean_inc(v_liftWith_3626_);
v_restoreM_3627_ = lean_ctor_get(v_inst_3569_, 1);
lean_inc(v_restoreM_3627_);
lean_inc_ref(v_matcherLevels_3561_);
v___x_3628_ = lean_array_to_list(v_matcherLevels_3561_);
lean_inc(v___x_3628_);
lean_inc(v_matcherName_3560_);
v___x_3629_ = l_Lean_mkConst(v_matcherName_3560_, v___x_3628_);
v_aux1_3630_ = l_Lean_mkAppN(v___x_3629_, v_params_x27_3562_);
lean_inc_ref(v_fst_3563_);
v_aux1_3631_ = l_Lean_Expr_app___override(v_aux1_3630_, v_fst_3563_);
v_aux1_3632_ = l_Lean_mkAppN(v_aux1_3631_, v_discrs_x27_3564_);
lean_inc_ref(v_aux1_3632_);
v___x_3633_ = l_Lean_indentExpr(v_aux1_3632_);
v___x_3634_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3);
if (v_isShared_3593_ == 0)
{
lean_ctor_set_tag(v___x_3592_, 7);
lean_ctor_set(v___x_3592_, 1, v___x_3633_);
lean_ctor_set(v___x_3592_, 0, v___x_3634_);
v___x_3636_ = v___x_3592_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3634_);
lean_ctor_set(v_reuseFailAlloc_3653_, 1, v___x_3633_);
v___x_3636_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___f_3639_; uint8_t v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___f_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___f_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3637_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5);
v___x_3638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3638_, 0, v___x_3636_);
lean_ctor_set(v___x_3638_, 1, v___x_3637_);
v___f_3639_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3639_, 0, v___x_3638_);
v___x_3640_ = 0;
v___x_3641_ = lean_box(v___x_3572_);
v___x_3642_ = lean_box(v_useSplitter_3580_);
v___x_3643_ = lean_box(v___x_3640_);
lean_inc_ref(v_aux1_3632_);
lean_inc(v_restoreM_3627_);
lean_inc(v_liftWith_3626_);
lean_inc(v_inst_3573_);
lean_inc_n(v_toBind_3568_, 2);
v___f_3644_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed), 39, 38);
lean_closure_set(v___f_3644_, 0, v_alts_3570_);
lean_closure_set(v___f_3644_, 1, v_toPure_3565_);
lean_closure_set(v___f_3644_, 2, v_toBind_3568_);
lean_closure_set(v___f_3644_, 3, v___f_3582_);
lean_closure_set(v___f_3644_, 4, v___x_3579_);
lean_closure_set(v___f_3644_, 5, v___x_3583_);
lean_closure_set(v___f_3644_, 6, v_inst_3573_);
lean_closure_set(v___f_3644_, 7, v___x_3584_);
lean_closure_set(v___f_3644_, 8, v_toMonadExceptOf_3585_);
lean_closure_set(v___f_3644_, 9, v___x_3641_);
lean_closure_set(v___f_3644_, 10, v___x_3642_);
lean_closure_set(v___f_3644_, 11, v_onAlt_3575_);
lean_closure_set(v___f_3644_, 12, v___f_3586_);
lean_closure_set(v___f_3644_, 13, v_fst_3594_);
lean_closure_set(v___f_3644_, 14, v_inst_3569_);
lean_closure_set(v___f_3644_, 15, v_inst_3576_);
lean_closure_set(v___f_3644_, 16, v_numDiscrEqs_3587_);
lean_closure_set(v___f_3644_, 17, v___x_3628_);
lean_closure_set(v___f_3644_, 18, v_params_x27_3562_);
lean_closure_set(v___f_3644_, 19, v_fst_3563_);
lean_closure_set(v___f_3644_, 20, v_discrs_x27_3564_);
lean_closure_set(v___f_3644_, 21, v_fst_3590_);
lean_closure_set(v___f_3644_, 22, v_numParams_3554_);
lean_closure_set(v___f_3644_, 23, v_numDiscrs_3555_);
lean_closure_set(v___f_3644_, 24, v_altInfos_3556_);
lean_closure_set(v___f_3644_, 25, v_uElimPos_x3f_3557_);
lean_closure_set(v___f_3644_, 26, v_snd_3558_);
lean_closure_set(v___f_3644_, 27, v_overlaps_3559_);
lean_closure_set(v___f_3644_, 28, v_matcherLevels_3561_);
lean_closure_set(v___f_3644_, 29, v_onRemaining_3566_);
lean_closure_set(v___f_3644_, 30, v_remaining_3567_);
lean_closure_set(v___f_3644_, 31, v_remaining_x27_3574_);
lean_closure_set(v___f_3644_, 32, v___x_3637_);
lean_closure_set(v___f_3644_, 33, v___x_3643_);
lean_closure_set(v___f_3644_, 34, v_liftWith_3626_);
lean_closure_set(v___f_3644_, 35, v_restoreM_3627_);
lean_closure_set(v___f_3644_, 36, v_matcherName_3560_);
lean_closure_set(v___f_3644_, 37, v_aux1_3632_);
v___x_3645_ = lean_box(v___x_3640_);
v___x_3646_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_3646_, 0, v_aux1_3632_);
lean_closure_set(v___x_3646_, 1, v___x_3645_);
v___x_3647_ = lean_apply_2(v_inst_3573_, lean_box(0), v___x_3646_);
v___f_3648_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3648_, 0, v___x_3647_);
lean_closure_set(v___f_3648_, 1, v___f_3639_);
v___x_3649_ = lean_apply_2(v_liftWith_3626_, lean_box(0), v___f_3648_);
v___x_3650_ = lean_apply_1(v_restoreM_3627_, lean_box(0));
v___x_3651_ = lean_apply_4(v_toBind_3568_, lean_box(0), lean_box(0), v___x_3649_, v___x_3650_);
v___x_3652_ = lean_apply_4(v_toBind_3568_, lean_box(0), lean_box(0), v___x_3651_, v___f_3644_);
return v___x_3652_;
}
}
else
{
lean_del_object(v___x_3592_);
lean_dec(v_fst_3590_);
lean_dec(v_numDiscrEqs_3587_);
lean_dec(v___f_3586_);
lean_dec_ref(v_toMonadExceptOf_3585_);
lean_dec(v___x_3584_);
lean_dec(v___x_3583_);
lean_dec(v___f_3582_);
lean_dec_ref(v_remaining_3567_);
lean_dec(v_onRemaining_3566_);
lean_dec_ref(v_overlaps_3559_);
lean_dec_ref(v_snd_3558_);
lean_dec(v_uElimPos_x3f_3557_);
lean_dec_ref(v_altInfos_3556_);
lean_dec(v_numDiscrs_3555_);
lean_dec(v_numParams_3554_);
goto v___jp_3599_;
}
}
v___jp_3599_:
{
lean_object* v_liftWith_3600_; lean_object* v_restoreM_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v_aux_3604_; lean_object* v_aux_3605_; lean_object* v_aux_3606_; lean_object* v___x_3607_; uint8_t v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___f_3611_; lean_object* v___x_3612_; lean_object* v___x_3614_; 
v_liftWith_3600_ = lean_ctor_get(v_inst_3569_, 0);
lean_inc(v_liftWith_3600_);
v_restoreM_3601_ = lean_ctor_get(v_inst_3569_, 1);
lean_inc(v_restoreM_3601_);
v___x_3602_ = lean_array_to_list(v_matcherLevels_3561_);
v___x_3603_ = l_Lean_mkConst(v_matcherName_3560_, v___x_3602_);
v_aux_3604_ = l_Lean_mkAppN(v___x_3603_, v_params_x27_3562_);
lean_dec_ref(v_params_x27_3562_);
v_aux_3605_ = l_Lean_Expr_app___override(v_aux_3604_, v_fst_3563_);
v_aux_3606_ = l_Lean_mkAppN(v_aux_3605_, v_discrs_x27_3564_);
lean_dec_ref(v_discrs_x27_3564_);
lean_inc_ref_n(v_aux_3606_, 2);
v___x_3607_ = l_Lean_indentExpr(v_aux_3606_);
v___x_3608_ = 1;
v___x_3609_ = lean_box(v___x_3572_);
v___x_3610_ = lean_box(v___x_3608_);
lean_inc(v_inst_3573_);
lean_inc(v_toBind_3568_);
v___f_3611_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 18, 17);
lean_closure_set(v___f_3611_, 0, v_alts_3570_);
lean_closure_set(v___f_3611_, 1, v_toPure_3565_);
lean_closure_set(v___f_3611_, 2, v_toBind_3568_);
lean_closure_set(v___f_3611_, 3, v___f_3571_);
lean_closure_set(v___f_3611_, 4, v___x_3609_);
lean_closure_set(v___f_3611_, 5, v___x_3610_);
lean_closure_set(v___f_3611_, 6, v_inst_3573_);
lean_closure_set(v___f_3611_, 7, v_remaining_x27_3574_);
lean_closure_set(v___f_3611_, 8, v_onAlt_3575_);
lean_closure_set(v___f_3611_, 9, v_inst_3569_);
lean_closure_set(v___f_3611_, 10, v_inst_3576_);
lean_closure_set(v___f_3611_, 11, v___f_3577_);
lean_closure_set(v___f_3611_, 12, v_fst_3594_);
lean_closure_set(v___f_3611_, 13, v_matcherApp_3578_);
lean_closure_set(v___f_3611_, 14, v___x_3579_);
lean_closure_set(v___f_3611_, 15, v___f_3598_);
lean_closure_set(v___f_3611_, 16, v_aux_3606_);
v___x_3612_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1);
if (v_isShared_3597_ == 0)
{
lean_ctor_set_tag(v___x_3596_, 7);
lean_ctor_set(v___x_3596_, 1, v___x_3607_);
lean_ctor_set(v___x_3596_, 0, v___x_3612_);
v___x_3614_ = v___x_3596_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3612_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v___x_3607_);
v___x_3614_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
lean_object* v___f_3615_; uint8_t v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___f_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
v___f_3615_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3615_, 0, v___x_3614_);
v___x_3616_ = 0;
v___x_3617_ = lean_box(v___x_3616_);
v___x_3618_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_3618_, 0, v_aux_3606_);
lean_closure_set(v___x_3618_, 1, v___x_3617_);
v___x_3619_ = lean_apply_2(v_inst_3573_, lean_box(0), v___x_3618_);
v___f_3620_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3620_, 0, v___x_3619_);
lean_closure_set(v___f_3620_, 1, v___f_3615_);
v___x_3621_ = lean_apply_2(v_liftWith_3600_, lean_box(0), v___f_3620_);
v___x_3622_ = lean_apply_1(v_restoreM_3601_, lean_box(0));
lean_inc(v_toBind_3568_);
v___x_3623_ = lean_apply_4(v_toBind_3568_, lean_box(0), lean_box(0), v___x_3621_, v___x_3622_);
v___x_3624_ = lean_apply_4(v_toBind_3568_, lean_box(0), lean_box(0), v___x_3623_, v___f_3611_);
return v___x_3624_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___boxed(lean_object** _args){
lean_object* v_numParams_3657_ = _args[0];
lean_object* v_numDiscrs_3658_ = _args[1];
lean_object* v_altInfos_3659_ = _args[2];
lean_object* v_uElimPos_x3f_3660_ = _args[3];
lean_object* v_snd_3661_ = _args[4];
lean_object* v_overlaps_3662_ = _args[5];
lean_object* v_matcherName_3663_ = _args[6];
lean_object* v_matcherLevels_3664_ = _args[7];
lean_object* v_params_x27_3665_ = _args[8];
lean_object* v_fst_3666_ = _args[9];
lean_object* v_discrs_x27_3667_ = _args[10];
lean_object* v_toPure_3668_ = _args[11];
lean_object* v_onRemaining_3669_ = _args[12];
lean_object* v_remaining_3670_ = _args[13];
lean_object* v_toBind_3671_ = _args[14];
lean_object* v_inst_3672_ = _args[15];
lean_object* v_alts_3673_ = _args[16];
lean_object* v___f_3674_ = _args[17];
lean_object* v___x_3675_ = _args[18];
lean_object* v_inst_3676_ = _args[19];
lean_object* v_remaining_x27_3677_ = _args[20];
lean_object* v_onAlt_3678_ = _args[21];
lean_object* v_inst_3679_ = _args[22];
lean_object* v___f_3680_ = _args[23];
lean_object* v_matcherApp_3681_ = _args[24];
lean_object* v___x_3682_ = _args[25];
lean_object* v_useSplitter_3683_ = _args[26];
lean_object* v_isCasesOn_3684_ = _args[27];
lean_object* v___f_3685_ = _args[28];
lean_object* v___x_3686_ = _args[29];
lean_object* v___x_3687_ = _args[30];
lean_object* v_toMonadExceptOf_3688_ = _args[31];
lean_object* v___f_3689_ = _args[32];
lean_object* v_numDiscrEqs_3690_ = _args[33];
lean_object* v_____s_3691_ = _args[34];
_start:
{
uint8_t v___x_14375__boxed_3692_; uint8_t v_useSplitter_boxed_3693_; uint8_t v_isCasesOn_boxed_3694_; lean_object* v_res_3695_; 
v___x_14375__boxed_3692_ = lean_unbox(v___x_3675_);
v_useSplitter_boxed_3693_ = lean_unbox(v_useSplitter_3683_);
v_isCasesOn_boxed_3694_ = lean_unbox(v_isCasesOn_3684_);
v_res_3695_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__55(v_numParams_3657_, v_numDiscrs_3658_, v_altInfos_3659_, v_uElimPos_x3f_3660_, v_snd_3661_, v_overlaps_3662_, v_matcherName_3663_, v_matcherLevels_3664_, v_params_x27_3665_, v_fst_3666_, v_discrs_x27_3667_, v_toPure_3668_, v_onRemaining_3669_, v_remaining_3670_, v_toBind_3671_, v_inst_3672_, v_alts_3673_, v___f_3674_, v___x_14375__boxed_3692_, v_inst_3676_, v_remaining_x27_3677_, v_onAlt_3678_, v_inst_3679_, v___f_3680_, v_matcherApp_3681_, v___x_3682_, v_useSplitter_boxed_3693_, v_isCasesOn_boxed_3694_, v___f_3685_, v___x_3686_, v___x_3687_, v_toMonadExceptOf_3688_, v___f_3689_, v_numDiscrEqs_3690_, v_____s_3691_);
return v_res_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54(lean_object* v_numParams_3696_, lean_object* v_numDiscrs_3697_, lean_object* v_altInfos_3698_, lean_object* v_uElimPos_x3f_3699_, lean_object* v_snd_3700_, lean_object* v_overlaps_3701_, lean_object* v_matcherName_3702_, lean_object* v_params_x27_3703_, lean_object* v_fst_3704_, lean_object* v_discrs_x27_3705_, lean_object* v_toPure_3706_, lean_object* v_onRemaining_3707_, lean_object* v_remaining_3708_, lean_object* v_toBind_3709_, lean_object* v_inst_3710_, lean_object* v_alts_3711_, lean_object* v___f_3712_, uint8_t v___x_3713_, lean_object* v_inst_3714_, lean_object* v_onAlt_3715_, lean_object* v_inst_3716_, lean_object* v___f_3717_, lean_object* v_matcherApp_3718_, uint8_t v_useSplitter_3719_, uint8_t v_isCasesOn_3720_, lean_object* v___f_3721_, lean_object* v___x_3722_, lean_object* v___x_3723_, lean_object* v_toMonadExceptOf_3724_, lean_object* v___f_3725_, lean_object* v_numDiscrEqs_3726_, lean_object* v_fst_3727_, lean_object* v___f_3728_, lean_object* v_matcherLevels_3729_){
_start:
{
lean_object* v___x_3730_; lean_object* v_remaining_x27_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___f_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; size_t v_sz_3742_; size_t v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3730_ = lean_unsigned_to_nat(0u);
v_remaining_x27_3731_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_3732_ = lean_box(v___x_3713_);
v___x_3733_ = lean_box(v_useSplitter_3719_);
v___x_3734_ = lean_box(v_isCasesOn_3720_);
lean_inc_ref(v_inst_3716_);
lean_inc(v_toBind_3709_);
lean_inc_ref(v_discrs_x27_3705_);
v___f_3735_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___boxed), 35, 34);
lean_closure_set(v___f_3735_, 0, v_numParams_3696_);
lean_closure_set(v___f_3735_, 1, v_numDiscrs_3697_);
lean_closure_set(v___f_3735_, 2, v_altInfos_3698_);
lean_closure_set(v___f_3735_, 3, v_uElimPos_x3f_3699_);
lean_closure_set(v___f_3735_, 4, v_snd_3700_);
lean_closure_set(v___f_3735_, 5, v_overlaps_3701_);
lean_closure_set(v___f_3735_, 6, v_matcherName_3702_);
lean_closure_set(v___f_3735_, 7, v_matcherLevels_3729_);
lean_closure_set(v___f_3735_, 8, v_params_x27_3703_);
lean_closure_set(v___f_3735_, 9, v_fst_3704_);
lean_closure_set(v___f_3735_, 10, v_discrs_x27_3705_);
lean_closure_set(v___f_3735_, 11, v_toPure_3706_);
lean_closure_set(v___f_3735_, 12, v_onRemaining_3707_);
lean_closure_set(v___f_3735_, 13, v_remaining_3708_);
lean_closure_set(v___f_3735_, 14, v_toBind_3709_);
lean_closure_set(v___f_3735_, 15, v_inst_3710_);
lean_closure_set(v___f_3735_, 16, v_alts_3711_);
lean_closure_set(v___f_3735_, 17, v___f_3712_);
lean_closure_set(v___f_3735_, 18, v___x_3732_);
lean_closure_set(v___f_3735_, 19, v_inst_3714_);
lean_closure_set(v___f_3735_, 20, v_remaining_x27_3731_);
lean_closure_set(v___f_3735_, 21, v_onAlt_3715_);
lean_closure_set(v___f_3735_, 22, v_inst_3716_);
lean_closure_set(v___f_3735_, 23, v___f_3717_);
lean_closure_set(v___f_3735_, 24, v_matcherApp_3718_);
lean_closure_set(v___f_3735_, 25, v___x_3730_);
lean_closure_set(v___f_3735_, 26, v___x_3733_);
lean_closure_set(v___f_3735_, 27, v___x_3734_);
lean_closure_set(v___f_3735_, 28, v___f_3721_);
lean_closure_set(v___f_3735_, 29, v___x_3722_);
lean_closure_set(v___f_3735_, 30, v___x_3723_);
lean_closure_set(v___f_3735_, 31, v_toMonadExceptOf_3724_);
lean_closure_set(v___f_3735_, 32, v___f_3725_);
lean_closure_set(v___f_3735_, 33, v_numDiscrEqs_3726_);
v___x_3736_ = l_Array_reverse___redArg(v_fst_3727_);
v___x_3737_ = lean_array_get_size(v___x_3736_);
v___x_3738_ = l_Array_toSubarray___redArg(v___x_3736_, v___x_3730_, v___x_3737_);
v___x_3739_ = l_Array_reverse___redArg(v_discrs_x27_3705_);
v___x_3740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3730_);
lean_ctor_set(v___x_3740_, 1, v___x_3738_);
v___x_3741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3741_, 0, v_remaining_x27_3731_);
lean_ctor_set(v___x_3741_, 1, v___x_3740_);
v_sz_3742_ = lean_array_size(v___x_3739_);
v___x_3743_ = ((size_t)0ULL);
v___x_3744_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3716_, v___x_3739_, v___f_3728_, v_sz_3742_, v___x_3743_, v___x_3741_);
v___x_3745_ = lean_apply_4(v_toBind_3709_, lean_box(0), lean_box(0), v___x_3744_, v___f_3735_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed(lean_object** _args){
lean_object* v_numParams_3746_ = _args[0];
lean_object* v_numDiscrs_3747_ = _args[1];
lean_object* v_altInfos_3748_ = _args[2];
lean_object* v_uElimPos_x3f_3749_ = _args[3];
lean_object* v_snd_3750_ = _args[4];
lean_object* v_overlaps_3751_ = _args[5];
lean_object* v_matcherName_3752_ = _args[6];
lean_object* v_params_x27_3753_ = _args[7];
lean_object* v_fst_3754_ = _args[8];
lean_object* v_discrs_x27_3755_ = _args[9];
lean_object* v_toPure_3756_ = _args[10];
lean_object* v_onRemaining_3757_ = _args[11];
lean_object* v_remaining_3758_ = _args[12];
lean_object* v_toBind_3759_ = _args[13];
lean_object* v_inst_3760_ = _args[14];
lean_object* v_alts_3761_ = _args[15];
lean_object* v___f_3762_ = _args[16];
lean_object* v___x_3763_ = _args[17];
lean_object* v_inst_3764_ = _args[18];
lean_object* v_onAlt_3765_ = _args[19];
lean_object* v_inst_3766_ = _args[20];
lean_object* v___f_3767_ = _args[21];
lean_object* v_matcherApp_3768_ = _args[22];
lean_object* v_useSplitter_3769_ = _args[23];
lean_object* v_isCasesOn_3770_ = _args[24];
lean_object* v___f_3771_ = _args[25];
lean_object* v___x_3772_ = _args[26];
lean_object* v___x_3773_ = _args[27];
lean_object* v_toMonadExceptOf_3774_ = _args[28];
lean_object* v___f_3775_ = _args[29];
lean_object* v_numDiscrEqs_3776_ = _args[30];
lean_object* v_fst_3777_ = _args[31];
lean_object* v___f_3778_ = _args[32];
lean_object* v_matcherLevels_3779_ = _args[33];
_start:
{
uint8_t v___x_14537__boxed_3780_; uint8_t v_useSplitter_boxed_3781_; uint8_t v_isCasesOn_boxed_3782_; lean_object* v_res_3783_; 
v___x_14537__boxed_3780_ = lean_unbox(v___x_3763_);
v_useSplitter_boxed_3781_ = lean_unbox(v_useSplitter_3769_);
v_isCasesOn_boxed_3782_ = lean_unbox(v_isCasesOn_3770_);
v_res_3783_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__54(v_numParams_3746_, v_numDiscrs_3747_, v_altInfos_3748_, v_uElimPos_x3f_3749_, v_snd_3750_, v_overlaps_3751_, v_matcherName_3752_, v_params_x27_3753_, v_fst_3754_, v_discrs_x27_3755_, v_toPure_3756_, v_onRemaining_3757_, v_remaining_3758_, v_toBind_3759_, v_inst_3760_, v_alts_3761_, v___f_3762_, v___x_14537__boxed_3780_, v_inst_3764_, v_onAlt_3765_, v_inst_3766_, v___f_3767_, v_matcherApp_3768_, v_useSplitter_boxed_3781_, v_isCasesOn_boxed_3782_, v___f_3771_, v___x_3772_, v___x_3773_, v_toMonadExceptOf_3774_, v___f_3775_, v_numDiscrEqs_3776_, v_fst_3777_, v___f_3778_, v_matcherLevels_3779_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56(lean_object* v___f_3784_, lean_object* v_matcherLevels_3785_){
_start:
{
lean_object* v___x_3786_; 
v___x_3786_ = lean_apply_1(v___f_3784_, v_matcherLevels_3785_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58(lean_object* v_toMatcherInfo_3787_, lean_object* v_matcherName_3788_, lean_object* v_params_x27_3789_, lean_object* v_discrs_x27_3790_, lean_object* v_toPure_3791_, lean_object* v_onRemaining_3792_, lean_object* v_remaining_3793_, lean_object* v_toBind_3794_, lean_object* v_inst_3795_, lean_object* v_alts_3796_, lean_object* v___f_3797_, uint8_t v___x_3798_, lean_object* v_inst_3799_, lean_object* v_onAlt_3800_, lean_object* v_inst_3801_, lean_object* v___f_3802_, lean_object* v_matcherApp_3803_, uint8_t v_useSplitter_3804_, uint8_t v_isCasesOn_3805_, lean_object* v___f_3806_, lean_object* v___x_3807_, lean_object* v___x_3808_, lean_object* v_toMonadExceptOf_3809_, lean_object* v___f_3810_, lean_object* v_numDiscrEqs_3811_, lean_object* v___f_3812_, lean_object* v_matcherLevels_3813_, lean_object* v_____x_3814_){
_start:
{
lean_object* v_snd_3815_; lean_object* v_snd_3816_; lean_object* v_fst_3817_; lean_object* v_fst_3818_; lean_object* v_fst_3819_; lean_object* v_snd_3820_; lean_object* v_numParams_3821_; lean_object* v_numDiscrs_3822_; lean_object* v_altInfos_3823_; lean_object* v_uElimPos_x3f_3824_; lean_object* v_overlaps_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___f_3829_; 
v_snd_3815_ = lean_ctor_get(v_____x_3814_, 1);
lean_inc(v_snd_3815_);
v_snd_3816_ = lean_ctor_get(v_snd_3815_, 1);
lean_inc(v_snd_3816_);
v_fst_3817_ = lean_ctor_get(v_____x_3814_, 0);
lean_inc(v_fst_3817_);
lean_dec_ref(v_____x_3814_);
v_fst_3818_ = lean_ctor_get(v_snd_3815_, 0);
lean_inc(v_fst_3818_);
lean_dec(v_snd_3815_);
v_fst_3819_ = lean_ctor_get(v_snd_3816_, 0);
lean_inc(v_fst_3819_);
v_snd_3820_ = lean_ctor_get(v_snd_3816_, 1);
lean_inc(v_snd_3820_);
lean_dec(v_snd_3816_);
v_numParams_3821_ = lean_ctor_get(v_toMatcherInfo_3787_, 0);
lean_inc(v_numParams_3821_);
v_numDiscrs_3822_ = lean_ctor_get(v_toMatcherInfo_3787_, 1);
lean_inc(v_numDiscrs_3822_);
v_altInfos_3823_ = lean_ctor_get(v_toMatcherInfo_3787_, 2);
lean_inc_ref(v_altInfos_3823_);
v_uElimPos_x3f_3824_ = lean_ctor_get(v_toMatcherInfo_3787_, 3);
lean_inc_n(v_uElimPos_x3f_3824_, 2);
v_overlaps_3825_ = lean_ctor_get(v_toMatcherInfo_3787_, 5);
lean_inc_ref(v_overlaps_3825_);
lean_dec_ref(v_toMatcherInfo_3787_);
v___x_3826_ = lean_box(v___x_3798_);
v___x_3827_ = lean_box(v_useSplitter_3804_);
v___x_3828_ = lean_box(v_isCasesOn_3805_);
lean_inc(v_toBind_3794_);
lean_inc(v_toPure_3791_);
v___f_3829_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed), 34, 33);
lean_closure_set(v___f_3829_, 0, v_numParams_3821_);
lean_closure_set(v___f_3829_, 1, v_numDiscrs_3822_);
lean_closure_set(v___f_3829_, 2, v_altInfos_3823_);
lean_closure_set(v___f_3829_, 3, v_uElimPos_x3f_3824_);
lean_closure_set(v___f_3829_, 4, v_snd_3820_);
lean_closure_set(v___f_3829_, 5, v_overlaps_3825_);
lean_closure_set(v___f_3829_, 6, v_matcherName_3788_);
lean_closure_set(v___f_3829_, 7, v_params_x27_3789_);
lean_closure_set(v___f_3829_, 8, v_fst_3817_);
lean_closure_set(v___f_3829_, 9, v_discrs_x27_3790_);
lean_closure_set(v___f_3829_, 10, v_toPure_3791_);
lean_closure_set(v___f_3829_, 11, v_onRemaining_3792_);
lean_closure_set(v___f_3829_, 12, v_remaining_3793_);
lean_closure_set(v___f_3829_, 13, v_toBind_3794_);
lean_closure_set(v___f_3829_, 14, v_inst_3795_);
lean_closure_set(v___f_3829_, 15, v_alts_3796_);
lean_closure_set(v___f_3829_, 16, v___f_3797_);
lean_closure_set(v___f_3829_, 17, v___x_3826_);
lean_closure_set(v___f_3829_, 18, v_inst_3799_);
lean_closure_set(v___f_3829_, 19, v_onAlt_3800_);
lean_closure_set(v___f_3829_, 20, v_inst_3801_);
lean_closure_set(v___f_3829_, 21, v___f_3802_);
lean_closure_set(v___f_3829_, 22, v_matcherApp_3803_);
lean_closure_set(v___f_3829_, 23, v___x_3827_);
lean_closure_set(v___f_3829_, 24, v___x_3828_);
lean_closure_set(v___f_3829_, 25, v___f_3806_);
lean_closure_set(v___f_3829_, 26, v___x_3807_);
lean_closure_set(v___f_3829_, 27, v___x_3808_);
lean_closure_set(v___f_3829_, 28, v_toMonadExceptOf_3809_);
lean_closure_set(v___f_3829_, 29, v___f_3810_);
lean_closure_set(v___f_3829_, 30, v_numDiscrEqs_3811_);
lean_closure_set(v___f_3829_, 31, v_fst_3819_);
lean_closure_set(v___f_3829_, 32, v___f_3812_);
if (lean_obj_tag(v_uElimPos_x3f_3824_) == 0)
{
lean_object* v___f_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
lean_dec(v_fst_3818_);
v___f_3830_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56), 2, 1);
lean_closure_set(v___f_3830_, 0, v___f_3829_);
v___x_3831_ = lean_apply_2(v_toPure_3791_, lean_box(0), v_matcherLevels_3813_);
v___x_3832_ = lean_apply_4(v_toBind_3794_, lean_box(0), lean_box(0), v___x_3831_, v___f_3830_);
return v___x_3832_;
}
else
{
lean_object* v_val_3833_; lean_object* v___f_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; 
v_val_3833_ = lean_ctor_get(v_uElimPos_x3f_3824_, 0);
lean_inc(v_val_3833_);
lean_dec_ref_known(v_uElimPos_x3f_3824_, 1);
v___f_3834_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56), 2, 1);
lean_closure_set(v___f_3834_, 0, v___f_3829_);
v___x_3835_ = lean_array_set(v_matcherLevels_3813_, v_val_3833_, v_fst_3818_);
lean_dec(v_val_3833_);
v___x_3836_ = lean_apply_2(v_toPure_3791_, lean_box(0), v___x_3835_);
v___x_3837_ = lean_apply_4(v_toBind_3794_, lean_box(0), lean_box(0), v___x_3836_, v___f_3834_);
return v___x_3837_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed(lean_object** _args){
lean_object* v_toMatcherInfo_3838_ = _args[0];
lean_object* v_matcherName_3839_ = _args[1];
lean_object* v_params_x27_3840_ = _args[2];
lean_object* v_discrs_x27_3841_ = _args[3];
lean_object* v_toPure_3842_ = _args[4];
lean_object* v_onRemaining_3843_ = _args[5];
lean_object* v_remaining_3844_ = _args[6];
lean_object* v_toBind_3845_ = _args[7];
lean_object* v_inst_3846_ = _args[8];
lean_object* v_alts_3847_ = _args[9];
lean_object* v___f_3848_ = _args[10];
lean_object* v___x_3849_ = _args[11];
lean_object* v_inst_3850_ = _args[12];
lean_object* v_onAlt_3851_ = _args[13];
lean_object* v_inst_3852_ = _args[14];
lean_object* v___f_3853_ = _args[15];
lean_object* v_matcherApp_3854_ = _args[16];
lean_object* v_useSplitter_3855_ = _args[17];
lean_object* v_isCasesOn_3856_ = _args[18];
lean_object* v___f_3857_ = _args[19];
lean_object* v___x_3858_ = _args[20];
lean_object* v___x_3859_ = _args[21];
lean_object* v_toMonadExceptOf_3860_ = _args[22];
lean_object* v___f_3861_ = _args[23];
lean_object* v_numDiscrEqs_3862_ = _args[24];
lean_object* v___f_3863_ = _args[25];
lean_object* v_matcherLevels_3864_ = _args[26];
lean_object* v_____x_3865_ = _args[27];
_start:
{
uint8_t v___x_14609__boxed_3866_; uint8_t v_useSplitter_boxed_3867_; uint8_t v_isCasesOn_boxed_3868_; lean_object* v_res_3869_; 
v___x_14609__boxed_3866_ = lean_unbox(v___x_3849_);
v_useSplitter_boxed_3867_ = lean_unbox(v_useSplitter_3855_);
v_isCasesOn_boxed_3868_ = lean_unbox(v_isCasesOn_3856_);
v_res_3869_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__58(v_toMatcherInfo_3838_, v_matcherName_3839_, v_params_x27_3840_, v_discrs_x27_3841_, v_toPure_3842_, v_onRemaining_3843_, v_remaining_3844_, v_toBind_3845_, v_inst_3846_, v_alts_3847_, v___f_3848_, v___x_14609__boxed_3866_, v_inst_3850_, v_onAlt_3851_, v_inst_3852_, v___f_3853_, v_matcherApp_3854_, v_useSplitter_boxed_3867_, v_isCasesOn_boxed_3868_, v___f_3857_, v___x_3858_, v___x_3859_, v_toMonadExceptOf_3860_, v___f_3861_, v_numDiscrEqs_3862_, v___f_3863_, v_matcherLevels_3864_, v_____x_3865_);
return v_res_3869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57(lean_object* v_toPure_3870_, lean_object* v_inst_3871_, lean_object* v_toBind_3872_, lean_object* v_toMatcherInfo_3873_, lean_object* v_inst_3874_, lean_object* v___f_3875_, lean_object* v_onMotive_3876_, lean_object* v_discrs_3877_, lean_object* v_inst_3878_, lean_object* v_matcherName_3879_, lean_object* v_params_x27_3880_, lean_object* v_onRemaining_3881_, lean_object* v_remaining_3882_, lean_object* v_inst_3883_, lean_object* v_alts_3884_, lean_object* v___f_3885_, lean_object* v_onAlt_3886_, lean_object* v___f_3887_, lean_object* v_matcherApp_3888_, uint8_t v_useSplitter_3889_, uint8_t v_isCasesOn_3890_, lean_object* v___f_3891_, lean_object* v___x_3892_, lean_object* v___x_3893_, lean_object* v_toMonadExceptOf_3894_, lean_object* v___f_3895_, lean_object* v_numDiscrEqs_3896_, lean_object* v___f_3897_, lean_object* v_matcherLevels_3898_, lean_object* v_motive_3899_, lean_object* v_discrs_x27_3900_){
_start:
{
lean_object* v___f_3901_; uint8_t v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___f_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; 
lean_inc_ref_n(v_inst_3874_, 2);
lean_inc_ref(v_discrs_x27_3900_);
lean_inc_ref(v_toMatcherInfo_3873_);
lean_inc_n(v_toBind_3872_, 2);
lean_inc(v_inst_3871_);
lean_inc(v_toPure_3870_);
v___f_3901_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__19___boxed), 12, 10);
lean_closure_set(v___f_3901_, 0, v_toPure_3870_);
lean_closure_set(v___f_3901_, 1, v_inst_3871_);
lean_closure_set(v___f_3901_, 2, v_toBind_3872_);
lean_closure_set(v___f_3901_, 3, v_toMatcherInfo_3873_);
lean_closure_set(v___f_3901_, 4, v_discrs_x27_3900_);
lean_closure_set(v___f_3901_, 5, v_inst_3874_);
lean_closure_set(v___f_3901_, 6, v___f_3875_);
lean_closure_set(v___f_3901_, 7, v_onMotive_3876_);
lean_closure_set(v___f_3901_, 8, v_discrs_3877_);
lean_closure_set(v___f_3901_, 9, v_inst_3878_);
v___x_3902_ = 0;
v___x_3903_ = lean_box(v___x_3902_);
v___x_3904_ = lean_box(v_useSplitter_3889_);
v___x_3905_ = lean_box(v_isCasesOn_3890_);
lean_inc_ref(v_inst_3883_);
v___f_3906_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed), 28, 27);
lean_closure_set(v___f_3906_, 0, v_toMatcherInfo_3873_);
lean_closure_set(v___f_3906_, 1, v_matcherName_3879_);
lean_closure_set(v___f_3906_, 2, v_params_x27_3880_);
lean_closure_set(v___f_3906_, 3, v_discrs_x27_3900_);
lean_closure_set(v___f_3906_, 4, v_toPure_3870_);
lean_closure_set(v___f_3906_, 5, v_onRemaining_3881_);
lean_closure_set(v___f_3906_, 6, v_remaining_3882_);
lean_closure_set(v___f_3906_, 7, v_toBind_3872_);
lean_closure_set(v___f_3906_, 8, v_inst_3883_);
lean_closure_set(v___f_3906_, 9, v_alts_3884_);
lean_closure_set(v___f_3906_, 10, v___f_3885_);
lean_closure_set(v___f_3906_, 11, v___x_3903_);
lean_closure_set(v___f_3906_, 12, v_inst_3871_);
lean_closure_set(v___f_3906_, 13, v_onAlt_3886_);
lean_closure_set(v___f_3906_, 14, v_inst_3874_);
lean_closure_set(v___f_3906_, 15, v___f_3887_);
lean_closure_set(v___f_3906_, 16, v_matcherApp_3888_);
lean_closure_set(v___f_3906_, 17, v___x_3904_);
lean_closure_set(v___f_3906_, 18, v___x_3905_);
lean_closure_set(v___f_3906_, 19, v___f_3891_);
lean_closure_set(v___f_3906_, 20, v___x_3892_);
lean_closure_set(v___f_3906_, 21, v___x_3893_);
lean_closure_set(v___f_3906_, 22, v_toMonadExceptOf_3894_);
lean_closure_set(v___f_3906_, 23, v___f_3895_);
lean_closure_set(v___f_3906_, 24, v_numDiscrEqs_3896_);
lean_closure_set(v___f_3906_, 25, v___f_3897_);
lean_closure_set(v___f_3906_, 26, v_matcherLevels_3898_);
v___x_3907_ = l_Lean_Meta_lambdaTelescope___redArg(v_inst_3883_, v_inst_3874_, v_motive_3899_, v___f_3901_, v___x_3902_);
v___x_3908_ = lean_apply_4(v_toBind_3872_, lean_box(0), lean_box(0), v___x_3907_, v___f_3906_);
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
lean_object* v___x_3931_ = _args[22];
lean_object* v___x_3932_ = _args[23];
lean_object* v_toMonadExceptOf_3933_ = _args[24];
lean_object* v___f_3934_ = _args[25];
lean_object* v_numDiscrEqs_3935_ = _args[26];
lean_object* v___f_3936_ = _args[27];
lean_object* v_matcherLevels_3937_ = _args[28];
lean_object* v_motive_3938_ = _args[29];
lean_object* v_discrs_x27_3939_ = _args[30];
_start:
{
uint8_t v_useSplitter_boxed_3940_; uint8_t v_isCasesOn_boxed_3941_; lean_object* v_res_3942_; 
v_useSplitter_boxed_3940_ = lean_unbox(v_useSplitter_3928_);
v_isCasesOn_boxed_3941_ = lean_unbox(v_isCasesOn_3929_);
v_res_3942_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__57(v_toPure_3909_, v_inst_3910_, v_toBind_3911_, v_toMatcherInfo_3912_, v_inst_3913_, v___f_3914_, v_onMotive_3915_, v_discrs_3916_, v_inst_3917_, v_matcherName_3918_, v_params_x27_3919_, v_onRemaining_3920_, v_remaining_3921_, v_inst_3922_, v_alts_3923_, v___f_3924_, v_onAlt_3925_, v___f_3926_, v_matcherApp_3927_, v_useSplitter_boxed_3940_, v_isCasesOn_boxed_3941_, v___f_3930_, v___x_3931_, v___x_3932_, v_toMonadExceptOf_3933_, v___f_3934_, v_numDiscrEqs_3935_, v___f_3936_, v_matcherLevels_3937_, v_motive_3938_, v_discrs_x27_3939_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59(lean_object* v_toPure_3943_, lean_object* v_inst_3944_, lean_object* v_toBind_3945_, lean_object* v_toMatcherInfo_3946_, lean_object* v_inst_3947_, lean_object* v___f_3948_, lean_object* v_onMotive_3949_, lean_object* v_discrs_3950_, lean_object* v_inst_3951_, lean_object* v_matcherName_3952_, lean_object* v_onRemaining_3953_, lean_object* v_remaining_3954_, lean_object* v_inst_3955_, lean_object* v_alts_3956_, lean_object* v___f_3957_, lean_object* v_onAlt_3958_, lean_object* v___f_3959_, lean_object* v_matcherApp_3960_, uint8_t v_useSplitter_3961_, uint8_t v_isCasesOn_3962_, lean_object* v___f_3963_, lean_object* v___x_3964_, lean_object* v___x_3965_, lean_object* v_toMonadExceptOf_3966_, lean_object* v___f_3967_, lean_object* v_numDiscrEqs_3968_, lean_object* v___f_3969_, lean_object* v_matcherLevels_3970_, lean_object* v_motive_3971_, lean_object* v_onParams_3972_, lean_object* v_params_x27_3973_){
_start:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___f_3976_; size_t v_sz_3977_; size_t v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3974_ = lean_box(v_useSplitter_3961_);
v___x_3975_ = lean_box(v_isCasesOn_3962_);
lean_inc_ref(v_discrs_3950_);
lean_inc_ref(v_inst_3947_);
lean_inc(v_toBind_3945_);
v___f_3976_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed), 31, 30);
lean_closure_set(v___f_3976_, 0, v_toPure_3943_);
lean_closure_set(v___f_3976_, 1, v_inst_3944_);
lean_closure_set(v___f_3976_, 2, v_toBind_3945_);
lean_closure_set(v___f_3976_, 3, v_toMatcherInfo_3946_);
lean_closure_set(v___f_3976_, 4, v_inst_3947_);
lean_closure_set(v___f_3976_, 5, v___f_3948_);
lean_closure_set(v___f_3976_, 6, v_onMotive_3949_);
lean_closure_set(v___f_3976_, 7, v_discrs_3950_);
lean_closure_set(v___f_3976_, 8, v_inst_3951_);
lean_closure_set(v___f_3976_, 9, v_matcherName_3952_);
lean_closure_set(v___f_3976_, 10, v_params_x27_3973_);
lean_closure_set(v___f_3976_, 11, v_onRemaining_3953_);
lean_closure_set(v___f_3976_, 12, v_remaining_3954_);
lean_closure_set(v___f_3976_, 13, v_inst_3955_);
lean_closure_set(v___f_3976_, 14, v_alts_3956_);
lean_closure_set(v___f_3976_, 15, v___f_3957_);
lean_closure_set(v___f_3976_, 16, v_onAlt_3958_);
lean_closure_set(v___f_3976_, 17, v___f_3959_);
lean_closure_set(v___f_3976_, 18, v_matcherApp_3960_);
lean_closure_set(v___f_3976_, 19, v___x_3974_);
lean_closure_set(v___f_3976_, 20, v___x_3975_);
lean_closure_set(v___f_3976_, 21, v___f_3963_);
lean_closure_set(v___f_3976_, 22, v___x_3964_);
lean_closure_set(v___f_3976_, 23, v___x_3965_);
lean_closure_set(v___f_3976_, 24, v_toMonadExceptOf_3966_);
lean_closure_set(v___f_3976_, 25, v___f_3967_);
lean_closure_set(v___f_3976_, 26, v_numDiscrEqs_3968_);
lean_closure_set(v___f_3976_, 27, v___f_3969_);
lean_closure_set(v___f_3976_, 28, v_matcherLevels_3970_);
lean_closure_set(v___f_3976_, 29, v_motive_3971_);
v_sz_3977_ = lean_array_size(v_discrs_3950_);
v___x_3978_ = ((size_t)0ULL);
v___x_3979_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_3947_, v_onParams_3972_, v_sz_3977_, v___x_3978_, v_discrs_3950_);
v___x_3980_ = lean_apply_4(v_toBind_3945_, lean_box(0), lean_box(0), v___x_3979_, v___f_3976_);
return v___x_3980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed(lean_object** _args){
lean_object* v_toPure_3981_ = _args[0];
lean_object* v_inst_3982_ = _args[1];
lean_object* v_toBind_3983_ = _args[2];
lean_object* v_toMatcherInfo_3984_ = _args[3];
lean_object* v_inst_3985_ = _args[4];
lean_object* v___f_3986_ = _args[5];
lean_object* v_onMotive_3987_ = _args[6];
lean_object* v_discrs_3988_ = _args[7];
lean_object* v_inst_3989_ = _args[8];
lean_object* v_matcherName_3990_ = _args[9];
lean_object* v_onRemaining_3991_ = _args[10];
lean_object* v_remaining_3992_ = _args[11];
lean_object* v_inst_3993_ = _args[12];
lean_object* v_alts_3994_ = _args[13];
lean_object* v___f_3995_ = _args[14];
lean_object* v_onAlt_3996_ = _args[15];
lean_object* v___f_3997_ = _args[16];
lean_object* v_matcherApp_3998_ = _args[17];
lean_object* v_useSplitter_3999_ = _args[18];
lean_object* v_isCasesOn_4000_ = _args[19];
lean_object* v___f_4001_ = _args[20];
lean_object* v___x_4002_ = _args[21];
lean_object* v___x_4003_ = _args[22];
lean_object* v_toMonadExceptOf_4004_ = _args[23];
lean_object* v___f_4005_ = _args[24];
lean_object* v_numDiscrEqs_4006_ = _args[25];
lean_object* v___f_4007_ = _args[26];
lean_object* v_matcherLevels_4008_ = _args[27];
lean_object* v_motive_4009_ = _args[28];
lean_object* v_onParams_4010_ = _args[29];
lean_object* v_params_x27_4011_ = _args[30];
_start:
{
uint8_t v_useSplitter_boxed_4012_; uint8_t v_isCasesOn_boxed_4013_; lean_object* v_res_4014_; 
v_useSplitter_boxed_4012_ = lean_unbox(v_useSplitter_3999_);
v_isCasesOn_boxed_4013_ = lean_unbox(v_isCasesOn_4000_);
v_res_4014_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__59(v_toPure_3981_, v_inst_3982_, v_toBind_3983_, v_toMatcherInfo_3984_, v_inst_3985_, v___f_3986_, v_onMotive_3987_, v_discrs_3988_, v_inst_3989_, v_matcherName_3990_, v_onRemaining_3991_, v_remaining_3992_, v_inst_3993_, v_alts_3994_, v___f_3995_, v_onAlt_3996_, v___f_3997_, v_matcherApp_3998_, v_useSplitter_boxed_4012_, v_isCasesOn_boxed_4013_, v___f_4001_, v___x_4002_, v___x_4003_, v_toMonadExceptOf_4004_, v___f_4005_, v_numDiscrEqs_4006_, v___f_4007_, v_matcherLevels_4008_, v_motive_4009_, v_onParams_4010_, v_params_x27_4011_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60(lean_object* v_toPure_4015_, lean_object* v_inst_4016_, lean_object* v_toBind_4017_, lean_object* v_toMatcherInfo_4018_, lean_object* v_inst_4019_, lean_object* v___f_4020_, lean_object* v_onMotive_4021_, lean_object* v_discrs_4022_, lean_object* v_inst_4023_, lean_object* v_matcherName_4024_, lean_object* v_onRemaining_4025_, lean_object* v_remaining_4026_, lean_object* v_inst_4027_, lean_object* v_alts_4028_, lean_object* v___f_4029_, lean_object* v_onAlt_4030_, lean_object* v___f_4031_, lean_object* v_matcherApp_4032_, uint8_t v_useSplitter_4033_, uint8_t v_isCasesOn_4034_, lean_object* v___f_4035_, lean_object* v___x_4036_, lean_object* v___x_4037_, lean_object* v_toMonadExceptOf_4038_, lean_object* v___f_4039_, lean_object* v___f_4040_, lean_object* v_matcherLevels_4041_, lean_object* v_motive_4042_, lean_object* v_onParams_4043_, lean_object* v_params_4044_, lean_object* v_numDiscrEqs_4045_){
_start:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___f_4048_; size_t v_sz_4049_; size_t v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; 
v___x_4046_ = lean_box(v_useSplitter_4033_);
v___x_4047_ = lean_box(v_isCasesOn_4034_);
lean_inc(v_onParams_4043_);
lean_inc_ref(v_inst_4019_);
lean_inc(v_toBind_4017_);
v___f_4048_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed), 31, 30);
lean_closure_set(v___f_4048_, 0, v_toPure_4015_);
lean_closure_set(v___f_4048_, 1, v_inst_4016_);
lean_closure_set(v___f_4048_, 2, v_toBind_4017_);
lean_closure_set(v___f_4048_, 3, v_toMatcherInfo_4018_);
lean_closure_set(v___f_4048_, 4, v_inst_4019_);
lean_closure_set(v___f_4048_, 5, v___f_4020_);
lean_closure_set(v___f_4048_, 6, v_onMotive_4021_);
lean_closure_set(v___f_4048_, 7, v_discrs_4022_);
lean_closure_set(v___f_4048_, 8, v_inst_4023_);
lean_closure_set(v___f_4048_, 9, v_matcherName_4024_);
lean_closure_set(v___f_4048_, 10, v_onRemaining_4025_);
lean_closure_set(v___f_4048_, 11, v_remaining_4026_);
lean_closure_set(v___f_4048_, 12, v_inst_4027_);
lean_closure_set(v___f_4048_, 13, v_alts_4028_);
lean_closure_set(v___f_4048_, 14, v___f_4029_);
lean_closure_set(v___f_4048_, 15, v_onAlt_4030_);
lean_closure_set(v___f_4048_, 16, v___f_4031_);
lean_closure_set(v___f_4048_, 17, v_matcherApp_4032_);
lean_closure_set(v___f_4048_, 18, v___x_4046_);
lean_closure_set(v___f_4048_, 19, v___x_4047_);
lean_closure_set(v___f_4048_, 20, v___f_4035_);
lean_closure_set(v___f_4048_, 21, v___x_4036_);
lean_closure_set(v___f_4048_, 22, v___x_4037_);
lean_closure_set(v___f_4048_, 23, v_toMonadExceptOf_4038_);
lean_closure_set(v___f_4048_, 24, v___f_4039_);
lean_closure_set(v___f_4048_, 25, v_numDiscrEqs_4045_);
lean_closure_set(v___f_4048_, 26, v___f_4040_);
lean_closure_set(v___f_4048_, 27, v_matcherLevels_4041_);
lean_closure_set(v___f_4048_, 28, v_motive_4042_);
lean_closure_set(v___f_4048_, 29, v_onParams_4043_);
v_sz_4049_ = lean_array_size(v_params_4044_);
v___x_4050_ = ((size_t)0ULL);
v___x_4051_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_4019_, v_onParams_4043_, v_sz_4049_, v___x_4050_, v_params_4044_);
v___x_4052_ = lean_apply_4(v_toBind_4017_, lean_box(0), lean_box(0), v___x_4051_, v___f_4048_);
return v___x_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed(lean_object** _args){
lean_object* v_toPure_4053_ = _args[0];
lean_object* v_inst_4054_ = _args[1];
lean_object* v_toBind_4055_ = _args[2];
lean_object* v_toMatcherInfo_4056_ = _args[3];
lean_object* v_inst_4057_ = _args[4];
lean_object* v___f_4058_ = _args[5];
lean_object* v_onMotive_4059_ = _args[6];
lean_object* v_discrs_4060_ = _args[7];
lean_object* v_inst_4061_ = _args[8];
lean_object* v_matcherName_4062_ = _args[9];
lean_object* v_onRemaining_4063_ = _args[10];
lean_object* v_remaining_4064_ = _args[11];
lean_object* v_inst_4065_ = _args[12];
lean_object* v_alts_4066_ = _args[13];
lean_object* v___f_4067_ = _args[14];
lean_object* v_onAlt_4068_ = _args[15];
lean_object* v___f_4069_ = _args[16];
lean_object* v_matcherApp_4070_ = _args[17];
lean_object* v_useSplitter_4071_ = _args[18];
lean_object* v_isCasesOn_4072_ = _args[19];
lean_object* v___f_4073_ = _args[20];
lean_object* v___x_4074_ = _args[21];
lean_object* v___x_4075_ = _args[22];
lean_object* v_toMonadExceptOf_4076_ = _args[23];
lean_object* v___f_4077_ = _args[24];
lean_object* v___f_4078_ = _args[25];
lean_object* v_matcherLevels_4079_ = _args[26];
lean_object* v_motive_4080_ = _args[27];
lean_object* v_onParams_4081_ = _args[28];
lean_object* v_params_4082_ = _args[29];
lean_object* v_numDiscrEqs_4083_ = _args[30];
_start:
{
uint8_t v_useSplitter_boxed_4084_; uint8_t v_isCasesOn_boxed_4085_; lean_object* v_res_4086_; 
v_useSplitter_boxed_4084_ = lean_unbox(v_useSplitter_4071_);
v_isCasesOn_boxed_4085_ = lean_unbox(v_isCasesOn_4072_);
v_res_4086_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__60(v_toPure_4053_, v_inst_4054_, v_toBind_4055_, v_toMatcherInfo_4056_, v_inst_4057_, v___f_4058_, v_onMotive_4059_, v_discrs_4060_, v_inst_4061_, v_matcherName_4062_, v_onRemaining_4063_, v_remaining_4064_, v_inst_4065_, v_alts_4066_, v___f_4067_, v_onAlt_4068_, v___f_4069_, v_matcherApp_4070_, v_useSplitter_boxed_4084_, v_isCasesOn_boxed_4085_, v___f_4073_, v___x_4074_, v___x_4075_, v_toMonadExceptOf_4076_, v___f_4077_, v___f_4078_, v_matcherLevels_4079_, v_motive_4080_, v_onParams_4081_, v_params_4082_, v_numDiscrEqs_4083_);
return v_res_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__61(lean_object* v___f_4087_, lean_object* v_numDiscrEqs_4088_){
_start:
{
lean_object* v___x_4089_; 
v___x_4089_ = lean_apply_1(v___f_4087_, v_numDiscrEqs_4088_);
return v___x_4089_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1(void){
_start:
{
lean_object* v___x_4091_; lean_object* v___x_4092_; 
v___x_4091_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__0));
v___x_4092_ = l_Lean_stringToMessageData(v___x_4091_);
return v___x_4092_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3(void){
_start:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4094_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__2));
v___x_4095_ = l_Lean_stringToMessageData(v___x_4094_);
return v___x_4095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63(lean_object* v_matcherName_4096_, lean_object* v_inst_4097_, lean_object* v_inst_4098_, lean_object* v_toBind_4099_, lean_object* v___f_4100_, lean_object* v_toPure_4101_, lean_object* v___f_4102_, lean_object* v_____do__lift_4103_){
_start:
{
if (lean_obj_tag(v_____do__lift_4103_) == 0)
{
lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; 
lean_dec(v___f_4102_);
lean_dec(v_toPure_4101_);
v___x_4104_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1);
v___x_4105_ = l_Lean_MessageData_ofName(v_matcherName_4096_);
v___x_4106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4104_);
lean_ctor_set(v___x_4106_, 1, v___x_4105_);
v___x_4107_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3);
v___x_4108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4106_);
lean_ctor_set(v___x_4108_, 1, v___x_4107_);
v___x_4109_ = l_Lean_throwError___redArg(v_inst_4097_, v_inst_4098_, v___x_4108_);
v___x_4110_ = lean_apply_4(v_toBind_4099_, lean_box(0), lean_box(0), v___x_4109_, v___f_4100_);
return v___x_4110_;
}
else
{
lean_object* v_val_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; 
lean_dec(v___f_4100_);
lean_dec_ref(v_inst_4098_);
lean_dec_ref(v_inst_4097_);
lean_dec(v_matcherName_4096_);
v_val_4111_ = lean_ctor_get(v_____do__lift_4103_, 0);
v___x_4112_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_4111_);
v___x_4113_ = lean_apply_2(v_toPure_4101_, lean_box(0), v___x_4112_);
v___x_4114_ = lean_apply_4(v_toBind_4099_, lean_box(0), lean_box(0), v___x_4113_, v___f_4102_);
return v___x_4114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed(lean_object* v_matcherName_4115_, lean_object* v_inst_4116_, lean_object* v_inst_4117_, lean_object* v_toBind_4118_, lean_object* v___f_4119_, lean_object* v_toPure_4120_, lean_object* v___f_4121_, lean_object* v_____do__lift_4122_){
_start:
{
lean_object* v_res_4123_; 
v_res_4123_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__63(v_matcherName_4115_, v_inst_4116_, v_inst_4117_, v_toBind_4118_, v___f_4119_, v_toPure_4120_, v___f_4121_, v_____do__lift_4122_);
lean_dec(v_____do__lift_4122_);
return v_res_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64(lean_object* v_matcherApp_4124_, lean_object* v_toPure_4125_, lean_object* v_inst_4126_, lean_object* v_toBind_4127_, lean_object* v_inst_4128_, lean_object* v___f_4129_, lean_object* v_onMotive_4130_, lean_object* v_inst_4131_, lean_object* v_onRemaining_4132_, lean_object* v_inst_4133_, lean_object* v___f_4134_, lean_object* v_onAlt_4135_, lean_object* v___f_4136_, uint8_t v_useSplitter_4137_, lean_object* v___f_4138_, lean_object* v___x_4139_, lean_object* v___x_4140_, lean_object* v_toMonadExceptOf_4141_, lean_object* v___f_4142_, lean_object* v___f_4143_, lean_object* v_onParams_4144_, lean_object* v_inst_4145_, lean_object* v_____do__lift_4146_){
_start:
{
lean_object* v_toMatcherInfo_4147_; lean_object* v_matcherName_4148_; lean_object* v_matcherLevels_4149_; lean_object* v_params_4150_; lean_object* v_motive_4151_; lean_object* v_discrs_4152_; lean_object* v_alts_4153_; lean_object* v_remaining_4154_; uint8_t v_isCasesOn_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___f_4158_; 
v_toMatcherInfo_4147_ = lean_ctor_get(v_matcherApp_4124_, 0);
lean_inc_ref(v_toMatcherInfo_4147_);
v_matcherName_4148_ = lean_ctor_get(v_matcherApp_4124_, 1);
lean_inc_n(v_matcherName_4148_, 3);
v_matcherLevels_4149_ = lean_ctor_get(v_matcherApp_4124_, 2);
lean_inc_ref(v_matcherLevels_4149_);
v_params_4150_ = lean_ctor_get(v_matcherApp_4124_, 3);
lean_inc_ref(v_params_4150_);
v_motive_4151_ = lean_ctor_get(v_matcherApp_4124_, 4);
lean_inc_ref(v_motive_4151_);
v_discrs_4152_ = lean_ctor_get(v_matcherApp_4124_, 5);
lean_inc_ref(v_discrs_4152_);
v_alts_4153_ = lean_ctor_get(v_matcherApp_4124_, 6);
lean_inc_ref(v_alts_4153_);
v_remaining_4154_ = lean_ctor_get(v_matcherApp_4124_, 7);
lean_inc_ref(v_remaining_4154_);
v_isCasesOn_4155_ = l_Lean_isCasesOnRecursor(v_____do__lift_4146_, v_matcherName_4148_);
v___x_4156_ = lean_box(v_useSplitter_4137_);
v___x_4157_ = lean_box(v_isCasesOn_4155_);
lean_inc_ref(v_inst_4131_);
lean_inc_ref(v_inst_4128_);
lean_inc(v_toBind_4127_);
lean_inc(v_toPure_4125_);
v___f_4158_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed), 31, 30);
lean_closure_set(v___f_4158_, 0, v_toPure_4125_);
lean_closure_set(v___f_4158_, 1, v_inst_4126_);
lean_closure_set(v___f_4158_, 2, v_toBind_4127_);
lean_closure_set(v___f_4158_, 3, v_toMatcherInfo_4147_);
lean_closure_set(v___f_4158_, 4, v_inst_4128_);
lean_closure_set(v___f_4158_, 5, v___f_4129_);
lean_closure_set(v___f_4158_, 6, v_onMotive_4130_);
lean_closure_set(v___f_4158_, 7, v_discrs_4152_);
lean_closure_set(v___f_4158_, 8, v_inst_4131_);
lean_closure_set(v___f_4158_, 9, v_matcherName_4148_);
lean_closure_set(v___f_4158_, 10, v_onRemaining_4132_);
lean_closure_set(v___f_4158_, 11, v_remaining_4154_);
lean_closure_set(v___f_4158_, 12, v_inst_4133_);
lean_closure_set(v___f_4158_, 13, v_alts_4153_);
lean_closure_set(v___f_4158_, 14, v___f_4134_);
lean_closure_set(v___f_4158_, 15, v_onAlt_4135_);
lean_closure_set(v___f_4158_, 16, v___f_4136_);
lean_closure_set(v___f_4158_, 17, v_matcherApp_4124_);
lean_closure_set(v___f_4158_, 18, v___x_4156_);
lean_closure_set(v___f_4158_, 19, v___x_4157_);
lean_closure_set(v___f_4158_, 20, v___f_4138_);
lean_closure_set(v___f_4158_, 21, v___x_4139_);
lean_closure_set(v___f_4158_, 22, v___x_4140_);
lean_closure_set(v___f_4158_, 23, v_toMonadExceptOf_4141_);
lean_closure_set(v___f_4158_, 24, v___f_4142_);
lean_closure_set(v___f_4158_, 25, v___f_4143_);
lean_closure_set(v___f_4158_, 26, v_matcherLevels_4149_);
lean_closure_set(v___f_4158_, 27, v_motive_4151_);
lean_closure_set(v___f_4158_, 28, v_onParams_4144_);
lean_closure_set(v___f_4158_, 29, v_params_4150_);
if (v_isCasesOn_4155_ == 0)
{
lean_object* v___f_4159_; lean_object* v___f_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; 
v___f_4159_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61), 2, 1);
lean_closure_set(v___f_4159_, 0, v___f_4158_);
lean_inc_ref(v___f_4159_);
lean_inc(v_toBind_4127_);
lean_inc_ref(v_inst_4128_);
lean_inc(v_matcherName_4148_);
v___f_4160_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed), 8, 7);
lean_closure_set(v___f_4160_, 0, v_matcherName_4148_);
lean_closure_set(v___f_4160_, 1, v_inst_4128_);
lean_closure_set(v___f_4160_, 2, v_inst_4131_);
lean_closure_set(v___f_4160_, 3, v_toBind_4127_);
lean_closure_set(v___f_4160_, 4, v___f_4159_);
lean_closure_set(v___f_4160_, 5, v_toPure_4125_);
lean_closure_set(v___f_4160_, 6, v___f_4159_);
v___x_4161_ = l_Lean_Meta_getMatcherInfo_x3f___redArg(v_inst_4128_, v_inst_4145_, v_matcherName_4148_);
v___x_4162_ = lean_apply_4(v_toBind_4127_, lean_box(0), lean_box(0), v___x_4161_, v___f_4160_);
return v___x_4162_;
}
else
{
lean_object* v___f_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; 
lean_dec(v_matcherName_4148_);
lean_dec_ref(v_inst_4145_);
lean_dec_ref(v_inst_4131_);
lean_dec_ref(v_inst_4128_);
v___f_4163_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61), 2, 1);
lean_closure_set(v___f_4163_, 0, v___f_4158_);
v___x_4164_ = lean_unsigned_to_nat(0u);
v___x_4165_ = lean_apply_2(v_toPure_4125_, lean_box(0), v___x_4164_);
v___x_4166_ = lean_apply_4(v_toBind_4127_, lean_box(0), lean_box(0), v___x_4165_, v___f_4163_);
return v___x_4166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed(lean_object** _args){
lean_object* v_matcherApp_4167_ = _args[0];
lean_object* v_toPure_4168_ = _args[1];
lean_object* v_inst_4169_ = _args[2];
lean_object* v_toBind_4170_ = _args[3];
lean_object* v_inst_4171_ = _args[4];
lean_object* v___f_4172_ = _args[5];
lean_object* v_onMotive_4173_ = _args[6];
lean_object* v_inst_4174_ = _args[7];
lean_object* v_onRemaining_4175_ = _args[8];
lean_object* v_inst_4176_ = _args[9];
lean_object* v___f_4177_ = _args[10];
lean_object* v_onAlt_4178_ = _args[11];
lean_object* v___f_4179_ = _args[12];
lean_object* v_useSplitter_4180_ = _args[13];
lean_object* v___f_4181_ = _args[14];
lean_object* v___x_4182_ = _args[15];
lean_object* v___x_4183_ = _args[16];
lean_object* v_toMonadExceptOf_4184_ = _args[17];
lean_object* v___f_4185_ = _args[18];
lean_object* v___f_4186_ = _args[19];
lean_object* v_onParams_4187_ = _args[20];
lean_object* v_inst_4188_ = _args[21];
lean_object* v_____do__lift_4189_ = _args[22];
_start:
{
uint8_t v_useSplitter_boxed_4190_; lean_object* v_res_4191_; 
v_useSplitter_boxed_4190_ = lean_unbox(v_useSplitter_4180_);
v_res_4191_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__64(v_matcherApp_4167_, v_toPure_4168_, v_inst_4169_, v_toBind_4170_, v_inst_4171_, v___f_4172_, v_onMotive_4173_, v_inst_4174_, v_onRemaining_4175_, v_inst_4176_, v___f_4177_, v_onAlt_4178_, v___f_4179_, v_useSplitter_boxed_4190_, v___f_4181_, v___x_4182_, v___x_4183_, v_toMonadExceptOf_4184_, v___f_4185_, v___f_4186_, v_onParams_4187_, v_inst_4188_, v_____do__lift_4189_);
return v_res_4191_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0(void){
_start:
{
lean_object* v___x_4192_; 
v___x_4192_ = l_Subarray_empty(lean_box(0));
return v___x_4192_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__1(void){
_start:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4193_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0);
v___x_4194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4193_);
lean_ctor_set(v___x_4194_, 1, v___x_4193_);
return v___x_4194_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__2(void){
_start:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; 
v___x_4195_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__1);
v___x_4196_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0);
v___x_4197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4196_);
lean_ctor_set(v___x_4197_, 1, v___x_4195_);
return v___x_4197_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__3(void){
_start:
{
lean_object* v___x_4198_; 
v___x_4198_ = l_Array_instInhabited(lean_box(0));
return v___x_4198_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__4(void){
_start:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; 
v___x_4199_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__2);
v___x_4200_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0);
v___x_4201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4201_, 0, v___x_4200_);
lean_ctor_set(v___x_4201_, 1, v___x_4199_);
return v___x_4201_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__5(void){
_start:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
v___x_4202_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__4, &l_Lean_Meta_MatcherApp_transform___redArg___closed__4_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__4);
v___x_4203_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0);
v___x_4204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4203_);
lean_ctor_set(v___x_4204_, 1, v___x_4202_);
return v___x_4204_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__6(void){
_start:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4205_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__5);
v___x_4206_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__3);
v___x_4207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4206_);
lean_ctor_set(v___x_4207_, 1, v___x_4205_);
return v___x_4207_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__7(void){
_start:
{
lean_object* v___x_4208_; lean_object* v___x_4209_; 
v___x_4208_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__6);
v___x_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4208_);
return v___x_4209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg(lean_object* v_inst_4210_, lean_object* v_inst_4211_, lean_object* v_inst_4212_, lean_object* v_inst_4213_, lean_object* v_inst_4214_, lean_object* v_matcherApp_4215_, uint8_t v_useSplitter_4216_, uint8_t v_addEqualities_4217_, lean_object* v_onParams_4218_, lean_object* v_onMotive_4219_, lean_object* v_onAlt_4220_, lean_object* v_onRemaining_4221_){
_start:
{
lean_object* v_toApplicative_4222_; lean_object* v_toBind_4223_; lean_object* v_getEnv_4224_; lean_object* v_toPure_4225_; lean_object* v_toMonadExceptOf_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___f_4229_; lean_object* v___f_4230_; lean_object* v___f_4231_; lean_object* v___x_4232_; lean_object* v___f_4233_; lean_object* v___x_4234_; lean_object* v___f_4235_; lean_object* v___f_4236_; lean_object* v___f_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___f_4240_; lean_object* v___x_4241_; 
v_toApplicative_4222_ = lean_ctor_get(v_inst_4212_, 0);
v_toBind_4223_ = lean_ctor_get(v_inst_4212_, 1);
lean_inc_n(v_toBind_4223_, 4);
v_getEnv_4224_ = lean_ctor_get(v_inst_4214_, 0);
lean_inc(v_getEnv_4224_);
v_toPure_4225_ = lean_ctor_get(v_toApplicative_4222_, 1);
lean_inc_n(v_toPure_4225_, 5);
v_toMonadExceptOf_4226_ = lean_ctor_get(v_inst_4213_, 0);
lean_inc_ref(v_toMonadExceptOf_4226_);
v___x_4227_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__7, &l_Lean_Meta_MatcherApp_transform___redArg___closed__7_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__7);
lean_inc_ref_n(v_inst_4212_, 4);
v___x_4228_ = l_instInhabitedOfMonad___redArg(v_inst_4212_, v___x_4227_);
lean_inc_ref(v_inst_4213_);
v___f_4229_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4229_, 0, v_inst_4212_);
lean_closure_set(v___f_4229_, 1, v_inst_4213_);
lean_inc_n(v_inst_4210_, 3);
v___f_4230_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4230_, 0, v_inst_4210_);
v___f_4231_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4231_, 0, v_inst_4212_);
lean_closure_set(v___f_4231_, 1, v___f_4230_);
v___x_4232_ = l_Lean_instInhabitedExpr;
v___f_4233_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__5), 6, 3);
lean_closure_set(v___f_4233_, 0, v_toPure_4225_);
lean_closure_set(v___f_4233_, 1, v_inst_4210_);
lean_closure_set(v___f_4233_, 2, v_toBind_4223_);
v___x_4234_ = lean_box(v_addEqualities_4217_);
v___f_4235_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__10___boxed), 7, 4);
lean_closure_set(v___f_4235_, 0, v_toPure_4225_);
lean_closure_set(v___f_4235_, 1, v___x_4234_);
lean_closure_set(v___f_4235_, 2, v_inst_4210_);
lean_closure_set(v___f_4235_, 3, v_toBind_4223_);
v___f_4236_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__11), 2, 1);
lean_closure_set(v___f_4236_, 0, v_toPure_4225_);
v___f_4237_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__12), 2, 1);
lean_closure_set(v___f_4237_, 0, v_toPure_4225_);
v___x_4238_ = l_instInhabitedOfMonad___redArg(v_inst_4212_, v___x_4232_);
v___x_4239_ = lean_box(v_useSplitter_4216_);
v___f_4240_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed), 23, 22);
lean_closure_set(v___f_4240_, 0, v_matcherApp_4215_);
lean_closure_set(v___f_4240_, 1, v_toPure_4225_);
lean_closure_set(v___f_4240_, 2, v_inst_4210_);
lean_closure_set(v___f_4240_, 3, v_toBind_4223_);
lean_closure_set(v___f_4240_, 4, v_inst_4212_);
lean_closure_set(v___f_4240_, 5, v___f_4235_);
lean_closure_set(v___f_4240_, 6, v_onMotive_4219_);
lean_closure_set(v___f_4240_, 7, v_inst_4213_);
lean_closure_set(v___f_4240_, 8, v_onRemaining_4221_);
lean_closure_set(v___f_4240_, 9, v_inst_4211_);
lean_closure_set(v___f_4240_, 10, v___f_4237_);
lean_closure_set(v___f_4240_, 11, v_onAlt_4220_);
lean_closure_set(v___f_4240_, 12, v___f_4231_);
lean_closure_set(v___f_4240_, 13, v___x_4239_);
lean_closure_set(v___f_4240_, 14, v___f_4236_);
lean_closure_set(v___f_4240_, 15, v___x_4228_);
lean_closure_set(v___f_4240_, 16, v___x_4238_);
lean_closure_set(v___f_4240_, 17, v_toMonadExceptOf_4226_);
lean_closure_set(v___f_4240_, 18, v___f_4229_);
lean_closure_set(v___f_4240_, 19, v___f_4233_);
lean_closure_set(v___f_4240_, 20, v_onParams_4218_);
lean_closure_set(v___f_4240_, 21, v_inst_4214_);
v___x_4241_ = lean_apply_4(v_toBind_4223_, lean_box(0), lean_box(0), v_getEnv_4224_, v___f_4240_);
return v___x_4241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___boxed(lean_object* v_inst_4242_, lean_object* v_inst_4243_, lean_object* v_inst_4244_, lean_object* v_inst_4245_, lean_object* v_inst_4246_, lean_object* v_matcherApp_4247_, lean_object* v_useSplitter_4248_, lean_object* v_addEqualities_4249_, lean_object* v_onParams_4250_, lean_object* v_onMotive_4251_, lean_object* v_onAlt_4252_, lean_object* v_onRemaining_4253_){
_start:
{
uint8_t v_useSplitter_boxed_4254_; uint8_t v_addEqualities_boxed_4255_; lean_object* v_res_4256_; 
v_useSplitter_boxed_4254_ = lean_unbox(v_useSplitter_4248_);
v_addEqualities_boxed_4255_ = lean_unbox(v_addEqualities_4249_);
v_res_4256_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_4242_, v_inst_4243_, v_inst_4244_, v_inst_4245_, v_inst_4246_, v_matcherApp_4247_, v_useSplitter_boxed_4254_, v_addEqualities_boxed_4255_, v_onParams_4250_, v_onMotive_4251_, v_onAlt_4252_, v_onRemaining_4253_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform(lean_object* v_n_4257_, lean_object* v_inst_4258_, lean_object* v_inst_4259_, lean_object* v_inst_4260_, lean_object* v_inst_4261_, lean_object* v_inst_4262_, lean_object* v_inst_4263_, lean_object* v_inst_4264_, lean_object* v_inst_4265_, lean_object* v_matcherApp_4266_, uint8_t v_useSplitter_4267_, uint8_t v_addEqualities_4268_, lean_object* v_onParams_4269_, lean_object* v_onMotive_4270_, lean_object* v_onAlt_4271_, lean_object* v_onRemaining_4272_){
_start:
{
lean_object* v___x_4273_; 
v___x_4273_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_4258_, v_inst_4259_, v_inst_4260_, v_inst_4261_, v_inst_4262_, v_matcherApp_4266_, v_useSplitter_4267_, v_addEqualities_4268_, v_onParams_4269_, v_onMotive_4270_, v_onAlt_4271_, v_onRemaining_4272_);
return v___x_4273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___boxed(lean_object* v_n_4274_, lean_object* v_inst_4275_, lean_object* v_inst_4276_, lean_object* v_inst_4277_, lean_object* v_inst_4278_, lean_object* v_inst_4279_, lean_object* v_inst_4280_, lean_object* v_inst_4281_, lean_object* v_inst_4282_, lean_object* v_matcherApp_4283_, lean_object* v_useSplitter_4284_, lean_object* v_addEqualities_4285_, lean_object* v_onParams_4286_, lean_object* v_onMotive_4287_, lean_object* v_onAlt_4288_, lean_object* v_onRemaining_4289_){
_start:
{
uint8_t v_useSplitter_boxed_4290_; uint8_t v_addEqualities_boxed_4291_; lean_object* v_res_4292_; 
v_useSplitter_boxed_4290_ = lean_unbox(v_useSplitter_4284_);
v_addEqualities_boxed_4291_ = lean_unbox(v_addEqualities_4285_);
v_res_4292_ = l_Lean_Meta_MatcherApp_transform(v_n_4274_, v_inst_4275_, v_inst_4276_, v_inst_4277_, v_inst_4278_, v_inst_4279_, v_inst_4280_, v_inst_4281_, v_inst_4282_, v_matcherApp_4283_, v_useSplitter_boxed_4290_, v_addEqualities_boxed_4291_, v_onParams_4286_, v_onMotive_4287_, v_onAlt_4288_, v_onRemaining_4289_);
lean_dec(v_inst_4282_);
lean_dec(v_inst_4281_);
lean_dec_ref(v_inst_4280_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0(lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_){
_start:
{
lean_object* v___x_4299_; 
v___x_4299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4299_, 0, v___y_4293_);
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0___boxed(lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_){
_start:
{
lean_object* v_res_4306_; 
v_res_4306_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__0(v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec(v___y_4302_);
lean_dec_ref(v___y_4301_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1(lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_){
_start:
{
lean_object* v___x_4313_; 
v___x_4313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4313_, 0, v___y_4307_);
return v___x_4313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1___boxed(lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__1(v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
lean_dec(v___y_4318_);
lean_dec_ref(v___y_4317_);
lean_dec(v___y_4316_);
lean_dec_ref(v___y_4315_);
return v_res_4320_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(lean_object* v_opts_4321_, lean_object* v_opt_4322_){
_start:
{
lean_object* v_name_4323_; lean_object* v_defValue_4324_; lean_object* v_map_4325_; lean_object* v___x_4326_; 
v_name_4323_ = lean_ctor_get(v_opt_4322_, 0);
v_defValue_4324_ = lean_ctor_get(v_opt_4322_, 1);
v_map_4325_ = lean_ctor_get(v_opts_4321_, 0);
v___x_4326_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4325_, v_name_4323_);
if (lean_obj_tag(v___x_4326_) == 0)
{
uint8_t v___x_4327_; 
v___x_4327_ = lean_unbox(v_defValue_4324_);
return v___x_4327_;
}
else
{
lean_object* v_val_4328_; 
v_val_4328_ = lean_ctor_get(v___x_4326_, 0);
lean_inc(v_val_4328_);
lean_dec_ref_known(v___x_4326_, 1);
if (lean_obj_tag(v_val_4328_) == 1)
{
uint8_t v_v_4329_; 
v_v_4329_ = lean_ctor_get_uint8(v_val_4328_, 0);
lean_dec_ref_known(v_val_4328_, 0);
return v_v_4329_;
}
else
{
uint8_t v___x_4330_; 
lean_dec(v_val_4328_);
v___x_4330_ = lean_unbox(v_defValue_4324_);
return v___x_4330_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11___boxed(lean_object* v_opts_4331_, lean_object* v_opt_4332_){
_start:
{
uint8_t v_res_4333_; lean_object* v_r_4334_; 
v_res_4333_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(v_opts_4331_, v_opt_4332_);
lean_dec_ref(v_opt_4332_);
lean_dec_ref(v_opts_4331_);
v_r_4334_ = lean_box(v_res_4333_);
return v_r_4334_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_4343_, uint8_t v___y_4344_, lean_object* v_x_4345_){
_start:
{
if (lean_obj_tag(v_x_4345_) == 1)
{
lean_object* v_pre_4346_; 
v_pre_4346_ = lean_ctor_get(v_x_4345_, 0);
switch(lean_obj_tag(v_pre_4346_))
{
case 1:
{
lean_object* v_pre_4347_; 
v_pre_4347_ = lean_ctor_get(v_pre_4346_, 0);
switch(lean_obj_tag(v_pre_4347_))
{
case 0:
{
lean_object* v_str_4348_; lean_object* v_str_4349_; lean_object* v___x_4350_; uint8_t v___x_4351_; 
v_str_4348_ = lean_ctor_get(v_x_4345_, 1);
v_str_4349_ = lean_ctor_get(v_pre_4346_, 1);
v___x_4350_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_4351_ = lean_string_dec_eq(v_str_4349_, v___x_4350_);
if (v___x_4351_ == 0)
{
lean_object* v___x_4352_; uint8_t v___x_4353_; 
v___x_4352_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_4353_ = lean_string_dec_eq(v_str_4349_, v___x_4352_);
if (v___x_4353_ == 0)
{
return v___x_4353_;
}
else
{
lean_object* v___x_4354_; uint8_t v___x_4355_; 
v___x_4354_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_4355_ = lean_string_dec_eq(v_str_4348_, v___x_4354_);
if (v___x_4355_ == 0)
{
return v___x_4355_;
}
else
{
return v_suppressElabErrors_4343_;
}
}
}
else
{
lean_object* v___x_4356_; uint8_t v___x_4357_; 
v___x_4356_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_4357_ = lean_string_dec_eq(v_str_4348_, v___x_4356_);
if (v___x_4357_ == 0)
{
return v___x_4357_;
}
else
{
return v_suppressElabErrors_4343_;
}
}
}
case 1:
{
lean_object* v_pre_4358_; 
v_pre_4358_ = lean_ctor_get(v_pre_4347_, 0);
if (lean_obj_tag(v_pre_4358_) == 0)
{
lean_object* v_str_4359_; lean_object* v_str_4360_; lean_object* v_str_4361_; lean_object* v___x_4362_; uint8_t v___x_4363_; 
v_str_4359_ = lean_ctor_get(v_x_4345_, 1);
v_str_4360_ = lean_ctor_get(v_pre_4346_, 1);
v_str_4361_ = lean_ctor_get(v_pre_4347_, 1);
v___x_4362_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_4363_ = lean_string_dec_eq(v_str_4361_, v___x_4362_);
if (v___x_4363_ == 0)
{
return v___x_4363_;
}
else
{
lean_object* v___x_4364_; uint8_t v___x_4365_; 
v___x_4364_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_4365_ = lean_string_dec_eq(v_str_4360_, v___x_4364_);
if (v___x_4365_ == 0)
{
return v___x_4365_;
}
else
{
lean_object* v___x_4366_; uint8_t v___x_4367_; 
v___x_4366_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_4367_ = lean_string_dec_eq(v_str_4359_, v___x_4366_);
if (v___x_4367_ == 0)
{
return v___x_4367_;
}
else
{
return v_suppressElabErrors_4343_;
}
}
}
}
else
{
return v___y_4344_;
}
}
default: 
{
return v___y_4344_;
}
}
}
case 0:
{
lean_object* v_str_4368_; lean_object* v___x_4369_; uint8_t v___x_4370_; 
v_str_4368_ = lean_ctor_get(v_x_4345_, 1);
v___x_4369_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_4370_ = lean_string_dec_eq(v_str_4368_, v___x_4369_);
if (v___x_4370_ == 0)
{
return v___x_4370_;
}
else
{
return v_suppressElabErrors_4343_;
}
}
default: 
{
return v___y_4344_;
}
}
}
else
{
return v___y_4344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_4371_, lean_object* v___y_4372_, lean_object* v_x_4373_){
_start:
{
uint8_t v_suppressElabErrors_boxed_4374_; uint8_t v___y_32104__boxed_4375_; uint8_t v_res_4376_; lean_object* v_r_4377_; 
v_suppressElabErrors_boxed_4374_ = lean_unbox(v_suppressElabErrors_4371_);
v___y_32104__boxed_4375_ = lean_unbox(v___y_4372_);
v_res_4376_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_4374_, v___y_32104__boxed_4375_, v_x_4373_);
lean_dec(v_x_4373_);
v_r_4377_ = lean_box(v_res_4376_);
return v_r_4377_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(lean_object* v_ref_4379_, lean_object* v_msgData_4380_, uint8_t v_severity_4381_, uint8_t v_isSilent_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_){
_start:
{
uint8_t v___y_4389_; lean_object* v___y_4390_; uint8_t v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4425_; lean_object* v___y_4426_; uint8_t v___y_4427_; uint8_t v___y_4428_; uint8_t v___y_4429_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4451_; lean_object* v___y_4452_; uint8_t v___y_4453_; lean_object* v___y_4454_; uint8_t v___y_4455_; uint8_t v___y_4456_; lean_object* v___y_4457_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; uint8_t v___y_4464_; uint8_t v___y_4465_; uint8_t v___y_4466_; uint8_t v___x_4471_; lean_object* v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; uint8_t v___y_4476_; uint8_t v___y_4477_; uint8_t v___y_4478_; uint8_t v___y_4480_; uint8_t v___x_4494_; 
v___x_4471_ = 2;
v___x_4494_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4381_, v___x_4471_);
if (v___x_4494_ == 0)
{
v___y_4480_ = v___x_4494_;
goto v___jp_4479_;
}
else
{
uint8_t v___x_4495_; 
lean_inc_ref(v_msgData_4380_);
v___x_4495_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4380_);
v___y_4480_ = v___x_4495_;
goto v___jp_4479_;
}
v___jp_4388_:
{
lean_object* v___x_4398_; lean_object* v_currNamespace_4399_; lean_object* v_openDecls_4400_; lean_object* v_env_4401_; lean_object* v_nextMacroScope_4402_; lean_object* v_ngen_4403_; lean_object* v_auxDeclNGen_4404_; lean_object* v_traceState_4405_; lean_object* v_cache_4406_; lean_object* v_messages_4407_; lean_object* v_infoState_4408_; lean_object* v_snapshotTasks_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4423_; 
v___x_4398_ = lean_st_ref_take(v___y_4397_);
v_currNamespace_4399_ = lean_ctor_get(v___y_4396_, 5);
v_openDecls_4400_ = lean_ctor_get(v___y_4396_, 6);
v_env_4401_ = lean_ctor_get(v___x_4398_, 0);
v_nextMacroScope_4402_ = lean_ctor_get(v___x_4398_, 1);
v_ngen_4403_ = lean_ctor_get(v___x_4398_, 2);
v_auxDeclNGen_4404_ = lean_ctor_get(v___x_4398_, 3);
v_traceState_4405_ = lean_ctor_get(v___x_4398_, 4);
v_cache_4406_ = lean_ctor_get(v___x_4398_, 5);
v_messages_4407_ = lean_ctor_get(v___x_4398_, 6);
v_infoState_4408_ = lean_ctor_get(v___x_4398_, 7);
v_snapshotTasks_4409_ = lean_ctor_get(v___x_4398_, 8);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4398_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4411_ = v___x_4398_;
v_isShared_4412_ = v_isSharedCheck_4423_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_snapshotTasks_4409_);
lean_inc(v_infoState_4408_);
lean_inc(v_messages_4407_);
lean_inc(v_cache_4406_);
lean_inc(v_traceState_4405_);
lean_inc(v_auxDeclNGen_4404_);
lean_inc(v_ngen_4403_);
lean_inc(v_nextMacroScope_4402_);
lean_inc(v_env_4401_);
lean_dec(v___x_4398_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4423_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4418_; 
lean_inc(v_openDecls_4400_);
lean_inc(v_currNamespace_4399_);
v___x_4413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4413_, 0, v_currNamespace_4399_);
lean_ctor_set(v___x_4413_, 1, v_openDecls_4400_);
v___x_4414_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4414_, 0, v___x_4413_);
lean_ctor_set(v___x_4414_, 1, v___y_4392_);
lean_inc_ref(v___y_4390_);
lean_inc_ref(v___y_4395_);
v___x_4415_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4415_, 0, v___y_4395_);
lean_ctor_set(v___x_4415_, 1, v___y_4393_);
lean_ctor_set(v___x_4415_, 2, v___y_4394_);
lean_ctor_set(v___x_4415_, 3, v___y_4390_);
lean_ctor_set(v___x_4415_, 4, v___x_4414_);
lean_ctor_set_uint8(v___x_4415_, sizeof(void*)*5, v___y_4391_);
lean_ctor_set_uint8(v___x_4415_, sizeof(void*)*5 + 1, v___y_4389_);
lean_ctor_set_uint8(v___x_4415_, sizeof(void*)*5 + 2, v_isSilent_4382_);
v___x_4416_ = l_Lean_MessageLog_add(v___x_4415_, v_messages_4407_);
if (v_isShared_4412_ == 0)
{
lean_ctor_set(v___x_4411_, 6, v___x_4416_);
v___x_4418_ = v___x_4411_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v_env_4401_);
lean_ctor_set(v_reuseFailAlloc_4422_, 1, v_nextMacroScope_4402_);
lean_ctor_set(v_reuseFailAlloc_4422_, 2, v_ngen_4403_);
lean_ctor_set(v_reuseFailAlloc_4422_, 3, v_auxDeclNGen_4404_);
lean_ctor_set(v_reuseFailAlloc_4422_, 4, v_traceState_4405_);
lean_ctor_set(v_reuseFailAlloc_4422_, 5, v_cache_4406_);
lean_ctor_set(v_reuseFailAlloc_4422_, 6, v___x_4416_);
lean_ctor_set(v_reuseFailAlloc_4422_, 7, v_infoState_4408_);
lean_ctor_set(v_reuseFailAlloc_4422_, 8, v_snapshotTasks_4409_);
v___x_4418_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; 
v___x_4419_ = lean_st_ref_put(v___y_4397_, v___x_4418_);
v___x_4420_ = lean_box(0);
v___x_4421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4421_, 0, v___x_4420_);
return v___x_4421_;
}
}
}
v___jp_4424_:
{
lean_object* v_fileName_4432_; lean_object* v_fileMap_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4449_; 
v_fileName_4432_ = lean_ctor_get(v___y_4426_, 0);
v_fileMap_4433_ = lean_ctor_get(v___y_4426_, 1);
v___x_4434_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4380_);
v___x_4435_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(v___x_4434_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_);
v_a_4436_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4449_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4449_ == 0)
{
v___x_4438_ = v___x_4435_;
v_isShared_4439_ = v_isSharedCheck_4449_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4435_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4449_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; 
lean_inc_ref_n(v_fileMap_4433_, 2);
v___x_4440_ = l_Lean_FileMap_toPosition(v_fileMap_4433_, v___y_4430_);
lean_dec(v___y_4430_);
v___x_4441_ = l_Lean_FileMap_toPosition(v_fileMap_4433_, v___y_4431_);
lean_dec(v___y_4431_);
v___x_4442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4442_, 0, v___x_4441_);
v___x_4443_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___closed__0));
if (v___y_4429_ == 0)
{
lean_del_object(v___x_4438_);
lean_dec_ref(v___y_4425_);
v___y_4389_ = v___y_4427_;
v___y_4390_ = v___x_4443_;
v___y_4391_ = v___y_4428_;
v___y_4392_ = v_a_4436_;
v___y_4393_ = v___x_4440_;
v___y_4394_ = v___x_4442_;
v___y_4395_ = v_fileName_4432_;
v___y_4396_ = v___y_4385_;
v___y_4397_ = v___y_4386_;
goto v___jp_4388_;
}
else
{
uint8_t v___x_4444_; 
lean_inc(v_a_4436_);
v___x_4444_ = l_Lean_MessageData_hasTag(v___y_4425_, v_a_4436_);
if (v___x_4444_ == 0)
{
lean_object* v___x_4445_; lean_object* v___x_4447_; 
lean_dec_ref_known(v___x_4442_, 1);
lean_dec_ref(v___x_4440_);
lean_dec(v_a_4436_);
v___x_4445_ = lean_box(0);
if (v_isShared_4439_ == 0)
{
lean_ctor_set(v___x_4438_, 0, v___x_4445_);
v___x_4447_ = v___x_4438_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v___x_4445_);
v___x_4447_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
return v___x_4447_;
}
}
else
{
lean_del_object(v___x_4438_);
v___y_4389_ = v___y_4427_;
v___y_4390_ = v___x_4443_;
v___y_4391_ = v___y_4428_;
v___y_4392_ = v_a_4436_;
v___y_4393_ = v___x_4440_;
v___y_4394_ = v___x_4442_;
v___y_4395_ = v_fileName_4432_;
v___y_4396_ = v___y_4385_;
v___y_4397_ = v___y_4386_;
goto v___jp_4388_;
}
}
}
}
v___jp_4450_:
{
lean_object* v___x_4458_; 
v___x_4458_ = l_Lean_Syntax_getTailPos_x3f(v___y_4454_, v___y_4455_);
lean_dec(v___y_4454_);
if (lean_obj_tag(v___x_4458_) == 0)
{
lean_inc(v___y_4457_);
v___y_4425_ = v___y_4451_;
v___y_4426_ = v___y_4452_;
v___y_4427_ = v___y_4453_;
v___y_4428_ = v___y_4455_;
v___y_4429_ = v___y_4456_;
v___y_4430_ = v___y_4457_;
v___y_4431_ = v___y_4457_;
goto v___jp_4424_;
}
else
{
lean_object* v_val_4459_; 
v_val_4459_ = lean_ctor_get(v___x_4458_, 0);
lean_inc(v_val_4459_);
lean_dec_ref_known(v___x_4458_, 1);
v___y_4425_ = v___y_4451_;
v___y_4426_ = v___y_4452_;
v___y_4427_ = v___y_4453_;
v___y_4428_ = v___y_4455_;
v___y_4429_ = v___y_4456_;
v___y_4430_ = v___y_4457_;
v___y_4431_ = v_val_4459_;
goto v___jp_4424_;
}
}
v___jp_4460_:
{
lean_object* v_ref_4467_; lean_object* v___x_4468_; 
v_ref_4467_ = l_Lean_replaceRef(v_ref_4379_, v___y_4463_);
v___x_4468_ = l_Lean_Syntax_getPos_x3f(v_ref_4467_, v___y_4464_);
if (lean_obj_tag(v___x_4468_) == 0)
{
lean_object* v___x_4469_; 
v___x_4469_ = lean_unsigned_to_nat(0u);
v___y_4451_ = v___y_4461_;
v___y_4452_ = v___y_4462_;
v___y_4453_ = v___y_4466_;
v___y_4454_ = v_ref_4467_;
v___y_4455_ = v___y_4464_;
v___y_4456_ = v___y_4465_;
v___y_4457_ = v___x_4469_;
goto v___jp_4450_;
}
else
{
lean_object* v_val_4470_; 
v_val_4470_ = lean_ctor_get(v___x_4468_, 0);
lean_inc(v_val_4470_);
lean_dec_ref_known(v___x_4468_, 1);
v___y_4451_ = v___y_4461_;
v___y_4452_ = v___y_4462_;
v___y_4453_ = v___y_4466_;
v___y_4454_ = v_ref_4467_;
v___y_4455_ = v___y_4464_;
v___y_4456_ = v___y_4465_;
v___y_4457_ = v_val_4470_;
goto v___jp_4450_;
}
}
v___jp_4472_:
{
if (v___y_4478_ == 0)
{
v___y_4461_ = v___y_4475_;
v___y_4462_ = v___y_4473_;
v___y_4463_ = v___y_4474_;
v___y_4464_ = v___y_4477_;
v___y_4465_ = v___y_4476_;
v___y_4466_ = v_severity_4381_;
goto v___jp_4460_;
}
else
{
v___y_4461_ = v___y_4475_;
v___y_4462_ = v___y_4473_;
v___y_4463_ = v___y_4474_;
v___y_4464_ = v___y_4477_;
v___y_4465_ = v___y_4476_;
v___y_4466_ = v___x_4471_;
goto v___jp_4460_;
}
}
v___jp_4479_:
{
if (v___y_4480_ == 0)
{
lean_object* v_toCold_4481_; lean_object* v_options_4482_; lean_object* v_ref_4483_; uint8_t v_suppressElabErrors_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___f_4487_; uint8_t v___x_4488_; uint8_t v___x_4489_; 
v_toCold_4481_ = lean_ctor_get(v___y_4385_, 0);
v_options_4482_ = lean_ctor_get(v___y_4385_, 1);
v_ref_4483_ = lean_ctor_get(v___y_4385_, 4);
v_suppressElabErrors_4484_ = lean_ctor_get_uint8(v___y_4385_, sizeof(void*)*10 + 1);
v___x_4485_ = lean_box(v_suppressElabErrors_4484_);
v___x_4486_ = lean_box(v___y_4480_);
v___f_4487_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4487_, 0, v___x_4485_);
lean_closure_set(v___f_4487_, 1, v___x_4486_);
v___x_4488_ = 1;
v___x_4489_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4381_, v___x_4488_);
if (v___x_4489_ == 0)
{
v___y_4473_ = v_toCold_4481_;
v___y_4474_ = v_ref_4483_;
v___y_4475_ = v___f_4487_;
v___y_4476_ = v_suppressElabErrors_4484_;
v___y_4477_ = v___y_4480_;
v___y_4478_ = v___x_4489_;
goto v___jp_4472_;
}
else
{
lean_object* v___x_4490_; uint8_t v___x_4491_; 
v___x_4490_ = l_Lean_warningAsError;
v___x_4491_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(v_options_4482_, v___x_4490_);
v___y_4473_ = v_toCold_4481_;
v___y_4474_ = v_ref_4483_;
v___y_4475_ = v___f_4487_;
v___y_4476_ = v_suppressElabErrors_4484_;
v___y_4477_ = v___y_4480_;
v___y_4478_ = v___x_4491_;
goto v___jp_4472_;
}
}
else
{
lean_object* v___x_4492_; lean_object* v___x_4493_; 
lean_dec_ref(v_msgData_4380_);
v___x_4492_ = lean_box(0);
v___x_4493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4493_, 0, v___x_4492_);
return v___x_4493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_4496_, lean_object* v_msgData_4497_, lean_object* v_severity_4498_, lean_object* v_isSilent_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_){
_start:
{
uint8_t v_severity_boxed_4505_; uint8_t v_isSilent_boxed_4506_; lean_object* v_res_4507_; 
v_severity_boxed_4505_ = lean_unbox(v_severity_4498_);
v_isSilent_boxed_4506_ = lean_unbox(v_isSilent_4499_);
v_res_4507_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(v_ref_4496_, v_msgData_4497_, v_severity_boxed_4505_, v_isSilent_boxed_4506_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec(v_ref_4496_);
return v_res_4507_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(lean_object* v_msgData_4508_, uint8_t v_severity_4509_, uint8_t v_isSilent_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_){
_start:
{
lean_object* v_ref_4516_; lean_object* v___x_4517_; 
v_ref_4516_ = lean_ctor_get(v___y_4513_, 4);
v___x_4517_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(v_ref_4516_, v_msgData_4508_, v_severity_4509_, v_isSilent_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_);
return v___x_4517_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0___boxed(lean_object* v_msgData_4518_, lean_object* v_severity_4519_, lean_object* v_isSilent_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_){
_start:
{
uint8_t v_severity_boxed_4526_; uint8_t v_isSilent_boxed_4527_; lean_object* v_res_4528_; 
v_severity_boxed_4526_ = lean_unbox(v_severity_4519_);
v_isSilent_boxed_4527_ = lean_unbox(v_isSilent_4520_);
v_res_4528_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(v_msgData_4518_, v_severity_boxed_4526_, v_isSilent_boxed_4527_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_);
lean_dec(v___y_4524_);
lean_dec_ref(v___y_4523_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
return v_res_4528_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(lean_object* v_msgData_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_){
_start:
{
uint8_t v___x_4535_; uint8_t v___x_4536_; lean_object* v___x_4537_; 
v___x_4535_ = 0;
v___x_4536_ = 0;
v___x_4537_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(v_msgData_4529_, v___x_4535_, v___x_4536_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_);
return v___x_4537_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0___boxed(lean_object* v_msgData_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(v_msgData_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_);
lean_dec(v___y_4542_);
lean_dec_ref(v___y_4541_);
lean_dec(v___y_4540_);
lean_dec_ref(v___y_4539_);
return v_res_4544_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1(void){
_start:
{
lean_object* v___x_4546_; lean_object* v___x_4547_; 
v___x_4546_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0));
v___x_4547_ = l_Lean_stringToMessageData(v___x_4546_);
return v___x_4547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2(uint8_t v___x_4548_, lean_object* v___altIdx_4549_, lean_object* v_expAltType_4550_, lean_object* v___altFVars_4551_, lean_object* v_alt_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_){
_start:
{
lean_object* v___x_4558_; 
lean_inc(v___y_4556_);
lean_inc_ref(v___y_4555_);
lean_inc(v___y_4554_);
lean_inc_ref(v___y_4553_);
lean_inc_ref(v_alt_4552_);
v___x_4558_ = lean_infer_type(v_alt_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_);
if (lean_obj_tag(v___x_4558_) == 0)
{
lean_object* v_a_4559_; lean_object* v___x_4560_; 
v_a_4559_ = lean_ctor_get(v___x_4558_, 0);
lean_inc(v_a_4559_);
lean_dec_ref_known(v___x_4558_, 1);
v___x_4560_ = l_Lean_Meta_mkEq(v_expAltType_4550_, v_a_4559_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_);
if (lean_obj_tag(v___x_4560_) == 0)
{
lean_object* v_a_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; 
v_a_4561_ = lean_ctor_get(v___x_4560_, 0);
lean_inc(v_a_4561_);
lean_dec_ref_known(v___x_4560_, 1);
v___x_4562_ = lean_box(0);
v___x_4563_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4561_, v___x_4562_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_);
if (lean_obj_tag(v___x_4563_) == 0)
{
lean_object* v_a_4564_; lean_object* v___y_4566_; lean_object* v___x_4576_; lean_object* v___x_4577_; 
v_a_4564_ = lean_ctor_get(v___x_4563_, 0);
lean_inc(v_a_4564_);
lean_dec_ref_known(v___x_4563_, 1);
v___x_4576_ = l_Lean_Expr_mvarId_x21(v_a_4564_);
v___x_4577_ = l_Lean_Meta_Split_simpMatchTarget(v___x_4576_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_);
if (lean_obj_tag(v___x_4577_) == 0)
{
lean_object* v_a_4578_; lean_object* v___x_4579_; 
v_a_4578_ = lean_ctor_get(v___x_4577_, 0);
lean_inc_n(v_a_4578_, 2);
lean_dec_ref_known(v___x_4577_, 1);
v___x_4579_ = l_Lean_MVarId_refl(v_a_4578_, v___x_4548_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_);
if (lean_obj_tag(v___x_4579_) == 0)
{
lean_dec(v_a_4578_);
v___y_4566_ = v___x_4579_;
goto v___jp_4565_;
}
else
{
lean_object* v_a_4580_; uint8_t v___y_4582_; uint8_t v___x_4595_; 
v_a_4580_ = lean_ctor_get(v___x_4579_, 0);
lean_inc(v_a_4580_);
v___x_4595_ = l_Lean_Exception_isInterrupt(v_a_4580_);
if (v___x_4595_ == 0)
{
uint8_t v___x_4596_; 
v___x_4596_ = l_Lean_Exception_isRuntime(v_a_4580_);
v___y_4582_ = v___x_4596_;
goto v___jp_4581_;
}
else
{
lean_dec(v_a_4580_);
v___y_4582_ = v___x_4595_;
goto v___jp_4581_;
}
v___jp_4581_:
{
if (v___y_4582_ == 0)
{
lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4593_; 
v_isSharedCheck_4593_ = !lean_is_exclusive(v___x_4579_);
if (v_isSharedCheck_4593_ == 0)
{
lean_object* v_unused_4594_; 
v_unused_4594_ = lean_ctor_get(v___x_4579_, 0);
lean_dec(v_unused_4594_);
v___x_4584_ = v___x_4579_;
v_isShared_4585_ = v_isSharedCheck_4593_;
goto v_resetjp_4583_;
}
else
{
lean_dec(v___x_4579_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4593_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
lean_object* v___x_4586_; lean_object* v___x_4588_; 
v___x_4586_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1, &l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1);
lean_inc(v_a_4578_);
if (v_isShared_4585_ == 0)
{
lean_ctor_set(v___x_4584_, 0, v_a_4578_);
v___x_4588_ = v___x_4584_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v_a_4578_);
v___x_4588_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
lean_object* v___x_4589_; lean_object* v___x_4590_; 
v___x_4589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4586_);
lean_ctor_set(v___x_4589_, 1, v___x_4588_);
v___x_4590_ = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(v___x_4589_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_);
if (lean_obj_tag(v___x_4590_) == 0)
{
lean_object* v___x_4591_; 
lean_dec_ref_known(v___x_4590_, 1);
v___x_4591_ = l_Lean_MVarId_admit(v_a_4578_, v___x_4548_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_);
v___y_4566_ = v___x_4591_;
goto v___jp_4565_;
}
else
{
lean_dec(v_a_4578_);
v___y_4566_ = v___x_4590_;
goto v___jp_4565_;
}
}
}
}
else
{
lean_dec(v_a_4578_);
v___y_4566_ = v___x_4579_;
goto v___jp_4565_;
}
}
}
}
else
{
lean_object* v_a_4597_; lean_object* v___x_4599_; uint8_t v_isShared_4600_; uint8_t v_isSharedCheck_4604_; 
lean_dec(v_a_4564_);
lean_dec_ref(v_alt_4552_);
v_a_4597_ = lean_ctor_get(v___x_4577_, 0);
v_isSharedCheck_4604_ = !lean_is_exclusive(v___x_4577_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4599_ = v___x_4577_;
v_isShared_4600_ = v_isSharedCheck_4604_;
goto v_resetjp_4598_;
}
else
{
lean_inc(v_a_4597_);
lean_dec(v___x_4577_);
v___x_4599_ = lean_box(0);
v_isShared_4600_ = v_isSharedCheck_4604_;
goto v_resetjp_4598_;
}
v_resetjp_4598_:
{
lean_object* v___x_4602_; 
if (v_isShared_4600_ == 0)
{
v___x_4602_ = v___x_4599_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v_a_4597_);
v___x_4602_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
return v___x_4602_;
}
}
}
v___jp_4565_:
{
if (lean_obj_tag(v___y_4566_) == 0)
{
lean_object* v___x_4567_; 
lean_dec_ref_known(v___y_4566_, 1);
v___x_4567_ = l_Lean_Meta_mkEqMPR(v_a_4564_, v_alt_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_);
return v___x_4567_;
}
else
{
lean_object* v_a_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4575_; 
lean_dec(v_a_4564_);
lean_dec_ref(v_alt_4552_);
v_a_4568_ = lean_ctor_get(v___y_4566_, 0);
v_isSharedCheck_4575_ = !lean_is_exclusive(v___y_4566_);
if (v_isSharedCheck_4575_ == 0)
{
v___x_4570_ = v___y_4566_;
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_a_4568_);
lean_dec(v___y_4566_);
v___x_4570_ = lean_box(0);
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
v_resetjp_4569_:
{
lean_object* v___x_4573_; 
if (v_isShared_4571_ == 0)
{
v___x_4573_ = v___x_4570_;
goto v_reusejp_4572_;
}
else
{
lean_object* v_reuseFailAlloc_4574_; 
v_reuseFailAlloc_4574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4574_, 0, v_a_4568_);
v___x_4573_ = v_reuseFailAlloc_4574_;
goto v_reusejp_4572_;
}
v_reusejp_4572_:
{
return v___x_4573_;
}
}
}
}
}
else
{
lean_dec_ref(v_alt_4552_);
return v___x_4563_;
}
}
else
{
lean_dec_ref(v_alt_4552_);
return v___x_4560_;
}
}
else
{
lean_dec_ref(v_alt_4552_);
lean_dec_ref(v_expAltType_4550_);
return v___x_4558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___boxed(lean_object* v___x_4605_, lean_object* v___altIdx_4606_, lean_object* v_expAltType_4607_, lean_object* v___altFVars_4608_, lean_object* v_alt_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_){
_start:
{
uint8_t v___x_32418__boxed_4615_; lean_object* v_res_4616_; 
v___x_32418__boxed_4615_ = lean_unbox(v___x_4605_);
v_res_4616_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__2(v___x_32418__boxed_4615_, v___altIdx_4606_, v_expAltType_4607_, v___altFVars_4608_, v_alt_4609_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_);
lean_dec(v___y_4613_);
lean_dec_ref(v___y_4612_);
lean_dec(v___y_4611_);
lean_dec_ref(v___y_4610_);
lean_dec_ref(v___altFVars_4608_);
lean_dec(v___altIdx_4606_);
return v_res_4616_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(lean_object* v___x_4617_, lean_object* v_e_4618_){
_start:
{
uint8_t v___x_4619_; lean_object* v_d_4621_; lean_object* v_b_4622_; 
v___x_4619_ = l_Lean_Expr_hasFVar(v_e_4618_);
if (v___x_4619_ == 0)
{
return v___x_4619_;
}
else
{
switch(lean_obj_tag(v_e_4618_))
{
case 7:
{
lean_object* v_binderType_4625_; lean_object* v_body_4626_; 
v_binderType_4625_ = lean_ctor_get(v_e_4618_, 1);
v_body_4626_ = lean_ctor_get(v_e_4618_, 2);
v_d_4621_ = v_binderType_4625_;
v_b_4622_ = v_body_4626_;
goto v___jp_4620_;
}
case 6:
{
lean_object* v_binderType_4627_; lean_object* v_body_4628_; 
v_binderType_4627_ = lean_ctor_get(v_e_4618_, 1);
v_body_4628_ = lean_ctor_get(v_e_4618_, 2);
v_d_4621_ = v_binderType_4627_;
v_b_4622_ = v_body_4628_;
goto v___jp_4620_;
}
case 10:
{
lean_object* v_expr_4629_; 
v_expr_4629_ = lean_ctor_get(v_e_4618_, 1);
v_e_4618_ = v_expr_4629_;
goto _start;
}
case 8:
{
lean_object* v_type_4631_; lean_object* v_value_4632_; lean_object* v_body_4633_; uint8_t v___x_4634_; 
v_type_4631_ = lean_ctor_get(v_e_4618_, 1);
v_value_4632_ = lean_ctor_get(v_e_4618_, 2);
v_body_4633_ = lean_ctor_get(v_e_4618_, 3);
v___x_4634_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4617_, v_type_4631_);
if (v___x_4634_ == 0)
{
uint8_t v___x_4635_; 
v___x_4635_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4617_, v_value_4632_);
if (v___x_4635_ == 0)
{
v_e_4618_ = v_body_4633_;
goto _start;
}
else
{
return v___x_4619_;
}
}
else
{
return v___x_4619_;
}
}
case 5:
{
lean_object* v_fn_4637_; lean_object* v_arg_4638_; uint8_t v___x_4639_; 
v_fn_4637_ = lean_ctor_get(v_e_4618_, 0);
v_arg_4638_ = lean_ctor_get(v_e_4618_, 1);
v___x_4639_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4617_, v_fn_4637_);
if (v___x_4639_ == 0)
{
v_e_4618_ = v_arg_4638_;
goto _start;
}
else
{
return v___x_4619_;
}
}
case 11:
{
lean_object* v_struct_4641_; 
v_struct_4641_ = lean_ctor_get(v_e_4618_, 2);
v_e_4618_ = v_struct_4641_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4643_; lean_object* v___x_4644_; uint8_t v___x_4645_; 
v_fvarId_4643_ = lean_ctor_get(v_e_4618_, 0);
v___x_4644_ = l_Lean_Expr_fvarId_x21(v___x_4617_);
v___x_4645_ = l_Lean_instBEqFVarId_beq(v_fvarId_4643_, v___x_4644_);
lean_dec(v___x_4644_);
return v___x_4645_;
}
default: 
{
uint8_t v___x_4646_; 
v___x_4646_ = 0;
return v___x_4646_;
}
}
}
v___jp_4620_:
{
uint8_t v___x_4623_; 
v___x_4623_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4617_, v_d_4621_);
if (v___x_4623_ == 0)
{
v_e_4618_ = v_b_4622_;
goto _start;
}
else
{
return v___x_4619_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1___boxed(lean_object* v___x_4647_, lean_object* v_e_4648_){
_start:
{
uint8_t v_res_4649_; lean_object* v_r_4650_; 
v_res_4649_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4647_, v_e_4648_);
lean_dec_ref(v_e_4648_);
lean_dec_ref(v___x_4647_);
v_r_4650_ = lean_box(v_res_4649_);
return v_r_4650_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4652_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__0));
v___x_4653_ = l_Lean_stringToMessageData(v___x_4652_);
return v___x_4653_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4655_; lean_object* v___x_4656_; 
v___x_4655_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__2));
v___x_4656_ = l_Lean_stringToMessageData(v___x_4655_);
return v___x_4656_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_4658_; lean_object* v___x_4659_; 
v___x_4658_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__4));
v___x_4659_ = l_Lean_stringToMessageData(v___x_4658_);
return v___x_4659_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(lean_object* v_a_4660_, lean_object* v_termAlt_4661_, lean_object* v_a_4662_, lean_object* v_b_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_){
_start:
{
lean_object* v_array_4669_; lean_object* v_start_4670_; lean_object* v_stop_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4699_; 
v_array_4669_ = lean_ctor_get(v_a_4662_, 0);
v_start_4670_ = lean_ctor_get(v_a_4662_, 1);
v_stop_4671_ = lean_ctor_get(v_a_4662_, 2);
v_isSharedCheck_4699_ = !lean_is_exclusive(v_a_4662_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4673_ = v_a_4662_;
v_isShared_4674_ = v_isSharedCheck_4699_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_stop_4671_);
lean_inc(v_start_4670_);
lean_inc(v_array_4669_);
lean_dec(v_a_4662_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4699_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
uint8_t v___x_4675_; 
v___x_4675_ = lean_nat_dec_lt(v_start_4670_, v_stop_4671_);
if (v___x_4675_ == 0)
{
lean_object* v___x_4676_; 
lean_del_object(v___x_4673_);
lean_dec(v_stop_4671_);
lean_dec(v_start_4670_);
lean_dec_ref(v_array_4669_);
lean_dec_ref(v_termAlt_4661_);
lean_dec_ref(v_a_4660_);
v___x_4676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4676_, 0, v_b_4663_);
return v___x_4676_;
}
else
{
lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4681_; 
v___x_4677_ = lean_box(0);
v___x_4678_ = lean_unsigned_to_nat(1u);
v___x_4679_ = lean_nat_add(v_start_4670_, v___x_4678_);
lean_inc_ref(v_array_4669_);
if (v_isShared_4674_ == 0)
{
lean_ctor_set(v___x_4673_, 1, v___x_4679_);
v___x_4681_ = v___x_4673_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v_array_4669_);
lean_ctor_set(v_reuseFailAlloc_4698_, 1, v___x_4679_);
lean_ctor_set(v_reuseFailAlloc_4698_, 2, v_stop_4671_);
v___x_4681_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
lean_object* v___x_4682_; uint8_t v___x_4683_; 
v___x_4682_ = lean_array_fget(v_array_4669_, v_start_4670_);
lean_dec(v_start_4670_);
lean_dec_ref(v_array_4669_);
v___x_4683_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4682_, v_a_4660_);
if (v___x_4683_ == 0)
{
lean_dec(v___x_4682_);
v_a_4662_ = v___x_4681_;
v_b_4663_ = v___x_4677_;
goto _start;
}
else
{
lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; 
v___x_4685_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1);
lean_inc_ref(v_a_4660_);
v___x_4686_ = l_Lean_MessageData_ofExpr(v_a_4660_);
v___x_4687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4687_, 0, v___x_4685_);
lean_ctor_set(v___x_4687_, 1, v___x_4686_);
v___x_4688_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3);
v___x_4689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4689_, 0, v___x_4687_);
lean_ctor_set(v___x_4689_, 1, v___x_4688_);
lean_inc_ref(v_termAlt_4661_);
v___x_4690_ = l_Lean_MessageData_ofExpr(v_termAlt_4661_);
v___x_4691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4691_, 0, v___x_4689_);
lean_ctor_set(v___x_4691_, 1, v___x_4690_);
v___x_4692_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5);
v___x_4693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4693_, 0, v___x_4691_);
lean_ctor_set(v___x_4693_, 1, v___x_4692_);
v___x_4694_ = l_Lean_MessageData_ofExpr(v___x_4682_);
v___x_4695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4695_, 0, v___x_4693_);
lean_ctor_set(v___x_4695_, 1, v___x_4694_);
v___x_4696_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_4695_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_);
if (lean_obj_tag(v___x_4696_) == 0)
{
lean_dec_ref_known(v___x_4696_, 1);
v_a_4662_ = v___x_4681_;
v_b_4663_ = v___x_4677_;
goto _start;
}
else
{
lean_dec_ref(v___x_4681_);
lean_dec_ref(v_termAlt_4661_);
lean_dec_ref(v_a_4660_);
return v___x_4696_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___boxed(lean_object* v_a_4700_, lean_object* v_termAlt_4701_, lean_object* v_a_4702_, lean_object* v_b_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_){
_start:
{
lean_object* v_res_4709_; 
v_res_4709_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_4700_, v_termAlt_4701_, v_a_4702_, v_b_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_);
lean_dec(v___y_4707_);
lean_dec_ref(v___y_4706_);
lean_dec(v___y_4705_);
lean_dec_ref(v___y_4704_);
return v_res_4709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(lean_object* v_nExtra_4710_, lean_object* v_v_4711_, uint8_t v___x_4712_, uint8_t v___x_4713_, uint8_t v___x_4714_, lean_object* v_xs_4715_, lean_object* v_termAltBody_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_){
_start:
{
lean_object* v___x_4722_; 
lean_inc(v___y_4720_);
lean_inc_ref(v___y_4719_);
lean_inc(v___y_4718_);
lean_inc_ref(v___y_4717_);
v___x_4722_ = lean_infer_type(v_termAltBody_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
if (lean_obj_tag(v___x_4722_) == 0)
{
lean_object* v_a_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; 
v_a_4723_ = lean_ctor_get(v___x_4722_, 0);
lean_inc_n(v_a_4723_, 2);
lean_dec_ref_known(v___x_4722_, 1);
v___x_4724_ = lean_array_get_size(v_xs_4715_);
v___x_4725_ = lean_nat_sub(v___x_4724_, v_nExtra_4710_);
v___x_4726_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_4725_);
lean_inc_ref(v_xs_4715_);
v___x_4727_ = l_Array_toSubarray___redArg(v_xs_4715_, v___x_4726_, v___x_4725_);
v___x_4728_ = l_Array_toSubarray___redArg(v_xs_4715_, v___x_4725_, v___x_4724_);
v___x_4729_ = lean_box(0);
v___x_4730_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_4723_, v_v_4711_, v___x_4728_, v___x_4729_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
if (lean_obj_tag(v___x_4730_) == 0)
{
lean_object* v___x_4731_; lean_object* v___x_4732_; 
lean_dec_ref_known(v___x_4730_, 1);
v___x_4731_ = l_Subarray_copy___redArg(v___x_4727_);
v___x_4732_ = l_Lean_Meta_mkLambdaFVars(v___x_4731_, v_a_4723_, v___x_4712_, v___x_4713_, v___x_4712_, v___x_4713_, v___x_4714_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
lean_dec_ref(v___x_4731_);
return v___x_4732_;
}
else
{
lean_object* v_a_4733_; lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4740_; 
lean_dec_ref(v___x_4727_);
lean_dec(v_a_4723_);
v_a_4733_ = lean_ctor_get(v___x_4730_, 0);
v_isSharedCheck_4740_ = !lean_is_exclusive(v___x_4730_);
if (v_isSharedCheck_4740_ == 0)
{
v___x_4735_ = v___x_4730_;
v_isShared_4736_ = v_isSharedCheck_4740_;
goto v_resetjp_4734_;
}
else
{
lean_inc(v_a_4733_);
lean_dec(v___x_4730_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4740_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
lean_object* v___x_4738_; 
if (v_isShared_4736_ == 0)
{
v___x_4738_ = v___x_4735_;
goto v_reusejp_4737_;
}
else
{
lean_object* v_reuseFailAlloc_4739_; 
v_reuseFailAlloc_4739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4739_, 0, v_a_4733_);
v___x_4738_ = v_reuseFailAlloc_4739_;
goto v_reusejp_4737_;
}
v_reusejp_4737_:
{
return v___x_4738_;
}
}
}
}
else
{
lean_dec_ref(v_xs_4715_);
lean_dec(v_v_4711_);
return v___x_4722_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed(lean_object* v_nExtra_4741_, lean_object* v_v_4742_, lean_object* v___x_4743_, lean_object* v___x_4744_, lean_object* v___x_4745_, lean_object* v_xs_4746_, lean_object* v_termAltBody_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_, lean_object* v___y_4752_){
_start:
{
uint8_t v___x_32707__boxed_4753_; uint8_t v___x_32708__boxed_4754_; uint8_t v___x_32709__boxed_4755_; lean_object* v_res_4756_; 
v___x_32707__boxed_4753_ = lean_unbox(v___x_4743_);
v___x_32708__boxed_4754_ = lean_unbox(v___x_4744_);
v___x_32709__boxed_4755_ = lean_unbox(v___x_4745_);
v_res_4756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(v_nExtra_4741_, v_v_4742_, v___x_32707__boxed_4753_, v___x_32708__boxed_4754_, v___x_32709__boxed_4755_, v_xs_4746_, v_termAltBody_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
lean_dec(v___y_4751_);
lean_dec_ref(v___y_4750_);
lean_dec(v___y_4749_);
lean_dec_ref(v___y_4748_);
lean_dec(v_nExtra_4741_);
return v_res_4756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(lean_object* v_nExtra_4757_, size_t v_sz_4758_, size_t v_i_4759_, lean_object* v_bs_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_){
_start:
{
uint8_t v___x_4766_; 
v___x_4766_ = lean_usize_dec_lt(v_i_4759_, v_sz_4758_);
if (v___x_4766_ == 0)
{
lean_object* v___x_4767_; 
lean_dec(v_nExtra_4757_);
v___x_4767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4767_, 0, v_bs_4760_);
return v___x_4767_;
}
else
{
uint8_t v___x_4768_; uint8_t v___x_4769_; lean_object* v_v_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___f_4774_; lean_object* v___x_4775_; 
v___x_4768_ = 0;
v___x_4769_ = 1;
v_v_4770_ = lean_array_uget_borrowed(v_bs_4760_, v_i_4759_);
v___x_4771_ = lean_box(v___x_4768_);
v___x_4772_ = lean_box(v___x_4766_);
v___x_4773_ = lean_box(v___x_4769_);
lean_inc_n(v_v_4770_, 2);
lean_inc(v_nExtra_4757_);
v___f_4774_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4774_, 0, v_nExtra_4757_);
lean_closure_set(v___f_4774_, 1, v_v_4770_);
lean_closure_set(v___f_4774_, 2, v___x_4771_);
lean_closure_set(v___f_4774_, 3, v___x_4772_);
lean_closure_set(v___f_4774_, 4, v___x_4773_);
v___x_4775_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_v_4770_, v___f_4774_, v___x_4768_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
if (lean_obj_tag(v___x_4775_) == 0)
{
lean_object* v_a_4776_; lean_object* v___x_4777_; lean_object* v_bs_x27_4778_; size_t v___x_4779_; size_t v___x_4780_; lean_object* v___x_4781_; 
v_a_4776_ = lean_ctor_get(v___x_4775_, 0);
lean_inc(v_a_4776_);
lean_dec_ref_known(v___x_4775_, 1);
v___x_4777_ = lean_unsigned_to_nat(0u);
v_bs_x27_4778_ = lean_array_uset(v_bs_4760_, v_i_4759_, v___x_4777_);
v___x_4779_ = ((size_t)1ULL);
v___x_4780_ = lean_usize_add(v_i_4759_, v___x_4779_);
v___x_4781_ = lean_array_uset(v_bs_x27_4778_, v_i_4759_, v_a_4776_);
v_i_4759_ = v___x_4780_;
v_bs_4760_ = v___x_4781_;
goto _start;
}
else
{
lean_object* v_a_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4790_; 
lean_dec_ref(v_bs_4760_);
lean_dec(v_nExtra_4757_);
v_a_4783_ = lean_ctor_get(v___x_4775_, 0);
v_isSharedCheck_4790_ = !lean_is_exclusive(v___x_4775_);
if (v_isSharedCheck_4790_ == 0)
{
v___x_4785_ = v___x_4775_;
v_isShared_4786_ = v_isSharedCheck_4790_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_a_4783_);
lean_dec(v___x_4775_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4790_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v___x_4788_; 
if (v_isShared_4786_ == 0)
{
v___x_4788_ = v___x_4785_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v_a_4783_);
v___x_4788_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
return v___x_4788_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___boxed(lean_object* v_nExtra_4791_, lean_object* v_sz_4792_, lean_object* v_i_4793_, lean_object* v_bs_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_){
_start:
{
size_t v_sz_boxed_4800_; size_t v_i_boxed_4801_; lean_object* v_res_4802_; 
v_sz_boxed_4800_ = lean_unbox_usize(v_sz_4792_);
lean_dec(v_sz_4792_);
v_i_boxed_4801_ = lean_unbox_usize(v_i_4793_);
lean_dec(v_i_4793_);
v_res_4802_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(v_nExtra_4791_, v_sz_boxed_4800_, v_i_boxed_4801_, v_bs_4794_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_);
lean_dec(v___y_4798_);
lean_dec_ref(v___y_4797_);
lean_dec(v___y_4796_);
lean_dec_ref(v___y_4795_);
return v_res_4802_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0(void){
_start:
{
lean_object* v___x_4803_; lean_object* v___x_4804_; 
v___x_4803_ = lean_box(0);
v___x_4804_ = l_Lean_Expr_sort___override(v___x_4803_);
return v___x_4804_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1(void){
_start:
{
lean_object* v___x_4805_; lean_object* v___x_4806_; 
v___x_4805_ = lean_box(0);
v___x_4806_ = l_Lean_Level_succ___override(v___x_4805_);
return v___x_4806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3(lean_object* v_nExtra_4807_, uint8_t v___x_4808_, uint8_t v___x_4809_, lean_object* v_alts_4810_, lean_object* v_toMatcherInfo_4811_, lean_object* v_matcherName_4812_, lean_object* v_params_4813_, lean_object* v_matcherLevels_4814_, lean_object* v_motiveArgs_4815_, lean_object* v_body_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_){
_start:
{
lean_object* v___x_4822_; 
lean_inc(v_nExtra_4807_);
v___x_4822_ = l_Lean_Meta_arrowDomainsN(v_nExtra_4807_, v_body_4816_, v___y_4817_, v___y_4818_, v___y_4819_, v___y_4820_);
if (lean_obj_tag(v___x_4822_) == 0)
{
lean_object* v_a_4823_; lean_object* v___x_4824_; uint8_t v___x_4825_; lean_object* v___x_4826_; 
v_a_4823_ = lean_ctor_get(v___x_4822_, 0);
lean_inc(v_a_4823_);
lean_dec_ref_known(v___x_4822_, 1);
v___x_4824_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0, &l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0);
v___x_4825_ = 1;
v___x_4826_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_4815_, v___x_4824_, v___x_4808_, v___x_4809_, v___x_4808_, v___x_4809_, v___x_4825_, v___y_4817_, v___y_4818_, v___y_4819_, v___y_4820_);
if (lean_obj_tag(v___x_4826_) == 0)
{
lean_object* v_a_4827_; size_t v_sz_4828_; size_t v___x_4829_; lean_object* v___x_4830_; 
v_a_4827_ = lean_ctor_get(v___x_4826_, 0);
lean_inc(v_a_4827_);
lean_dec_ref_known(v___x_4826_, 1);
v_sz_4828_ = lean_array_size(v_alts_4810_);
v___x_4829_ = ((size_t)0ULL);
v___x_4830_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(v_nExtra_4807_, v_sz_4828_, v___x_4829_, v_alts_4810_, v___y_4817_, v___y_4818_, v___y_4819_, v___y_4820_);
if (lean_obj_tag(v___x_4830_) == 0)
{
lean_object* v_a_4831_; lean_object* v_matcherLevels_4833_; lean_object* v___y_4834_; lean_object* v___y_4835_; lean_object* v_uElimPos_x3f_4840_; 
v_a_4831_ = lean_ctor_get(v___x_4830_, 0);
lean_inc(v_a_4831_);
lean_dec_ref_known(v___x_4830_, 1);
v_uElimPos_x3f_4840_ = lean_ctor_get(v_toMatcherInfo_4811_, 3);
if (lean_obj_tag(v_uElimPos_x3f_4840_) == 0)
{
v_matcherLevels_4833_ = v_matcherLevels_4814_;
v___y_4834_ = v___y_4819_;
v___y_4835_ = v___y_4820_;
goto v___jp_4832_;
}
else
{
lean_object* v_val_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; 
v_val_4841_ = lean_ctor_get(v_uElimPos_x3f_4840_, 0);
v___x_4842_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1, &l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1);
v___x_4843_ = lean_array_set(v_matcherLevels_4814_, v_val_4841_, v___x_4842_);
v_matcherLevels_4833_ = v___x_4843_;
v___y_4834_ = v___y_4819_;
v___y_4835_ = v___y_4820_;
goto v___jp_4832_;
}
v___jp_4832_:
{
lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; 
v___x_4836_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_4837_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4837_, 0, v_toMatcherInfo_4811_);
lean_ctor_set(v___x_4837_, 1, v_matcherName_4812_);
lean_ctor_set(v___x_4837_, 2, v_matcherLevels_4833_);
lean_ctor_set(v___x_4837_, 3, v_params_4813_);
lean_ctor_set(v___x_4837_, 4, v_a_4827_);
lean_ctor_set(v___x_4837_, 5, v_motiveArgs_4815_);
lean_ctor_set(v___x_4837_, 6, v_a_4831_);
lean_ctor_set(v___x_4837_, 7, v___x_4836_);
v___x_4838_ = l_Lean_Meta_MatcherApp_toExpr(v___x_4837_);
v___x_4839_ = l_Lean_mkArrowN(v_a_4823_, v___x_4838_, v___y_4834_, v___y_4835_);
lean_dec(v_a_4823_);
return v___x_4839_;
}
}
else
{
lean_object* v_a_4844_; lean_object* v___x_4846_; uint8_t v_isShared_4847_; uint8_t v_isSharedCheck_4851_; 
lean_dec(v_a_4827_);
lean_dec(v_a_4823_);
lean_dec_ref(v_motiveArgs_4815_);
lean_dec_ref(v_matcherLevels_4814_);
lean_dec_ref(v_params_4813_);
lean_dec(v_matcherName_4812_);
lean_dec_ref(v_toMatcherInfo_4811_);
v_a_4844_ = lean_ctor_get(v___x_4830_, 0);
v_isSharedCheck_4851_ = !lean_is_exclusive(v___x_4830_);
if (v_isSharedCheck_4851_ == 0)
{
v___x_4846_ = v___x_4830_;
v_isShared_4847_ = v_isSharedCheck_4851_;
goto v_resetjp_4845_;
}
else
{
lean_inc(v_a_4844_);
lean_dec(v___x_4830_);
v___x_4846_ = lean_box(0);
v_isShared_4847_ = v_isSharedCheck_4851_;
goto v_resetjp_4845_;
}
v_resetjp_4845_:
{
lean_object* v___x_4849_; 
if (v_isShared_4847_ == 0)
{
v___x_4849_ = v___x_4846_;
goto v_reusejp_4848_;
}
else
{
lean_object* v_reuseFailAlloc_4850_; 
v_reuseFailAlloc_4850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4850_, 0, v_a_4844_);
v___x_4849_ = v_reuseFailAlloc_4850_;
goto v_reusejp_4848_;
}
v_reusejp_4848_:
{
return v___x_4849_;
}
}
}
}
else
{
lean_dec(v_a_4823_);
lean_dec_ref(v_motiveArgs_4815_);
lean_dec_ref(v_matcherLevels_4814_);
lean_dec_ref(v_params_4813_);
lean_dec(v_matcherName_4812_);
lean_dec_ref(v_toMatcherInfo_4811_);
lean_dec_ref(v_alts_4810_);
lean_dec(v_nExtra_4807_);
return v___x_4826_;
}
}
else
{
lean_object* v_a_4852_; lean_object* v___x_4854_; uint8_t v_isShared_4855_; uint8_t v_isSharedCheck_4859_; 
lean_dec_ref(v_motiveArgs_4815_);
lean_dec_ref(v_matcherLevels_4814_);
lean_dec_ref(v_params_4813_);
lean_dec(v_matcherName_4812_);
lean_dec_ref(v_toMatcherInfo_4811_);
lean_dec_ref(v_alts_4810_);
lean_dec(v_nExtra_4807_);
v_a_4852_ = lean_ctor_get(v___x_4822_, 0);
v_isSharedCheck_4859_ = !lean_is_exclusive(v___x_4822_);
if (v_isSharedCheck_4859_ == 0)
{
v___x_4854_ = v___x_4822_;
v_isShared_4855_ = v_isSharedCheck_4859_;
goto v_resetjp_4853_;
}
else
{
lean_inc(v_a_4852_);
lean_dec(v___x_4822_);
v___x_4854_ = lean_box(0);
v_isShared_4855_ = v_isSharedCheck_4859_;
goto v_resetjp_4853_;
}
v_resetjp_4853_:
{
lean_object* v___x_4857_; 
if (v_isShared_4855_ == 0)
{
v___x_4857_ = v___x_4854_;
goto v_reusejp_4856_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_a_4852_);
v___x_4857_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4856_;
}
v_reusejp_4856_:
{
return v___x_4857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed(lean_object* v_nExtra_4860_, lean_object* v___x_4861_, lean_object* v___x_4862_, lean_object* v_alts_4863_, lean_object* v_toMatcherInfo_4864_, lean_object* v_matcherName_4865_, lean_object* v_params_4866_, lean_object* v_matcherLevels_4867_, lean_object* v_motiveArgs_4868_, lean_object* v_body_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_){
_start:
{
uint8_t v___x_32842__boxed_4875_; uint8_t v___x_32843__boxed_4876_; lean_object* v_res_4877_; 
v___x_32842__boxed_4875_ = lean_unbox(v___x_4861_);
v___x_32843__boxed_4876_ = lean_unbox(v___x_4862_);
v_res_4877_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__3(v_nExtra_4860_, v___x_32842__boxed_4875_, v___x_32843__boxed_4876_, v_alts_4863_, v_toMatcherInfo_4864_, v_matcherName_4865_, v_params_4866_, v_matcherLevels_4867_, v_motiveArgs_4868_, v_body_4869_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_);
lean_dec(v___y_4873_);
lean_dec_ref(v___y_4872_);
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
return v_res_4877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(lean_object* v_k_4878_, lean_object* v_ys_4879_, lean_object* v_args_4880_, lean_object* v___mask_4881_, lean_object* v___bodyType_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_){
_start:
{
lean_object* v___x_4888_; 
lean_inc(v___y_4886_);
lean_inc_ref(v___y_4885_);
lean_inc(v___y_4884_);
lean_inc_ref(v___y_4883_);
v___x_4888_ = lean_apply_7(v_k_4878_, v_ys_4879_, v_args_4880_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_, lean_box(0));
return v___x_4888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed(lean_object* v_k_4889_, lean_object* v_ys_4890_, lean_object* v_args_4891_, lean_object* v___mask_4892_, lean_object* v___bodyType_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_){
_start:
{
lean_object* v_res_4899_; 
v_res_4899_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(v_k_4889_, v_ys_4890_, v_args_4891_, v___mask_4892_, v___bodyType_4893_, v___y_4894_, v___y_4895_, v___y_4896_, v___y_4897_);
lean_dec(v___y_4897_);
lean_dec_ref(v___y_4896_);
lean_dec(v___y_4895_);
lean_dec_ref(v___y_4894_);
lean_dec_ref(v___bodyType_4893_);
lean_dec_ref(v___mask_4892_);
return v_res_4899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(lean_object* v_origAltType_4900_, lean_object* v_altInfo_4901_, lean_object* v_k_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_){
_start:
{
lean_object* v___f_4908_; lean_object* v___x_4909_; 
v___f_4908_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_4908_, 0, v_k_4902_);
v___x_4909_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_origAltType_4900_, v_altInfo_4901_, v___f_4908_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_object* v_a_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4917_; 
v_a_4910_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4917_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4917_ == 0)
{
v___x_4912_ = v___x_4909_;
v_isShared_4913_ = v_isSharedCheck_4917_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_a_4910_);
lean_dec(v___x_4909_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4917_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v___x_4915_; 
if (v_isShared_4913_ == 0)
{
v___x_4915_ = v___x_4912_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v_a_4910_);
v___x_4915_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
return v___x_4915_;
}
}
}
else
{
lean_object* v_a_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4925_; 
v_a_4918_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4925_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4920_ = v___x_4909_;
v_isShared_4921_ = v_isSharedCheck_4925_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_a_4918_);
lean_dec(v___x_4909_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4925_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v___x_4923_; 
if (v_isShared_4921_ == 0)
{
v___x_4923_ = v___x_4920_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v_a_4918_);
v___x_4923_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
return v___x_4923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___boxed(lean_object* v_origAltType_4926_, lean_object* v_altInfo_4927_, lean_object* v_k_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_){
_start:
{
lean_object* v_res_4934_; 
v_res_4934_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v_origAltType_4926_, v_altInfo_4927_, v_k_4928_, v___y_4929_, v___y_4930_, v___y_4931_, v___y_4932_);
lean_dec(v___y_4932_);
lean_dec_ref(v___y_4931_);
lean_dec(v___y_4930_);
lean_dec_ref(v___y_4929_);
return v_res_4934_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(lean_object* v___x_4935_, lean_object* v___x_4936_, lean_object* v___f_4937_, lean_object* v_fst_4938_, lean_object* v___x_4939_, lean_object* v___x_4940_, lean_object* v___x_4941_, lean_object* v___x_4942_, lean_object* v___x_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_){
_start:
{
lean_object* v___x_4949_; 
v___x_4949_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v___x_4935_, v___x_4936_, v___f_4937_, v___y_4944_, v___y_4945_, v___y_4946_, v___y_4947_);
if (lean_obj_tag(v___x_4949_) == 0)
{
lean_object* v_a_4950_; lean_object* v___x_4952_; uint8_t v_isShared_4953_; uint8_t v_isSharedCheck_4964_; 
v_a_4950_ = lean_ctor_get(v___x_4949_, 0);
v_isSharedCheck_4964_ = !lean_is_exclusive(v___x_4949_);
if (v_isSharedCheck_4964_ == 0)
{
v___x_4952_ = v___x_4949_;
v_isShared_4953_ = v_isSharedCheck_4964_;
goto v_resetjp_4951_;
}
else
{
lean_inc(v_a_4950_);
lean_dec(v___x_4949_);
v___x_4952_ = lean_box(0);
v_isShared_4953_ = v_isSharedCheck_4964_;
goto v_resetjp_4951_;
}
v_resetjp_4951_:
{
lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4962_; 
v___x_4954_ = lean_array_push(v_fst_4938_, v_a_4950_);
v___x_4955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4955_, 0, v___x_4939_);
lean_ctor_set(v___x_4955_, 1, v___x_4940_);
v___x_4956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4956_, 0, v___x_4941_);
lean_ctor_set(v___x_4956_, 1, v___x_4955_);
v___x_4957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4957_, 0, v___x_4942_);
lean_ctor_set(v___x_4957_, 1, v___x_4956_);
v___x_4958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4958_, 0, v___x_4943_);
lean_ctor_set(v___x_4958_, 1, v___x_4957_);
v___x_4959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4959_, 0, v___x_4954_);
lean_ctor_set(v___x_4959_, 1, v___x_4958_);
v___x_4960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4960_, 0, v___x_4959_);
if (v_isShared_4953_ == 0)
{
lean_ctor_set(v___x_4952_, 0, v___x_4960_);
v___x_4962_ = v___x_4952_;
goto v_reusejp_4961_;
}
else
{
lean_object* v_reuseFailAlloc_4963_; 
v_reuseFailAlloc_4963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4963_, 0, v___x_4960_);
v___x_4962_ = v_reuseFailAlloc_4963_;
goto v_reusejp_4961_;
}
v_reusejp_4961_:
{
return v___x_4962_;
}
}
}
else
{
lean_object* v_a_4965_; lean_object* v___x_4967_; uint8_t v_isShared_4968_; uint8_t v_isSharedCheck_4972_; 
lean_dec_ref(v___x_4943_);
lean_dec_ref(v___x_4942_);
lean_dec_ref(v___x_4941_);
lean_dec_ref(v___x_4940_);
lean_dec_ref(v___x_4939_);
lean_dec(v_fst_4938_);
v_a_4965_ = lean_ctor_get(v___x_4949_, 0);
v_isSharedCheck_4972_ = !lean_is_exclusive(v___x_4949_);
if (v_isSharedCheck_4972_ == 0)
{
v___x_4967_ = v___x_4949_;
v_isShared_4968_ = v_isSharedCheck_4972_;
goto v_resetjp_4966_;
}
else
{
lean_inc(v_a_4965_);
lean_dec(v___x_4949_);
v___x_4967_ = lean_box(0);
v_isShared_4968_ = v_isSharedCheck_4972_;
goto v_resetjp_4966_;
}
v_resetjp_4966_:
{
lean_object* v___x_4970_; 
if (v_isShared_4968_ == 0)
{
v___x_4970_ = v___x_4967_;
goto v_reusejp_4969_;
}
else
{
lean_object* v_reuseFailAlloc_4971_; 
v_reuseFailAlloc_4971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4971_, 0, v_a_4965_);
v___x_4970_ = v_reuseFailAlloc_4971_;
goto v_reusejp_4969_;
}
v_reusejp_4969_:
{
return v___x_4970_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed(lean_object* v___x_4973_, lean_object* v___x_4974_, lean_object* v___f_4975_, lean_object* v_fst_4976_, lean_object* v___x_4977_, lean_object* v___x_4978_, lean_object* v___x_4979_, lean_object* v___x_4980_, lean_object* v___x_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_){
_start:
{
lean_object* v_res_4987_; 
v_res_4987_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(v___x_4973_, v___x_4974_, v___f_4975_, v_fst_4976_, v___x_4977_, v___x_4978_, v___x_4979_, v___x_4980_, v___x_4981_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_);
lean_dec(v___y_4985_);
lean_dec_ref(v___y_4984_);
lean_dec(v___y_4983_);
lean_dec_ref(v___y_4982_);
return v_res_4987_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(lean_object* v_args_4988_, lean_object* v_ys_4989_, lean_object* v_ys2_4990_, lean_object* v_ys3_4991_, lean_object* v_onAlt_4992_, lean_object* v_a_4993_, uint8_t v___x_4994_, uint8_t v_useSplitter_4995_, lean_object* v___x_4996_, lean_object* v_ys4_4997_, lean_object* v_altType_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_){
_start:
{
lean_object* v___y_5005_; lean_object* v___x_5015_; lean_object* v___x_5016_; 
lean_inc_ref(v_args_4988_);
v___x_5015_ = l_Array_append___redArg(v_args_4988_, v_ys3_4991_);
v___x_5016_ = l_Lean_Meta_instantiateLambda(v___x_4996_, v___x_5015_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
lean_dec_ref(v___x_5015_);
if (lean_obj_tag(v___x_5016_) == 0)
{
v___y_5005_ = v___x_5016_;
goto v___jp_5004_;
}
else
{
lean_object* v_a_5017_; uint8_t v___y_5019_; uint8_t v___x_5022_; 
v_a_5017_ = lean_ctor_get(v___x_5016_, 0);
lean_inc(v_a_5017_);
v___x_5022_ = l_Lean_Exception_isInterrupt(v_a_5017_);
if (v___x_5022_ == 0)
{
uint8_t v___x_5023_; 
v___x_5023_ = l_Lean_Exception_isRuntime(v_a_5017_);
v___y_5019_ = v___x_5023_;
goto v___jp_5018_;
}
else
{
lean_dec(v_a_5017_);
v___y_5019_ = v___x_5022_;
goto v___jp_5018_;
}
v___jp_5018_:
{
if (v___y_5019_ == 0)
{
lean_object* v___x_5020_; lean_object* v___x_5021_; 
lean_dec_ref_known(v___x_5016_, 1);
v___x_5020_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2);
v___x_5021_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_5020_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
v___y_5005_ = v___x_5021_;
goto v___jp_5004_;
}
else
{
v___y_5005_ = v___x_5016_;
goto v___jp_5004_;
}
}
}
v___jp_5004_:
{
if (lean_obj_tag(v___y_5005_) == 0)
{
lean_object* v_a_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; 
v_a_5006_ = lean_ctor_get(v___y_5005_, 0);
lean_inc(v_a_5006_);
lean_dec_ref_known(v___y_5005_, 1);
lean_inc_ref(v_ys4_4997_);
lean_inc_ref(v_ys3_4991_);
lean_inc_ref(v_ys2_4990_);
lean_inc_ref(v_ys_4989_);
v___x_5007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5007_, 0, v_args_4988_);
lean_ctor_set(v___x_5007_, 1, v_ys_4989_);
lean_ctor_set(v___x_5007_, 2, v_ys2_4990_);
lean_ctor_set(v___x_5007_, 3, v_ys3_4991_);
lean_ctor_set(v___x_5007_, 4, v_ys4_4997_);
lean_inc(v___y_5002_);
lean_inc_ref(v___y_5001_);
lean_inc(v___y_5000_);
lean_inc_ref(v___y_4999_);
v___x_5008_ = lean_apply_9(v_onAlt_4992_, v_a_4993_, v_altType_4998_, v___x_5007_, v_a_5006_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, lean_box(0));
if (lean_obj_tag(v___x_5008_) == 0)
{
lean_object* v_a_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; uint8_t v___x_5013_; lean_object* v___x_5014_; 
v_a_5009_ = lean_ctor_get(v___x_5008_, 0);
lean_inc(v_a_5009_);
lean_dec_ref_known(v___x_5008_, 1);
v___x_5010_ = l_Array_append___redArg(v_ys_4989_, v_ys2_4990_);
lean_dec_ref(v_ys2_4990_);
v___x_5011_ = l_Array_append___redArg(v___x_5010_, v_ys3_4991_);
lean_dec_ref(v_ys3_4991_);
v___x_5012_ = l_Array_append___redArg(v___x_5011_, v_ys4_4997_);
lean_dec_ref(v_ys4_4997_);
v___x_5013_ = 1;
v___x_5014_ = l_Lean_Meta_mkLambdaFVars(v___x_5012_, v_a_5009_, v___x_4994_, v_useSplitter_4995_, v___x_4994_, v_useSplitter_4995_, v___x_5013_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
lean_dec_ref(v___x_5012_);
return v___x_5014_;
}
else
{
lean_dec_ref(v_ys4_4997_);
lean_dec_ref(v_ys3_4991_);
lean_dec_ref(v_ys2_4990_);
lean_dec_ref(v_ys_4989_);
return v___x_5008_;
}
}
else
{
lean_dec_ref(v_altType_4998_);
lean_dec_ref(v_ys4_4997_);
lean_dec(v_a_4993_);
lean_dec_ref(v_onAlt_4992_);
lean_dec_ref(v_ys3_4991_);
lean_dec_ref(v_ys2_4990_);
lean_dec_ref(v_ys_4989_);
lean_dec_ref(v_args_4988_);
return v___y_5005_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed(lean_object* v_args_5024_, lean_object* v_ys_5025_, lean_object* v_ys2_5026_, lean_object* v_ys3_5027_, lean_object* v_onAlt_5028_, lean_object* v_a_5029_, lean_object* v___x_5030_, lean_object* v_useSplitter_5031_, lean_object* v___x_5032_, lean_object* v_ys4_5033_, lean_object* v_altType_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_){
_start:
{
uint8_t v___x_33096__boxed_5040_; uint8_t v_useSplitter_boxed_5041_; lean_object* v_res_5042_; 
v___x_33096__boxed_5040_ = lean_unbox(v___x_5030_);
v_useSplitter_boxed_5041_ = lean_unbox(v_useSplitter_5031_);
v_res_5042_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(v_args_5024_, v_ys_5025_, v_ys2_5026_, v_ys3_5027_, v_onAlt_5028_, v_a_5029_, v___x_33096__boxed_5040_, v_useSplitter_boxed_5041_, v___x_5032_, v_ys4_5033_, v_altType_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_);
lean_dec(v___y_5038_);
lean_dec_ref(v___y_5037_);
lean_dec(v___y_5036_);
lean_dec_ref(v___y_5035_);
return v_res_5042_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(lean_object* v_args_5043_, lean_object* v_ys_5044_, lean_object* v_ys2_5045_, lean_object* v_onAlt_5046_, lean_object* v_a_5047_, uint8_t v___x_5048_, uint8_t v_useSplitter_5049_, lean_object* v___x_5050_, lean_object* v_extraEqualities_5051_, lean_object* v_ys3_5052_, lean_object* v_altType_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_){
_start:
{
lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___f_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; 
v___x_5059_ = lean_box(v___x_5048_);
v___x_5060_ = lean_box(v_useSplitter_5049_);
v___f_5061_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed), 16, 9);
lean_closure_set(v___f_5061_, 0, v_args_5043_);
lean_closure_set(v___f_5061_, 1, v_ys_5044_);
lean_closure_set(v___f_5061_, 2, v_ys2_5045_);
lean_closure_set(v___f_5061_, 3, v_ys3_5052_);
lean_closure_set(v___f_5061_, 4, v_onAlt_5046_);
lean_closure_set(v___f_5061_, 5, v_a_5047_);
lean_closure_set(v___f_5061_, 6, v___x_5059_);
lean_closure_set(v___f_5061_, 7, v___x_5060_);
lean_closure_set(v___f_5061_, 8, v___x_5050_);
v___x_5062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5062_, 0, v_extraEqualities_5051_);
v___x_5063_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_5053_, v___x_5062_, v___f_5061_, v___x_5048_, v___x_5048_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_);
return v___x_5063_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed(lean_object* v_args_5064_, lean_object* v_ys_5065_, lean_object* v_ys2_5066_, lean_object* v_onAlt_5067_, lean_object* v_a_5068_, lean_object* v___x_5069_, lean_object* v_useSplitter_5070_, lean_object* v___x_5071_, lean_object* v_extraEqualities_5072_, lean_object* v_ys3_5073_, lean_object* v_altType_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_){
_start:
{
uint8_t v___x_33161__boxed_5080_; uint8_t v_useSplitter_boxed_5081_; lean_object* v_res_5082_; 
v___x_33161__boxed_5080_ = lean_unbox(v___x_5069_);
v_useSplitter_boxed_5081_ = lean_unbox(v_useSplitter_5070_);
v_res_5082_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(v_args_5064_, v_ys_5065_, v_ys2_5066_, v_onAlt_5067_, v_a_5068_, v___x_33161__boxed_5080_, v_useSplitter_boxed_5081_, v___x_5071_, v_extraEqualities_5072_, v_ys3_5073_, v_altType_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_);
lean_dec(v___y_5078_);
lean_dec_ref(v___y_5077_);
lean_dec(v___y_5076_);
lean_dec_ref(v___y_5075_);
return v_res_5082_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(lean_object* v_args_5083_, lean_object* v_ys_5084_, lean_object* v_onAlt_5085_, lean_object* v_a_5086_, uint8_t v___x_5087_, uint8_t v_useSplitter_5088_, lean_object* v___x_5089_, lean_object* v_extraEqualities_5090_, lean_object* v_numDiscrEqs_5091_, lean_object* v_ys2_5092_, lean_object* v_altType_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_){
_start:
{
lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___f_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; 
v___x_5099_ = lean_box(v___x_5087_);
v___x_5100_ = lean_box(v_useSplitter_5088_);
v___f_5101_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_5101_, 0, v_args_5083_);
lean_closure_set(v___f_5101_, 1, v_ys_5084_);
lean_closure_set(v___f_5101_, 2, v_ys2_5092_);
lean_closure_set(v___f_5101_, 3, v_onAlt_5085_);
lean_closure_set(v___f_5101_, 4, v_a_5086_);
lean_closure_set(v___f_5101_, 5, v___x_5099_);
lean_closure_set(v___f_5101_, 6, v___x_5100_);
lean_closure_set(v___f_5101_, 7, v___x_5089_);
lean_closure_set(v___f_5101_, 8, v_extraEqualities_5090_);
v___x_5102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5102_, 0, v_numDiscrEqs_5091_);
v___x_5103_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_5093_, v___x_5102_, v___f_5101_, v___x_5087_, v___x_5087_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_);
return v___x_5103_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed(lean_object* v_args_5104_, lean_object* v_ys_5105_, lean_object* v_onAlt_5106_, lean_object* v_a_5107_, lean_object* v___x_5108_, lean_object* v_useSplitter_5109_, lean_object* v___x_5110_, lean_object* v_extraEqualities_5111_, lean_object* v_numDiscrEqs_5112_, lean_object* v_ys2_5113_, lean_object* v_altType_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_){
_start:
{
uint8_t v___x_33192__boxed_5120_; uint8_t v_useSplitter_boxed_5121_; lean_object* v_res_5122_; 
v___x_33192__boxed_5120_ = lean_unbox(v___x_5108_);
v_useSplitter_boxed_5121_ = lean_unbox(v_useSplitter_5109_);
v_res_5122_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(v_args_5104_, v_ys_5105_, v_onAlt_5106_, v_a_5107_, v___x_33192__boxed_5120_, v_useSplitter_boxed_5121_, v___x_5110_, v_extraEqualities_5111_, v_numDiscrEqs_5112_, v_ys2_5113_, v_altType_5114_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_);
lean_dec(v___y_5118_);
lean_dec_ref(v___y_5117_);
lean_dec(v___y_5116_);
lean_dec_ref(v___y_5115_);
return v_res_5122_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0(void){
_start:
{
lean_object* v___x_5123_; 
v___x_5123_ = l_instMonadEIO(lean_box(0));
return v___x_5123_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(lean_object* v_msg_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_){
_start:
{
lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v_toApplicative_5136_; lean_object* v___x_5138_; uint8_t v_isShared_5139_; uint8_t v_isSharedCheck_5197_; 
v___x_5134_ = lean_obj_once(&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0, &l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0_once, _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0);
v___x_5135_ = l_StateRefT_x27_instMonad___redArg(v___x_5134_);
v_toApplicative_5136_ = lean_ctor_get(v___x_5135_, 0);
v_isSharedCheck_5197_ = !lean_is_exclusive(v___x_5135_);
if (v_isSharedCheck_5197_ == 0)
{
lean_object* v_unused_5198_; 
v_unused_5198_ = lean_ctor_get(v___x_5135_, 1);
lean_dec(v_unused_5198_);
v___x_5138_ = v___x_5135_;
v_isShared_5139_ = v_isSharedCheck_5197_;
goto v_resetjp_5137_;
}
else
{
lean_inc(v_toApplicative_5136_);
lean_dec(v___x_5135_);
v___x_5138_ = lean_box(0);
v_isShared_5139_ = v_isSharedCheck_5197_;
goto v_resetjp_5137_;
}
v_resetjp_5137_:
{
lean_object* v_toFunctor_5140_; lean_object* v_toSeq_5141_; lean_object* v_toSeqLeft_5142_; lean_object* v_toSeqRight_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5195_; 
v_toFunctor_5140_ = lean_ctor_get(v_toApplicative_5136_, 0);
v_toSeq_5141_ = lean_ctor_get(v_toApplicative_5136_, 2);
v_toSeqLeft_5142_ = lean_ctor_get(v_toApplicative_5136_, 3);
v_toSeqRight_5143_ = lean_ctor_get(v_toApplicative_5136_, 4);
v_isSharedCheck_5195_ = !lean_is_exclusive(v_toApplicative_5136_);
if (v_isSharedCheck_5195_ == 0)
{
lean_object* v_unused_5196_; 
v_unused_5196_ = lean_ctor_get(v_toApplicative_5136_, 1);
lean_dec(v_unused_5196_);
v___x_5145_ = v_toApplicative_5136_;
v_isShared_5146_ = v_isSharedCheck_5195_;
goto v_resetjp_5144_;
}
else
{
lean_inc(v_toSeqRight_5143_);
lean_inc(v_toSeqLeft_5142_);
lean_inc(v_toSeq_5141_);
lean_inc(v_toFunctor_5140_);
lean_dec(v_toApplicative_5136_);
v___x_5145_ = lean_box(0);
v_isShared_5146_ = v_isSharedCheck_5195_;
goto v_resetjp_5144_;
}
v_resetjp_5144_:
{
lean_object* v___f_5147_; lean_object* v___f_5148_; lean_object* v___f_5149_; lean_object* v___f_5150_; lean_object* v___x_5151_; lean_object* v___f_5152_; lean_object* v___f_5153_; lean_object* v___f_5154_; lean_object* v___x_5156_; 
v___f_5147_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__1));
v___f_5148_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__2));
lean_inc_ref(v_toFunctor_5140_);
v___f_5149_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5149_, 0, v_toFunctor_5140_);
v___f_5150_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5150_, 0, v_toFunctor_5140_);
v___x_5151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5151_, 0, v___f_5149_);
lean_ctor_set(v___x_5151_, 1, v___f_5150_);
v___f_5152_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5152_, 0, v_toSeqRight_5143_);
v___f_5153_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5153_, 0, v_toSeqLeft_5142_);
v___f_5154_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5154_, 0, v_toSeq_5141_);
if (v_isShared_5146_ == 0)
{
lean_ctor_set(v___x_5145_, 4, v___f_5152_);
lean_ctor_set(v___x_5145_, 3, v___f_5153_);
lean_ctor_set(v___x_5145_, 2, v___f_5154_);
lean_ctor_set(v___x_5145_, 1, v___f_5147_);
lean_ctor_set(v___x_5145_, 0, v___x_5151_);
v___x_5156_ = v___x_5145_;
goto v_reusejp_5155_;
}
else
{
lean_object* v_reuseFailAlloc_5194_; 
v_reuseFailAlloc_5194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5194_, 0, v___x_5151_);
lean_ctor_set(v_reuseFailAlloc_5194_, 1, v___f_5147_);
lean_ctor_set(v_reuseFailAlloc_5194_, 2, v___f_5154_);
lean_ctor_set(v_reuseFailAlloc_5194_, 3, v___f_5153_);
lean_ctor_set(v_reuseFailAlloc_5194_, 4, v___f_5152_);
v___x_5156_ = v_reuseFailAlloc_5194_;
goto v_reusejp_5155_;
}
v_reusejp_5155_:
{
lean_object* v___x_5158_; 
if (v_isShared_5139_ == 0)
{
lean_ctor_set(v___x_5138_, 1, v___f_5148_);
lean_ctor_set(v___x_5138_, 0, v___x_5156_);
v___x_5158_ = v___x_5138_;
goto v_reusejp_5157_;
}
else
{
lean_object* v_reuseFailAlloc_5193_; 
v_reuseFailAlloc_5193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5193_, 0, v___x_5156_);
lean_ctor_set(v_reuseFailAlloc_5193_, 1, v___f_5148_);
v___x_5158_ = v_reuseFailAlloc_5193_;
goto v_reusejp_5157_;
}
v_reusejp_5157_:
{
lean_object* v___x_5159_; lean_object* v_toApplicative_5160_; lean_object* v___x_5162_; uint8_t v_isShared_5163_; uint8_t v_isSharedCheck_5191_; 
v___x_5159_ = l_StateRefT_x27_instMonad___redArg(v___x_5158_);
v_toApplicative_5160_ = lean_ctor_get(v___x_5159_, 0);
v_isSharedCheck_5191_ = !lean_is_exclusive(v___x_5159_);
if (v_isSharedCheck_5191_ == 0)
{
lean_object* v_unused_5192_; 
v_unused_5192_ = lean_ctor_get(v___x_5159_, 1);
lean_dec(v_unused_5192_);
v___x_5162_ = v___x_5159_;
v_isShared_5163_ = v_isSharedCheck_5191_;
goto v_resetjp_5161_;
}
else
{
lean_inc(v_toApplicative_5160_);
lean_dec(v___x_5159_);
v___x_5162_ = lean_box(0);
v_isShared_5163_ = v_isSharedCheck_5191_;
goto v_resetjp_5161_;
}
v_resetjp_5161_:
{
lean_object* v_toFunctor_5164_; lean_object* v_toSeq_5165_; lean_object* v_toSeqLeft_5166_; lean_object* v_toSeqRight_5167_; lean_object* v___x_5169_; uint8_t v_isShared_5170_; uint8_t v_isSharedCheck_5189_; 
v_toFunctor_5164_ = lean_ctor_get(v_toApplicative_5160_, 0);
v_toSeq_5165_ = lean_ctor_get(v_toApplicative_5160_, 2);
v_toSeqLeft_5166_ = lean_ctor_get(v_toApplicative_5160_, 3);
v_toSeqRight_5167_ = lean_ctor_get(v_toApplicative_5160_, 4);
v_isSharedCheck_5189_ = !lean_is_exclusive(v_toApplicative_5160_);
if (v_isSharedCheck_5189_ == 0)
{
lean_object* v_unused_5190_; 
v_unused_5190_ = lean_ctor_get(v_toApplicative_5160_, 1);
lean_dec(v_unused_5190_);
v___x_5169_ = v_toApplicative_5160_;
v_isShared_5170_ = v_isSharedCheck_5189_;
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
v_isShared_5170_ = v_isSharedCheck_5189_;
goto v_resetjp_5168_;
}
v_resetjp_5168_:
{
lean_object* v___f_5171_; lean_object* v___f_5172_; lean_object* v___f_5173_; lean_object* v___f_5174_; lean_object* v___x_5175_; lean_object* v___f_5176_; lean_object* v___f_5177_; lean_object* v___f_5178_; lean_object* v___x_5180_; 
v___f_5171_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__3));
v___f_5172_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__4));
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
lean_object* v_reuseFailAlloc_5188_; 
v_reuseFailAlloc_5188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5188_, 0, v___x_5175_);
lean_ctor_set(v_reuseFailAlloc_5188_, 1, v___f_5171_);
lean_ctor_set(v_reuseFailAlloc_5188_, 2, v___f_5178_);
lean_ctor_set(v_reuseFailAlloc_5188_, 3, v___f_5177_);
lean_ctor_set(v_reuseFailAlloc_5188_, 4, v___f_5176_);
v___x_5180_ = v_reuseFailAlloc_5188_;
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
lean_object* v_reuseFailAlloc_5187_; 
v_reuseFailAlloc_5187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5187_, 0, v___x_5180_);
lean_ctor_set(v_reuseFailAlloc_5187_, 1, v___f_5172_);
v___x_5182_ = v_reuseFailAlloc_5187_;
goto v_reusejp_5181_;
}
v_reusejp_5181_:
{
lean_object* v___x_5183_; lean_object* v___x_5184_; lean_object* v___x_27312__overap_5185_; lean_object* v___x_5186_; 
v___x_5183_ = l_Lean_instInhabitedExpr;
v___x_5184_ = l_instInhabitedOfMonad___redArg(v___x_5182_, v___x_5183_);
v___x_27312__overap_5185_ = lean_panic_fn_borrowed(v___x_5184_, v_msg_5128_);
lean_dec(v___x_5184_);
lean_inc(v___y_5132_);
lean_inc_ref(v___y_5131_);
lean_inc(v___y_5130_);
lean_inc_ref(v___y_5129_);
v___x_5186_ = lean_apply_5(v___x_27312__overap_5185_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_, lean_box(0));
return v___x_5186_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed(lean_object* v_msg_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_){
_start:
{
lean_object* v_res_5205_; 
v_res_5205_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(v_msg_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_);
lean_dec(v___y_5203_);
lean_dec_ref(v___y_5202_);
lean_dec(v___y_5201_);
lean_dec_ref(v___y_5200_);
return v_res_5205_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(lean_object* v___x_5206_, lean_object* v___x_5207_, lean_object* v___x_5208_, lean_object* v_onAlt_5209_, lean_object* v_a_5210_, uint8_t v___x_5211_, uint8_t v_useSplitter_5212_, lean_object* v___x_5213_, lean_object* v_extraEqualities_5214_, lean_object* v_numDiscrEqs_5215_, lean_object* v___x_5216_, lean_object* v_ys_5217_, lean_object* v_args_5218_, lean_object* v___y_5219_, lean_object* v___y_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_){
_start:
{
lean_object* v_numFields_5224_; lean_object* v_numOverlaps_5225_; uint8_t v_hasUnitThunk_5226_; lean_object* v___x_5227_; uint8_t v___x_5228_; 
v_numFields_5224_ = lean_ctor_get(v___x_5206_, 0);
v_numOverlaps_5225_ = lean_ctor_get(v___x_5206_, 1);
v_hasUnitThunk_5226_ = lean_ctor_get_uint8(v___x_5206_, sizeof(void*)*2);
v___x_5227_ = lean_array_get_size(v_ys_5217_);
v___x_5228_ = lean_nat_dec_eq(v___x_5227_, v_numFields_5224_);
if (v___x_5228_ == 0)
{
lean_object* v___x_5229_; lean_object* v___x_5230_; 
lean_dec_ref(v_args_5218_);
lean_dec_ref(v_ys_5217_);
lean_dec(v_numDiscrEqs_5215_);
lean_dec(v_extraEqualities_5214_);
lean_dec_ref(v___x_5213_);
lean_dec(v_a_5210_);
lean_dec_ref(v_onAlt_5209_);
lean_dec_ref(v___x_5207_);
v___x_5229_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3);
v___x_5230_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(v___x_5229_, v___y_5219_, v___y_5220_, v___y_5221_, v___y_5222_);
return v___x_5230_;
}
else
{
lean_object* v___x_5231_; 
v___x_5231_ = l_Lean_Meta_instantiateForall(v___x_5207_, v_ys_5217_, v___y_5219_, v___y_5220_, v___y_5221_, v___y_5222_);
if (lean_obj_tag(v___x_5231_) == 0)
{
lean_object* v_a_5232_; lean_object* v___x_5234_; uint8_t v_isShared_5235_; uint8_t v_isSharedCheck_5262_; 
v_a_5232_ = lean_ctor_get(v___x_5231_, 0);
v_isSharedCheck_5262_ = !lean_is_exclusive(v___x_5231_);
if (v_isSharedCheck_5262_ == 0)
{
v___x_5234_ = v___x_5231_;
v_isShared_5235_ = v_isSharedCheck_5262_;
goto v_resetjp_5233_;
}
else
{
lean_inc(v_a_5232_);
lean_dec(v___x_5231_);
v___x_5234_ = lean_box(0);
v_isShared_5235_ = v_isSharedCheck_5262_;
goto v_resetjp_5233_;
}
v_resetjp_5233_:
{
uint8_t v_hasUnitThunk_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___f_5239_; lean_object* v_altType_5241_; lean_object* v___y_5242_; lean_object* v___y_5243_; lean_object* v___y_5244_; lean_object* v___y_5245_; 
v_hasUnitThunk_5236_ = lean_ctor_get_uint8(v___x_5208_, sizeof(void*)*2);
v___x_5237_ = lean_box(v___x_5211_);
v___x_5238_ = lean_box(v_useSplitter_5212_);
v___f_5239_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed), 16, 9);
lean_closure_set(v___f_5239_, 0, v_args_5218_);
lean_closure_set(v___f_5239_, 1, v_ys_5217_);
lean_closure_set(v___f_5239_, 2, v_onAlt_5209_);
lean_closure_set(v___f_5239_, 3, v_a_5210_);
lean_closure_set(v___f_5239_, 4, v___x_5237_);
lean_closure_set(v___f_5239_, 5, v___x_5238_);
lean_closure_set(v___f_5239_, 6, v___x_5213_);
lean_closure_set(v___f_5239_, 7, v_extraEqualities_5214_);
lean_closure_set(v___f_5239_, 8, v_numDiscrEqs_5215_);
if (v_hasUnitThunk_5236_ == 0)
{
v_altType_5241_ = v_a_5232_;
v___y_5242_ = v___y_5219_;
v___y_5243_ = v___y_5220_;
v___y_5244_ = v___y_5221_;
v___y_5245_ = v___y_5222_;
goto v___jp_5240_;
}
else
{
lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; 
v___x_5257_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2);
v___x_5258_ = lean_mk_empty_array_with_capacity(v___x_5216_);
v___x_5259_ = lean_array_push(v___x_5258_, v___x_5257_);
v___x_5260_ = l_Lean_Meta_instantiateForall(v_a_5232_, v___x_5259_, v___y_5219_, v___y_5220_, v___y_5221_, v___y_5222_);
lean_dec_ref(v___x_5259_);
if (lean_obj_tag(v___x_5260_) == 0)
{
lean_object* v_a_5261_; 
v_a_5261_ = lean_ctor_get(v___x_5260_, 0);
lean_inc(v_a_5261_);
lean_dec_ref_known(v___x_5260_, 1);
v_altType_5241_ = v_a_5261_;
v___y_5242_ = v___y_5219_;
v___y_5243_ = v___y_5220_;
v___y_5244_ = v___y_5221_;
v___y_5245_ = v___y_5222_;
goto v___jp_5240_;
}
else
{
lean_dec_ref(v___f_5239_);
lean_del_object(v___x_5234_);
return v___x_5260_;
}
}
v___jp_5240_:
{
lean_object* v___x_5247_; 
lean_inc(v_numOverlaps_5225_);
if (v_isShared_5235_ == 0)
{
lean_ctor_set_tag(v___x_5234_, 1);
lean_ctor_set(v___x_5234_, 0, v_numOverlaps_5225_);
v___x_5247_ = v___x_5234_;
goto v_reusejp_5246_;
}
else
{
lean_object* v_reuseFailAlloc_5256_; 
v_reuseFailAlloc_5256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5256_, 0, v_numOverlaps_5225_);
v___x_5247_ = v_reuseFailAlloc_5256_;
goto v_reusejp_5246_;
}
v_reusejp_5246_:
{
lean_object* v___x_5248_; 
v___x_5248_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_5241_, v___x_5247_, v___f_5239_, v___x_5211_, v___x_5211_, v___y_5242_, v___y_5243_, v___y_5244_, v___y_5245_);
if (lean_obj_tag(v___x_5248_) == 0)
{
if (v_hasUnitThunk_5226_ == 0)
{
return v___x_5248_;
}
else
{
lean_object* v_a_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; 
v_a_5249_ = lean_ctor_get(v___x_5248_, 0);
lean_inc(v_a_5249_);
lean_dec_ref_known(v___x_5248_, 1);
v___x_5250_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__2));
v___x_5251_ = lean_unsigned_to_nat(2u);
v___x_5252_ = lean_mk_empty_array_with_capacity(v___x_5251_);
lean_dec_ref(v___x_5252_);
v___x_5253_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6);
v___x_5254_ = lean_array_push(v___x_5253_, v_a_5249_);
v___x_5255_ = l_Lean_Meta_mkAppM(v___x_5250_, v___x_5254_, v___y_5242_, v___y_5243_, v___y_5244_, v___y_5245_);
return v___x_5255_;
}
}
else
{
return v___x_5248_;
}
}
}
}
}
else
{
lean_dec_ref(v_args_5218_);
lean_dec_ref(v_ys_5217_);
lean_dec(v_numDiscrEqs_5215_);
lean_dec(v_extraEqualities_5214_);
lean_dec_ref(v___x_5213_);
lean_dec(v_a_5210_);
lean_dec_ref(v_onAlt_5209_);
return v___x_5231_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_5263_ = _args[0];
lean_object* v___x_5264_ = _args[1];
lean_object* v___x_5265_ = _args[2];
lean_object* v_onAlt_5266_ = _args[3];
lean_object* v_a_5267_ = _args[4];
lean_object* v___x_5268_ = _args[5];
lean_object* v_useSplitter_5269_ = _args[6];
lean_object* v___x_5270_ = _args[7];
lean_object* v_extraEqualities_5271_ = _args[8];
lean_object* v_numDiscrEqs_5272_ = _args[9];
lean_object* v___x_5273_ = _args[10];
lean_object* v_ys_5274_ = _args[11];
lean_object* v_args_5275_ = _args[12];
lean_object* v___y_5276_ = _args[13];
lean_object* v___y_5277_ = _args[14];
lean_object* v___y_5278_ = _args[15];
lean_object* v___y_5279_ = _args[16];
lean_object* v___y_5280_ = _args[17];
_start:
{
uint8_t v___x_33396__boxed_5281_; uint8_t v_useSplitter_boxed_5282_; lean_object* v_res_5283_; 
v___x_33396__boxed_5281_ = lean_unbox(v___x_5268_);
v_useSplitter_boxed_5282_ = lean_unbox(v_useSplitter_5269_);
v_res_5283_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(v___x_5263_, v___x_5264_, v___x_5265_, v_onAlt_5266_, v_a_5267_, v___x_33396__boxed_5281_, v_useSplitter_boxed_5282_, v___x_5270_, v_extraEqualities_5271_, v_numDiscrEqs_5272_, v___x_5273_, v_ys_5274_, v_args_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_);
lean_dec(v___y_5279_);
lean_dec_ref(v___y_5278_);
lean_dec(v___y_5277_);
lean_dec_ref(v___y_5276_);
lean_dec(v___x_5273_);
lean_dec_ref(v___x_5265_);
lean_dec_ref(v___x_5263_);
return v_res_5283_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(lean_object* v_msg_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_){
_start:
{
lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v_toApplicative_5292_; lean_object* v___x_5294_; uint8_t v_isShared_5295_; uint8_t v_isSharedCheck_5353_; 
v___x_5290_ = lean_obj_once(&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0, &l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0_once, _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0);
v___x_5291_ = l_StateRefT_x27_instMonad___redArg(v___x_5290_);
v_toApplicative_5292_ = lean_ctor_get(v___x_5291_, 0);
v_isSharedCheck_5353_ = !lean_is_exclusive(v___x_5291_);
if (v_isSharedCheck_5353_ == 0)
{
lean_object* v_unused_5354_; 
v_unused_5354_ = lean_ctor_get(v___x_5291_, 1);
lean_dec(v_unused_5354_);
v___x_5294_ = v___x_5291_;
v_isShared_5295_ = v_isSharedCheck_5353_;
goto v_resetjp_5293_;
}
else
{
lean_inc(v_toApplicative_5292_);
lean_dec(v___x_5291_);
v___x_5294_ = lean_box(0);
v_isShared_5295_ = v_isSharedCheck_5353_;
goto v_resetjp_5293_;
}
v_resetjp_5293_:
{
lean_object* v_toFunctor_5296_; lean_object* v_toSeq_5297_; lean_object* v_toSeqLeft_5298_; lean_object* v_toSeqRight_5299_; lean_object* v___x_5301_; uint8_t v_isShared_5302_; uint8_t v_isSharedCheck_5351_; 
v_toFunctor_5296_ = lean_ctor_get(v_toApplicative_5292_, 0);
v_toSeq_5297_ = lean_ctor_get(v_toApplicative_5292_, 2);
v_toSeqLeft_5298_ = lean_ctor_get(v_toApplicative_5292_, 3);
v_toSeqRight_5299_ = lean_ctor_get(v_toApplicative_5292_, 4);
v_isSharedCheck_5351_ = !lean_is_exclusive(v_toApplicative_5292_);
if (v_isSharedCheck_5351_ == 0)
{
lean_object* v_unused_5352_; 
v_unused_5352_ = lean_ctor_get(v_toApplicative_5292_, 1);
lean_dec(v_unused_5352_);
v___x_5301_ = v_toApplicative_5292_;
v_isShared_5302_ = v_isSharedCheck_5351_;
goto v_resetjp_5300_;
}
else
{
lean_inc(v_toSeqRight_5299_);
lean_inc(v_toSeqLeft_5298_);
lean_inc(v_toSeq_5297_);
lean_inc(v_toFunctor_5296_);
lean_dec(v_toApplicative_5292_);
v___x_5301_ = lean_box(0);
v_isShared_5302_ = v_isSharedCheck_5351_;
goto v_resetjp_5300_;
}
v_resetjp_5300_:
{
lean_object* v___f_5303_; lean_object* v___f_5304_; lean_object* v___f_5305_; lean_object* v___f_5306_; lean_object* v___x_5307_; lean_object* v___f_5308_; lean_object* v___f_5309_; lean_object* v___f_5310_; lean_object* v___x_5312_; 
v___f_5303_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__1));
v___f_5304_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__2));
lean_inc_ref(v_toFunctor_5296_);
v___f_5305_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5305_, 0, v_toFunctor_5296_);
v___f_5306_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5306_, 0, v_toFunctor_5296_);
v___x_5307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5307_, 0, v___f_5305_);
lean_ctor_set(v___x_5307_, 1, v___f_5306_);
v___f_5308_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5308_, 0, v_toSeqRight_5299_);
v___f_5309_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5309_, 0, v_toSeqLeft_5298_);
v___f_5310_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5310_, 0, v_toSeq_5297_);
if (v_isShared_5302_ == 0)
{
lean_ctor_set(v___x_5301_, 4, v___f_5308_);
lean_ctor_set(v___x_5301_, 3, v___f_5309_);
lean_ctor_set(v___x_5301_, 2, v___f_5310_);
lean_ctor_set(v___x_5301_, 1, v___f_5303_);
lean_ctor_set(v___x_5301_, 0, v___x_5307_);
v___x_5312_ = v___x_5301_;
goto v_reusejp_5311_;
}
else
{
lean_object* v_reuseFailAlloc_5350_; 
v_reuseFailAlloc_5350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5350_, 0, v___x_5307_);
lean_ctor_set(v_reuseFailAlloc_5350_, 1, v___f_5303_);
lean_ctor_set(v_reuseFailAlloc_5350_, 2, v___f_5310_);
lean_ctor_set(v_reuseFailAlloc_5350_, 3, v___f_5309_);
lean_ctor_set(v_reuseFailAlloc_5350_, 4, v___f_5308_);
v___x_5312_ = v_reuseFailAlloc_5350_;
goto v_reusejp_5311_;
}
v_reusejp_5311_:
{
lean_object* v___x_5314_; 
if (v_isShared_5295_ == 0)
{
lean_ctor_set(v___x_5294_, 1, v___f_5304_);
lean_ctor_set(v___x_5294_, 0, v___x_5312_);
v___x_5314_ = v___x_5294_;
goto v_reusejp_5313_;
}
else
{
lean_object* v_reuseFailAlloc_5349_; 
v_reuseFailAlloc_5349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5349_, 0, v___x_5312_);
lean_ctor_set(v_reuseFailAlloc_5349_, 1, v___f_5304_);
v___x_5314_ = v_reuseFailAlloc_5349_;
goto v_reusejp_5313_;
}
v_reusejp_5313_:
{
lean_object* v___x_5315_; lean_object* v_toApplicative_5316_; lean_object* v___x_5318_; uint8_t v_isShared_5319_; uint8_t v_isSharedCheck_5347_; 
v___x_5315_ = l_StateRefT_x27_instMonad___redArg(v___x_5314_);
v_toApplicative_5316_ = lean_ctor_get(v___x_5315_, 0);
v_isSharedCheck_5347_ = !lean_is_exclusive(v___x_5315_);
if (v_isSharedCheck_5347_ == 0)
{
lean_object* v_unused_5348_; 
v_unused_5348_ = lean_ctor_get(v___x_5315_, 1);
lean_dec(v_unused_5348_);
v___x_5318_ = v___x_5315_;
v_isShared_5319_ = v_isSharedCheck_5347_;
goto v_resetjp_5317_;
}
else
{
lean_inc(v_toApplicative_5316_);
lean_dec(v___x_5315_);
v___x_5318_ = lean_box(0);
v_isShared_5319_ = v_isSharedCheck_5347_;
goto v_resetjp_5317_;
}
v_resetjp_5317_:
{
lean_object* v_toFunctor_5320_; lean_object* v_toSeq_5321_; lean_object* v_toSeqLeft_5322_; lean_object* v_toSeqRight_5323_; lean_object* v___x_5325_; uint8_t v_isShared_5326_; uint8_t v_isSharedCheck_5345_; 
v_toFunctor_5320_ = lean_ctor_get(v_toApplicative_5316_, 0);
v_toSeq_5321_ = lean_ctor_get(v_toApplicative_5316_, 2);
v_toSeqLeft_5322_ = lean_ctor_get(v_toApplicative_5316_, 3);
v_toSeqRight_5323_ = lean_ctor_get(v_toApplicative_5316_, 4);
v_isSharedCheck_5345_ = !lean_is_exclusive(v_toApplicative_5316_);
if (v_isSharedCheck_5345_ == 0)
{
lean_object* v_unused_5346_; 
v_unused_5346_ = lean_ctor_get(v_toApplicative_5316_, 1);
lean_dec(v_unused_5346_);
v___x_5325_ = v_toApplicative_5316_;
v_isShared_5326_ = v_isSharedCheck_5345_;
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
v_isShared_5326_ = v_isSharedCheck_5345_;
goto v_resetjp_5324_;
}
v_resetjp_5324_:
{
lean_object* v___f_5327_; lean_object* v___f_5328_; lean_object* v___f_5329_; lean_object* v___f_5330_; lean_object* v___x_5331_; lean_object* v___f_5332_; lean_object* v___f_5333_; lean_object* v___f_5334_; lean_object* v___x_5336_; 
v___f_5327_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__3));
v___f_5328_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__4));
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
lean_object* v_reuseFailAlloc_5344_; 
v_reuseFailAlloc_5344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5344_, 0, v___x_5331_);
lean_ctor_set(v_reuseFailAlloc_5344_, 1, v___f_5327_);
lean_ctor_set(v_reuseFailAlloc_5344_, 2, v___f_5334_);
lean_ctor_set(v_reuseFailAlloc_5344_, 3, v___f_5333_);
lean_ctor_set(v_reuseFailAlloc_5344_, 4, v___f_5332_);
v___x_5336_ = v_reuseFailAlloc_5344_;
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
lean_object* v_reuseFailAlloc_5343_; 
v_reuseFailAlloc_5343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5343_, 0, v___x_5336_);
lean_ctor_set(v_reuseFailAlloc_5343_, 1, v___f_5328_);
v___x_5338_ = v_reuseFailAlloc_5343_;
goto v_reusejp_5337_;
}
v_reusejp_5337_:
{
lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_27332__overap_5341_; lean_object* v___x_5342_; 
v___x_5339_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__7, &l_Lean_Meta_MatcherApp_transform___redArg___closed__7_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__7);
v___x_5340_ = l_instInhabitedOfMonad___redArg(v___x_5338_, v___x_5339_);
v___x_27332__overap_5341_ = lean_panic_fn_borrowed(v___x_5340_, v_msg_5284_);
lean_dec(v___x_5340_);
lean_inc(v___y_5288_);
lean_inc_ref(v___y_5287_);
lean_inc(v___y_5286_);
lean_inc_ref(v___y_5285_);
v___x_5342_ = lean_apply_5(v___x_27332__overap_5341_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_, lean_box(0));
return v___x_5342_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___boxed(lean_object* v_msg_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_){
_start:
{
lean_object* v_res_5361_; 
v_res_5361_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(v_msg_5355_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_);
lean_dec(v___y_5359_);
lean_dec_ref(v___y_5358_);
lean_dec(v___y_5357_);
lean_dec_ref(v___y_5356_);
return v_res_5361_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(lean_object* v___x_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_){
_start:
{
lean_object* v___x_5368_; 
v___x_5368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5368_, 0, v___x_5362_);
return v___x_5368_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed(lean_object* v___x_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_){
_start:
{
lean_object* v_res_5375_; 
v_res_5375_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(v___x_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_);
lean_dec(v___y_5373_);
lean_dec_ref(v___y_5372_);
lean_dec(v___y_5371_);
lean_dec_ref(v___y_5370_);
return v_res_5375_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(lean_object* v_upperBound_5376_, lean_object* v_onAlt_5377_, uint8_t v_useSplitter_5378_, lean_object* v_extraEqualities_5379_, lean_object* v_numDiscrEqs_5380_, lean_object* v_a_5381_, lean_object* v_b_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_){
_start:
{
lean_object* v___y_5389_; uint8_t v___x_5412_; 
v___x_5412_ = lean_nat_dec_lt(v_a_5381_, v_upperBound_5376_);
if (v___x_5412_ == 0)
{
lean_object* v___x_5413_; 
lean_dec(v_a_5381_);
lean_dec(v_numDiscrEqs_5380_);
lean_dec(v_extraEqualities_5379_);
lean_dec_ref(v_onAlt_5377_);
v___x_5413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5413_, 0, v_b_5382_);
return v___x_5413_;
}
else
{
lean_object* v_snd_5414_; lean_object* v_snd_5415_; lean_object* v_snd_5416_; lean_object* v_snd_5417_; lean_object* v_snd_5418_; lean_object* v_fst_5419_; lean_object* v___x_5421_; uint8_t v_isShared_5422_; uint8_t v_isSharedCheck_5623_; 
v_snd_5414_ = lean_ctor_get(v_b_5382_, 1);
lean_inc(v_snd_5414_);
v_snd_5415_ = lean_ctor_get(v_snd_5414_, 1);
lean_inc(v_snd_5415_);
v_snd_5416_ = lean_ctor_get(v_snd_5415_, 1);
lean_inc(v_snd_5416_);
v_snd_5417_ = lean_ctor_get(v_snd_5416_, 1);
lean_inc(v_snd_5417_);
v_snd_5418_ = lean_ctor_get(v_snd_5417_, 1);
lean_inc(v_snd_5418_);
v_fst_5419_ = lean_ctor_get(v_b_5382_, 0);
v_isSharedCheck_5623_ = !lean_is_exclusive(v_b_5382_);
if (v_isSharedCheck_5623_ == 0)
{
lean_object* v_unused_5624_; 
v_unused_5624_ = lean_ctor_get(v_b_5382_, 1);
lean_dec(v_unused_5624_);
v___x_5421_ = v_b_5382_;
v_isShared_5422_ = v_isSharedCheck_5623_;
goto v_resetjp_5420_;
}
else
{
lean_inc(v_fst_5419_);
lean_dec(v_b_5382_);
v___x_5421_ = lean_box(0);
v_isShared_5422_ = v_isSharedCheck_5623_;
goto v_resetjp_5420_;
}
v_resetjp_5420_:
{
lean_object* v_fst_5423_; lean_object* v___x_5425_; uint8_t v_isShared_5426_; uint8_t v_isSharedCheck_5621_; 
v_fst_5423_ = lean_ctor_get(v_snd_5414_, 0);
v_isSharedCheck_5621_ = !lean_is_exclusive(v_snd_5414_);
if (v_isSharedCheck_5621_ == 0)
{
lean_object* v_unused_5622_; 
v_unused_5622_ = lean_ctor_get(v_snd_5414_, 1);
lean_dec(v_unused_5622_);
v___x_5425_ = v_snd_5414_;
v_isShared_5426_ = v_isSharedCheck_5621_;
goto v_resetjp_5424_;
}
else
{
lean_inc(v_fst_5423_);
lean_dec(v_snd_5414_);
v___x_5425_ = lean_box(0);
v_isShared_5426_ = v_isSharedCheck_5621_;
goto v_resetjp_5424_;
}
v_resetjp_5424_:
{
lean_object* v_fst_5427_; lean_object* v___x_5429_; uint8_t v_isShared_5430_; uint8_t v_isSharedCheck_5619_; 
v_fst_5427_ = lean_ctor_get(v_snd_5415_, 0);
v_isSharedCheck_5619_ = !lean_is_exclusive(v_snd_5415_);
if (v_isSharedCheck_5619_ == 0)
{
lean_object* v_unused_5620_; 
v_unused_5620_ = lean_ctor_get(v_snd_5415_, 1);
lean_dec(v_unused_5620_);
v___x_5429_ = v_snd_5415_;
v_isShared_5430_ = v_isSharedCheck_5619_;
goto v_resetjp_5428_;
}
else
{
lean_inc(v_fst_5427_);
lean_dec(v_snd_5415_);
v___x_5429_ = lean_box(0);
v_isShared_5430_ = v_isSharedCheck_5619_;
goto v_resetjp_5428_;
}
v_resetjp_5428_:
{
lean_object* v_fst_5431_; lean_object* v___x_5433_; uint8_t v_isShared_5434_; uint8_t v_isSharedCheck_5617_; 
v_fst_5431_ = lean_ctor_get(v_snd_5416_, 0);
v_isSharedCheck_5617_ = !lean_is_exclusive(v_snd_5416_);
if (v_isSharedCheck_5617_ == 0)
{
lean_object* v_unused_5618_; 
v_unused_5618_ = lean_ctor_get(v_snd_5416_, 1);
lean_dec(v_unused_5618_);
v___x_5433_ = v_snd_5416_;
v_isShared_5434_ = v_isSharedCheck_5617_;
goto v_resetjp_5432_;
}
else
{
lean_inc(v_fst_5431_);
lean_dec(v_snd_5416_);
v___x_5433_ = lean_box(0);
v_isShared_5434_ = v_isSharedCheck_5617_;
goto v_resetjp_5432_;
}
v_resetjp_5432_:
{
lean_object* v_fst_5435_; lean_object* v___x_5437_; uint8_t v_isShared_5438_; uint8_t v_isSharedCheck_5615_; 
v_fst_5435_ = lean_ctor_get(v_snd_5417_, 0);
v_isSharedCheck_5615_ = !lean_is_exclusive(v_snd_5417_);
if (v_isSharedCheck_5615_ == 0)
{
lean_object* v_unused_5616_; 
v_unused_5616_ = lean_ctor_get(v_snd_5417_, 1);
lean_dec(v_unused_5616_);
v___x_5437_ = v_snd_5417_;
v_isShared_5438_ = v_isSharedCheck_5615_;
goto v_resetjp_5436_;
}
else
{
lean_inc(v_fst_5435_);
lean_dec(v_snd_5417_);
v___x_5437_ = lean_box(0);
v_isShared_5438_ = v_isSharedCheck_5615_;
goto v_resetjp_5436_;
}
v_resetjp_5436_:
{
lean_object* v_array_5439_; lean_object* v_start_5440_; lean_object* v_stop_5441_; uint8_t v___x_5442_; 
v_array_5439_ = lean_ctor_get(v_snd_5418_, 0);
v_start_5440_ = lean_ctor_get(v_snd_5418_, 1);
v_stop_5441_ = lean_ctor_get(v_snd_5418_, 2);
v___x_5442_ = lean_nat_dec_lt(v_start_5440_, v_stop_5441_);
if (v___x_5442_ == 0)
{
lean_object* v___x_5444_; 
if (v_isShared_5438_ == 0)
{
v___x_5444_ = v___x_5437_;
goto v_reusejp_5443_;
}
else
{
lean_object* v_reuseFailAlloc_5459_; 
v_reuseFailAlloc_5459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5459_, 0, v_fst_5435_);
lean_ctor_set(v_reuseFailAlloc_5459_, 1, v_snd_5418_);
v___x_5444_ = v_reuseFailAlloc_5459_;
goto v_reusejp_5443_;
}
v_reusejp_5443_:
{
lean_object* v___x_5446_; 
if (v_isShared_5434_ == 0)
{
lean_ctor_set(v___x_5433_, 1, v___x_5444_);
v___x_5446_ = v___x_5433_;
goto v_reusejp_5445_;
}
else
{
lean_object* v_reuseFailAlloc_5458_; 
v_reuseFailAlloc_5458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5458_, 0, v_fst_5431_);
lean_ctor_set(v_reuseFailAlloc_5458_, 1, v___x_5444_);
v___x_5446_ = v_reuseFailAlloc_5458_;
goto v_reusejp_5445_;
}
v_reusejp_5445_:
{
lean_object* v___x_5448_; 
if (v_isShared_5430_ == 0)
{
lean_ctor_set(v___x_5429_, 1, v___x_5446_);
v___x_5448_ = v___x_5429_;
goto v_reusejp_5447_;
}
else
{
lean_object* v_reuseFailAlloc_5457_; 
v_reuseFailAlloc_5457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5457_, 0, v_fst_5427_);
lean_ctor_set(v_reuseFailAlloc_5457_, 1, v___x_5446_);
v___x_5448_ = v_reuseFailAlloc_5457_;
goto v_reusejp_5447_;
}
v_reusejp_5447_:
{
lean_object* v___x_5450_; 
if (v_isShared_5426_ == 0)
{
lean_ctor_set(v___x_5425_, 1, v___x_5448_);
v___x_5450_ = v___x_5425_;
goto v_reusejp_5449_;
}
else
{
lean_object* v_reuseFailAlloc_5456_; 
v_reuseFailAlloc_5456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5456_, 0, v_fst_5423_);
lean_ctor_set(v_reuseFailAlloc_5456_, 1, v___x_5448_);
v___x_5450_ = v_reuseFailAlloc_5456_;
goto v_reusejp_5449_;
}
v_reusejp_5449_:
{
lean_object* v___x_5452_; 
if (v_isShared_5422_ == 0)
{
lean_ctor_set(v___x_5421_, 1, v___x_5450_);
v___x_5452_ = v___x_5421_;
goto v_reusejp_5451_;
}
else
{
lean_object* v_reuseFailAlloc_5455_; 
v_reuseFailAlloc_5455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5455_, 0, v_fst_5419_);
lean_ctor_set(v_reuseFailAlloc_5455_, 1, v___x_5450_);
v___x_5452_ = v_reuseFailAlloc_5455_;
goto v_reusejp_5451_;
}
v_reusejp_5451_:
{
lean_object* v___x_5453_; lean_object* v___f_5454_; 
v___x_5453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5453_, 0, v___x_5452_);
v___f_5454_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5454_, 0, v___x_5453_);
v___y_5389_ = v___f_5454_;
goto v___jp_5388_;
}
}
}
}
}
}
else
{
lean_object* v___x_5461_; uint8_t v_isShared_5462_; uint8_t v_isSharedCheck_5611_; 
lean_inc(v_stop_5441_);
lean_inc(v_start_5440_);
lean_inc_ref(v_array_5439_);
v_isSharedCheck_5611_ = !lean_is_exclusive(v_snd_5418_);
if (v_isSharedCheck_5611_ == 0)
{
lean_object* v_unused_5612_; lean_object* v_unused_5613_; lean_object* v_unused_5614_; 
v_unused_5612_ = lean_ctor_get(v_snd_5418_, 2);
lean_dec(v_unused_5612_);
v_unused_5613_ = lean_ctor_get(v_snd_5418_, 1);
lean_dec(v_unused_5613_);
v_unused_5614_ = lean_ctor_get(v_snd_5418_, 0);
lean_dec(v_unused_5614_);
v___x_5461_ = v_snd_5418_;
v_isShared_5462_ = v_isSharedCheck_5611_;
goto v_resetjp_5460_;
}
else
{
lean_dec(v_snd_5418_);
v___x_5461_ = lean_box(0);
v_isShared_5462_ = v_isSharedCheck_5611_;
goto v_resetjp_5460_;
}
v_resetjp_5460_:
{
lean_object* v_array_5463_; lean_object* v_start_5464_; lean_object* v_stop_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5470_; 
v_array_5463_ = lean_ctor_get(v_fst_5435_, 0);
v_start_5464_ = lean_ctor_get(v_fst_5435_, 1);
v_stop_5465_ = lean_ctor_get(v_fst_5435_, 2);
v___x_5466_ = lean_array_fget(v_array_5439_, v_start_5440_);
v___x_5467_ = lean_unsigned_to_nat(1u);
v___x_5468_ = lean_nat_add(v_start_5440_, v___x_5467_);
lean_dec(v_start_5440_);
if (v_isShared_5462_ == 0)
{
lean_ctor_set(v___x_5461_, 1, v___x_5468_);
v___x_5470_ = v___x_5461_;
goto v_reusejp_5469_;
}
else
{
lean_object* v_reuseFailAlloc_5610_; 
v_reuseFailAlloc_5610_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5610_, 0, v_array_5439_);
lean_ctor_set(v_reuseFailAlloc_5610_, 1, v___x_5468_);
lean_ctor_set(v_reuseFailAlloc_5610_, 2, v_stop_5441_);
v___x_5470_ = v_reuseFailAlloc_5610_;
goto v_reusejp_5469_;
}
v_reusejp_5469_:
{
uint8_t v___x_5471_; 
v___x_5471_ = lean_nat_dec_lt(v_start_5464_, v_stop_5465_);
if (v___x_5471_ == 0)
{
lean_object* v___x_5473_; 
lean_dec(v___x_5466_);
if (v_isShared_5438_ == 0)
{
lean_ctor_set(v___x_5437_, 1, v___x_5470_);
v___x_5473_ = v___x_5437_;
goto v_reusejp_5472_;
}
else
{
lean_object* v_reuseFailAlloc_5488_; 
v_reuseFailAlloc_5488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5488_, 0, v_fst_5435_);
lean_ctor_set(v_reuseFailAlloc_5488_, 1, v___x_5470_);
v___x_5473_ = v_reuseFailAlloc_5488_;
goto v_reusejp_5472_;
}
v_reusejp_5472_:
{
lean_object* v___x_5475_; 
if (v_isShared_5434_ == 0)
{
lean_ctor_set(v___x_5433_, 1, v___x_5473_);
v___x_5475_ = v___x_5433_;
goto v_reusejp_5474_;
}
else
{
lean_object* v_reuseFailAlloc_5487_; 
v_reuseFailAlloc_5487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5487_, 0, v_fst_5431_);
lean_ctor_set(v_reuseFailAlloc_5487_, 1, v___x_5473_);
v___x_5475_ = v_reuseFailAlloc_5487_;
goto v_reusejp_5474_;
}
v_reusejp_5474_:
{
lean_object* v___x_5477_; 
if (v_isShared_5430_ == 0)
{
lean_ctor_set(v___x_5429_, 1, v___x_5475_);
v___x_5477_ = v___x_5429_;
goto v_reusejp_5476_;
}
else
{
lean_object* v_reuseFailAlloc_5486_; 
v_reuseFailAlloc_5486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5486_, 0, v_fst_5427_);
lean_ctor_set(v_reuseFailAlloc_5486_, 1, v___x_5475_);
v___x_5477_ = v_reuseFailAlloc_5486_;
goto v_reusejp_5476_;
}
v_reusejp_5476_:
{
lean_object* v___x_5479_; 
if (v_isShared_5426_ == 0)
{
lean_ctor_set(v___x_5425_, 1, v___x_5477_);
v___x_5479_ = v___x_5425_;
goto v_reusejp_5478_;
}
else
{
lean_object* v_reuseFailAlloc_5485_; 
v_reuseFailAlloc_5485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5485_, 0, v_fst_5423_);
lean_ctor_set(v_reuseFailAlloc_5485_, 1, v___x_5477_);
v___x_5479_ = v_reuseFailAlloc_5485_;
goto v_reusejp_5478_;
}
v_reusejp_5478_:
{
lean_object* v___x_5481_; 
if (v_isShared_5422_ == 0)
{
lean_ctor_set(v___x_5421_, 1, v___x_5479_);
v___x_5481_ = v___x_5421_;
goto v_reusejp_5480_;
}
else
{
lean_object* v_reuseFailAlloc_5484_; 
v_reuseFailAlloc_5484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5484_, 0, v_fst_5419_);
lean_ctor_set(v_reuseFailAlloc_5484_, 1, v___x_5479_);
v___x_5481_ = v_reuseFailAlloc_5484_;
goto v_reusejp_5480_;
}
v_reusejp_5480_:
{
lean_object* v___x_5482_; lean_object* v___f_5483_; 
v___x_5482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5482_, 0, v___x_5481_);
v___f_5483_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5483_, 0, v___x_5482_);
v___y_5389_ = v___f_5483_;
goto v___jp_5388_;
}
}
}
}
}
}
else
{
lean_object* v___x_5490_; uint8_t v_isShared_5491_; uint8_t v_isSharedCheck_5606_; 
lean_inc(v_stop_5465_);
lean_inc(v_start_5464_);
lean_inc_ref(v_array_5463_);
v_isSharedCheck_5606_ = !lean_is_exclusive(v_fst_5435_);
if (v_isSharedCheck_5606_ == 0)
{
lean_object* v_unused_5607_; lean_object* v_unused_5608_; lean_object* v_unused_5609_; 
v_unused_5607_ = lean_ctor_get(v_fst_5435_, 2);
lean_dec(v_unused_5607_);
v_unused_5608_ = lean_ctor_get(v_fst_5435_, 1);
lean_dec(v_unused_5608_);
v_unused_5609_ = lean_ctor_get(v_fst_5435_, 0);
lean_dec(v_unused_5609_);
v___x_5490_ = v_fst_5435_;
v_isShared_5491_ = v_isSharedCheck_5606_;
goto v_resetjp_5489_;
}
else
{
lean_dec(v_fst_5435_);
v___x_5490_ = lean_box(0);
v_isShared_5491_ = v_isSharedCheck_5606_;
goto v_resetjp_5489_;
}
v_resetjp_5489_:
{
lean_object* v_array_5492_; lean_object* v_start_5493_; lean_object* v_stop_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5498_; 
v_array_5492_ = lean_ctor_get(v_fst_5431_, 0);
v_start_5493_ = lean_ctor_get(v_fst_5431_, 1);
v_stop_5494_ = lean_ctor_get(v_fst_5431_, 2);
v___x_5495_ = lean_array_fget(v_array_5463_, v_start_5464_);
v___x_5496_ = lean_nat_add(v_start_5464_, v___x_5467_);
lean_dec(v_start_5464_);
if (v_isShared_5491_ == 0)
{
lean_ctor_set(v___x_5490_, 1, v___x_5496_);
v___x_5498_ = v___x_5490_;
goto v_reusejp_5497_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v_array_5463_);
lean_ctor_set(v_reuseFailAlloc_5605_, 1, v___x_5496_);
lean_ctor_set(v_reuseFailAlloc_5605_, 2, v_stop_5465_);
v___x_5498_ = v_reuseFailAlloc_5605_;
goto v_reusejp_5497_;
}
v_reusejp_5497_:
{
uint8_t v___x_5499_; 
v___x_5499_ = lean_nat_dec_lt(v_start_5493_, v_stop_5494_);
if (v___x_5499_ == 0)
{
lean_object* v___x_5501_; 
lean_dec(v___x_5495_);
lean_dec(v___x_5466_);
if (v_isShared_5438_ == 0)
{
lean_ctor_set(v___x_5437_, 1, v___x_5470_);
lean_ctor_set(v___x_5437_, 0, v___x_5498_);
v___x_5501_ = v___x_5437_;
goto v_reusejp_5500_;
}
else
{
lean_object* v_reuseFailAlloc_5516_; 
v_reuseFailAlloc_5516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5516_, 0, v___x_5498_);
lean_ctor_set(v_reuseFailAlloc_5516_, 1, v___x_5470_);
v___x_5501_ = v_reuseFailAlloc_5516_;
goto v_reusejp_5500_;
}
v_reusejp_5500_:
{
lean_object* v___x_5503_; 
if (v_isShared_5434_ == 0)
{
lean_ctor_set(v___x_5433_, 1, v___x_5501_);
v___x_5503_ = v___x_5433_;
goto v_reusejp_5502_;
}
else
{
lean_object* v_reuseFailAlloc_5515_; 
v_reuseFailAlloc_5515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5515_, 0, v_fst_5431_);
lean_ctor_set(v_reuseFailAlloc_5515_, 1, v___x_5501_);
v___x_5503_ = v_reuseFailAlloc_5515_;
goto v_reusejp_5502_;
}
v_reusejp_5502_:
{
lean_object* v___x_5505_; 
if (v_isShared_5430_ == 0)
{
lean_ctor_set(v___x_5429_, 1, v___x_5503_);
v___x_5505_ = v___x_5429_;
goto v_reusejp_5504_;
}
else
{
lean_object* v_reuseFailAlloc_5514_; 
v_reuseFailAlloc_5514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5514_, 0, v_fst_5427_);
lean_ctor_set(v_reuseFailAlloc_5514_, 1, v___x_5503_);
v___x_5505_ = v_reuseFailAlloc_5514_;
goto v_reusejp_5504_;
}
v_reusejp_5504_:
{
lean_object* v___x_5507_; 
if (v_isShared_5426_ == 0)
{
lean_ctor_set(v___x_5425_, 1, v___x_5505_);
v___x_5507_ = v___x_5425_;
goto v_reusejp_5506_;
}
else
{
lean_object* v_reuseFailAlloc_5513_; 
v_reuseFailAlloc_5513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5513_, 0, v_fst_5423_);
lean_ctor_set(v_reuseFailAlloc_5513_, 1, v___x_5505_);
v___x_5507_ = v_reuseFailAlloc_5513_;
goto v_reusejp_5506_;
}
v_reusejp_5506_:
{
lean_object* v___x_5509_; 
if (v_isShared_5422_ == 0)
{
lean_ctor_set(v___x_5421_, 1, v___x_5507_);
v___x_5509_ = v___x_5421_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5512_; 
v_reuseFailAlloc_5512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5512_, 0, v_fst_5419_);
lean_ctor_set(v_reuseFailAlloc_5512_, 1, v___x_5507_);
v___x_5509_ = v_reuseFailAlloc_5512_;
goto v_reusejp_5508_;
}
v_reusejp_5508_:
{
lean_object* v___x_5510_; lean_object* v___f_5511_; 
v___x_5510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5510_, 0, v___x_5509_);
v___f_5511_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5511_, 0, v___x_5510_);
v___y_5389_ = v___f_5511_;
goto v___jp_5388_;
}
}
}
}
}
}
else
{
lean_object* v___x_5518_; uint8_t v_isShared_5519_; uint8_t v_isSharedCheck_5601_; 
lean_inc(v_stop_5494_);
lean_inc(v_start_5493_);
lean_inc_ref(v_array_5492_);
v_isSharedCheck_5601_ = !lean_is_exclusive(v_fst_5431_);
if (v_isSharedCheck_5601_ == 0)
{
lean_object* v_unused_5602_; lean_object* v_unused_5603_; lean_object* v_unused_5604_; 
v_unused_5602_ = lean_ctor_get(v_fst_5431_, 2);
lean_dec(v_unused_5602_);
v_unused_5603_ = lean_ctor_get(v_fst_5431_, 1);
lean_dec(v_unused_5603_);
v_unused_5604_ = lean_ctor_get(v_fst_5431_, 0);
lean_dec(v_unused_5604_);
v___x_5518_ = v_fst_5431_;
v_isShared_5519_ = v_isSharedCheck_5601_;
goto v_resetjp_5517_;
}
else
{
lean_dec(v_fst_5431_);
v___x_5518_ = lean_box(0);
v_isShared_5519_ = v_isSharedCheck_5601_;
goto v_resetjp_5517_;
}
v_resetjp_5517_:
{
lean_object* v_array_5520_; lean_object* v_start_5521_; lean_object* v_stop_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5526_; 
v_array_5520_ = lean_ctor_get(v_fst_5427_, 0);
v_start_5521_ = lean_ctor_get(v_fst_5427_, 1);
v_stop_5522_ = lean_ctor_get(v_fst_5427_, 2);
v___x_5523_ = lean_array_fget(v_array_5492_, v_start_5493_);
v___x_5524_ = lean_nat_add(v_start_5493_, v___x_5467_);
lean_dec(v_start_5493_);
if (v_isShared_5519_ == 0)
{
lean_ctor_set(v___x_5518_, 1, v___x_5524_);
v___x_5526_ = v___x_5518_;
goto v_reusejp_5525_;
}
else
{
lean_object* v_reuseFailAlloc_5600_; 
v_reuseFailAlloc_5600_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5600_, 0, v_array_5492_);
lean_ctor_set(v_reuseFailAlloc_5600_, 1, v___x_5524_);
lean_ctor_set(v_reuseFailAlloc_5600_, 2, v_stop_5494_);
v___x_5526_ = v_reuseFailAlloc_5600_;
goto v_reusejp_5525_;
}
v_reusejp_5525_:
{
uint8_t v___x_5527_; 
v___x_5527_ = lean_nat_dec_lt(v_start_5521_, v_stop_5522_);
if (v___x_5527_ == 0)
{
lean_object* v___x_5529_; 
lean_dec(v___x_5523_);
lean_dec(v___x_5495_);
lean_dec(v___x_5466_);
if (v_isShared_5438_ == 0)
{
lean_ctor_set(v___x_5437_, 1, v___x_5470_);
lean_ctor_set(v___x_5437_, 0, v___x_5498_);
v___x_5529_ = v___x_5437_;
goto v_reusejp_5528_;
}
else
{
lean_object* v_reuseFailAlloc_5544_; 
v_reuseFailAlloc_5544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5544_, 0, v___x_5498_);
lean_ctor_set(v_reuseFailAlloc_5544_, 1, v___x_5470_);
v___x_5529_ = v_reuseFailAlloc_5544_;
goto v_reusejp_5528_;
}
v_reusejp_5528_:
{
lean_object* v___x_5531_; 
if (v_isShared_5434_ == 0)
{
lean_ctor_set(v___x_5433_, 1, v___x_5529_);
lean_ctor_set(v___x_5433_, 0, v___x_5526_);
v___x_5531_ = v___x_5433_;
goto v_reusejp_5530_;
}
else
{
lean_object* v_reuseFailAlloc_5543_; 
v_reuseFailAlloc_5543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5543_, 0, v___x_5526_);
lean_ctor_set(v_reuseFailAlloc_5543_, 1, v___x_5529_);
v___x_5531_ = v_reuseFailAlloc_5543_;
goto v_reusejp_5530_;
}
v_reusejp_5530_:
{
lean_object* v___x_5533_; 
if (v_isShared_5430_ == 0)
{
lean_ctor_set(v___x_5429_, 1, v___x_5531_);
v___x_5533_ = v___x_5429_;
goto v_reusejp_5532_;
}
else
{
lean_object* v_reuseFailAlloc_5542_; 
v_reuseFailAlloc_5542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5542_, 0, v_fst_5427_);
lean_ctor_set(v_reuseFailAlloc_5542_, 1, v___x_5531_);
v___x_5533_ = v_reuseFailAlloc_5542_;
goto v_reusejp_5532_;
}
v_reusejp_5532_:
{
lean_object* v___x_5535_; 
if (v_isShared_5426_ == 0)
{
lean_ctor_set(v___x_5425_, 1, v___x_5533_);
v___x_5535_ = v___x_5425_;
goto v_reusejp_5534_;
}
else
{
lean_object* v_reuseFailAlloc_5541_; 
v_reuseFailAlloc_5541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5541_, 0, v_fst_5423_);
lean_ctor_set(v_reuseFailAlloc_5541_, 1, v___x_5533_);
v___x_5535_ = v_reuseFailAlloc_5541_;
goto v_reusejp_5534_;
}
v_reusejp_5534_:
{
lean_object* v___x_5537_; 
if (v_isShared_5422_ == 0)
{
lean_ctor_set(v___x_5421_, 1, v___x_5535_);
v___x_5537_ = v___x_5421_;
goto v_reusejp_5536_;
}
else
{
lean_object* v_reuseFailAlloc_5540_; 
v_reuseFailAlloc_5540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5540_, 0, v_fst_5419_);
lean_ctor_set(v_reuseFailAlloc_5540_, 1, v___x_5535_);
v___x_5537_ = v_reuseFailAlloc_5540_;
goto v_reusejp_5536_;
}
v_reusejp_5536_:
{
lean_object* v___x_5538_; lean_object* v___f_5539_; 
v___x_5538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5538_, 0, v___x_5537_);
v___f_5539_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5539_, 0, v___x_5538_);
v___y_5389_ = v___f_5539_;
goto v___jp_5388_;
}
}
}
}
}
}
else
{
lean_object* v___x_5546_; uint8_t v_isShared_5547_; uint8_t v_isSharedCheck_5596_; 
lean_inc(v_stop_5522_);
lean_inc(v_start_5521_);
lean_inc_ref(v_array_5520_);
v_isSharedCheck_5596_ = !lean_is_exclusive(v_fst_5427_);
if (v_isSharedCheck_5596_ == 0)
{
lean_object* v_unused_5597_; lean_object* v_unused_5598_; lean_object* v_unused_5599_; 
v_unused_5597_ = lean_ctor_get(v_fst_5427_, 2);
lean_dec(v_unused_5597_);
v_unused_5598_ = lean_ctor_get(v_fst_5427_, 1);
lean_dec(v_unused_5598_);
v_unused_5599_ = lean_ctor_get(v_fst_5427_, 0);
lean_dec(v_unused_5599_);
v___x_5546_ = v_fst_5427_;
v_isShared_5547_ = v_isSharedCheck_5596_;
goto v_resetjp_5545_;
}
else
{
lean_dec(v_fst_5427_);
v___x_5546_ = lean_box(0);
v_isShared_5547_ = v_isSharedCheck_5596_;
goto v_resetjp_5545_;
}
v_resetjp_5545_:
{
lean_object* v_array_5548_; lean_object* v_start_5549_; lean_object* v_stop_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5554_; 
v_array_5548_ = lean_ctor_get(v_fst_5423_, 0);
v_start_5549_ = lean_ctor_get(v_fst_5423_, 1);
v_stop_5550_ = lean_ctor_get(v_fst_5423_, 2);
v___x_5551_ = lean_array_fget(v_array_5520_, v_start_5521_);
v___x_5552_ = lean_nat_add(v_start_5521_, v___x_5467_);
lean_dec(v_start_5521_);
if (v_isShared_5547_ == 0)
{
lean_ctor_set(v___x_5546_, 1, v___x_5552_);
v___x_5554_ = v___x_5546_;
goto v_reusejp_5553_;
}
else
{
lean_object* v_reuseFailAlloc_5595_; 
v_reuseFailAlloc_5595_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5595_, 0, v_array_5520_);
lean_ctor_set(v_reuseFailAlloc_5595_, 1, v___x_5552_);
lean_ctor_set(v_reuseFailAlloc_5595_, 2, v_stop_5522_);
v___x_5554_ = v_reuseFailAlloc_5595_;
goto v_reusejp_5553_;
}
v_reusejp_5553_:
{
uint8_t v___x_5555_; 
v___x_5555_ = lean_nat_dec_lt(v_start_5549_, v_stop_5550_);
if (v___x_5555_ == 0)
{
lean_object* v___x_5557_; 
lean_dec(v___x_5551_);
lean_dec(v___x_5523_);
lean_dec(v___x_5495_);
lean_dec(v___x_5466_);
if (v_isShared_5438_ == 0)
{
lean_ctor_set(v___x_5437_, 1, v___x_5470_);
lean_ctor_set(v___x_5437_, 0, v___x_5498_);
v___x_5557_ = v___x_5437_;
goto v_reusejp_5556_;
}
else
{
lean_object* v_reuseFailAlloc_5572_; 
v_reuseFailAlloc_5572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5572_, 0, v___x_5498_);
lean_ctor_set(v_reuseFailAlloc_5572_, 1, v___x_5470_);
v___x_5557_ = v_reuseFailAlloc_5572_;
goto v_reusejp_5556_;
}
v_reusejp_5556_:
{
lean_object* v___x_5559_; 
if (v_isShared_5434_ == 0)
{
lean_ctor_set(v___x_5433_, 1, v___x_5557_);
lean_ctor_set(v___x_5433_, 0, v___x_5526_);
v___x_5559_ = v___x_5433_;
goto v_reusejp_5558_;
}
else
{
lean_object* v_reuseFailAlloc_5571_; 
v_reuseFailAlloc_5571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5571_, 0, v___x_5526_);
lean_ctor_set(v_reuseFailAlloc_5571_, 1, v___x_5557_);
v___x_5559_ = v_reuseFailAlloc_5571_;
goto v_reusejp_5558_;
}
v_reusejp_5558_:
{
lean_object* v___x_5561_; 
if (v_isShared_5430_ == 0)
{
lean_ctor_set(v___x_5429_, 1, v___x_5559_);
lean_ctor_set(v___x_5429_, 0, v___x_5554_);
v___x_5561_ = v___x_5429_;
goto v_reusejp_5560_;
}
else
{
lean_object* v_reuseFailAlloc_5570_; 
v_reuseFailAlloc_5570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5570_, 0, v___x_5554_);
lean_ctor_set(v_reuseFailAlloc_5570_, 1, v___x_5559_);
v___x_5561_ = v_reuseFailAlloc_5570_;
goto v_reusejp_5560_;
}
v_reusejp_5560_:
{
lean_object* v___x_5563_; 
if (v_isShared_5426_ == 0)
{
lean_ctor_set(v___x_5425_, 1, v___x_5561_);
v___x_5563_ = v___x_5425_;
goto v_reusejp_5562_;
}
else
{
lean_object* v_reuseFailAlloc_5569_; 
v_reuseFailAlloc_5569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5569_, 0, v_fst_5423_);
lean_ctor_set(v_reuseFailAlloc_5569_, 1, v___x_5561_);
v___x_5563_ = v_reuseFailAlloc_5569_;
goto v_reusejp_5562_;
}
v_reusejp_5562_:
{
lean_object* v___x_5565_; 
if (v_isShared_5422_ == 0)
{
lean_ctor_set(v___x_5421_, 1, v___x_5563_);
v___x_5565_ = v___x_5421_;
goto v_reusejp_5564_;
}
else
{
lean_object* v_reuseFailAlloc_5568_; 
v_reuseFailAlloc_5568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5568_, 0, v_fst_5419_);
lean_ctor_set(v_reuseFailAlloc_5568_, 1, v___x_5563_);
v___x_5565_ = v_reuseFailAlloc_5568_;
goto v_reusejp_5564_;
}
v_reusejp_5564_:
{
lean_object* v___x_5566_; lean_object* v___f_5567_; 
v___x_5566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5566_, 0, v___x_5565_);
v___f_5567_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5567_, 0, v___x_5566_);
v___y_5389_ = v___f_5567_;
goto v___jp_5388_;
}
}
}
}
}
}
else
{
lean_object* v___x_5574_; uint8_t v_isShared_5575_; uint8_t v_isSharedCheck_5591_; 
lean_inc(v_stop_5550_);
lean_inc(v_start_5549_);
lean_inc_ref(v_array_5548_);
lean_del_object(v___x_5437_);
lean_del_object(v___x_5433_);
lean_del_object(v___x_5429_);
lean_del_object(v___x_5425_);
lean_del_object(v___x_5421_);
v_isSharedCheck_5591_ = !lean_is_exclusive(v_fst_5423_);
if (v_isSharedCheck_5591_ == 0)
{
lean_object* v_unused_5592_; lean_object* v_unused_5593_; lean_object* v_unused_5594_; 
v_unused_5592_ = lean_ctor_get(v_fst_5423_, 2);
lean_dec(v_unused_5592_);
v_unused_5593_ = lean_ctor_get(v_fst_5423_, 1);
lean_dec(v_unused_5593_);
v_unused_5594_ = lean_ctor_get(v_fst_5423_, 0);
lean_dec(v_unused_5594_);
v___x_5574_ = v_fst_5423_;
v_isShared_5575_ = v_isSharedCheck_5591_;
goto v_resetjp_5573_;
}
else
{
lean_dec(v_fst_5423_);
v___x_5574_ = lean_box(0);
v_isShared_5575_ = v_isSharedCheck_5591_;
goto v_resetjp_5573_;
}
v_resetjp_5573_:
{
lean_object* v_numOverlaps_5576_; lean_object* v___x_5577_; uint8_t v___x_5578_; 
v_numOverlaps_5576_ = lean_ctor_get(v___x_5551_, 1);
v___x_5577_ = lean_unsigned_to_nat(0u);
v___x_5578_ = lean_nat_dec_eq(v_numOverlaps_5576_, v___x_5577_);
if (v___x_5578_ == 0)
{
lean_object* v___x_5579_; lean_object* v___x_5580_; 
lean_del_object(v___x_5574_);
lean_dec_ref(v___x_5554_);
lean_dec(v___x_5551_);
lean_dec(v_stop_5550_);
lean_dec(v_start_5549_);
lean_dec_ref(v_array_5548_);
lean_dec_ref(v___x_5526_);
lean_dec(v___x_5523_);
lean_dec_ref(v___x_5498_);
lean_dec(v___x_5495_);
lean_dec_ref(v___x_5470_);
lean_dec(v___x_5466_);
lean_dec(v_fst_5419_);
v___x_5579_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_5580_ = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___boxed), 6, 1);
lean_closure_set(v___x_5580_, 0, v___x_5579_);
v___y_5389_ = v___x_5580_;
goto v___jp_5388_;
}
else
{
uint8_t v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v___f_5585_; lean_object* v___x_5586_; lean_object* v___x_5588_; 
v___x_5581_ = 0;
v___x_5582_ = lean_array_fget_borrowed(v_array_5548_, v_start_5549_);
v___x_5583_ = lean_box(v___x_5581_);
v___x_5584_ = lean_box(v_useSplitter_5378_);
lean_inc(v_numDiscrEqs_5380_);
lean_inc(v_extraEqualities_5379_);
lean_inc(v___x_5582_);
lean_inc(v_a_5381_);
lean_inc_ref(v_onAlt_5377_);
lean_inc(v___x_5551_);
v___f_5585_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed), 18, 11);
lean_closure_set(v___f_5585_, 0, v___x_5523_);
lean_closure_set(v___f_5585_, 1, v___x_5466_);
lean_closure_set(v___f_5585_, 2, v___x_5551_);
lean_closure_set(v___f_5585_, 3, v_onAlt_5377_);
lean_closure_set(v___f_5585_, 4, v_a_5381_);
lean_closure_set(v___f_5585_, 5, v___x_5583_);
lean_closure_set(v___f_5585_, 6, v___x_5584_);
lean_closure_set(v___f_5585_, 7, v___x_5582_);
lean_closure_set(v___f_5585_, 8, v_extraEqualities_5379_);
lean_closure_set(v___f_5585_, 9, v_numDiscrEqs_5380_);
lean_closure_set(v___f_5585_, 10, v___x_5467_);
v___x_5586_ = lean_nat_add(v_start_5549_, v___x_5467_);
lean_dec(v_start_5549_);
if (v_isShared_5575_ == 0)
{
lean_ctor_set(v___x_5574_, 1, v___x_5586_);
v___x_5588_ = v___x_5574_;
goto v_reusejp_5587_;
}
else
{
lean_object* v_reuseFailAlloc_5590_; 
v_reuseFailAlloc_5590_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5590_, 0, v_array_5548_);
lean_ctor_set(v_reuseFailAlloc_5590_, 1, v___x_5586_);
lean_ctor_set(v_reuseFailAlloc_5590_, 2, v_stop_5550_);
v___x_5588_ = v_reuseFailAlloc_5590_;
goto v_reusejp_5587_;
}
v_reusejp_5587_:
{
lean_object* v___f_5589_; 
v___f_5589_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed), 14, 9);
lean_closure_set(v___f_5589_, 0, v___x_5495_);
lean_closure_set(v___f_5589_, 1, v___x_5551_);
lean_closure_set(v___f_5589_, 2, v___f_5585_);
lean_closure_set(v___f_5589_, 3, v_fst_5419_);
lean_closure_set(v___f_5589_, 4, v___x_5498_);
lean_closure_set(v___f_5589_, 5, v___x_5470_);
lean_closure_set(v___f_5589_, 6, v___x_5526_);
lean_closure_set(v___f_5589_, 7, v___x_5554_);
lean_closure_set(v___f_5589_, 8, v___x_5588_);
v___y_5389_ = v___f_5589_;
goto v___jp_5388_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_5388_:
{
lean_object* v___x_5390_; 
lean_inc(v___y_5386_);
lean_inc_ref(v___y_5385_);
lean_inc(v___y_5384_);
lean_inc_ref(v___y_5383_);
v___x_5390_ = lean_apply_5(v___y_5389_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, lean_box(0));
if (lean_obj_tag(v___x_5390_) == 0)
{
lean_object* v_a_5391_; lean_object* v___x_5393_; uint8_t v_isShared_5394_; uint8_t v_isSharedCheck_5403_; 
v_a_5391_ = lean_ctor_get(v___x_5390_, 0);
v_isSharedCheck_5403_ = !lean_is_exclusive(v___x_5390_);
if (v_isSharedCheck_5403_ == 0)
{
v___x_5393_ = v___x_5390_;
v_isShared_5394_ = v_isSharedCheck_5403_;
goto v_resetjp_5392_;
}
else
{
lean_inc(v_a_5391_);
lean_dec(v___x_5390_);
v___x_5393_ = lean_box(0);
v_isShared_5394_ = v_isSharedCheck_5403_;
goto v_resetjp_5392_;
}
v_resetjp_5392_:
{
if (lean_obj_tag(v_a_5391_) == 0)
{
lean_object* v_a_5395_; lean_object* v___x_5397_; 
lean_dec(v_a_5381_);
lean_dec(v_numDiscrEqs_5380_);
lean_dec(v_extraEqualities_5379_);
lean_dec_ref(v_onAlt_5377_);
v_a_5395_ = lean_ctor_get(v_a_5391_, 0);
lean_inc(v_a_5395_);
lean_dec_ref_known(v_a_5391_, 1);
if (v_isShared_5394_ == 0)
{
lean_ctor_set(v___x_5393_, 0, v_a_5395_);
v___x_5397_ = v___x_5393_;
goto v_reusejp_5396_;
}
else
{
lean_object* v_reuseFailAlloc_5398_; 
v_reuseFailAlloc_5398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5398_, 0, v_a_5395_);
v___x_5397_ = v_reuseFailAlloc_5398_;
goto v_reusejp_5396_;
}
v_reusejp_5396_:
{
return v___x_5397_;
}
}
else
{
lean_object* v_a_5399_; lean_object* v___x_5400_; lean_object* v___x_5401_; 
lean_del_object(v___x_5393_);
v_a_5399_ = lean_ctor_get(v_a_5391_, 0);
lean_inc(v_a_5399_);
lean_dec_ref_known(v_a_5391_, 1);
v___x_5400_ = lean_unsigned_to_nat(1u);
v___x_5401_ = lean_nat_add(v_a_5381_, v___x_5400_);
lean_dec(v_a_5381_);
v_a_5381_ = v___x_5401_;
v_b_5382_ = v_a_5399_;
goto _start;
}
}
}
else
{
lean_object* v_a_5404_; lean_object* v___x_5406_; uint8_t v_isShared_5407_; uint8_t v_isSharedCheck_5411_; 
lean_dec(v_a_5381_);
lean_dec(v_numDiscrEqs_5380_);
lean_dec(v_extraEqualities_5379_);
lean_dec_ref(v_onAlt_5377_);
v_a_5404_ = lean_ctor_get(v___x_5390_, 0);
v_isSharedCheck_5411_ = !lean_is_exclusive(v___x_5390_);
if (v_isSharedCheck_5411_ == 0)
{
v___x_5406_ = v___x_5390_;
v_isShared_5407_ = v_isSharedCheck_5411_;
goto v_resetjp_5405_;
}
else
{
lean_inc(v_a_5404_);
lean_dec(v___x_5390_);
v___x_5406_ = lean_box(0);
v_isShared_5407_ = v_isSharedCheck_5411_;
goto v_resetjp_5405_;
}
v_resetjp_5405_:
{
lean_object* v___x_5409_; 
if (v_isShared_5407_ == 0)
{
v___x_5409_ = v___x_5406_;
goto v_reusejp_5408_;
}
else
{
lean_object* v_reuseFailAlloc_5410_; 
v_reuseFailAlloc_5410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5410_, 0, v_a_5404_);
v___x_5409_ = v_reuseFailAlloc_5410_;
goto v_reusejp_5408_;
}
v_reusejp_5408_:
{
return v___x_5409_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___boxed(lean_object* v_upperBound_5625_, lean_object* v_onAlt_5626_, lean_object* v_useSplitter_5627_, lean_object* v_extraEqualities_5628_, lean_object* v_numDiscrEqs_5629_, lean_object* v_a_5630_, lean_object* v_b_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_){
_start:
{
uint8_t v_useSplitter_boxed_5637_; lean_object* v_res_5638_; 
v_useSplitter_boxed_5637_ = lean_unbox(v_useSplitter_5627_);
v_res_5638_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v_upperBound_5625_, v_onAlt_5626_, v_useSplitter_boxed_5637_, v_extraEqualities_5628_, v_numDiscrEqs_5629_, v_a_5630_, v_b_5631_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_);
lean_dec(v___y_5635_);
lean_dec_ref(v___y_5634_);
lean_dec(v___y_5633_);
lean_dec_ref(v___y_5632_);
lean_dec(v_upperBound_5625_);
return v_res_5638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(uint8_t v_addEqualities_5639_, lean_object* v_as_5640_, size_t v_sz_5641_, size_t v_i_5642_, lean_object* v_b_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_, lean_object* v___y_5646_, lean_object* v___y_5647_){
_start:
{
lean_object* v_a_5650_; uint8_t v___x_5654_; 
v___x_5654_ = lean_usize_dec_lt(v_i_5642_, v_sz_5641_);
if (v___x_5654_ == 0)
{
lean_object* v___x_5655_; 
v___x_5655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5655_, 0, v_b_5643_);
return v___x_5655_;
}
else
{
lean_object* v_snd_5656_; lean_object* v_snd_5657_; lean_object* v_snd_5658_; lean_object* v_snd_5659_; lean_object* v_fst_5660_; lean_object* v___x_5662_; uint8_t v_isShared_5663_; uint8_t v_isSharedCheck_5806_; 
v_snd_5656_ = lean_ctor_get(v_b_5643_, 1);
lean_inc(v_snd_5656_);
v_snd_5657_ = lean_ctor_get(v_snd_5656_, 1);
lean_inc(v_snd_5657_);
v_snd_5658_ = lean_ctor_get(v_snd_5657_, 1);
lean_inc(v_snd_5658_);
v_snd_5659_ = lean_ctor_get(v_snd_5658_, 1);
lean_inc(v_snd_5659_);
v_fst_5660_ = lean_ctor_get(v_b_5643_, 0);
v_isSharedCheck_5806_ = !lean_is_exclusive(v_b_5643_);
if (v_isSharedCheck_5806_ == 0)
{
lean_object* v_unused_5807_; 
v_unused_5807_ = lean_ctor_get(v_b_5643_, 1);
lean_dec(v_unused_5807_);
v___x_5662_ = v_b_5643_;
v_isShared_5663_ = v_isSharedCheck_5806_;
goto v_resetjp_5661_;
}
else
{
lean_inc(v_fst_5660_);
lean_dec(v_b_5643_);
v___x_5662_ = lean_box(0);
v_isShared_5663_ = v_isSharedCheck_5806_;
goto v_resetjp_5661_;
}
v_resetjp_5661_:
{
lean_object* v_fst_5664_; lean_object* v___x_5666_; uint8_t v_isShared_5667_; uint8_t v_isSharedCheck_5804_; 
v_fst_5664_ = lean_ctor_get(v_snd_5656_, 0);
v_isSharedCheck_5804_ = !lean_is_exclusive(v_snd_5656_);
if (v_isSharedCheck_5804_ == 0)
{
lean_object* v_unused_5805_; 
v_unused_5805_ = lean_ctor_get(v_snd_5656_, 1);
lean_dec(v_unused_5805_);
v___x_5666_ = v_snd_5656_;
v_isShared_5667_ = v_isSharedCheck_5804_;
goto v_resetjp_5665_;
}
else
{
lean_inc(v_fst_5664_);
lean_dec(v_snd_5656_);
v___x_5666_ = lean_box(0);
v_isShared_5667_ = v_isSharedCheck_5804_;
goto v_resetjp_5665_;
}
v_resetjp_5665_:
{
lean_object* v_fst_5668_; lean_object* v___x_5670_; uint8_t v_isShared_5671_; uint8_t v_isSharedCheck_5802_; 
v_fst_5668_ = lean_ctor_get(v_snd_5657_, 0);
v_isSharedCheck_5802_ = !lean_is_exclusive(v_snd_5657_);
if (v_isSharedCheck_5802_ == 0)
{
lean_object* v_unused_5803_; 
v_unused_5803_ = lean_ctor_get(v_snd_5657_, 1);
lean_dec(v_unused_5803_);
v___x_5670_ = v_snd_5657_;
v_isShared_5671_ = v_isSharedCheck_5802_;
goto v_resetjp_5669_;
}
else
{
lean_inc(v_fst_5668_);
lean_dec(v_snd_5657_);
v___x_5670_ = lean_box(0);
v_isShared_5671_ = v_isSharedCheck_5802_;
goto v_resetjp_5669_;
}
v_resetjp_5669_:
{
lean_object* v_fst_5672_; lean_object* v___x_5674_; uint8_t v_isShared_5675_; uint8_t v_isSharedCheck_5800_; 
v_fst_5672_ = lean_ctor_get(v_snd_5658_, 0);
v_isSharedCheck_5800_ = !lean_is_exclusive(v_snd_5658_);
if (v_isSharedCheck_5800_ == 0)
{
lean_object* v_unused_5801_; 
v_unused_5801_ = lean_ctor_get(v_snd_5658_, 1);
lean_dec(v_unused_5801_);
v___x_5674_ = v_snd_5658_;
v_isShared_5675_ = v_isSharedCheck_5800_;
goto v_resetjp_5673_;
}
else
{
lean_inc(v_fst_5672_);
lean_dec(v_snd_5658_);
v___x_5674_ = lean_box(0);
v_isShared_5675_ = v_isSharedCheck_5800_;
goto v_resetjp_5673_;
}
v_resetjp_5673_:
{
lean_object* v_array_5676_; lean_object* v_start_5677_; lean_object* v_stop_5678_; uint8_t v___x_5679_; 
v_array_5676_ = lean_ctor_get(v_snd_5659_, 0);
v_start_5677_ = lean_ctor_get(v_snd_5659_, 1);
v_stop_5678_ = lean_ctor_get(v_snd_5659_, 2);
v___x_5679_ = lean_nat_dec_lt(v_start_5677_, v_stop_5678_);
if (v___x_5679_ == 0)
{
lean_object* v___x_5681_; 
if (v_isShared_5675_ == 0)
{
v___x_5681_ = v___x_5674_;
goto v_reusejp_5680_;
}
else
{
lean_object* v_reuseFailAlloc_5692_; 
v_reuseFailAlloc_5692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5692_, 0, v_fst_5672_);
lean_ctor_set(v_reuseFailAlloc_5692_, 1, v_snd_5659_);
v___x_5681_ = v_reuseFailAlloc_5692_;
goto v_reusejp_5680_;
}
v_reusejp_5680_:
{
lean_object* v___x_5683_; 
if (v_isShared_5671_ == 0)
{
lean_ctor_set(v___x_5670_, 1, v___x_5681_);
v___x_5683_ = v___x_5670_;
goto v_reusejp_5682_;
}
else
{
lean_object* v_reuseFailAlloc_5691_; 
v_reuseFailAlloc_5691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5691_, 0, v_fst_5668_);
lean_ctor_set(v_reuseFailAlloc_5691_, 1, v___x_5681_);
v___x_5683_ = v_reuseFailAlloc_5691_;
goto v_reusejp_5682_;
}
v_reusejp_5682_:
{
lean_object* v___x_5685_; 
if (v_isShared_5667_ == 0)
{
lean_ctor_set(v___x_5666_, 1, v___x_5683_);
v___x_5685_ = v___x_5666_;
goto v_reusejp_5684_;
}
else
{
lean_object* v_reuseFailAlloc_5690_; 
v_reuseFailAlloc_5690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5690_, 0, v_fst_5664_);
lean_ctor_set(v_reuseFailAlloc_5690_, 1, v___x_5683_);
v___x_5685_ = v_reuseFailAlloc_5690_;
goto v_reusejp_5684_;
}
v_reusejp_5684_:
{
lean_object* v___x_5687_; 
if (v_isShared_5663_ == 0)
{
lean_ctor_set(v___x_5662_, 1, v___x_5685_);
v___x_5687_ = v___x_5662_;
goto v_reusejp_5686_;
}
else
{
lean_object* v_reuseFailAlloc_5689_; 
v_reuseFailAlloc_5689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5689_, 0, v_fst_5660_);
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
lean_object* v___x_5694_; uint8_t v_isShared_5695_; uint8_t v_isSharedCheck_5796_; 
lean_inc(v_stop_5678_);
lean_inc(v_start_5677_);
lean_inc_ref(v_array_5676_);
v_isSharedCheck_5796_ = !lean_is_exclusive(v_snd_5659_);
if (v_isSharedCheck_5796_ == 0)
{
lean_object* v_unused_5797_; lean_object* v_unused_5798_; lean_object* v_unused_5799_; 
v_unused_5797_ = lean_ctor_get(v_snd_5659_, 2);
lean_dec(v_unused_5797_);
v_unused_5798_ = lean_ctor_get(v_snd_5659_, 1);
lean_dec(v_unused_5798_);
v_unused_5799_ = lean_ctor_get(v_snd_5659_, 0);
lean_dec(v_unused_5799_);
v___x_5694_ = v_snd_5659_;
v_isShared_5695_ = v_isSharedCheck_5796_;
goto v_resetjp_5693_;
}
else
{
lean_dec(v_snd_5659_);
v___x_5694_ = lean_box(0);
v_isShared_5695_ = v_isSharedCheck_5796_;
goto v_resetjp_5693_;
}
v_resetjp_5693_:
{
lean_object* v_array_5696_; lean_object* v_start_5697_; lean_object* v_stop_5698_; lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5703_; 
v_array_5696_ = lean_ctor_get(v_fst_5672_, 0);
v_start_5697_ = lean_ctor_get(v_fst_5672_, 1);
v_stop_5698_ = lean_ctor_get(v_fst_5672_, 2);
v___x_5699_ = lean_array_fget(v_array_5676_, v_start_5677_);
v___x_5700_ = lean_unsigned_to_nat(1u);
v___x_5701_ = lean_nat_add(v_start_5677_, v___x_5700_);
lean_dec(v_start_5677_);
if (v_isShared_5695_ == 0)
{
lean_ctor_set(v___x_5694_, 1, v___x_5701_);
v___x_5703_ = v___x_5694_;
goto v_reusejp_5702_;
}
else
{
lean_object* v_reuseFailAlloc_5795_; 
v_reuseFailAlloc_5795_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5795_, 0, v_array_5676_);
lean_ctor_set(v_reuseFailAlloc_5795_, 1, v___x_5701_);
lean_ctor_set(v_reuseFailAlloc_5795_, 2, v_stop_5678_);
v___x_5703_ = v_reuseFailAlloc_5795_;
goto v_reusejp_5702_;
}
v_reusejp_5702_:
{
uint8_t v___x_5704_; 
v___x_5704_ = lean_nat_dec_lt(v_start_5697_, v_stop_5698_);
if (v___x_5704_ == 0)
{
lean_object* v___x_5706_; 
lean_dec(v___x_5699_);
if (v_isShared_5675_ == 0)
{
lean_ctor_set(v___x_5674_, 1, v___x_5703_);
v___x_5706_ = v___x_5674_;
goto v_reusejp_5705_;
}
else
{
lean_object* v_reuseFailAlloc_5717_; 
v_reuseFailAlloc_5717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5717_, 0, v_fst_5672_);
lean_ctor_set(v_reuseFailAlloc_5717_, 1, v___x_5703_);
v___x_5706_ = v_reuseFailAlloc_5717_;
goto v_reusejp_5705_;
}
v_reusejp_5705_:
{
lean_object* v___x_5708_; 
if (v_isShared_5671_ == 0)
{
lean_ctor_set(v___x_5670_, 1, v___x_5706_);
v___x_5708_ = v___x_5670_;
goto v_reusejp_5707_;
}
else
{
lean_object* v_reuseFailAlloc_5716_; 
v_reuseFailAlloc_5716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5716_, 0, v_fst_5668_);
lean_ctor_set(v_reuseFailAlloc_5716_, 1, v___x_5706_);
v___x_5708_ = v_reuseFailAlloc_5716_;
goto v_reusejp_5707_;
}
v_reusejp_5707_:
{
lean_object* v___x_5710_; 
if (v_isShared_5667_ == 0)
{
lean_ctor_set(v___x_5666_, 1, v___x_5708_);
v___x_5710_ = v___x_5666_;
goto v_reusejp_5709_;
}
else
{
lean_object* v_reuseFailAlloc_5715_; 
v_reuseFailAlloc_5715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5715_, 0, v_fst_5664_);
lean_ctor_set(v_reuseFailAlloc_5715_, 1, v___x_5708_);
v___x_5710_ = v_reuseFailAlloc_5715_;
goto v_reusejp_5709_;
}
v_reusejp_5709_:
{
lean_object* v___x_5712_; 
if (v_isShared_5663_ == 0)
{
lean_ctor_set(v___x_5662_, 1, v___x_5710_);
v___x_5712_ = v___x_5662_;
goto v_reusejp_5711_;
}
else
{
lean_object* v_reuseFailAlloc_5714_; 
v_reuseFailAlloc_5714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5714_, 0, v_fst_5660_);
lean_ctor_set(v_reuseFailAlloc_5714_, 1, v___x_5710_);
v___x_5712_ = v_reuseFailAlloc_5714_;
goto v_reusejp_5711_;
}
v_reusejp_5711_:
{
lean_object* v___x_5713_; 
v___x_5713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5713_, 0, v___x_5712_);
return v___x_5713_;
}
}
}
}
}
else
{
lean_object* v___x_5719_; uint8_t v_isShared_5720_; uint8_t v_isSharedCheck_5791_; 
lean_inc(v_stop_5698_);
lean_inc(v_start_5697_);
lean_inc_ref(v_array_5696_);
v_isSharedCheck_5791_ = !lean_is_exclusive(v_fst_5672_);
if (v_isSharedCheck_5791_ == 0)
{
lean_object* v_unused_5792_; lean_object* v_unused_5793_; lean_object* v_unused_5794_; 
v_unused_5792_ = lean_ctor_get(v_fst_5672_, 2);
lean_dec(v_unused_5792_);
v_unused_5793_ = lean_ctor_get(v_fst_5672_, 1);
lean_dec(v_unused_5793_);
v_unused_5794_ = lean_ctor_get(v_fst_5672_, 0);
lean_dec(v_unused_5794_);
v___x_5719_ = v_fst_5672_;
v_isShared_5720_ = v_isSharedCheck_5791_;
goto v_resetjp_5718_;
}
else
{
lean_dec(v_fst_5672_);
v___x_5719_ = lean_box(0);
v_isShared_5720_ = v_isSharedCheck_5791_;
goto v_resetjp_5718_;
}
v_resetjp_5718_:
{
lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5724_; 
v___x_5721_ = lean_array_fget(v_array_5696_, v_start_5697_);
v___x_5722_ = lean_nat_add(v_start_5697_, v___x_5700_);
lean_dec(v_start_5697_);
if (v_isShared_5720_ == 0)
{
lean_ctor_set(v___x_5719_, 1, v___x_5722_);
v___x_5724_ = v___x_5719_;
goto v_reusejp_5723_;
}
else
{
lean_object* v_reuseFailAlloc_5790_; 
v_reuseFailAlloc_5790_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5790_, 0, v_array_5696_);
lean_ctor_set(v_reuseFailAlloc_5790_, 1, v___x_5722_);
lean_ctor_set(v_reuseFailAlloc_5790_, 2, v_stop_5698_);
v___x_5724_ = v_reuseFailAlloc_5790_;
goto v_reusejp_5723_;
}
v_reusejp_5723_:
{
if (v_addEqualities_5639_ == 0)
{
lean_dec(v___x_5721_);
goto v___jp_5725_;
}
else
{
if (lean_obj_tag(v___x_5699_) == 0)
{
lean_object* v_a_5741_; lean_object* v___x_5742_; 
lean_del_object(v___x_5674_);
lean_del_object(v___x_5670_);
lean_del_object(v___x_5666_);
lean_del_object(v___x_5662_);
v_a_5741_ = lean_array_uget_borrowed(v_as_5640_, v_i_5642_);
lean_inc(v_a_5741_);
v___x_5742_ = l_Lean_Meta_isProof(v_a_5741_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_);
if (lean_obj_tag(v___x_5742_) == 0)
{
lean_object* v_a_5743_; uint8_t v___x_5744_; 
v_a_5743_ = lean_ctor_get(v___x_5742_, 0);
lean_inc(v_a_5743_);
lean_dec_ref_known(v___x_5742_, 1);
v___x_5744_ = lean_unbox(v_a_5743_);
lean_dec(v_a_5743_);
if (v___x_5744_ == 0)
{
lean_object* v___x_5745_; 
lean_inc(v_a_5741_);
v___x_5745_ = l_Lean_Meta_mkEqHEq(v___x_5721_, v_a_5741_, v___y_5644_, v___y_5645_, v___y_5646_, v___y_5647_);
if (lean_obj_tag(v___x_5745_) == 0)
{
lean_object* v_a_5746_; lean_object* v___x_5747_; 
v_a_5746_ = lean_ctor_get(v___x_5745_, 0);
lean_inc_n(v_a_5746_, 2);
lean_dec_ref_known(v___x_5745_, 1);
v___x_5747_ = l_Lean_mkArrow(v_a_5746_, v_fst_5660_, v___y_5646_, v___y_5647_);
if (lean_obj_tag(v___x_5747_) == 0)
{
lean_object* v_a_5748_; uint8_t v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; 
v_a_5748_ = lean_ctor_get(v___x_5747_, 0);
lean_inc(v_a_5748_);
lean_dec_ref_known(v___x_5747_, 1);
v___x_5749_ = l_Lean_Expr_isHEq(v_a_5746_);
lean_dec(v_a_5746_);
v___x_5750_ = lean_box(v___x_5749_);
v___x_5751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5751_, 0, v___x_5750_);
v___x_5752_ = lean_array_push(v_fst_5664_, v___x_5751_);
v___x_5753_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7___closed__0));
v___x_5754_ = lean_array_push(v_fst_5668_, v___x_5753_);
v___x_5755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5755_, 0, v___x_5724_);
lean_ctor_set(v___x_5755_, 1, v___x_5703_);
v___x_5756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5756_, 0, v___x_5754_);
lean_ctor_set(v___x_5756_, 1, v___x_5755_);
v___x_5757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5757_, 0, v___x_5752_);
lean_ctor_set(v___x_5757_, 1, v___x_5756_);
v___x_5758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5758_, 0, v_a_5748_);
lean_ctor_set(v___x_5758_, 1, v___x_5757_);
v_a_5650_ = v___x_5758_;
goto v___jp_5649_;
}
else
{
lean_object* v_a_5759_; lean_object* v___x_5761_; uint8_t v_isShared_5762_; uint8_t v_isSharedCheck_5766_; 
lean_dec(v_a_5746_);
lean_dec_ref(v___x_5724_);
lean_dec_ref(v___x_5703_);
lean_dec(v_fst_5668_);
lean_dec(v_fst_5664_);
v_a_5759_ = lean_ctor_get(v___x_5747_, 0);
v_isSharedCheck_5766_ = !lean_is_exclusive(v___x_5747_);
if (v_isSharedCheck_5766_ == 0)
{
v___x_5761_ = v___x_5747_;
v_isShared_5762_ = v_isSharedCheck_5766_;
goto v_resetjp_5760_;
}
else
{
lean_inc(v_a_5759_);
lean_dec(v___x_5747_);
v___x_5761_ = lean_box(0);
v_isShared_5762_ = v_isSharedCheck_5766_;
goto v_resetjp_5760_;
}
v_resetjp_5760_:
{
lean_object* v___x_5764_; 
if (v_isShared_5762_ == 0)
{
v___x_5764_ = v___x_5761_;
goto v_reusejp_5763_;
}
else
{
lean_object* v_reuseFailAlloc_5765_; 
v_reuseFailAlloc_5765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5765_, 0, v_a_5759_);
v___x_5764_ = v_reuseFailAlloc_5765_;
goto v_reusejp_5763_;
}
v_reusejp_5763_:
{
return v___x_5764_;
}
}
}
}
else
{
lean_object* v_a_5767_; lean_object* v___x_5769_; uint8_t v_isShared_5770_; uint8_t v_isSharedCheck_5774_; 
lean_dec_ref(v___x_5724_);
lean_dec_ref(v___x_5703_);
lean_dec(v_fst_5668_);
lean_dec(v_fst_5664_);
lean_dec(v_fst_5660_);
v_a_5767_ = lean_ctor_get(v___x_5745_, 0);
v_isSharedCheck_5774_ = !lean_is_exclusive(v___x_5745_);
if (v_isSharedCheck_5774_ == 0)
{
v___x_5769_ = v___x_5745_;
v_isShared_5770_ = v_isSharedCheck_5774_;
goto v_resetjp_5768_;
}
else
{
lean_inc(v_a_5767_);
lean_dec(v___x_5745_);
v___x_5769_ = lean_box(0);
v_isShared_5770_ = v_isSharedCheck_5774_;
goto v_resetjp_5768_;
}
v_resetjp_5768_:
{
lean_object* v___x_5772_; 
if (v_isShared_5770_ == 0)
{
v___x_5772_ = v___x_5769_;
goto v_reusejp_5771_;
}
else
{
lean_object* v_reuseFailAlloc_5773_; 
v_reuseFailAlloc_5773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5773_, 0, v_a_5767_);
v___x_5772_ = v_reuseFailAlloc_5773_;
goto v_reusejp_5771_;
}
v_reusejp_5771_:
{
return v___x_5772_;
}
}
}
}
else
{
lean_object* v___x_5775_; lean_object* v___x_5776_; lean_object* v___x_5777_; lean_object* v___x_5778_; lean_object* v___x_5779_; lean_object* v___x_5780_; lean_object* v___x_5781_; 
lean_dec(v___x_5721_);
v___x_5775_ = lean_box(0);
v___x_5776_ = lean_array_push(v_fst_5664_, v___x_5775_);
v___x_5777_ = lean_array_push(v_fst_5668_, v___x_5699_);
v___x_5778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5778_, 0, v___x_5724_);
lean_ctor_set(v___x_5778_, 1, v___x_5703_);
v___x_5779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5779_, 0, v___x_5777_);
lean_ctor_set(v___x_5779_, 1, v___x_5778_);
v___x_5780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5780_, 0, v___x_5776_);
lean_ctor_set(v___x_5780_, 1, v___x_5779_);
v___x_5781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5781_, 0, v_fst_5660_);
lean_ctor_set(v___x_5781_, 1, v___x_5780_);
v_a_5650_ = v___x_5781_;
goto v___jp_5649_;
}
}
else
{
lean_object* v_a_5782_; lean_object* v___x_5784_; uint8_t v_isShared_5785_; uint8_t v_isSharedCheck_5789_; 
lean_dec_ref(v___x_5724_);
lean_dec(v___x_5721_);
lean_dec_ref(v___x_5703_);
lean_dec(v_fst_5668_);
lean_dec(v_fst_5664_);
lean_dec(v_fst_5660_);
v_a_5782_ = lean_ctor_get(v___x_5742_, 0);
v_isSharedCheck_5789_ = !lean_is_exclusive(v___x_5742_);
if (v_isSharedCheck_5789_ == 0)
{
v___x_5784_ = v___x_5742_;
v_isShared_5785_ = v_isSharedCheck_5789_;
goto v_resetjp_5783_;
}
else
{
lean_inc(v_a_5782_);
lean_dec(v___x_5742_);
v___x_5784_ = lean_box(0);
v_isShared_5785_ = v_isSharedCheck_5789_;
goto v_resetjp_5783_;
}
v_resetjp_5783_:
{
lean_object* v___x_5787_; 
if (v_isShared_5785_ == 0)
{
v___x_5787_ = v___x_5784_;
goto v_reusejp_5786_;
}
else
{
lean_object* v_reuseFailAlloc_5788_; 
v_reuseFailAlloc_5788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5788_, 0, v_a_5782_);
v___x_5787_ = v_reuseFailAlloc_5788_;
goto v_reusejp_5786_;
}
v_reusejp_5786_:
{
return v___x_5787_;
}
}
}
}
else
{
lean_dec(v___x_5721_);
goto v___jp_5725_;
}
}
v___jp_5725_:
{
lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5730_; 
v___x_5726_ = lean_box(0);
v___x_5727_ = lean_array_push(v_fst_5664_, v___x_5726_);
v___x_5728_ = lean_array_push(v_fst_5668_, v___x_5699_);
if (v_isShared_5675_ == 0)
{
lean_ctor_set(v___x_5674_, 1, v___x_5703_);
lean_ctor_set(v___x_5674_, 0, v___x_5724_);
v___x_5730_ = v___x_5674_;
goto v_reusejp_5729_;
}
else
{
lean_object* v_reuseFailAlloc_5740_; 
v_reuseFailAlloc_5740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5740_, 0, v___x_5724_);
lean_ctor_set(v_reuseFailAlloc_5740_, 1, v___x_5703_);
v___x_5730_ = v_reuseFailAlloc_5740_;
goto v_reusejp_5729_;
}
v_reusejp_5729_:
{
lean_object* v___x_5732_; 
if (v_isShared_5671_ == 0)
{
lean_ctor_set(v___x_5670_, 1, v___x_5730_);
lean_ctor_set(v___x_5670_, 0, v___x_5728_);
v___x_5732_ = v___x_5670_;
goto v_reusejp_5731_;
}
else
{
lean_object* v_reuseFailAlloc_5739_; 
v_reuseFailAlloc_5739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5739_, 0, v___x_5728_);
lean_ctor_set(v_reuseFailAlloc_5739_, 1, v___x_5730_);
v___x_5732_ = v_reuseFailAlloc_5739_;
goto v_reusejp_5731_;
}
v_reusejp_5731_:
{
lean_object* v___x_5734_; 
if (v_isShared_5667_ == 0)
{
lean_ctor_set(v___x_5666_, 1, v___x_5732_);
lean_ctor_set(v___x_5666_, 0, v___x_5727_);
v___x_5734_ = v___x_5666_;
goto v_reusejp_5733_;
}
else
{
lean_object* v_reuseFailAlloc_5738_; 
v_reuseFailAlloc_5738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5738_, 0, v___x_5727_);
lean_ctor_set(v_reuseFailAlloc_5738_, 1, v___x_5732_);
v___x_5734_ = v_reuseFailAlloc_5738_;
goto v_reusejp_5733_;
}
v_reusejp_5733_:
{
lean_object* v___x_5736_; 
if (v_isShared_5663_ == 0)
{
lean_ctor_set(v___x_5662_, 1, v___x_5734_);
v___x_5736_ = v___x_5662_;
goto v_reusejp_5735_;
}
else
{
lean_object* v_reuseFailAlloc_5737_; 
v_reuseFailAlloc_5737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5737_, 0, v_fst_5660_);
lean_ctor_set(v_reuseFailAlloc_5737_, 1, v___x_5734_);
v___x_5736_ = v_reuseFailAlloc_5737_;
goto v_reusejp_5735_;
}
v_reusejp_5735_:
{
v_a_5650_ = v___x_5736_;
goto v___jp_5649_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_5649_:
{
size_t v___x_5651_; size_t v___x_5652_; 
v___x_5651_ = ((size_t)1ULL);
v___x_5652_ = lean_usize_add(v_i_5642_, v___x_5651_);
v_i_5642_ = v___x_5652_;
v_b_5643_ = v_a_5650_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7___boxed(lean_object* v_addEqualities_5808_, lean_object* v_as_5809_, lean_object* v_sz_5810_, lean_object* v_i_5811_, lean_object* v_b_5812_, lean_object* v___y_5813_, lean_object* v___y_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_, lean_object* v___y_5817_){
_start:
{
uint8_t v_addEqualities_boxed_5818_; size_t v_sz_boxed_5819_; size_t v_i_boxed_5820_; lean_object* v_res_5821_; 
v_addEqualities_boxed_5818_ = lean_unbox(v_addEqualities_5808_);
v_sz_boxed_5819_ = lean_unbox_usize(v_sz_5810_);
lean_dec(v_sz_5810_);
v_i_boxed_5820_ = lean_unbox_usize(v_i_5811_);
lean_dec(v_i_5811_);
v_res_5821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(v_addEqualities_boxed_5818_, v_as_5809_, v_sz_boxed_5819_, v_i_boxed_5820_, v_b_5812_, v___y_5813_, v___y_5814_, v___y_5815_, v___y_5816_);
lean_dec(v___y_5816_);
lean_dec_ref(v___y_5815_);
lean_dec(v___y_5814_);
lean_dec_ref(v___y_5813_);
lean_dec_ref(v_as_5809_);
return v_res_5821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(lean_object* v_onMotive_5822_, lean_object* v_toMatcherInfo_5823_, lean_object* v_a_5824_, uint8_t v_addEqualities_5825_, size_t v___x_5826_, lean_object* v_discrs_5827_, lean_object* v_motiveArgs_5828_, lean_object* v_motiveBody_5829_, lean_object* v___y_5830_, lean_object* v___y_5831_, lean_object* v___y_5832_, lean_object* v___y_5833_){
_start:
{
lean_object* v___x_5927_; lean_object* v___x_5928_; uint8_t v___x_5929_; 
v___x_5927_ = lean_array_get_size(v_motiveArgs_5828_);
v___x_5928_ = lean_array_get_size(v_discrs_5827_);
v___x_5929_ = lean_nat_dec_eq(v___x_5927_, v___x_5928_);
if (v___x_5929_ == 0)
{
lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v_a_5938_; lean_object* v___x_5940_; uint8_t v_isShared_5941_; uint8_t v_isSharedCheck_5945_; 
lean_dec_ref(v_motiveBody_5829_);
lean_dec_ref(v_motiveArgs_5828_);
lean_dec_ref(v_a_5824_);
lean_dec_ref(v_toMatcherInfo_5823_);
lean_dec_ref(v_onMotive_5822_);
v___x_5930_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_5931_ = l_Nat_reprFast(v___x_5928_);
v___x_5932_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5932_, 0, v___x_5931_);
v___x_5933_ = l_Lean_MessageData_ofFormat(v___x_5932_);
v___x_5934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5934_, 0, v___x_5930_);
lean_ctor_set(v___x_5934_, 1, v___x_5933_);
v___x_5935_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_5936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5936_, 0, v___x_5934_);
lean_ctor_set(v___x_5936_, 1, v___x_5935_);
v___x_5937_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_5936_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_);
v_a_5938_ = lean_ctor_get(v___x_5937_, 0);
v_isSharedCheck_5945_ = !lean_is_exclusive(v___x_5937_);
if (v_isSharedCheck_5945_ == 0)
{
v___x_5940_ = v___x_5937_;
v_isShared_5941_ = v_isSharedCheck_5945_;
goto v_resetjp_5939_;
}
else
{
lean_inc(v_a_5938_);
lean_dec(v___x_5937_);
v___x_5940_ = lean_box(0);
v_isShared_5941_ = v_isSharedCheck_5945_;
goto v_resetjp_5939_;
}
v_resetjp_5939_:
{
lean_object* v___x_5943_; 
if (v_isShared_5941_ == 0)
{
v___x_5943_ = v___x_5940_;
goto v_reusejp_5942_;
}
else
{
lean_object* v_reuseFailAlloc_5944_; 
v_reuseFailAlloc_5944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5944_, 0, v_a_5938_);
v___x_5943_ = v_reuseFailAlloc_5944_;
goto v_reusejp_5942_;
}
v_reusejp_5942_:
{
return v___x_5943_;
}
}
}
else
{
goto v___jp_5835_;
}
v___jp_5835_:
{
lean_object* v___x_5836_; 
lean_inc(v___y_5833_);
lean_inc_ref(v___y_5832_);
lean_inc(v___y_5831_);
lean_inc_ref(v___y_5830_);
lean_inc_ref(v_motiveArgs_5828_);
v___x_5836_ = lean_apply_7(v_onMotive_5822_, v_motiveArgs_5828_, v_motiveBody_5829_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_, lean_box(0));
if (lean_obj_tag(v___x_5836_) == 0)
{
lean_object* v_a_5837_; lean_object* v_discrInfos_5838_; lean_object* v___x_5839_; lean_object* v_addHEqualities_5840_; lean_object* v___x_5841_; lean_object* v___x_5842_; lean_object* v___x_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; lean_object* v___x_5848_; size_t v_sz_5849_; lean_object* v___x_5850_; 
v_a_5837_ = lean_ctor_get(v___x_5836_, 0);
lean_inc(v_a_5837_);
lean_dec_ref_known(v___x_5836_, 1);
v_discrInfos_5838_ = lean_ctor_get(v_toMatcherInfo_5823_, 4);
lean_inc_ref(v_discrInfos_5838_);
lean_dec_ref(v_toMatcherInfo_5823_);
v___x_5839_ = lean_unsigned_to_nat(0u);
v_addHEqualities_5840_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___closed__0));
v___x_5841_ = lean_array_get_size(v_a_5824_);
v___x_5842_ = l_Array_toSubarray___redArg(v_a_5824_, v___x_5839_, v___x_5841_);
v___x_5843_ = lean_array_get_size(v_discrInfos_5838_);
v___x_5844_ = l_Array_toSubarray___redArg(v_discrInfos_5838_, v___x_5839_, v___x_5843_);
v___x_5845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5845_, 0, v___x_5842_);
lean_ctor_set(v___x_5845_, 1, v___x_5844_);
v___x_5846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5846_, 0, v_addHEqualities_5840_);
lean_ctor_set(v___x_5846_, 1, v___x_5845_);
v___x_5847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5847_, 0, v_addHEqualities_5840_);
lean_ctor_set(v___x_5847_, 1, v___x_5846_);
v___x_5848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5848_, 0, v_a_5837_);
lean_ctor_set(v___x_5848_, 1, v___x_5847_);
v_sz_5849_ = lean_array_size(v_motiveArgs_5828_);
v___x_5850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(v_addEqualities_5825_, v_motiveArgs_5828_, v_sz_5849_, v___x_5826_, v___x_5848_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_);
if (lean_obj_tag(v___x_5850_) == 0)
{
lean_object* v_a_5851_; lean_object* v_snd_5852_; lean_object* v_snd_5853_; lean_object* v_fst_5854_; lean_object* v___x_5856_; uint8_t v_isShared_5857_; uint8_t v_isSharedCheck_5909_; 
v_a_5851_ = lean_ctor_get(v___x_5850_, 0);
lean_inc(v_a_5851_);
lean_dec_ref_known(v___x_5850_, 1);
v_snd_5852_ = lean_ctor_get(v_a_5851_, 1);
lean_inc(v_snd_5852_);
v_snd_5853_ = lean_ctor_get(v_snd_5852_, 1);
lean_inc(v_snd_5853_);
v_fst_5854_ = lean_ctor_get(v_a_5851_, 0);
v_isSharedCheck_5909_ = !lean_is_exclusive(v_a_5851_);
if (v_isSharedCheck_5909_ == 0)
{
lean_object* v_unused_5910_; 
v_unused_5910_ = lean_ctor_get(v_a_5851_, 1);
lean_dec(v_unused_5910_);
v___x_5856_ = v_a_5851_;
v_isShared_5857_ = v_isSharedCheck_5909_;
goto v_resetjp_5855_;
}
else
{
lean_inc(v_fst_5854_);
lean_dec(v_a_5851_);
v___x_5856_ = lean_box(0);
v_isShared_5857_ = v_isSharedCheck_5909_;
goto v_resetjp_5855_;
}
v_resetjp_5855_:
{
lean_object* v_fst_5858_; lean_object* v___x_5860_; uint8_t v_isShared_5861_; uint8_t v_isSharedCheck_5907_; 
v_fst_5858_ = lean_ctor_get(v_snd_5852_, 0);
v_isSharedCheck_5907_ = !lean_is_exclusive(v_snd_5852_);
if (v_isSharedCheck_5907_ == 0)
{
lean_object* v_unused_5908_; 
v_unused_5908_ = lean_ctor_get(v_snd_5852_, 1);
lean_dec(v_unused_5908_);
v___x_5860_ = v_snd_5852_;
v_isShared_5861_ = v_isSharedCheck_5907_;
goto v_resetjp_5859_;
}
else
{
lean_inc(v_fst_5858_);
lean_dec(v_snd_5852_);
v___x_5860_ = lean_box(0);
v_isShared_5861_ = v_isSharedCheck_5907_;
goto v_resetjp_5859_;
}
v_resetjp_5859_:
{
lean_object* v_fst_5862_; lean_object* v___x_5864_; uint8_t v_isShared_5865_; uint8_t v_isSharedCheck_5905_; 
v_fst_5862_ = lean_ctor_get(v_snd_5853_, 0);
v_isSharedCheck_5905_ = !lean_is_exclusive(v_snd_5853_);
if (v_isSharedCheck_5905_ == 0)
{
lean_object* v_unused_5906_; 
v_unused_5906_ = lean_ctor_get(v_snd_5853_, 1);
lean_dec(v_unused_5906_);
v___x_5864_ = v_snd_5853_;
v_isShared_5865_ = v_isSharedCheck_5905_;
goto v_resetjp_5863_;
}
else
{
lean_inc(v_fst_5862_);
lean_dec(v_snd_5853_);
v___x_5864_ = lean_box(0);
v_isShared_5865_ = v_isSharedCheck_5905_;
goto v_resetjp_5863_;
}
v_resetjp_5863_:
{
uint8_t v___x_5866_; uint8_t v___x_5867_; uint8_t v___x_5868_; lean_object* v___x_5869_; 
v___x_5866_ = 0;
v___x_5867_ = 1;
v___x_5868_ = 1;
lean_inc(v_fst_5854_);
v___x_5869_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_5828_, v_fst_5854_, v___x_5866_, v___x_5867_, v___x_5866_, v___x_5867_, v___x_5868_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_);
lean_dec_ref(v_motiveArgs_5828_);
if (lean_obj_tag(v___x_5869_) == 0)
{
lean_object* v_a_5870_; lean_object* v___x_5871_; 
v_a_5870_ = lean_ctor_get(v___x_5869_, 0);
lean_inc(v_a_5870_);
lean_dec_ref_known(v___x_5869_, 1);
v___x_5871_ = l_Lean_Meta_getLevel(v_fst_5854_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_);
if (lean_obj_tag(v___x_5871_) == 0)
{
lean_object* v_a_5872_; lean_object* v___x_5874_; uint8_t v_isShared_5875_; uint8_t v_isSharedCheck_5888_; 
v_a_5872_ = lean_ctor_get(v___x_5871_, 0);
v_isSharedCheck_5888_ = !lean_is_exclusive(v___x_5871_);
if (v_isSharedCheck_5888_ == 0)
{
v___x_5874_ = v___x_5871_;
v_isShared_5875_ = v_isSharedCheck_5888_;
goto v_resetjp_5873_;
}
else
{
lean_inc(v_a_5872_);
lean_dec(v___x_5871_);
v___x_5874_ = lean_box(0);
v_isShared_5875_ = v_isSharedCheck_5888_;
goto v_resetjp_5873_;
}
v_resetjp_5873_:
{
lean_object* v___x_5877_; 
if (v_isShared_5865_ == 0)
{
lean_ctor_set(v___x_5864_, 1, v_fst_5862_);
lean_ctor_set(v___x_5864_, 0, v_fst_5858_);
v___x_5877_ = v___x_5864_;
goto v_reusejp_5876_;
}
else
{
lean_object* v_reuseFailAlloc_5887_; 
v_reuseFailAlloc_5887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5887_, 0, v_fst_5858_);
lean_ctor_set(v_reuseFailAlloc_5887_, 1, v_fst_5862_);
v___x_5877_ = v_reuseFailAlloc_5887_;
goto v_reusejp_5876_;
}
v_reusejp_5876_:
{
lean_object* v___x_5879_; 
if (v_isShared_5861_ == 0)
{
lean_ctor_set(v___x_5860_, 1, v___x_5877_);
lean_ctor_set(v___x_5860_, 0, v_a_5872_);
v___x_5879_ = v___x_5860_;
goto v_reusejp_5878_;
}
else
{
lean_object* v_reuseFailAlloc_5886_; 
v_reuseFailAlloc_5886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5886_, 0, v_a_5872_);
lean_ctor_set(v_reuseFailAlloc_5886_, 1, v___x_5877_);
v___x_5879_ = v_reuseFailAlloc_5886_;
goto v_reusejp_5878_;
}
v_reusejp_5878_:
{
lean_object* v___x_5881_; 
if (v_isShared_5857_ == 0)
{
lean_ctor_set(v___x_5856_, 1, v___x_5879_);
lean_ctor_set(v___x_5856_, 0, v_a_5870_);
v___x_5881_ = v___x_5856_;
goto v_reusejp_5880_;
}
else
{
lean_object* v_reuseFailAlloc_5885_; 
v_reuseFailAlloc_5885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5885_, 0, v_a_5870_);
lean_ctor_set(v_reuseFailAlloc_5885_, 1, v___x_5879_);
v___x_5881_ = v_reuseFailAlloc_5885_;
goto v_reusejp_5880_;
}
v_reusejp_5880_:
{
lean_object* v___x_5883_; 
if (v_isShared_5875_ == 0)
{
lean_ctor_set(v___x_5874_, 0, v___x_5881_);
v___x_5883_ = v___x_5874_;
goto v_reusejp_5882_;
}
else
{
lean_object* v_reuseFailAlloc_5884_; 
v_reuseFailAlloc_5884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5884_, 0, v___x_5881_);
v___x_5883_ = v_reuseFailAlloc_5884_;
goto v_reusejp_5882_;
}
v_reusejp_5882_:
{
return v___x_5883_;
}
}
}
}
}
}
else
{
lean_object* v_a_5889_; lean_object* v___x_5891_; uint8_t v_isShared_5892_; uint8_t v_isSharedCheck_5896_; 
lean_dec(v_a_5870_);
lean_del_object(v___x_5864_);
lean_dec(v_fst_5862_);
lean_del_object(v___x_5860_);
lean_dec(v_fst_5858_);
lean_del_object(v___x_5856_);
v_a_5889_ = lean_ctor_get(v___x_5871_, 0);
v_isSharedCheck_5896_ = !lean_is_exclusive(v___x_5871_);
if (v_isSharedCheck_5896_ == 0)
{
v___x_5891_ = v___x_5871_;
v_isShared_5892_ = v_isSharedCheck_5896_;
goto v_resetjp_5890_;
}
else
{
lean_inc(v_a_5889_);
lean_dec(v___x_5871_);
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
lean_del_object(v___x_5864_);
lean_dec(v_fst_5862_);
lean_del_object(v___x_5860_);
lean_dec(v_fst_5858_);
lean_del_object(v___x_5856_);
lean_dec(v_fst_5854_);
v_a_5897_ = lean_ctor_get(v___x_5869_, 0);
v_isSharedCheck_5904_ = !lean_is_exclusive(v___x_5869_);
if (v_isSharedCheck_5904_ == 0)
{
v___x_5899_ = v___x_5869_;
v_isShared_5900_ = v_isSharedCheck_5904_;
goto v_resetjp_5898_;
}
else
{
lean_inc(v_a_5897_);
lean_dec(v___x_5869_);
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
}
else
{
lean_object* v_a_5911_; lean_object* v___x_5913_; uint8_t v_isShared_5914_; uint8_t v_isSharedCheck_5918_; 
lean_dec_ref(v_motiveArgs_5828_);
v_a_5911_ = lean_ctor_get(v___x_5850_, 0);
v_isSharedCheck_5918_ = !lean_is_exclusive(v___x_5850_);
if (v_isSharedCheck_5918_ == 0)
{
v___x_5913_ = v___x_5850_;
v_isShared_5914_ = v_isSharedCheck_5918_;
goto v_resetjp_5912_;
}
else
{
lean_inc(v_a_5911_);
lean_dec(v___x_5850_);
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
}
else
{
lean_object* v_a_5919_; lean_object* v___x_5921_; uint8_t v_isShared_5922_; uint8_t v_isSharedCheck_5926_; 
lean_dec_ref(v_motiveArgs_5828_);
lean_dec_ref(v_a_5824_);
lean_dec_ref(v_toMatcherInfo_5823_);
v_a_5919_ = lean_ctor_get(v___x_5836_, 0);
v_isSharedCheck_5926_ = !lean_is_exclusive(v___x_5836_);
if (v_isSharedCheck_5926_ == 0)
{
v___x_5921_ = v___x_5836_;
v_isShared_5922_ = v_isSharedCheck_5926_;
goto v_resetjp_5920_;
}
else
{
lean_inc(v_a_5919_);
lean_dec(v___x_5836_);
v___x_5921_ = lean_box(0);
v_isShared_5922_ = v_isSharedCheck_5926_;
goto v_resetjp_5920_;
}
v_resetjp_5920_:
{
lean_object* v___x_5924_; 
if (v_isShared_5922_ == 0)
{
v___x_5924_ = v___x_5921_;
goto v_reusejp_5923_;
}
else
{
lean_object* v_reuseFailAlloc_5925_; 
v_reuseFailAlloc_5925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5925_, 0, v_a_5919_);
v___x_5924_ = v_reuseFailAlloc_5925_;
goto v_reusejp_5923_;
}
v_reusejp_5923_:
{
return v___x_5924_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed(lean_object* v_onMotive_5946_, lean_object* v_toMatcherInfo_5947_, lean_object* v_a_5948_, lean_object* v_addEqualities_5949_, lean_object* v___x_5950_, lean_object* v_discrs_5951_, lean_object* v_motiveArgs_5952_, lean_object* v_motiveBody_5953_, lean_object* v___y_5954_, lean_object* v___y_5955_, lean_object* v___y_5956_, lean_object* v___y_5957_, lean_object* v___y_5958_){
_start:
{
uint8_t v_addEqualities_boxed_5959_; size_t v___x_34455__boxed_5960_; lean_object* v_res_5961_; 
v_addEqualities_boxed_5959_ = lean_unbox(v_addEqualities_5949_);
v___x_34455__boxed_5960_ = lean_unbox_usize(v___x_5950_);
lean_dec(v___x_5950_);
v_res_5961_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(v_onMotive_5946_, v_toMatcherInfo_5947_, v_a_5948_, v_addEqualities_boxed_5959_, v___x_34455__boxed_5960_, v_discrs_5951_, v_motiveArgs_5952_, v_motiveBody_5953_, v___y_5954_, v___y_5955_, v___y_5956_, v___y_5957_);
lean_dec(v___y_5957_);
lean_dec_ref(v___y_5956_);
lean_dec(v___y_5955_);
lean_dec_ref(v___y_5954_);
lean_dec_ref(v_discrs_5951_);
return v_res_5961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(lean_object* v_as_5962_, size_t v_sz_5963_, size_t v_i_5964_, lean_object* v_b_5965_, lean_object* v___y_5966_, lean_object* v___y_5967_, lean_object* v___y_5968_, lean_object* v___y_5969_){
_start:
{
lean_object* v_a_5972_; uint8_t v___x_5976_; 
v___x_5976_ = lean_usize_dec_lt(v_i_5964_, v_sz_5963_);
if (v___x_5976_ == 0)
{
lean_object* v___x_5977_; 
v___x_5977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5977_, 0, v_b_5965_);
return v___x_5977_;
}
else
{
lean_object* v_snd_5978_; lean_object* v_snd_5979_; lean_object* v_fst_5980_; lean_object* v___x_5982_; uint8_t v_isShared_5983_; uint8_t v_isSharedCheck_6040_; 
v_snd_5978_ = lean_ctor_get(v_b_5965_, 1);
lean_inc(v_snd_5978_);
v_snd_5979_ = lean_ctor_get(v_snd_5978_, 1);
lean_inc(v_snd_5979_);
v_fst_5980_ = lean_ctor_get(v_b_5965_, 0);
v_isSharedCheck_6040_ = !lean_is_exclusive(v_b_5965_);
if (v_isSharedCheck_6040_ == 0)
{
lean_object* v_unused_6041_; 
v_unused_6041_ = lean_ctor_get(v_b_5965_, 1);
lean_dec(v_unused_6041_);
v___x_5982_ = v_b_5965_;
v_isShared_5983_ = v_isSharedCheck_6040_;
goto v_resetjp_5981_;
}
else
{
lean_inc(v_fst_5980_);
lean_dec(v_b_5965_);
v___x_5982_ = lean_box(0);
v_isShared_5983_ = v_isSharedCheck_6040_;
goto v_resetjp_5981_;
}
v_resetjp_5981_:
{
lean_object* v_fst_5984_; lean_object* v___x_5986_; uint8_t v_isShared_5987_; uint8_t v_isSharedCheck_6038_; 
v_fst_5984_ = lean_ctor_get(v_snd_5978_, 0);
v_isSharedCheck_6038_ = !lean_is_exclusive(v_snd_5978_);
if (v_isSharedCheck_6038_ == 0)
{
lean_object* v_unused_6039_; 
v_unused_6039_ = lean_ctor_get(v_snd_5978_, 1);
lean_dec(v_unused_6039_);
v___x_5986_ = v_snd_5978_;
v_isShared_5987_ = v_isSharedCheck_6038_;
goto v_resetjp_5985_;
}
else
{
lean_inc(v_fst_5984_);
lean_dec(v_snd_5978_);
v___x_5986_ = lean_box(0);
v_isShared_5987_ = v_isSharedCheck_6038_;
goto v_resetjp_5985_;
}
v_resetjp_5985_:
{
lean_object* v_array_5988_; lean_object* v_start_5989_; lean_object* v_stop_5990_; uint8_t v___x_5991_; 
v_array_5988_ = lean_ctor_get(v_snd_5979_, 0);
v_start_5989_ = lean_ctor_get(v_snd_5979_, 1);
v_stop_5990_ = lean_ctor_get(v_snd_5979_, 2);
v___x_5991_ = lean_nat_dec_lt(v_start_5989_, v_stop_5990_);
if (v___x_5991_ == 0)
{
lean_object* v___x_5993_; 
if (v_isShared_5987_ == 0)
{
v___x_5993_ = v___x_5986_;
goto v_reusejp_5992_;
}
else
{
lean_object* v_reuseFailAlloc_5998_; 
v_reuseFailAlloc_5998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5998_, 0, v_fst_5984_);
lean_ctor_set(v_reuseFailAlloc_5998_, 1, v_snd_5979_);
v___x_5993_ = v_reuseFailAlloc_5998_;
goto v_reusejp_5992_;
}
v_reusejp_5992_:
{
lean_object* v___x_5995_; 
if (v_isShared_5983_ == 0)
{
lean_ctor_set(v___x_5982_, 1, v___x_5993_);
v___x_5995_ = v___x_5982_;
goto v_reusejp_5994_;
}
else
{
lean_object* v_reuseFailAlloc_5997_; 
v_reuseFailAlloc_5997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5997_, 0, v_fst_5980_);
lean_ctor_set(v_reuseFailAlloc_5997_, 1, v___x_5993_);
v___x_5995_ = v_reuseFailAlloc_5997_;
goto v_reusejp_5994_;
}
v_reusejp_5994_:
{
lean_object* v___x_5996_; 
v___x_5996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5996_, 0, v___x_5995_);
return v___x_5996_;
}
}
}
else
{
lean_object* v___x_6000_; uint8_t v_isShared_6001_; uint8_t v_isSharedCheck_6034_; 
lean_inc(v_stop_5990_);
lean_inc(v_start_5989_);
lean_inc_ref(v_array_5988_);
v_isSharedCheck_6034_ = !lean_is_exclusive(v_snd_5979_);
if (v_isSharedCheck_6034_ == 0)
{
lean_object* v_unused_6035_; lean_object* v_unused_6036_; lean_object* v_unused_6037_; 
v_unused_6035_ = lean_ctor_get(v_snd_5979_, 2);
lean_dec(v_unused_6035_);
v_unused_6036_ = lean_ctor_get(v_snd_5979_, 1);
lean_dec(v_unused_6036_);
v_unused_6037_ = lean_ctor_get(v_snd_5979_, 0);
lean_dec(v_unused_6037_);
v___x_6000_ = v_snd_5979_;
v_isShared_6001_ = v_isSharedCheck_6034_;
goto v_resetjp_5999_;
}
else
{
lean_dec(v_snd_5979_);
v___x_6000_ = lean_box(0);
v_isShared_6001_ = v_isSharedCheck_6034_;
goto v_resetjp_5999_;
}
v_resetjp_5999_:
{
lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6006_; 
v___x_6002_ = lean_array_fget(v_array_5988_, v_start_5989_);
v___x_6003_ = lean_unsigned_to_nat(1u);
v___x_6004_ = lean_nat_add(v_start_5989_, v___x_6003_);
lean_dec(v_start_5989_);
if (v_isShared_6001_ == 0)
{
lean_ctor_set(v___x_6000_, 1, v___x_6004_);
v___x_6006_ = v___x_6000_;
goto v_reusejp_6005_;
}
else
{
lean_object* v_reuseFailAlloc_6033_; 
v_reuseFailAlloc_6033_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6033_, 0, v_array_5988_);
lean_ctor_set(v_reuseFailAlloc_6033_, 1, v___x_6004_);
lean_ctor_set(v_reuseFailAlloc_6033_, 2, v_stop_5990_);
v___x_6006_ = v_reuseFailAlloc_6033_;
goto v_reusejp_6005_;
}
v_reusejp_6005_:
{
lean_object* v___y_6008_; 
if (lean_obj_tag(v___x_6002_) == 0)
{
lean_object* v___x_6026_; lean_object* v___x_6027_; 
lean_del_object(v___x_5986_);
lean_del_object(v___x_5982_);
v___x_6026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6026_, 0, v_fst_5984_);
lean_ctor_set(v___x_6026_, 1, v___x_6006_);
v___x_6027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6027_, 0, v_fst_5980_);
lean_ctor_set(v___x_6027_, 1, v___x_6026_);
v_a_5972_ = v___x_6027_;
goto v___jp_5971_;
}
else
{
lean_object* v_val_6028_; lean_object* v_a_6029_; uint8_t v___x_6030_; 
v_val_6028_ = lean_ctor_get(v___x_6002_, 0);
lean_inc(v_val_6028_);
lean_dec_ref_known(v___x_6002_, 1);
v_a_6029_ = lean_array_uget_borrowed(v_as_5962_, v_i_5964_);
v___x_6030_ = lean_unbox(v_val_6028_);
lean_dec(v_val_6028_);
if (v___x_6030_ == 0)
{
lean_object* v___x_6031_; 
lean_inc(v_a_6029_);
v___x_6031_ = l_Lean_Meta_mkEqRefl(v_a_6029_, v___y_5966_, v___y_5967_, v___y_5968_, v___y_5969_);
v___y_6008_ = v___x_6031_;
goto v___jp_6007_;
}
else
{
lean_object* v___x_6032_; 
lean_inc(v_a_6029_);
v___x_6032_ = l_Lean_Meta_mkHEqRefl(v_a_6029_, v___y_5966_, v___y_5967_, v___y_5968_, v___y_5969_);
v___y_6008_ = v___x_6032_;
goto v___jp_6007_;
}
}
v___jp_6007_:
{
if (lean_obj_tag(v___y_6008_) == 0)
{
lean_object* v_a_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6013_; 
v_a_6009_ = lean_ctor_get(v___y_6008_, 0);
lean_inc(v_a_6009_);
lean_dec_ref_known(v___y_6008_, 1);
v___x_6010_ = lean_array_push(v_fst_5980_, v_a_6009_);
v___x_6011_ = lean_nat_add(v_fst_5984_, v___x_6003_);
lean_dec(v_fst_5984_);
if (v_isShared_5987_ == 0)
{
lean_ctor_set(v___x_5986_, 1, v___x_6006_);
lean_ctor_set(v___x_5986_, 0, v___x_6011_);
v___x_6013_ = v___x_5986_;
goto v_reusejp_6012_;
}
else
{
lean_object* v_reuseFailAlloc_6017_; 
v_reuseFailAlloc_6017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6017_, 0, v___x_6011_);
lean_ctor_set(v_reuseFailAlloc_6017_, 1, v___x_6006_);
v___x_6013_ = v_reuseFailAlloc_6017_;
goto v_reusejp_6012_;
}
v_reusejp_6012_:
{
lean_object* v___x_6015_; 
if (v_isShared_5983_ == 0)
{
lean_ctor_set(v___x_5982_, 1, v___x_6013_);
lean_ctor_set(v___x_5982_, 0, v___x_6010_);
v___x_6015_ = v___x_5982_;
goto v_reusejp_6014_;
}
else
{
lean_object* v_reuseFailAlloc_6016_; 
v_reuseFailAlloc_6016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6016_, 0, v___x_6010_);
lean_ctor_set(v_reuseFailAlloc_6016_, 1, v___x_6013_);
v___x_6015_ = v_reuseFailAlloc_6016_;
goto v_reusejp_6014_;
}
v_reusejp_6014_:
{
v_a_5972_ = v___x_6015_;
goto v___jp_5971_;
}
}
}
else
{
lean_object* v_a_6018_; lean_object* v___x_6020_; uint8_t v_isShared_6021_; uint8_t v_isSharedCheck_6025_; 
lean_dec_ref(v___x_6006_);
lean_del_object(v___x_5986_);
lean_dec(v_fst_5984_);
lean_del_object(v___x_5982_);
lean_dec(v_fst_5980_);
v_a_6018_ = lean_ctor_get(v___y_6008_, 0);
v_isSharedCheck_6025_ = !lean_is_exclusive(v___y_6008_);
if (v_isSharedCheck_6025_ == 0)
{
v___x_6020_ = v___y_6008_;
v_isShared_6021_ = v_isSharedCheck_6025_;
goto v_resetjp_6019_;
}
else
{
lean_inc(v_a_6018_);
lean_dec(v___y_6008_);
v___x_6020_ = lean_box(0);
v_isShared_6021_ = v_isSharedCheck_6025_;
goto v_resetjp_6019_;
}
v_resetjp_6019_:
{
lean_object* v___x_6023_; 
if (v_isShared_6021_ == 0)
{
v___x_6023_ = v___x_6020_;
goto v_reusejp_6022_;
}
else
{
lean_object* v_reuseFailAlloc_6024_; 
v_reuseFailAlloc_6024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6024_, 0, v_a_6018_);
v___x_6023_ = v_reuseFailAlloc_6024_;
goto v_reusejp_6022_;
}
v_reusejp_6022_:
{
return v___x_6023_;
}
}
}
}
}
}
}
}
}
}
v___jp_5971_:
{
size_t v___x_5973_; size_t v___x_5974_; 
v___x_5973_ = ((size_t)1ULL);
v___x_5974_ = lean_usize_add(v_i_5964_, v___x_5973_);
v_i_5964_ = v___x_5974_;
v_b_5965_ = v_a_5972_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8___boxed(lean_object* v_as_6042_, lean_object* v_sz_6043_, lean_object* v_i_6044_, lean_object* v_b_6045_, lean_object* v___y_6046_, lean_object* v___y_6047_, lean_object* v___y_6048_, lean_object* v___y_6049_, lean_object* v___y_6050_){
_start:
{
size_t v_sz_boxed_6051_; size_t v_i_boxed_6052_; lean_object* v_res_6053_; 
v_sz_boxed_6051_ = lean_unbox_usize(v_sz_6043_);
lean_dec(v_sz_6043_);
v_i_boxed_6052_ = lean_unbox_usize(v_i_6044_);
lean_dec(v_i_6044_);
v_res_6053_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(v_as_6042_, v_sz_boxed_6051_, v_i_boxed_6052_, v_b_6045_, v___y_6046_, v___y_6047_, v___y_6048_, v___y_6049_);
lean_dec(v___y_6049_);
lean_dec_ref(v___y_6048_);
lean_dec(v___y_6047_);
lean_dec_ref(v___y_6046_);
lean_dec_ref(v_as_6042_);
return v_res_6053_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(lean_object* v___x_6054_, lean_object* v___y_6055_, lean_object* v___y_6056_, lean_object* v___y_6057_, lean_object* v___y_6058_){
_start:
{
lean_object* v___x_6060_; 
v___x_6060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6060_, 0, v___x_6054_);
return v___x_6060_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed(lean_object* v___x_6061_, lean_object* v___y_6062_, lean_object* v___y_6063_, lean_object* v___y_6064_, lean_object* v___y_6065_, lean_object* v___y_6066_){
_start:
{
lean_object* v_res_6067_; 
v_res_6067_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(v___x_6061_, v___y_6062_, v___y_6063_, v___y_6064_, v___y_6065_);
lean_dec(v___y_6065_);
lean_dec_ref(v___y_6064_);
lean_dec(v___y_6063_);
lean_dec_ref(v___y_6062_);
return v_res_6067_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(size_t v_sz_6068_, size_t v_i_6069_, lean_object* v_bs_6070_, lean_object* v___y_6071_, lean_object* v___y_6072_, lean_object* v___y_6073_){
_start:
{
uint8_t v___x_6075_; 
v___x_6075_ = lean_usize_dec_lt(v_i_6069_, v_sz_6068_);
if (v___x_6075_ == 0)
{
lean_object* v___x_6076_; 
v___x_6076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6076_, 0, v_bs_6070_);
return v___x_6076_;
}
else
{
lean_object* v_v_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; 
v_v_6077_ = lean_array_uget_borrowed(v_bs_6070_, v_i_6069_);
v___x_6078_ = l_Lean_Expr_fvarId_x21(v_v_6077_);
v___x_6079_ = l_Lean_FVarId_getUserName___redArg(v___x_6078_, v___y_6071_, v___y_6072_, v___y_6073_);
if (lean_obj_tag(v___x_6079_) == 0)
{
lean_object* v_a_6080_; lean_object* v___x_6081_; lean_object* v_bs_x27_6082_; size_t v___x_6083_; size_t v___x_6084_; lean_object* v___x_6085_; 
v_a_6080_ = lean_ctor_get(v___x_6079_, 0);
lean_inc(v_a_6080_);
lean_dec_ref_known(v___x_6079_, 1);
v___x_6081_ = lean_unsigned_to_nat(0u);
v_bs_x27_6082_ = lean_array_uset(v_bs_6070_, v_i_6069_, v___x_6081_);
v___x_6083_ = ((size_t)1ULL);
v___x_6084_ = lean_usize_add(v_i_6069_, v___x_6083_);
v___x_6085_ = lean_array_uset(v_bs_x27_6082_, v_i_6069_, v_a_6080_);
v_i_6069_ = v___x_6084_;
v_bs_6070_ = v___x_6085_;
goto _start;
}
else
{
lean_object* v_a_6087_; lean_object* v___x_6089_; uint8_t v_isShared_6090_; uint8_t v_isSharedCheck_6094_; 
lean_dec_ref(v_bs_6070_);
v_a_6087_ = lean_ctor_get(v___x_6079_, 0);
v_isSharedCheck_6094_ = !lean_is_exclusive(v___x_6079_);
if (v_isSharedCheck_6094_ == 0)
{
v___x_6089_ = v___x_6079_;
v_isShared_6090_ = v_isSharedCheck_6094_;
goto v_resetjp_6088_;
}
else
{
lean_inc(v_a_6087_);
lean_dec(v___x_6079_);
v___x_6089_ = lean_box(0);
v_isShared_6090_ = v_isSharedCheck_6094_;
goto v_resetjp_6088_;
}
v_resetjp_6088_:
{
lean_object* v___x_6092_; 
if (v_isShared_6090_ == 0)
{
v___x_6092_ = v___x_6089_;
goto v_reusejp_6091_;
}
else
{
lean_object* v_reuseFailAlloc_6093_; 
v_reuseFailAlloc_6093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6093_, 0, v_a_6087_);
v___x_6092_ = v_reuseFailAlloc_6093_;
goto v_reusejp_6091_;
}
v_reusejp_6091_:
{
return v___x_6092_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg___boxed(lean_object* v_sz_6095_, lean_object* v_i_6096_, lean_object* v_bs_6097_, lean_object* v___y_6098_, lean_object* v___y_6099_, lean_object* v___y_6100_, lean_object* v___y_6101_){
_start:
{
size_t v_sz_boxed_6102_; size_t v_i_boxed_6103_; lean_object* v_res_6104_; 
v_sz_boxed_6102_ = lean_unbox_usize(v_sz_6095_);
lean_dec(v_sz_6095_);
v_i_boxed_6103_ = lean_unbox_usize(v_i_6096_);
lean_dec(v_i_6096_);
v_res_6104_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_boxed_6102_, v_i_boxed_6103_, v_bs_6097_, v___y_6098_, v___y_6099_, v___y_6100_);
lean_dec(v___y_6100_);
lean_dec_ref(v___y_6099_);
lean_dec_ref(v___y_6098_);
return v_res_6104_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(lean_object* v_xs_6105_, lean_object* v_x_6106_, lean_object* v___y_6107_, lean_object* v___y_6108_, lean_object* v___y_6109_, lean_object* v___y_6110_){
_start:
{
size_t v_sz_6112_; size_t v___x_6113_; lean_object* v___x_6114_; 
v_sz_6112_ = lean_array_size(v_xs_6105_);
v___x_6113_ = ((size_t)0ULL);
v___x_6114_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_6112_, v___x_6113_, v_xs_6105_, v___y_6107_, v___y_6109_, v___y_6110_);
return v___x_6114_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3___boxed(lean_object* v_xs_6115_, lean_object* v_x_6116_, lean_object* v___y_6117_, lean_object* v___y_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_){
_start:
{
lean_object* v_res_6122_; 
v_res_6122_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(v_xs_6115_, v_x_6116_, v___y_6117_, v___y_6118_, v___y_6119_, v___y_6120_);
lean_dec(v___y_6120_);
lean_dec_ref(v___y_6119_);
lean_dec(v___y_6118_);
lean_dec_ref(v___y_6117_);
lean_dec_ref(v_x_6116_);
return v_res_6122_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(lean_object* v___x_6123_, lean_object* v___x_6124_, lean_object* v___f_6125_, uint8_t v___x_6126_, lean_object* v_fst_6127_, lean_object* v___x_6128_, lean_object* v___x_6129_, lean_object* v___x_6130_, lean_object* v___y_6131_, lean_object* v___y_6132_, lean_object* v___y_6133_, lean_object* v___y_6134_){
_start:
{
lean_object* v___x_6136_; 
v___x_6136_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v___x_6123_, v___x_6124_, v___f_6125_, v___x_6126_, v___x_6126_, v___y_6131_, v___y_6132_, v___y_6133_, v___y_6134_);
if (lean_obj_tag(v___x_6136_) == 0)
{
lean_object* v_a_6137_; lean_object* v___x_6139_; uint8_t v_isShared_6140_; uint8_t v_isSharedCheck_6149_; 
v_a_6137_ = lean_ctor_get(v___x_6136_, 0);
v_isSharedCheck_6149_ = !lean_is_exclusive(v___x_6136_);
if (v_isSharedCheck_6149_ == 0)
{
v___x_6139_ = v___x_6136_;
v_isShared_6140_ = v_isSharedCheck_6149_;
goto v_resetjp_6138_;
}
else
{
lean_inc(v_a_6137_);
lean_dec(v___x_6136_);
v___x_6139_ = lean_box(0);
v_isShared_6140_ = v_isSharedCheck_6149_;
goto v_resetjp_6138_;
}
v_resetjp_6138_:
{
lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6147_; 
v___x_6141_ = lean_array_push(v_fst_6127_, v_a_6137_);
v___x_6142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6142_, 0, v___x_6128_);
lean_ctor_set(v___x_6142_, 1, v___x_6129_);
v___x_6143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6143_, 0, v___x_6130_);
lean_ctor_set(v___x_6143_, 1, v___x_6142_);
v___x_6144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6144_, 0, v___x_6141_);
lean_ctor_set(v___x_6144_, 1, v___x_6143_);
v___x_6145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6145_, 0, v___x_6144_);
if (v_isShared_6140_ == 0)
{
lean_ctor_set(v___x_6139_, 0, v___x_6145_);
v___x_6147_ = v___x_6139_;
goto v_reusejp_6146_;
}
else
{
lean_object* v_reuseFailAlloc_6148_; 
v_reuseFailAlloc_6148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6148_, 0, v___x_6145_);
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
lean_dec_ref(v___x_6130_);
lean_dec_ref(v___x_6129_);
lean_dec_ref(v___x_6128_);
lean_dec(v_fst_6127_);
v_a_6150_ = lean_ctor_get(v___x_6136_, 0);
v_isSharedCheck_6157_ = !lean_is_exclusive(v___x_6136_);
if (v_isSharedCheck_6157_ == 0)
{
v___x_6152_ = v___x_6136_;
v_isShared_6153_ = v_isSharedCheck_6157_;
goto v_resetjp_6151_;
}
else
{
lean_inc(v_a_6150_);
lean_dec(v___x_6136_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed(lean_object* v___x_6158_, lean_object* v___x_6159_, lean_object* v___f_6160_, lean_object* v___x_6161_, lean_object* v_fst_6162_, lean_object* v___x_6163_, lean_object* v___x_6164_, lean_object* v___x_6165_, lean_object* v___y_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_){
_start:
{
uint8_t v___x_34918__boxed_6171_; lean_object* v_res_6172_; 
v___x_34918__boxed_6171_ = lean_unbox(v___x_6161_);
v_res_6172_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(v___x_6158_, v___x_6159_, v___f_6160_, v___x_34918__boxed_6171_, v_fst_6162_, v___x_6163_, v___x_6164_, v___x_6165_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_);
lean_dec(v___y_6169_);
lean_dec_ref(v___y_6168_);
lean_dec(v___y_6167_);
lean_dec_ref(v___y_6166_);
return v_res_6172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(lean_object* v_fvars_6173_, lean_object* v_names_6174_, lean_object* v_k_6175_, lean_object* v___y_6176_, lean_object* v___y_6177_, lean_object* v___y_6178_, lean_object* v___y_6179_){
_start:
{
lean_object* v___x_6181_; 
v___x_6181_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_6173_, v_names_6174_, v_k_6175_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_);
if (lean_obj_tag(v___x_6181_) == 0)
{
lean_object* v_a_6182_; lean_object* v___x_6184_; uint8_t v_isShared_6185_; uint8_t v_isSharedCheck_6189_; 
v_a_6182_ = lean_ctor_get(v___x_6181_, 0);
v_isSharedCheck_6189_ = !lean_is_exclusive(v___x_6181_);
if (v_isSharedCheck_6189_ == 0)
{
v___x_6184_ = v___x_6181_;
v_isShared_6185_ = v_isSharedCheck_6189_;
goto v_resetjp_6183_;
}
else
{
lean_inc(v_a_6182_);
lean_dec(v___x_6181_);
v___x_6184_ = lean_box(0);
v_isShared_6185_ = v_isSharedCheck_6189_;
goto v_resetjp_6183_;
}
v_resetjp_6183_:
{
lean_object* v___x_6187_; 
if (v_isShared_6185_ == 0)
{
v___x_6187_ = v___x_6184_;
goto v_reusejp_6186_;
}
else
{
lean_object* v_reuseFailAlloc_6188_; 
v_reuseFailAlloc_6188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6188_, 0, v_a_6182_);
v___x_6187_ = v_reuseFailAlloc_6188_;
goto v_reusejp_6186_;
}
v_reusejp_6186_:
{
return v___x_6187_;
}
}
}
else
{
lean_object* v_a_6190_; lean_object* v___x_6192_; uint8_t v_isShared_6193_; uint8_t v_isSharedCheck_6197_; 
v_a_6190_ = lean_ctor_get(v___x_6181_, 0);
v_isSharedCheck_6197_ = !lean_is_exclusive(v___x_6181_);
if (v_isSharedCheck_6197_ == 0)
{
v___x_6192_ = v___x_6181_;
v_isShared_6193_ = v_isSharedCheck_6197_;
goto v_resetjp_6191_;
}
else
{
lean_inc(v_a_6190_);
lean_dec(v___x_6181_);
v___x_6192_ = lean_box(0);
v_isShared_6193_ = v_isSharedCheck_6197_;
goto v_resetjp_6191_;
}
v_resetjp_6191_:
{
lean_object* v___x_6195_; 
if (v_isShared_6193_ == 0)
{
v___x_6195_ = v___x_6192_;
goto v_reusejp_6194_;
}
else
{
lean_object* v_reuseFailAlloc_6196_; 
v_reuseFailAlloc_6196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6196_, 0, v_a_6190_);
v___x_6195_ = v_reuseFailAlloc_6196_;
goto v_reusejp_6194_;
}
v_reusejp_6194_:
{
return v___x_6195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg___boxed(lean_object* v_fvars_6198_, lean_object* v_names_6199_, lean_object* v_k_6200_, lean_object* v___y_6201_, lean_object* v___y_6202_, lean_object* v___y_6203_, lean_object* v___y_6204_, lean_object* v___y_6205_){
_start:
{
lean_object* v_res_6206_; 
v_res_6206_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_fvars_6198_, v_names_6199_, v_k_6200_, v___y_6201_, v___y_6202_, v___y_6203_, v___y_6204_);
lean_dec(v___y_6204_);
lean_dec_ref(v___y_6203_);
lean_dec(v___y_6202_);
lean_dec_ref(v___y_6201_);
lean_dec_ref(v_names_6199_);
lean_dec_ref(v_fvars_6198_);
return v_res_6206_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(lean_object* v___x_6207_, lean_object* v_xs_6208_, lean_object* v_remaining_x27_6209_, lean_object* v_ys4_6210_, lean_object* v_onAlt_6211_, lean_object* v_a_6212_, lean_object* v_altType_6213_, uint8_t v___x_6214_, uint8_t v___x_6215_, lean_object* v___y_6216_, lean_object* v___y_6217_, lean_object* v___y_6218_, lean_object* v___y_6219_){
_start:
{
lean_object* v___x_6221_; 
v___x_6221_ = l_Lean_Meta_instantiateLambda(v___x_6207_, v_xs_6208_, v___y_6216_, v___y_6217_, v___y_6218_, v___y_6219_);
if (lean_obj_tag(v___x_6221_) == 0)
{
lean_object* v_a_6222_; lean_object* v___x_6223_; lean_object* v___x_6224_; 
v_a_6222_ = lean_ctor_get(v___x_6221_, 0);
lean_inc(v_a_6222_);
lean_dec_ref_known(v___x_6221_, 1);
lean_inc_ref(v_ys4_6210_);
lean_inc_ref(v_remaining_x27_6209_);
lean_inc_ref_n(v_xs_6208_, 2);
v___x_6223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6223_, 0, v_xs_6208_);
lean_ctor_set(v___x_6223_, 1, v_xs_6208_);
lean_ctor_set(v___x_6223_, 2, v_remaining_x27_6209_);
lean_ctor_set(v___x_6223_, 3, v_remaining_x27_6209_);
lean_ctor_set(v___x_6223_, 4, v_ys4_6210_);
lean_inc(v___y_6219_);
lean_inc_ref(v___y_6218_);
lean_inc(v___y_6217_);
lean_inc_ref(v___y_6216_);
v___x_6224_ = lean_apply_9(v_onAlt_6211_, v_a_6212_, v_altType_6213_, v___x_6223_, v_a_6222_, v___y_6216_, v___y_6217_, v___y_6218_, v___y_6219_, lean_box(0));
if (lean_obj_tag(v___x_6224_) == 0)
{
lean_object* v_a_6225_; lean_object* v___x_6226_; uint8_t v___x_6227_; lean_object* v___x_6228_; 
v_a_6225_ = lean_ctor_get(v___x_6224_, 0);
lean_inc(v_a_6225_);
lean_dec_ref_known(v___x_6224_, 1);
v___x_6226_ = l_Array_append___redArg(v_xs_6208_, v_ys4_6210_);
lean_dec_ref(v_ys4_6210_);
v___x_6227_ = 1;
v___x_6228_ = l_Lean_Meta_mkLambdaFVars(v___x_6226_, v_a_6225_, v___x_6214_, v___x_6215_, v___x_6214_, v___x_6215_, v___x_6227_, v___y_6216_, v___y_6217_, v___y_6218_, v___y_6219_);
lean_dec(v___y_6219_);
lean_dec_ref(v___y_6218_);
lean_dec(v___y_6217_);
lean_dec_ref(v___y_6216_);
lean_dec_ref(v___x_6226_);
return v___x_6228_;
}
else
{
lean_dec(v___y_6219_);
lean_dec_ref(v___y_6218_);
lean_dec(v___y_6217_);
lean_dec_ref(v___y_6216_);
lean_dec_ref(v_ys4_6210_);
lean_dec_ref(v_xs_6208_);
return v___x_6224_;
}
}
else
{
lean_dec(v___y_6219_);
lean_dec_ref(v___y_6218_);
lean_dec(v___y_6217_);
lean_dec_ref(v___y_6216_);
lean_dec_ref(v_altType_6213_);
lean_dec(v_a_6212_);
lean_dec_ref(v_onAlt_6211_);
lean_dec_ref(v_ys4_6210_);
lean_dec_ref(v_remaining_x27_6209_);
lean_dec_ref(v_xs_6208_);
return v___x_6221_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed(lean_object* v___x_6229_, lean_object* v_xs_6230_, lean_object* v_remaining_x27_6231_, lean_object* v_ys4_6232_, lean_object* v_onAlt_6233_, lean_object* v_a_6234_, lean_object* v_altType_6235_, lean_object* v___x_6236_, lean_object* v___x_6237_, lean_object* v___y_6238_, lean_object* v___y_6239_, lean_object* v___y_6240_, lean_object* v___y_6241_, lean_object* v___y_6242_){
_start:
{
uint8_t v___x_35045__boxed_6243_; uint8_t v___x_35046__boxed_6244_; lean_object* v_res_6245_; 
v___x_35045__boxed_6243_ = lean_unbox(v___x_6236_);
v___x_35046__boxed_6244_ = lean_unbox(v___x_6237_);
v_res_6245_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(v___x_6229_, v_xs_6230_, v_remaining_x27_6231_, v_ys4_6232_, v_onAlt_6233_, v_a_6234_, v_altType_6235_, v___x_35045__boxed_6243_, v___x_35046__boxed_6244_, v___y_6238_, v___y_6239_, v___y_6240_, v___y_6241_);
return v_res_6245_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(lean_object* v___x_6246_, lean_object* v___f_6247_, uint8_t v___x_6248_, lean_object* v_xs_6249_, lean_object* v_remaining_x27_6250_, lean_object* v_onAlt_6251_, lean_object* v_a_6252_, uint8_t v___x_6253_, lean_object* v_ys4_6254_, lean_object* v_altType_6255_, lean_object* v___y_6256_, lean_object* v___y_6257_, lean_object* v___y_6258_, lean_object* v___y_6259_){
_start:
{
lean_object* v___x_6261_; 
lean_inc_ref(v___x_6246_);
v___x_6261_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v___x_6246_, v___f_6247_, v___x_6248_, v___y_6256_, v___y_6257_, v___y_6258_, v___y_6259_);
if (lean_obj_tag(v___x_6261_) == 0)
{
lean_object* v_a_6262_; lean_object* v___x_6263_; lean_object* v___x_6264_; lean_object* v___f_6265_; lean_object* v___x_6266_; 
v_a_6262_ = lean_ctor_get(v___x_6261_, 0);
lean_inc(v_a_6262_);
lean_dec_ref_known(v___x_6261_, 1);
v___x_6263_ = lean_box(v___x_6248_);
v___x_6264_ = lean_box(v___x_6253_);
lean_inc_ref(v_xs_6249_);
v___f_6265_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_6265_, 0, v___x_6246_);
lean_closure_set(v___f_6265_, 1, v_xs_6249_);
lean_closure_set(v___f_6265_, 2, v_remaining_x27_6250_);
lean_closure_set(v___f_6265_, 3, v_ys4_6254_);
lean_closure_set(v___f_6265_, 4, v_onAlt_6251_);
lean_closure_set(v___f_6265_, 5, v_a_6252_);
lean_closure_set(v___f_6265_, 6, v_altType_6255_);
lean_closure_set(v___f_6265_, 7, v___x_6263_);
lean_closure_set(v___f_6265_, 8, v___x_6264_);
v___x_6266_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_xs_6249_, v_a_6262_, v___f_6265_, v___y_6256_, v___y_6257_, v___y_6258_, v___y_6259_);
lean_dec(v_a_6262_);
lean_dec_ref(v_xs_6249_);
return v___x_6266_;
}
else
{
lean_object* v_a_6267_; lean_object* v___x_6269_; uint8_t v_isShared_6270_; uint8_t v_isSharedCheck_6274_; 
lean_dec_ref(v_altType_6255_);
lean_dec_ref(v_ys4_6254_);
lean_dec(v_a_6252_);
lean_dec_ref(v_onAlt_6251_);
lean_dec_ref(v_remaining_x27_6250_);
lean_dec_ref(v_xs_6249_);
lean_dec_ref(v___x_6246_);
v_a_6267_ = lean_ctor_get(v___x_6261_, 0);
v_isSharedCheck_6274_ = !lean_is_exclusive(v___x_6261_);
if (v_isSharedCheck_6274_ == 0)
{
v___x_6269_ = v___x_6261_;
v_isShared_6270_ = v_isSharedCheck_6274_;
goto v_resetjp_6268_;
}
else
{
lean_inc(v_a_6267_);
lean_dec(v___x_6261_);
v___x_6269_ = lean_box(0);
v_isShared_6270_ = v_isSharedCheck_6274_;
goto v_resetjp_6268_;
}
v_resetjp_6268_:
{
lean_object* v___x_6272_; 
if (v_isShared_6270_ == 0)
{
v___x_6272_ = v___x_6269_;
goto v_reusejp_6271_;
}
else
{
lean_object* v_reuseFailAlloc_6273_; 
v_reuseFailAlloc_6273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6273_, 0, v_a_6267_);
v___x_6272_ = v_reuseFailAlloc_6273_;
goto v_reusejp_6271_;
}
v_reusejp_6271_:
{
return v___x_6272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed(lean_object* v___x_6275_, lean_object* v___f_6276_, lean_object* v___x_6277_, lean_object* v_xs_6278_, lean_object* v_remaining_x27_6279_, lean_object* v_onAlt_6280_, lean_object* v_a_6281_, lean_object* v___x_6282_, lean_object* v_ys4_6283_, lean_object* v_altType_6284_, lean_object* v___y_6285_, lean_object* v___y_6286_, lean_object* v___y_6287_, lean_object* v___y_6288_, lean_object* v___y_6289_){
_start:
{
uint8_t v___x_35088__boxed_6290_; uint8_t v___x_35089__boxed_6291_; lean_object* v_res_6292_; 
v___x_35088__boxed_6290_ = lean_unbox(v___x_6277_);
v___x_35089__boxed_6291_ = lean_unbox(v___x_6282_);
v_res_6292_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(v___x_6275_, v___f_6276_, v___x_35088__boxed_6290_, v_xs_6278_, v_remaining_x27_6279_, v_onAlt_6280_, v_a_6281_, v___x_35089__boxed_6291_, v_ys4_6283_, v_altType_6284_, v___y_6285_, v___y_6286_, v___y_6287_, v___y_6288_);
lean_dec(v___y_6288_);
lean_dec_ref(v___y_6287_);
lean_dec(v___y_6286_);
lean_dec_ref(v___y_6285_);
return v_res_6292_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(lean_object* v___x_6293_, lean_object* v___f_6294_, uint8_t v___x_6295_, lean_object* v_remaining_x27_6296_, lean_object* v_onAlt_6297_, lean_object* v_a_6298_, uint8_t v___x_6299_, lean_object* v_extraEqualities_6300_, lean_object* v_xs_6301_, lean_object* v_altType_6302_, lean_object* v___y_6303_, lean_object* v___y_6304_, lean_object* v___y_6305_, lean_object* v___y_6306_){
_start:
{
lean_object* v___x_6308_; lean_object* v___x_6309_; lean_object* v___f_6310_; lean_object* v___x_6311_; lean_object* v___x_6312_; 
v___x_6308_ = lean_box(v___x_6295_);
v___x_6309_ = lean_box(v___x_6299_);
v___f_6310_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed), 15, 8);
lean_closure_set(v___f_6310_, 0, v___x_6293_);
lean_closure_set(v___f_6310_, 1, v___f_6294_);
lean_closure_set(v___f_6310_, 2, v___x_6308_);
lean_closure_set(v___f_6310_, 3, v_xs_6301_);
lean_closure_set(v___f_6310_, 4, v_remaining_x27_6296_);
lean_closure_set(v___f_6310_, 5, v_onAlt_6297_);
lean_closure_set(v___f_6310_, 6, v_a_6298_);
lean_closure_set(v___f_6310_, 7, v___x_6309_);
v___x_6311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6311_, 0, v_extraEqualities_6300_);
v___x_6312_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_6302_, v___x_6311_, v___f_6310_, v___x_6295_, v___x_6295_, v___y_6303_, v___y_6304_, v___y_6305_, v___y_6306_);
return v___x_6312_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed(lean_object* v___x_6313_, lean_object* v___f_6314_, lean_object* v___x_6315_, lean_object* v_remaining_x27_6316_, lean_object* v_onAlt_6317_, lean_object* v_a_6318_, lean_object* v___x_6319_, lean_object* v_extraEqualities_6320_, lean_object* v_xs_6321_, lean_object* v_altType_6322_, lean_object* v___y_6323_, lean_object* v___y_6324_, lean_object* v___y_6325_, lean_object* v___y_6326_, lean_object* v___y_6327_){
_start:
{
uint8_t v___x_35143__boxed_6328_; uint8_t v___x_35144__boxed_6329_; lean_object* v_res_6330_; 
v___x_35143__boxed_6328_ = lean_unbox(v___x_6315_);
v___x_35144__boxed_6329_ = lean_unbox(v___x_6319_);
v_res_6330_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(v___x_6313_, v___f_6314_, v___x_35143__boxed_6328_, v_remaining_x27_6316_, v_onAlt_6317_, v_a_6318_, v___x_35144__boxed_6329_, v_extraEqualities_6320_, v_xs_6321_, v_altType_6322_, v___y_6323_, v___y_6324_, v___y_6325_, v___y_6326_);
lean_dec(v___y_6326_);
lean_dec_ref(v___y_6325_);
lean_dec(v___y_6324_);
lean_dec_ref(v___y_6323_);
return v_res_6330_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(lean_object* v_upperBound_6332_, lean_object* v_onAlt_6333_, lean_object* v_extraEqualities_6334_, lean_object* v_a_6335_, lean_object* v_b_6336_, lean_object* v___y_6337_, lean_object* v___y_6338_, lean_object* v___y_6339_, lean_object* v___y_6340_){
_start:
{
lean_object* v___y_6343_; uint8_t v___x_6366_; 
v___x_6366_ = lean_nat_dec_lt(v_a_6335_, v_upperBound_6332_);
if (v___x_6366_ == 0)
{
lean_object* v___x_6367_; 
lean_dec(v_a_6335_);
lean_dec(v_extraEqualities_6334_);
lean_dec_ref(v_onAlt_6333_);
v___x_6367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6367_, 0, v_b_6336_);
return v___x_6367_;
}
else
{
lean_object* v_snd_6368_; lean_object* v_snd_6369_; lean_object* v_snd_6370_; lean_object* v_fst_6371_; lean_object* v___x_6373_; uint8_t v_isShared_6374_; uint8_t v_isSharedCheck_6478_; 
v_snd_6368_ = lean_ctor_get(v_b_6336_, 1);
lean_inc(v_snd_6368_);
v_snd_6369_ = lean_ctor_get(v_snd_6368_, 1);
lean_inc(v_snd_6369_);
v_snd_6370_ = lean_ctor_get(v_snd_6369_, 1);
lean_inc(v_snd_6370_);
v_fst_6371_ = lean_ctor_get(v_b_6336_, 0);
v_isSharedCheck_6478_ = !lean_is_exclusive(v_b_6336_);
if (v_isSharedCheck_6478_ == 0)
{
lean_object* v_unused_6479_; 
v_unused_6479_ = lean_ctor_get(v_b_6336_, 1);
lean_dec(v_unused_6479_);
v___x_6373_ = v_b_6336_;
v_isShared_6374_ = v_isSharedCheck_6478_;
goto v_resetjp_6372_;
}
else
{
lean_inc(v_fst_6371_);
lean_dec(v_b_6336_);
v___x_6373_ = lean_box(0);
v_isShared_6374_ = v_isSharedCheck_6478_;
goto v_resetjp_6372_;
}
v_resetjp_6372_:
{
lean_object* v_fst_6375_; lean_object* v___x_6377_; uint8_t v_isShared_6378_; uint8_t v_isSharedCheck_6476_; 
v_fst_6375_ = lean_ctor_get(v_snd_6368_, 0);
v_isSharedCheck_6476_ = !lean_is_exclusive(v_snd_6368_);
if (v_isSharedCheck_6476_ == 0)
{
lean_object* v_unused_6477_; 
v_unused_6477_ = lean_ctor_get(v_snd_6368_, 1);
lean_dec(v_unused_6477_);
v___x_6377_ = v_snd_6368_;
v_isShared_6378_ = v_isSharedCheck_6476_;
goto v_resetjp_6376_;
}
else
{
lean_inc(v_fst_6375_);
lean_dec(v_snd_6368_);
v___x_6377_ = lean_box(0);
v_isShared_6378_ = v_isSharedCheck_6476_;
goto v_resetjp_6376_;
}
v_resetjp_6376_:
{
lean_object* v_fst_6379_; lean_object* v___x_6381_; uint8_t v_isShared_6382_; uint8_t v_isSharedCheck_6474_; 
v_fst_6379_ = lean_ctor_get(v_snd_6369_, 0);
v_isSharedCheck_6474_ = !lean_is_exclusive(v_snd_6369_);
if (v_isSharedCheck_6474_ == 0)
{
lean_object* v_unused_6475_; 
v_unused_6475_ = lean_ctor_get(v_snd_6369_, 1);
lean_dec(v_unused_6475_);
v___x_6381_ = v_snd_6369_;
v_isShared_6382_ = v_isSharedCheck_6474_;
goto v_resetjp_6380_;
}
else
{
lean_inc(v_fst_6379_);
lean_dec(v_snd_6369_);
v___x_6381_ = lean_box(0);
v_isShared_6382_ = v_isSharedCheck_6474_;
goto v_resetjp_6380_;
}
v_resetjp_6380_:
{
lean_object* v_array_6383_; lean_object* v_start_6384_; lean_object* v_stop_6385_; uint8_t v___x_6386_; 
v_array_6383_ = lean_ctor_get(v_snd_6370_, 0);
v_start_6384_ = lean_ctor_get(v_snd_6370_, 1);
v_stop_6385_ = lean_ctor_get(v_snd_6370_, 2);
v___x_6386_ = lean_nat_dec_lt(v_start_6384_, v_stop_6385_);
if (v___x_6386_ == 0)
{
lean_object* v___x_6388_; 
if (v_isShared_6382_ == 0)
{
v___x_6388_ = v___x_6381_;
goto v_reusejp_6387_;
}
else
{
lean_object* v_reuseFailAlloc_6397_; 
v_reuseFailAlloc_6397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6397_, 0, v_fst_6379_);
lean_ctor_set(v_reuseFailAlloc_6397_, 1, v_snd_6370_);
v___x_6388_ = v_reuseFailAlloc_6397_;
goto v_reusejp_6387_;
}
v_reusejp_6387_:
{
lean_object* v___x_6390_; 
if (v_isShared_6378_ == 0)
{
lean_ctor_set(v___x_6377_, 1, v___x_6388_);
v___x_6390_ = v___x_6377_;
goto v_reusejp_6389_;
}
else
{
lean_object* v_reuseFailAlloc_6396_; 
v_reuseFailAlloc_6396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6396_, 0, v_fst_6375_);
lean_ctor_set(v_reuseFailAlloc_6396_, 1, v___x_6388_);
v___x_6390_ = v_reuseFailAlloc_6396_;
goto v_reusejp_6389_;
}
v_reusejp_6389_:
{
lean_object* v___x_6392_; 
if (v_isShared_6374_ == 0)
{
lean_ctor_set(v___x_6373_, 1, v___x_6390_);
v___x_6392_ = v___x_6373_;
goto v_reusejp_6391_;
}
else
{
lean_object* v_reuseFailAlloc_6395_; 
v_reuseFailAlloc_6395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6395_, 0, v_fst_6371_);
lean_ctor_set(v_reuseFailAlloc_6395_, 1, v___x_6390_);
v___x_6392_ = v_reuseFailAlloc_6395_;
goto v_reusejp_6391_;
}
v_reusejp_6391_:
{
lean_object* v___x_6393_; lean_object* v___f_6394_; 
v___x_6393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6393_, 0, v___x_6392_);
v___f_6394_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6394_, 0, v___x_6393_);
v___y_6343_ = v___f_6394_;
goto v___jp_6342_;
}
}
}
}
else
{
lean_object* v___x_6399_; uint8_t v_isShared_6400_; uint8_t v_isSharedCheck_6470_; 
lean_inc(v_stop_6385_);
lean_inc(v_start_6384_);
lean_inc_ref(v_array_6383_);
v_isSharedCheck_6470_ = !lean_is_exclusive(v_snd_6370_);
if (v_isSharedCheck_6470_ == 0)
{
lean_object* v_unused_6471_; lean_object* v_unused_6472_; lean_object* v_unused_6473_; 
v_unused_6471_ = lean_ctor_get(v_snd_6370_, 2);
lean_dec(v_unused_6471_);
v_unused_6472_ = lean_ctor_get(v_snd_6370_, 1);
lean_dec(v_unused_6472_);
v_unused_6473_ = lean_ctor_get(v_snd_6370_, 0);
lean_dec(v_unused_6473_);
v___x_6399_ = v_snd_6370_;
v_isShared_6400_ = v_isSharedCheck_6470_;
goto v_resetjp_6398_;
}
else
{
lean_dec(v_snd_6370_);
v___x_6399_ = lean_box(0);
v_isShared_6400_ = v_isSharedCheck_6470_;
goto v_resetjp_6398_;
}
v_resetjp_6398_:
{
lean_object* v_array_6401_; lean_object* v_start_6402_; lean_object* v_stop_6403_; lean_object* v___x_6404_; lean_object* v___x_6405_; lean_object* v___x_6406_; lean_object* v___x_6408_; 
v_array_6401_ = lean_ctor_get(v_fst_6379_, 0);
v_start_6402_ = lean_ctor_get(v_fst_6379_, 1);
v_stop_6403_ = lean_ctor_get(v_fst_6379_, 2);
v___x_6404_ = lean_array_fget(v_array_6383_, v_start_6384_);
v___x_6405_ = lean_unsigned_to_nat(1u);
v___x_6406_ = lean_nat_add(v_start_6384_, v___x_6405_);
lean_dec(v_start_6384_);
if (v_isShared_6400_ == 0)
{
lean_ctor_set(v___x_6399_, 1, v___x_6406_);
v___x_6408_ = v___x_6399_;
goto v_reusejp_6407_;
}
else
{
lean_object* v_reuseFailAlloc_6469_; 
v_reuseFailAlloc_6469_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6469_, 0, v_array_6383_);
lean_ctor_set(v_reuseFailAlloc_6469_, 1, v___x_6406_);
lean_ctor_set(v_reuseFailAlloc_6469_, 2, v_stop_6385_);
v___x_6408_ = v_reuseFailAlloc_6469_;
goto v_reusejp_6407_;
}
v_reusejp_6407_:
{
uint8_t v___x_6409_; 
v___x_6409_ = lean_nat_dec_lt(v_start_6402_, v_stop_6403_);
if (v___x_6409_ == 0)
{
lean_object* v___x_6411_; 
lean_dec(v___x_6404_);
if (v_isShared_6382_ == 0)
{
lean_ctor_set(v___x_6381_, 1, v___x_6408_);
v___x_6411_ = v___x_6381_;
goto v_reusejp_6410_;
}
else
{
lean_object* v_reuseFailAlloc_6420_; 
v_reuseFailAlloc_6420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6420_, 0, v_fst_6379_);
lean_ctor_set(v_reuseFailAlloc_6420_, 1, v___x_6408_);
v___x_6411_ = v_reuseFailAlloc_6420_;
goto v_reusejp_6410_;
}
v_reusejp_6410_:
{
lean_object* v___x_6413_; 
if (v_isShared_6378_ == 0)
{
lean_ctor_set(v___x_6377_, 1, v___x_6411_);
v___x_6413_ = v___x_6377_;
goto v_reusejp_6412_;
}
else
{
lean_object* v_reuseFailAlloc_6419_; 
v_reuseFailAlloc_6419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6419_, 0, v_fst_6375_);
lean_ctor_set(v_reuseFailAlloc_6419_, 1, v___x_6411_);
v___x_6413_ = v_reuseFailAlloc_6419_;
goto v_reusejp_6412_;
}
v_reusejp_6412_:
{
lean_object* v___x_6415_; 
if (v_isShared_6374_ == 0)
{
lean_ctor_set(v___x_6373_, 1, v___x_6413_);
v___x_6415_ = v___x_6373_;
goto v_reusejp_6414_;
}
else
{
lean_object* v_reuseFailAlloc_6418_; 
v_reuseFailAlloc_6418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6418_, 0, v_fst_6371_);
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
v___y_6343_ = v___f_6417_;
goto v___jp_6342_;
}
}
}
}
else
{
lean_object* v___x_6422_; uint8_t v_isShared_6423_; uint8_t v_isSharedCheck_6465_; 
lean_inc(v_stop_6403_);
lean_inc(v_start_6402_);
lean_inc_ref(v_array_6401_);
v_isSharedCheck_6465_ = !lean_is_exclusive(v_fst_6379_);
if (v_isSharedCheck_6465_ == 0)
{
lean_object* v_unused_6466_; lean_object* v_unused_6467_; lean_object* v_unused_6468_; 
v_unused_6466_ = lean_ctor_get(v_fst_6379_, 2);
lean_dec(v_unused_6466_);
v_unused_6467_ = lean_ctor_get(v_fst_6379_, 1);
lean_dec(v_unused_6467_);
v_unused_6468_ = lean_ctor_get(v_fst_6379_, 0);
lean_dec(v_unused_6468_);
v___x_6422_ = v_fst_6379_;
v_isShared_6423_ = v_isSharedCheck_6465_;
goto v_resetjp_6421_;
}
else
{
lean_dec(v_fst_6379_);
v___x_6422_ = lean_box(0);
v_isShared_6423_ = v_isSharedCheck_6465_;
goto v_resetjp_6421_;
}
v_resetjp_6421_:
{
lean_object* v_array_6424_; lean_object* v_start_6425_; lean_object* v_stop_6426_; lean_object* v___x_6427_; lean_object* v___x_6428_; lean_object* v___x_6430_; 
v_array_6424_ = lean_ctor_get(v_fst_6375_, 0);
v_start_6425_ = lean_ctor_get(v_fst_6375_, 1);
v_stop_6426_ = lean_ctor_get(v_fst_6375_, 2);
v___x_6427_ = lean_array_fget(v_array_6401_, v_start_6402_);
v___x_6428_ = lean_nat_add(v_start_6402_, v___x_6405_);
lean_dec(v_start_6402_);
if (v_isShared_6423_ == 0)
{
lean_ctor_set(v___x_6422_, 1, v___x_6428_);
v___x_6430_ = v___x_6422_;
goto v_reusejp_6429_;
}
else
{
lean_object* v_reuseFailAlloc_6464_; 
v_reuseFailAlloc_6464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6464_, 0, v_array_6401_);
lean_ctor_set(v_reuseFailAlloc_6464_, 1, v___x_6428_);
lean_ctor_set(v_reuseFailAlloc_6464_, 2, v_stop_6403_);
v___x_6430_ = v_reuseFailAlloc_6464_;
goto v_reusejp_6429_;
}
v_reusejp_6429_:
{
uint8_t v___x_6431_; 
v___x_6431_ = lean_nat_dec_lt(v_start_6425_, v_stop_6426_);
if (v___x_6431_ == 0)
{
lean_object* v___x_6433_; 
lean_dec(v___x_6427_);
lean_dec(v___x_6404_);
if (v_isShared_6382_ == 0)
{
lean_ctor_set(v___x_6381_, 1, v___x_6408_);
lean_ctor_set(v___x_6381_, 0, v___x_6430_);
v___x_6433_ = v___x_6381_;
goto v_reusejp_6432_;
}
else
{
lean_object* v_reuseFailAlloc_6442_; 
v_reuseFailAlloc_6442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6442_, 0, v___x_6430_);
lean_ctor_set(v_reuseFailAlloc_6442_, 1, v___x_6408_);
v___x_6433_ = v_reuseFailAlloc_6442_;
goto v_reusejp_6432_;
}
v_reusejp_6432_:
{
lean_object* v___x_6435_; 
if (v_isShared_6378_ == 0)
{
lean_ctor_set(v___x_6377_, 1, v___x_6433_);
v___x_6435_ = v___x_6377_;
goto v_reusejp_6434_;
}
else
{
lean_object* v_reuseFailAlloc_6441_; 
v_reuseFailAlloc_6441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6441_, 0, v_fst_6375_);
lean_ctor_set(v_reuseFailAlloc_6441_, 1, v___x_6433_);
v___x_6435_ = v_reuseFailAlloc_6441_;
goto v_reusejp_6434_;
}
v_reusejp_6434_:
{
lean_object* v___x_6437_; 
if (v_isShared_6374_ == 0)
{
lean_ctor_set(v___x_6373_, 1, v___x_6435_);
v___x_6437_ = v___x_6373_;
goto v_reusejp_6436_;
}
else
{
lean_object* v_reuseFailAlloc_6440_; 
v_reuseFailAlloc_6440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6440_, 0, v_fst_6371_);
lean_ctor_set(v_reuseFailAlloc_6440_, 1, v___x_6435_);
v___x_6437_ = v_reuseFailAlloc_6440_;
goto v_reusejp_6436_;
}
v_reusejp_6436_:
{
lean_object* v___x_6438_; lean_object* v___f_6439_; 
v___x_6438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6438_, 0, v___x_6437_);
v___f_6439_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6439_, 0, v___x_6438_);
v___y_6343_ = v___f_6439_;
goto v___jp_6342_;
}
}
}
}
else
{
lean_object* v___x_6444_; uint8_t v_isShared_6445_; uint8_t v_isSharedCheck_6460_; 
lean_inc(v_stop_6426_);
lean_inc(v_start_6425_);
lean_inc_ref(v_array_6424_);
lean_del_object(v___x_6381_);
lean_del_object(v___x_6377_);
lean_del_object(v___x_6373_);
v_isSharedCheck_6460_ = !lean_is_exclusive(v_fst_6375_);
if (v_isSharedCheck_6460_ == 0)
{
lean_object* v_unused_6461_; lean_object* v_unused_6462_; lean_object* v_unused_6463_; 
v_unused_6461_ = lean_ctor_get(v_fst_6375_, 2);
lean_dec(v_unused_6461_);
v_unused_6462_ = lean_ctor_get(v_fst_6375_, 1);
lean_dec(v_unused_6462_);
v_unused_6463_ = lean_ctor_get(v_fst_6375_, 0);
lean_dec(v_unused_6463_);
v___x_6444_ = v_fst_6375_;
v_isShared_6445_ = v_isSharedCheck_6460_;
goto v_resetjp_6443_;
}
else
{
lean_dec(v_fst_6375_);
v___x_6444_ = lean_box(0);
v_isShared_6445_ = v_isSharedCheck_6460_;
goto v_resetjp_6443_;
}
v_resetjp_6443_:
{
lean_object* v___f_6446_; uint8_t v___x_6447_; lean_object* v_remaining_x27_6448_; lean_object* v___x_6449_; lean_object* v___x_6450_; lean_object* v___x_6451_; lean_object* v___f_6452_; lean_object* v___x_6453_; lean_object* v___x_6455_; 
v___f_6446_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___closed__0));
v___x_6447_ = 0;
v_remaining_x27_6448_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_6449_ = lean_array_fget_borrowed(v_array_6424_, v_start_6425_);
v___x_6450_ = lean_box(v___x_6447_);
v___x_6451_ = lean_box(v___x_6431_);
lean_inc(v_extraEqualities_6334_);
lean_inc(v_a_6335_);
lean_inc_ref(v_onAlt_6333_);
lean_inc(v___x_6449_);
v___f_6452_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed), 15, 8);
lean_closure_set(v___f_6452_, 0, v___x_6449_);
lean_closure_set(v___f_6452_, 1, v___f_6446_);
lean_closure_set(v___f_6452_, 2, v___x_6450_);
lean_closure_set(v___f_6452_, 3, v_remaining_x27_6448_);
lean_closure_set(v___f_6452_, 4, v_onAlt_6333_);
lean_closure_set(v___f_6452_, 5, v_a_6335_);
lean_closure_set(v___f_6452_, 6, v___x_6451_);
lean_closure_set(v___f_6452_, 7, v_extraEqualities_6334_);
v___x_6453_ = lean_nat_add(v_start_6425_, v___x_6405_);
lean_dec(v_start_6425_);
if (v_isShared_6445_ == 0)
{
lean_ctor_set(v___x_6444_, 1, v___x_6453_);
v___x_6455_ = v___x_6444_;
goto v_reusejp_6454_;
}
else
{
lean_object* v_reuseFailAlloc_6459_; 
v_reuseFailAlloc_6459_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6459_, 0, v_array_6424_);
lean_ctor_set(v_reuseFailAlloc_6459_, 1, v___x_6453_);
lean_ctor_set(v_reuseFailAlloc_6459_, 2, v_stop_6426_);
v___x_6455_ = v_reuseFailAlloc_6459_;
goto v_reusejp_6454_;
}
v_reusejp_6454_:
{
lean_object* v___x_6456_; lean_object* v___x_6457_; lean_object* v___f_6458_; 
v___x_6456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6456_, 0, v___x_6427_);
v___x_6457_ = lean_box(v___x_6447_);
v___f_6458_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed), 13, 8);
lean_closure_set(v___f_6458_, 0, v___x_6404_);
lean_closure_set(v___f_6458_, 1, v___x_6456_);
lean_closure_set(v___f_6458_, 2, v___f_6452_);
lean_closure_set(v___f_6458_, 3, v___x_6457_);
lean_closure_set(v___f_6458_, 4, v_fst_6371_);
lean_closure_set(v___f_6458_, 5, v___x_6430_);
lean_closure_set(v___f_6458_, 6, v___x_6408_);
lean_closure_set(v___f_6458_, 7, v___x_6455_);
v___y_6343_ = v___f_6458_;
goto v___jp_6342_;
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_6342_:
{
lean_object* v___x_6344_; 
lean_inc(v___y_6340_);
lean_inc_ref(v___y_6339_);
lean_inc(v___y_6338_);
lean_inc_ref(v___y_6337_);
v___x_6344_ = lean_apply_5(v___y_6343_, v___y_6337_, v___y_6338_, v___y_6339_, v___y_6340_, lean_box(0));
if (lean_obj_tag(v___x_6344_) == 0)
{
lean_object* v_a_6345_; lean_object* v___x_6347_; uint8_t v_isShared_6348_; uint8_t v_isSharedCheck_6357_; 
v_a_6345_ = lean_ctor_get(v___x_6344_, 0);
v_isSharedCheck_6357_ = !lean_is_exclusive(v___x_6344_);
if (v_isSharedCheck_6357_ == 0)
{
v___x_6347_ = v___x_6344_;
v_isShared_6348_ = v_isSharedCheck_6357_;
goto v_resetjp_6346_;
}
else
{
lean_inc(v_a_6345_);
lean_dec(v___x_6344_);
v___x_6347_ = lean_box(0);
v_isShared_6348_ = v_isSharedCheck_6357_;
goto v_resetjp_6346_;
}
v_resetjp_6346_:
{
if (lean_obj_tag(v_a_6345_) == 0)
{
lean_object* v_a_6349_; lean_object* v___x_6351_; 
lean_dec(v_a_6335_);
lean_dec(v_extraEqualities_6334_);
lean_dec_ref(v_onAlt_6333_);
v_a_6349_ = lean_ctor_get(v_a_6345_, 0);
lean_inc(v_a_6349_);
lean_dec_ref_known(v_a_6345_, 1);
if (v_isShared_6348_ == 0)
{
lean_ctor_set(v___x_6347_, 0, v_a_6349_);
v___x_6351_ = v___x_6347_;
goto v_reusejp_6350_;
}
else
{
lean_object* v_reuseFailAlloc_6352_; 
v_reuseFailAlloc_6352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6352_, 0, v_a_6349_);
v___x_6351_ = v_reuseFailAlloc_6352_;
goto v_reusejp_6350_;
}
v_reusejp_6350_:
{
return v___x_6351_;
}
}
else
{
lean_object* v_a_6353_; lean_object* v___x_6354_; lean_object* v___x_6355_; 
lean_del_object(v___x_6347_);
v_a_6353_ = lean_ctor_get(v_a_6345_, 0);
lean_inc(v_a_6353_);
lean_dec_ref_known(v_a_6345_, 1);
v___x_6354_ = lean_unsigned_to_nat(1u);
v___x_6355_ = lean_nat_add(v_a_6335_, v___x_6354_);
lean_dec(v_a_6335_);
v_a_6335_ = v___x_6355_;
v_b_6336_ = v_a_6353_;
goto _start;
}
}
}
else
{
lean_object* v_a_6358_; lean_object* v___x_6360_; uint8_t v_isShared_6361_; uint8_t v_isSharedCheck_6365_; 
lean_dec(v_a_6335_);
lean_dec(v_extraEqualities_6334_);
lean_dec_ref(v_onAlt_6333_);
v_a_6358_ = lean_ctor_get(v___x_6344_, 0);
v_isSharedCheck_6365_ = !lean_is_exclusive(v___x_6344_);
if (v_isSharedCheck_6365_ == 0)
{
v___x_6360_ = v___x_6344_;
v_isShared_6361_ = v_isSharedCheck_6365_;
goto v_resetjp_6359_;
}
else
{
lean_inc(v_a_6358_);
lean_dec(v___x_6344_);
v___x_6360_ = lean_box(0);
v_isShared_6361_ = v_isSharedCheck_6365_;
goto v_resetjp_6359_;
}
v_resetjp_6359_:
{
lean_object* v___x_6363_; 
if (v_isShared_6361_ == 0)
{
v___x_6363_ = v___x_6360_;
goto v_reusejp_6362_;
}
else
{
lean_object* v_reuseFailAlloc_6364_; 
v_reuseFailAlloc_6364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6364_, 0, v_a_6358_);
v___x_6363_ = v_reuseFailAlloc_6364_;
goto v_reusejp_6362_;
}
v_reusejp_6362_:
{
return v___x_6363_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___boxed(lean_object* v_upperBound_6480_, lean_object* v_onAlt_6481_, lean_object* v_extraEqualities_6482_, lean_object* v_a_6483_, lean_object* v_b_6484_, lean_object* v___y_6485_, lean_object* v___y_6486_, lean_object* v___y_6487_, lean_object* v___y_6488_, lean_object* v___y_6489_){
_start:
{
lean_object* v_res_6490_; 
v_res_6490_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v_upperBound_6480_, v_onAlt_6481_, v_extraEqualities_6482_, v_a_6483_, v_b_6484_, v___y_6485_, v___y_6486_, v___y_6487_, v___y_6488_);
lean_dec(v___y_6488_);
lean_dec_ref(v___y_6487_);
lean_dec(v___y_6486_);
lean_dec_ref(v___y_6485_);
lean_dec(v_upperBound_6480_);
return v_res_6490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(lean_object* v_onParams_6491_, size_t v_sz_6492_, size_t v_i_6493_, lean_object* v_bs_6494_, lean_object* v___y_6495_, lean_object* v___y_6496_, lean_object* v___y_6497_, lean_object* v___y_6498_){
_start:
{
uint8_t v___x_6500_; 
v___x_6500_ = lean_usize_dec_lt(v_i_6493_, v_sz_6492_);
if (v___x_6500_ == 0)
{
lean_object* v___x_6501_; 
lean_dec_ref(v_onParams_6491_);
v___x_6501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6501_, 0, v_bs_6494_);
return v___x_6501_;
}
else
{
lean_object* v_v_6502_; lean_object* v___x_6503_; 
v_v_6502_ = lean_array_uget_borrowed(v_bs_6494_, v_i_6493_);
lean_inc_ref(v_onParams_6491_);
lean_inc(v___y_6498_);
lean_inc_ref(v___y_6497_);
lean_inc(v___y_6496_);
lean_inc_ref(v___y_6495_);
lean_inc(v_v_6502_);
v___x_6503_ = lean_apply_6(v_onParams_6491_, v_v_6502_, v___y_6495_, v___y_6496_, v___y_6497_, v___y_6498_, lean_box(0));
if (lean_obj_tag(v___x_6503_) == 0)
{
lean_object* v_a_6504_; lean_object* v___x_6505_; lean_object* v_bs_x27_6506_; size_t v___x_6507_; size_t v___x_6508_; lean_object* v___x_6509_; 
v_a_6504_ = lean_ctor_get(v___x_6503_, 0);
lean_inc(v_a_6504_);
lean_dec_ref_known(v___x_6503_, 1);
v___x_6505_ = lean_unsigned_to_nat(0u);
v_bs_x27_6506_ = lean_array_uset(v_bs_6494_, v_i_6493_, v___x_6505_);
v___x_6507_ = ((size_t)1ULL);
v___x_6508_ = lean_usize_add(v_i_6493_, v___x_6507_);
v___x_6509_ = lean_array_uset(v_bs_x27_6506_, v_i_6493_, v_a_6504_);
v_i_6493_ = v___x_6508_;
v_bs_6494_ = v___x_6509_;
goto _start;
}
else
{
lean_object* v_a_6511_; lean_object* v___x_6513_; uint8_t v_isShared_6514_; uint8_t v_isSharedCheck_6518_; 
lean_dec_ref(v_bs_6494_);
lean_dec_ref(v_onParams_6491_);
v_a_6511_ = lean_ctor_get(v___x_6503_, 0);
v_isSharedCheck_6518_ = !lean_is_exclusive(v___x_6503_);
if (v_isSharedCheck_6518_ == 0)
{
v___x_6513_ = v___x_6503_;
v_isShared_6514_ = v_isSharedCheck_6518_;
goto v_resetjp_6512_;
}
else
{
lean_inc(v_a_6511_);
lean_dec(v___x_6503_);
v___x_6513_ = lean_box(0);
v_isShared_6514_ = v_isSharedCheck_6518_;
goto v_resetjp_6512_;
}
v_resetjp_6512_:
{
lean_object* v___x_6516_; 
if (v_isShared_6514_ == 0)
{
v___x_6516_ = v___x_6513_;
goto v_reusejp_6515_;
}
else
{
lean_object* v_reuseFailAlloc_6517_; 
v_reuseFailAlloc_6517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6517_, 0, v_a_6511_);
v___x_6516_ = v_reuseFailAlloc_6517_;
goto v_reusejp_6515_;
}
v_reusejp_6515_:
{
return v___x_6516_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6___boxed(lean_object* v_onParams_6519_, lean_object* v_sz_6520_, lean_object* v_i_6521_, lean_object* v_bs_6522_, lean_object* v___y_6523_, lean_object* v___y_6524_, lean_object* v___y_6525_, lean_object* v___y_6526_, lean_object* v___y_6527_){
_start:
{
size_t v_sz_boxed_6528_; size_t v_i_boxed_6529_; lean_object* v_res_6530_; 
v_sz_boxed_6528_ = lean_unbox_usize(v_sz_6520_);
lean_dec(v_sz_6520_);
v_i_boxed_6529_ = lean_unbox_usize(v_i_6521_);
lean_dec(v_i_6521_);
v_res_6530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6519_, v_sz_boxed_6528_, v_i_boxed_6529_, v_bs_6522_, v___y_6523_, v___y_6524_, v___y_6525_, v___y_6526_);
lean_dec(v___y_6526_);
lean_dec_ref(v___y_6525_);
lean_dec(v___y_6524_);
lean_dec_ref(v___y_6523_);
return v_res_6530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(lean_object* v_declName_6531_, lean_object* v___y_6532_){
_start:
{
lean_object* v___x_6534_; lean_object* v_env_6535_; lean_object* v___x_6536_; lean_object* v___x_6537_; 
v___x_6534_ = lean_st_ref_get(v___y_6532_);
v_env_6535_ = lean_ctor_get(v___x_6534_, 0);
lean_inc_ref(v_env_6535_);
lean_dec(v___x_6534_);
v___x_6536_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_6535_, v_declName_6531_);
v___x_6537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6537_, 0, v___x_6536_);
return v___x_6537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg___boxed(lean_object* v_declName_6538_, lean_object* v___y_6539_, lean_object* v___y_6540_){
_start:
{
lean_object* v_res_6541_; 
v_res_6541_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_declName_6538_, v___y_6539_);
lean_dec(v___y_6539_);
return v_res_6541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(lean_object* v_matcherApp_6544_, uint8_t v_useSplitter_6545_, uint8_t v_addEqualities_6546_, lean_object* v_onParams_6547_, lean_object* v_onMotive_6548_, lean_object* v_onAlt_6549_, lean_object* v_onRemaining_6550_, lean_object* v___y_6551_, lean_object* v___y_6552_, lean_object* v___y_6553_, lean_object* v___y_6554_){
_start:
{
lean_object* v___x_6556_; lean_object* v_env_6557_; lean_object* v_toMatcherInfo_6558_; lean_object* v_matcherName_6559_; lean_object* v_matcherLevels_6560_; lean_object* v_params_6561_; lean_object* v_motive_6562_; lean_object* v_discrs_6563_; lean_object* v_alts_6564_; lean_object* v_remaining_6565_; lean_object* v___y_6567_; lean_object* v___y_6568_; lean_object* v___y_6569_; lean_object* v___y_6570_; lean_object* v___y_6571_; lean_object* v___y_6572_; lean_object* v___y_6573_; lean_object* v___y_6574_; lean_object* v___y_6575_; lean_object* v___y_6576_; lean_object* v___y_6577_; lean_object* v___y_6578_; lean_object* v___y_6579_; uint8_t v_isCasesOn_6664_; size_t v___y_6666_; lean_object* v___y_6667_; lean_object* v___y_6668_; lean_object* v___y_6669_; lean_object* v___y_6670_; lean_object* v___y_6671_; lean_object* v___y_6672_; lean_object* v_matcherLevels_6673_; lean_object* v___y_6674_; lean_object* v___y_6675_; lean_object* v___y_6676_; lean_object* v___y_6677_; lean_object* v_numDiscrEqs_6871_; lean_object* v___y_6872_; lean_object* v___y_6873_; lean_object* v___y_6874_; lean_object* v___y_6875_; 
v___x_6556_ = lean_st_ref_get(v___y_6554_);
v_env_6557_ = lean_ctor_get(v___x_6556_, 0);
lean_inc_ref(v_env_6557_);
lean_dec(v___x_6556_);
v_toMatcherInfo_6558_ = lean_ctor_get(v_matcherApp_6544_, 0);
lean_inc_ref(v_toMatcherInfo_6558_);
v_matcherName_6559_ = lean_ctor_get(v_matcherApp_6544_, 1);
lean_inc_n(v_matcherName_6559_, 2);
v_matcherLevels_6560_ = lean_ctor_get(v_matcherApp_6544_, 2);
v_params_6561_ = lean_ctor_get(v_matcherApp_6544_, 3);
v_motive_6562_ = lean_ctor_get(v_matcherApp_6544_, 4);
v_discrs_6563_ = lean_ctor_get(v_matcherApp_6544_, 5);
v_alts_6564_ = lean_ctor_get(v_matcherApp_6544_, 6);
lean_inc_ref(v_alts_6564_);
v_remaining_6565_ = lean_ctor_get(v_matcherApp_6544_, 7);
lean_inc_ref(v_remaining_6565_);
v_isCasesOn_6664_ = l_Lean_isCasesOnRecursor(v_env_6557_, v_matcherName_6559_);
if (v_isCasesOn_6664_ == 0)
{
lean_object* v___x_6925_; lean_object* v_a_6926_; 
lean_inc(v_matcherName_6559_);
v___x_6925_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_matcherName_6559_, v___y_6554_);
v_a_6926_ = lean_ctor_get(v___x_6925_, 0);
lean_inc(v_a_6926_);
lean_dec_ref(v___x_6925_);
if (lean_obj_tag(v_a_6926_) == 0)
{
lean_object* v___x_6927_; lean_object* v___x_6928_; lean_object* v___x_6929_; lean_object* v___x_6930_; lean_object* v___x_6931_; lean_object* v___x_6932_; lean_object* v_a_6933_; lean_object* v___x_6935_; uint8_t v_isShared_6936_; uint8_t v_isSharedCheck_6940_; 
lean_dec_ref(v_remaining_6565_);
lean_dec_ref(v_alts_6564_);
lean_dec_ref(v_toMatcherInfo_6558_);
lean_dec_ref(v_onRemaining_6550_);
lean_dec_ref(v_onAlt_6549_);
lean_dec_ref(v_onMotive_6548_);
lean_dec_ref(v_onParams_6547_);
lean_dec_ref(v_matcherApp_6544_);
v___x_6927_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1);
v___x_6928_ = l_Lean_MessageData_ofName(v_matcherName_6559_);
v___x_6929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6929_, 0, v___x_6927_);
lean_ctor_set(v___x_6929_, 1, v___x_6928_);
v___x_6930_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3);
v___x_6931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6931_, 0, v___x_6929_);
lean_ctor_set(v___x_6931_, 1, v___x_6930_);
v___x_6932_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_6931_, v___y_6551_, v___y_6552_, v___y_6553_, v___y_6554_);
v_a_6933_ = lean_ctor_get(v___x_6932_, 0);
v_isSharedCheck_6940_ = !lean_is_exclusive(v___x_6932_);
if (v_isSharedCheck_6940_ == 0)
{
v___x_6935_ = v___x_6932_;
v_isShared_6936_ = v_isSharedCheck_6940_;
goto v_resetjp_6934_;
}
else
{
lean_inc(v_a_6933_);
lean_dec(v___x_6932_);
v___x_6935_ = lean_box(0);
v_isShared_6936_ = v_isSharedCheck_6940_;
goto v_resetjp_6934_;
}
v_resetjp_6934_:
{
lean_object* v___x_6938_; 
if (v_isShared_6936_ == 0)
{
v___x_6938_ = v___x_6935_;
goto v_reusejp_6937_;
}
else
{
lean_object* v_reuseFailAlloc_6939_; 
v_reuseFailAlloc_6939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6939_, 0, v_a_6933_);
v___x_6938_ = v_reuseFailAlloc_6939_;
goto v_reusejp_6937_;
}
v_reusejp_6937_:
{
return v___x_6938_;
}
}
}
else
{
lean_object* v_val_6941_; lean_object* v___x_6942_; 
v_val_6941_ = lean_ctor_get(v_a_6926_, 0);
lean_inc(v_val_6941_);
lean_dec_ref_known(v_a_6926_, 1);
v___x_6942_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_6941_);
lean_dec(v_val_6941_);
v_numDiscrEqs_6871_ = v___x_6942_;
v___y_6872_ = v___y_6551_;
v___y_6873_ = v___y_6552_;
v___y_6874_ = v___y_6553_;
v___y_6875_ = v___y_6554_;
goto v___jp_6870_;
}
}
else
{
lean_object* v___x_6943_; 
v___x_6943_ = lean_unsigned_to_nat(0u);
v_numDiscrEqs_6871_ = v___x_6943_;
v___y_6872_ = v___y_6551_;
v___y_6873_ = v___y_6552_;
v___y_6874_ = v___y_6553_;
v___y_6875_ = v___y_6554_;
goto v___jp_6870_;
}
v___jp_6566_:
{
lean_object* v___x_6580_; lean_object* v___x_6581_; lean_object* v_aux_6582_; lean_object* v_aux_6583_; lean_object* v_aux_6584_; lean_object* v___x_6585_; lean_object* v___x_6586_; lean_object* v___x_6587_; lean_object* v___f_6588_; uint8_t v___x_6589_; lean_object* v___x_6590_; lean_object* v___x_6591_; lean_object* v___x_6592_; 
lean_inc_ref(v___y_6573_);
v___x_6580_ = lean_array_to_list(v___y_6573_);
lean_inc(v_matcherName_6559_);
v___x_6581_ = l_Lean_mkConst(v_matcherName_6559_, v___x_6580_);
v_aux_6582_ = l_Lean_mkAppN(v___x_6581_, v___y_6571_);
lean_inc_ref(v___y_6569_);
v_aux_6583_ = l_Lean_Expr_app___override(v_aux_6582_, v___y_6569_);
v_aux_6584_ = l_Lean_mkAppN(v_aux_6583_, v___y_6577_);
v___x_6585_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1);
lean_inc_ref_n(v_aux_6584_, 2);
v___x_6586_ = l_Lean_indentExpr(v_aux_6584_);
v___x_6587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6587_, 0, v___x_6585_);
lean_ctor_set(v___x_6587_, 1, v___x_6586_);
v___f_6588_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6588_, 0, v___x_6587_);
v___x_6589_ = 0;
v___x_6590_ = lean_box(v___x_6589_);
v___x_6591_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6591_, 0, v_aux_6584_);
lean_closure_set(v___x_6591_, 1, v___x_6590_);
v___x_6592_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6591_, v___f_6588_, v___y_6575_, v___y_6572_, v___y_6567_, v___y_6578_);
if (lean_obj_tag(v___x_6592_) == 0)
{
lean_object* v___x_6593_; lean_object* v___x_6594_; 
lean_dec_ref_known(v___x_6592_, 1);
v___x_6593_ = lean_array_get_size(v_alts_6564_);
v___x_6594_ = l_Lean_Meta_inferArgumentTypesN(v___x_6593_, v_aux_6584_, v___y_6575_, v___y_6572_, v___y_6567_, v___y_6578_);
if (lean_obj_tag(v___x_6594_) == 0)
{
lean_object* v_a_6595_; lean_object* v___x_6596_; lean_object* v___x_6597_; lean_object* v___x_6598_; lean_object* v___x_6599_; lean_object* v___x_6600_; lean_object* v___x_6601_; lean_object* v___x_6602_; lean_object* v___x_6603_; lean_object* v___x_6604_; lean_object* v___x_6605_; 
v_a_6595_ = lean_ctor_get(v___x_6594_, 0);
lean_inc(v_a_6595_);
lean_dec_ref_known(v___x_6594_, 1);
v___x_6596_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_6544_);
v___x_6597_ = lean_array_get_size(v___x_6596_);
v___x_6598_ = lean_array_get_size(v_a_6595_);
lean_inc_n(v___y_6570_, 3);
v___x_6599_ = l_Array_toSubarray___redArg(v_alts_6564_, v___y_6570_, v___x_6593_);
v___x_6600_ = l_Array_toSubarray___redArg(v___x_6596_, v___y_6570_, v___x_6597_);
v___x_6601_ = l_Array_toSubarray___redArg(v_a_6595_, v___y_6570_, v___x_6598_);
v___x_6602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6602_, 0, v___x_6600_);
lean_ctor_set(v___x_6602_, 1, v___x_6601_);
v___x_6603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6603_, 0, v___x_6599_);
lean_ctor_set(v___x_6603_, 1, v___x_6602_);
lean_inc_ref(v___y_6579_);
v___x_6604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6604_, 0, v___y_6579_);
lean_ctor_set(v___x_6604_, 1, v___x_6603_);
v___x_6605_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v___x_6593_, v_onAlt_6549_, v___y_6574_, v___y_6570_, v___x_6604_, v___y_6575_, v___y_6572_, v___y_6567_, v___y_6578_);
if (lean_obj_tag(v___x_6605_) == 0)
{
lean_object* v_a_6606_; lean_object* v_fst_6607_; lean_object* v___x_6608_; 
v_a_6606_ = lean_ctor_get(v___x_6605_, 0);
lean_inc(v_a_6606_);
lean_dec_ref_known(v___x_6605_, 1);
v_fst_6607_ = lean_ctor_get(v_a_6606_, 0);
lean_inc(v_fst_6607_);
lean_dec(v_a_6606_);
lean_inc(v___y_6578_);
lean_inc_ref(v___y_6567_);
lean_inc(v___y_6572_);
lean_inc_ref(v___y_6575_);
v___x_6608_ = lean_apply_6(v_onRemaining_6550_, v_remaining_6565_, v___y_6575_, v___y_6572_, v___y_6567_, v___y_6578_, lean_box(0));
if (lean_obj_tag(v___x_6608_) == 0)
{
lean_object* v_a_6609_; lean_object* v___x_6611_; uint8_t v_isShared_6612_; uint8_t v_isSharedCheck_6631_; 
v_a_6609_ = lean_ctor_get(v___x_6608_, 0);
v_isSharedCheck_6631_ = !lean_is_exclusive(v___x_6608_);
if (v_isSharedCheck_6631_ == 0)
{
v___x_6611_ = v___x_6608_;
v_isShared_6612_ = v_isSharedCheck_6631_;
goto v_resetjp_6610_;
}
else
{
lean_inc(v_a_6609_);
lean_dec(v___x_6608_);
v___x_6611_ = lean_box(0);
v_isShared_6612_ = v_isSharedCheck_6631_;
goto v_resetjp_6610_;
}
v_resetjp_6610_:
{
lean_object* v_numParams_6613_; lean_object* v_numDiscrs_6614_; lean_object* v_altInfos_6615_; lean_object* v_uElimPos_x3f_6616_; lean_object* v_overlaps_6617_; lean_object* v___x_6619_; uint8_t v_isShared_6620_; uint8_t v_isSharedCheck_6629_; 
v_numParams_6613_ = lean_ctor_get(v_toMatcherInfo_6558_, 0);
v_numDiscrs_6614_ = lean_ctor_get(v_toMatcherInfo_6558_, 1);
v_altInfos_6615_ = lean_ctor_get(v_toMatcherInfo_6558_, 2);
v_uElimPos_x3f_6616_ = lean_ctor_get(v_toMatcherInfo_6558_, 3);
v_overlaps_6617_ = lean_ctor_get(v_toMatcherInfo_6558_, 5);
v_isSharedCheck_6629_ = !lean_is_exclusive(v_toMatcherInfo_6558_);
if (v_isSharedCheck_6629_ == 0)
{
lean_object* v_unused_6630_; 
v_unused_6630_ = lean_ctor_get(v_toMatcherInfo_6558_, 4);
lean_dec(v_unused_6630_);
v___x_6619_ = v_toMatcherInfo_6558_;
v_isShared_6620_ = v_isSharedCheck_6629_;
goto v_resetjp_6618_;
}
else
{
lean_inc(v_overlaps_6617_);
lean_inc(v_uElimPos_x3f_6616_);
lean_inc(v_altInfos_6615_);
lean_inc(v_numDiscrs_6614_);
lean_inc(v_numParams_6613_);
lean_dec(v_toMatcherInfo_6558_);
v___x_6619_ = lean_box(0);
v_isShared_6620_ = v_isSharedCheck_6629_;
goto v_resetjp_6618_;
}
v_resetjp_6618_:
{
lean_object* v_remaining_x27_6621_; lean_object* v___x_6623_; 
v_remaining_x27_6621_ = l_Array_append___redArg(v___y_6568_, v_a_6609_);
lean_dec(v_a_6609_);
if (v_isShared_6620_ == 0)
{
lean_ctor_set(v___x_6619_, 4, v___y_6576_);
v___x_6623_ = v___x_6619_;
goto v_reusejp_6622_;
}
else
{
lean_object* v_reuseFailAlloc_6628_; 
v_reuseFailAlloc_6628_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6628_, 0, v_numParams_6613_);
lean_ctor_set(v_reuseFailAlloc_6628_, 1, v_numDiscrs_6614_);
lean_ctor_set(v_reuseFailAlloc_6628_, 2, v_altInfos_6615_);
lean_ctor_set(v_reuseFailAlloc_6628_, 3, v_uElimPos_x3f_6616_);
lean_ctor_set(v_reuseFailAlloc_6628_, 4, v___y_6576_);
lean_ctor_set(v_reuseFailAlloc_6628_, 5, v_overlaps_6617_);
v___x_6623_ = v_reuseFailAlloc_6628_;
goto v_reusejp_6622_;
}
v_reusejp_6622_:
{
lean_object* v___x_6624_; lean_object* v___x_6626_; 
v___x_6624_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6624_, 0, v___x_6623_);
lean_ctor_set(v___x_6624_, 1, v_matcherName_6559_);
lean_ctor_set(v___x_6624_, 2, v___y_6573_);
lean_ctor_set(v___x_6624_, 3, v___y_6571_);
lean_ctor_set(v___x_6624_, 4, v___y_6569_);
lean_ctor_set(v___x_6624_, 5, v___y_6577_);
lean_ctor_set(v___x_6624_, 6, v_fst_6607_);
lean_ctor_set(v___x_6624_, 7, v_remaining_x27_6621_);
if (v_isShared_6612_ == 0)
{
lean_ctor_set(v___x_6611_, 0, v___x_6624_);
v___x_6626_ = v___x_6611_;
goto v_reusejp_6625_;
}
else
{
lean_object* v_reuseFailAlloc_6627_; 
v_reuseFailAlloc_6627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6627_, 0, v___x_6624_);
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
}
else
{
lean_object* v_a_6632_; lean_object* v___x_6634_; uint8_t v_isShared_6635_; uint8_t v_isSharedCheck_6639_; 
lean_dec(v_fst_6607_);
lean_dec_ref(v___y_6577_);
lean_dec_ref(v___y_6576_);
lean_dec_ref(v___y_6573_);
lean_dec_ref(v___y_6571_);
lean_dec_ref(v___y_6569_);
lean_dec(v___y_6568_);
lean_dec(v_matcherName_6559_);
lean_dec_ref(v_toMatcherInfo_6558_);
v_a_6632_ = lean_ctor_get(v___x_6608_, 0);
v_isSharedCheck_6639_ = !lean_is_exclusive(v___x_6608_);
if (v_isSharedCheck_6639_ == 0)
{
v___x_6634_ = v___x_6608_;
v_isShared_6635_ = v_isSharedCheck_6639_;
goto v_resetjp_6633_;
}
else
{
lean_inc(v_a_6632_);
lean_dec(v___x_6608_);
v___x_6634_ = lean_box(0);
v_isShared_6635_ = v_isSharedCheck_6639_;
goto v_resetjp_6633_;
}
v_resetjp_6633_:
{
lean_object* v___x_6637_; 
if (v_isShared_6635_ == 0)
{
v___x_6637_ = v___x_6634_;
goto v_reusejp_6636_;
}
else
{
lean_object* v_reuseFailAlloc_6638_; 
v_reuseFailAlloc_6638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6638_, 0, v_a_6632_);
v___x_6637_ = v_reuseFailAlloc_6638_;
goto v_reusejp_6636_;
}
v_reusejp_6636_:
{
return v___x_6637_;
}
}
}
}
else
{
lean_object* v_a_6640_; lean_object* v___x_6642_; uint8_t v_isShared_6643_; uint8_t v_isSharedCheck_6647_; 
lean_dec_ref(v___y_6577_);
lean_dec_ref(v___y_6576_);
lean_dec_ref(v___y_6573_);
lean_dec_ref(v___y_6571_);
lean_dec_ref(v___y_6569_);
lean_dec(v___y_6568_);
lean_dec_ref(v_remaining_6565_);
lean_dec(v_matcherName_6559_);
lean_dec_ref(v_toMatcherInfo_6558_);
lean_dec_ref(v_onRemaining_6550_);
v_a_6640_ = lean_ctor_get(v___x_6605_, 0);
v_isSharedCheck_6647_ = !lean_is_exclusive(v___x_6605_);
if (v_isSharedCheck_6647_ == 0)
{
v___x_6642_ = v___x_6605_;
v_isShared_6643_ = v_isSharedCheck_6647_;
goto v_resetjp_6641_;
}
else
{
lean_inc(v_a_6640_);
lean_dec(v___x_6605_);
v___x_6642_ = lean_box(0);
v_isShared_6643_ = v_isSharedCheck_6647_;
goto v_resetjp_6641_;
}
v_resetjp_6641_:
{
lean_object* v___x_6645_; 
if (v_isShared_6643_ == 0)
{
v___x_6645_ = v___x_6642_;
goto v_reusejp_6644_;
}
else
{
lean_object* v_reuseFailAlloc_6646_; 
v_reuseFailAlloc_6646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6646_, 0, v_a_6640_);
v___x_6645_ = v_reuseFailAlloc_6646_;
goto v_reusejp_6644_;
}
v_reusejp_6644_:
{
return v___x_6645_;
}
}
}
}
else
{
lean_object* v_a_6648_; lean_object* v___x_6650_; uint8_t v_isShared_6651_; uint8_t v_isSharedCheck_6655_; 
lean_dec_ref(v___y_6577_);
lean_dec_ref(v___y_6576_);
lean_dec(v___y_6574_);
lean_dec_ref(v___y_6573_);
lean_dec_ref(v___y_6571_);
lean_dec(v___y_6570_);
lean_dec_ref(v___y_6569_);
lean_dec(v___y_6568_);
lean_dec_ref(v_remaining_6565_);
lean_dec_ref(v_alts_6564_);
lean_dec(v_matcherName_6559_);
lean_dec_ref(v_toMatcherInfo_6558_);
lean_dec_ref(v_onRemaining_6550_);
lean_dec_ref(v_onAlt_6549_);
lean_dec_ref(v_matcherApp_6544_);
v_a_6648_ = lean_ctor_get(v___x_6594_, 0);
v_isSharedCheck_6655_ = !lean_is_exclusive(v___x_6594_);
if (v_isSharedCheck_6655_ == 0)
{
v___x_6650_ = v___x_6594_;
v_isShared_6651_ = v_isSharedCheck_6655_;
goto v_resetjp_6649_;
}
else
{
lean_inc(v_a_6648_);
lean_dec(v___x_6594_);
v___x_6650_ = lean_box(0);
v_isShared_6651_ = v_isSharedCheck_6655_;
goto v_resetjp_6649_;
}
v_resetjp_6649_:
{
lean_object* v___x_6653_; 
if (v_isShared_6651_ == 0)
{
v___x_6653_ = v___x_6650_;
goto v_reusejp_6652_;
}
else
{
lean_object* v_reuseFailAlloc_6654_; 
v_reuseFailAlloc_6654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6654_, 0, v_a_6648_);
v___x_6653_ = v_reuseFailAlloc_6654_;
goto v_reusejp_6652_;
}
v_reusejp_6652_:
{
return v___x_6653_;
}
}
}
}
else
{
lean_object* v_a_6656_; lean_object* v___x_6658_; uint8_t v_isShared_6659_; uint8_t v_isSharedCheck_6663_; 
lean_dec_ref(v_aux_6584_);
lean_dec_ref(v___y_6577_);
lean_dec_ref(v___y_6576_);
lean_dec(v___y_6574_);
lean_dec_ref(v___y_6573_);
lean_dec_ref(v___y_6571_);
lean_dec(v___y_6570_);
lean_dec_ref(v___y_6569_);
lean_dec(v___y_6568_);
lean_dec_ref(v_remaining_6565_);
lean_dec_ref(v_alts_6564_);
lean_dec(v_matcherName_6559_);
lean_dec_ref(v_toMatcherInfo_6558_);
lean_dec_ref(v_onRemaining_6550_);
lean_dec_ref(v_onAlt_6549_);
lean_dec_ref(v_matcherApp_6544_);
v_a_6656_ = lean_ctor_get(v___x_6592_, 0);
v_isSharedCheck_6663_ = !lean_is_exclusive(v___x_6592_);
if (v_isSharedCheck_6663_ == 0)
{
v___x_6658_ = v___x_6592_;
v_isShared_6659_ = v_isSharedCheck_6663_;
goto v_resetjp_6657_;
}
else
{
lean_inc(v_a_6656_);
lean_dec(v___x_6592_);
v___x_6658_ = lean_box(0);
v_isShared_6659_ = v_isSharedCheck_6663_;
goto v_resetjp_6657_;
}
v_resetjp_6657_:
{
lean_object* v___x_6661_; 
if (v_isShared_6659_ == 0)
{
v___x_6661_ = v___x_6658_;
goto v_reusejp_6660_;
}
else
{
lean_object* v_reuseFailAlloc_6662_; 
v_reuseFailAlloc_6662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6662_, 0, v_a_6656_);
v___x_6661_ = v_reuseFailAlloc_6662_;
goto v_reusejp_6660_;
}
v_reusejp_6660_:
{
return v___x_6661_;
}
}
}
}
v___jp_6665_:
{
lean_object* v___x_6678_; lean_object* v_remaining_x27_6679_; lean_object* v___x_6680_; lean_object* v___x_6681_; lean_object* v___x_6682_; lean_object* v___x_6683_; lean_object* v___x_6684_; lean_object* v___x_6685_; size_t v_sz_6686_; lean_object* v___x_6687_; 
v___x_6678_ = lean_unsigned_to_nat(0u);
v_remaining_x27_6679_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_6680_ = l_Array_reverse___redArg(v___y_6667_);
v___x_6681_ = lean_array_get_size(v___x_6680_);
v___x_6682_ = l_Array_toSubarray___redArg(v___x_6680_, v___x_6678_, v___x_6681_);
lean_inc_ref(v___y_6672_);
v___x_6683_ = l_Array_reverse___redArg(v___y_6672_);
v___x_6684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6684_, 0, v___x_6678_);
lean_ctor_set(v___x_6684_, 1, v___x_6682_);
v___x_6685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6685_, 0, v_remaining_x27_6679_);
lean_ctor_set(v___x_6685_, 1, v___x_6684_);
v_sz_6686_ = lean_array_size(v___x_6683_);
v___x_6687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(v___x_6683_, v_sz_6686_, v___y_6666_, v___x_6685_, v___y_6674_, v___y_6675_, v___y_6676_, v___y_6677_);
lean_dec_ref(v___x_6683_);
if (lean_obj_tag(v___x_6687_) == 0)
{
lean_object* v_a_6688_; lean_object* v_snd_6689_; 
v_a_6688_ = lean_ctor_get(v___x_6687_, 0);
lean_inc(v_a_6688_);
lean_dec_ref_known(v___x_6687_, 1);
v_snd_6689_ = lean_ctor_get(v_a_6688_, 1);
lean_inc(v_snd_6689_);
if (v_useSplitter_6545_ == 0)
{
lean_object* v_fst_6690_; lean_object* v_fst_6691_; 
lean_dec(v___y_6669_);
v_fst_6690_ = lean_ctor_get(v_a_6688_, 0);
lean_inc(v_fst_6690_);
lean_dec(v_a_6688_);
v_fst_6691_ = lean_ctor_get(v_snd_6689_, 0);
lean_inc(v_fst_6691_);
lean_dec(v_snd_6689_);
v___y_6567_ = v___y_6676_;
v___y_6568_ = v_fst_6690_;
v___y_6569_ = v___y_6668_;
v___y_6570_ = v___x_6678_;
v___y_6571_ = v___y_6670_;
v___y_6572_ = v___y_6675_;
v___y_6573_ = v_matcherLevels_6673_;
v___y_6574_ = v_fst_6691_;
v___y_6575_ = v___y_6674_;
v___y_6576_ = v___y_6671_;
v___y_6577_ = v___y_6672_;
v___y_6578_ = v___y_6677_;
v___y_6579_ = v_remaining_x27_6679_;
goto v___jp_6566_;
}
else
{
if (v_isCasesOn_6664_ == 0)
{
lean_object* v___x_6693_; uint8_t v_isShared_6694_; uint8_t v_isSharedCheck_6851_; 
v_isSharedCheck_6851_ = !lean_is_exclusive(v_matcherApp_6544_);
if (v_isSharedCheck_6851_ == 0)
{
lean_object* v_unused_6852_; lean_object* v_unused_6853_; lean_object* v_unused_6854_; lean_object* v_unused_6855_; lean_object* v_unused_6856_; lean_object* v_unused_6857_; lean_object* v_unused_6858_; lean_object* v_unused_6859_; 
v_unused_6852_ = lean_ctor_get(v_matcherApp_6544_, 7);
lean_dec(v_unused_6852_);
v_unused_6853_ = lean_ctor_get(v_matcherApp_6544_, 6);
lean_dec(v_unused_6853_);
v_unused_6854_ = lean_ctor_get(v_matcherApp_6544_, 5);
lean_dec(v_unused_6854_);
v_unused_6855_ = lean_ctor_get(v_matcherApp_6544_, 4);
lean_dec(v_unused_6855_);
v_unused_6856_ = lean_ctor_get(v_matcherApp_6544_, 3);
lean_dec(v_unused_6856_);
v_unused_6857_ = lean_ctor_get(v_matcherApp_6544_, 2);
lean_dec(v_unused_6857_);
v_unused_6858_ = lean_ctor_get(v_matcherApp_6544_, 1);
lean_dec(v_unused_6858_);
v_unused_6859_ = lean_ctor_get(v_matcherApp_6544_, 0);
lean_dec(v_unused_6859_);
v___x_6693_ = v_matcherApp_6544_;
v_isShared_6694_ = v_isSharedCheck_6851_;
goto v_resetjp_6692_;
}
else
{
lean_dec(v_matcherApp_6544_);
v___x_6693_ = lean_box(0);
v_isShared_6694_ = v_isSharedCheck_6851_;
goto v_resetjp_6692_;
}
v_resetjp_6692_:
{
lean_object* v_fst_6695_; lean_object* v___x_6697_; uint8_t v_isShared_6698_; uint8_t v_isSharedCheck_6849_; 
v_fst_6695_ = lean_ctor_get(v_a_6688_, 0);
v_isSharedCheck_6849_ = !lean_is_exclusive(v_a_6688_);
if (v_isSharedCheck_6849_ == 0)
{
lean_object* v_unused_6850_; 
v_unused_6850_ = lean_ctor_get(v_a_6688_, 1);
lean_dec(v_unused_6850_);
v___x_6697_ = v_a_6688_;
v_isShared_6698_ = v_isSharedCheck_6849_;
goto v_resetjp_6696_;
}
else
{
lean_inc(v_fst_6695_);
lean_dec(v_a_6688_);
v___x_6697_ = lean_box(0);
v_isShared_6698_ = v_isSharedCheck_6849_;
goto v_resetjp_6696_;
}
v_resetjp_6696_:
{
lean_object* v_fst_6699_; lean_object* v___x_6701_; uint8_t v_isShared_6702_; uint8_t v_isSharedCheck_6847_; 
v_fst_6699_ = lean_ctor_get(v_snd_6689_, 0);
v_isSharedCheck_6847_ = !lean_is_exclusive(v_snd_6689_);
if (v_isSharedCheck_6847_ == 0)
{
lean_object* v_unused_6848_; 
v_unused_6848_ = lean_ctor_get(v_snd_6689_, 1);
lean_dec(v_unused_6848_);
v___x_6701_ = v_snd_6689_;
v_isShared_6702_ = v_isSharedCheck_6847_;
goto v_resetjp_6700_;
}
else
{
lean_inc(v_fst_6699_);
lean_dec(v_snd_6689_);
v___x_6701_ = lean_box(0);
v_isShared_6702_ = v_isSharedCheck_6847_;
goto v_resetjp_6700_;
}
v_resetjp_6700_:
{
lean_object* v___x_6703_; lean_object* v___x_6704_; lean_object* v_aux1_6705_; lean_object* v_aux1_6706_; lean_object* v_aux1_6707_; lean_object* v___x_6708_; lean_object* v___x_6709_; lean_object* v___x_6710_; lean_object* v___x_6711_; lean_object* v___x_6712_; lean_object* v___f_6713_; uint8_t v___x_6714_; lean_object* v___x_6715_; lean_object* v___x_6716_; lean_object* v___x_6717_; 
lean_inc_ref(v_matcherLevels_6673_);
v___x_6703_ = lean_array_to_list(v_matcherLevels_6673_);
lean_inc(v___x_6703_);
lean_inc(v_matcherName_6559_);
v___x_6704_ = l_Lean_mkConst(v_matcherName_6559_, v___x_6703_);
v_aux1_6705_ = l_Lean_mkAppN(v___x_6704_, v___y_6670_);
lean_inc_ref(v___y_6668_);
v_aux1_6706_ = l_Lean_Expr_app___override(v_aux1_6705_, v___y_6668_);
v_aux1_6707_ = l_Lean_mkAppN(v_aux1_6706_, v___y_6672_);
v___x_6708_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3);
lean_inc_ref_n(v_aux1_6707_, 2);
v___x_6709_ = l_Lean_indentExpr(v_aux1_6707_);
v___x_6710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6710_, 0, v___x_6708_);
lean_ctor_set(v___x_6710_, 1, v___x_6709_);
v___x_6711_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5);
v___x_6712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6712_, 0, v___x_6710_);
lean_ctor_set(v___x_6712_, 1, v___x_6711_);
v___f_6713_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6713_, 0, v___x_6712_);
v___x_6714_ = 0;
v___x_6715_ = lean_box(v___x_6714_);
v___x_6716_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6716_, 0, v_aux1_6707_);
lean_closure_set(v___x_6716_, 1, v___x_6715_);
v___x_6717_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6716_, v___f_6713_, v___y_6674_, v___y_6675_, v___y_6676_, v___y_6677_);
if (lean_obj_tag(v___x_6717_) == 0)
{
lean_object* v___x_6718_; lean_object* v___x_6719_; 
lean_dec_ref_known(v___x_6717_, 1);
v___x_6718_ = lean_array_get_size(v_alts_6564_);
v___x_6719_ = l_Lean_Meta_inferArgumentTypesN(v___x_6718_, v_aux1_6707_, v___y_6674_, v___y_6675_, v___y_6676_, v___y_6677_);
if (lean_obj_tag(v___x_6719_) == 0)
{
lean_object* v_a_6720_; lean_object* v___x_6721_; 
v_a_6720_ = lean_ctor_get(v___x_6719_, 0);
lean_inc(v_a_6720_);
lean_dec_ref_known(v___x_6719_, 1);
lean_inc(v___y_6677_);
lean_inc_ref(v___y_6676_);
lean_inc(v___y_6675_);
lean_inc_ref(v___y_6674_);
v___x_6721_ = lean_get_match_equations_for(v_matcherName_6559_, v___y_6674_, v___y_6675_, v___y_6676_, v___y_6677_);
if (lean_obj_tag(v___x_6721_) == 0)
{
lean_object* v_a_6722_; lean_object* v_splitterName_6723_; lean_object* v_splitterMatchInfo_6724_; lean_object* v___x_6725_; lean_object* v_aux2_6726_; lean_object* v_aux2_6727_; lean_object* v_aux2_6728_; lean_object* v___x_6729_; lean_object* v___x_6730_; lean_object* v___x_6731_; lean_object* v___x_6732_; lean_object* v___f_6733_; lean_object* v___x_6734_; lean_object* v___x_6735_; lean_object* v___x_6736_; 
v_a_6722_ = lean_ctor_get(v___x_6721_, 0);
lean_inc(v_a_6722_);
lean_dec_ref_known(v___x_6721_, 1);
v_splitterName_6723_ = lean_ctor_get(v_a_6722_, 1);
lean_inc_n(v_splitterName_6723_, 2);
v_splitterMatchInfo_6724_ = lean_ctor_get(v_a_6722_, 2);
lean_inc_ref(v_splitterMatchInfo_6724_);
lean_dec(v_a_6722_);
v___x_6725_ = l_Lean_mkConst(v_splitterName_6723_, v___x_6703_);
v_aux2_6726_ = l_Lean_mkAppN(v___x_6725_, v___y_6670_);
lean_inc_ref(v___y_6668_);
v_aux2_6727_ = l_Lean_Expr_app___override(v_aux2_6726_, v___y_6668_);
v_aux2_6728_ = l_Lean_mkAppN(v_aux2_6727_, v___y_6672_);
v___x_6729_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1);
lean_inc_ref_n(v_aux2_6728_, 2);
v___x_6730_ = l_Lean_indentExpr(v_aux2_6728_);
v___x_6731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6731_, 0, v___x_6729_);
lean_ctor_set(v___x_6731_, 1, v___x_6730_);
v___x_6732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6732_, 0, v___x_6731_);
lean_ctor_set(v___x_6732_, 1, v___x_6711_);
v___f_6733_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6733_, 0, v___x_6732_);
v___x_6734_ = lean_box(v___x_6714_);
v___x_6735_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6735_, 0, v_aux2_6728_);
lean_closure_set(v___x_6735_, 1, v___x_6734_);
v___x_6736_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6735_, v___f_6733_, v___y_6674_, v___y_6675_, v___y_6676_, v___y_6677_);
if (lean_obj_tag(v___x_6736_) == 0)
{
lean_object* v___x_6737_; 
lean_dec_ref_known(v___x_6736_, 1);
v___x_6737_ = l_Lean_Meta_inferArgumentTypesN(v___x_6718_, v_aux2_6728_, v___y_6674_, v___y_6675_, v___y_6676_, v___y_6677_);
if (lean_obj_tag(v___x_6737_) == 0)
{
lean_object* v_a_6738_; lean_object* v_numParams_6739_; lean_object* v_numDiscrs_6740_; lean_object* v_altInfos_6741_; lean_object* v_uElimPos_x3f_6742_; lean_object* v_overlaps_6743_; lean_object* v_altInfos_6744_; lean_object* v___x_6746_; uint8_t v_isShared_6747_; uint8_t v_isSharedCheck_6801_; 
v_a_6738_ = lean_ctor_get(v___x_6737_, 0);
lean_inc(v_a_6738_);
lean_dec_ref_known(v___x_6737_, 1);
v_numParams_6739_ = lean_ctor_get(v_toMatcherInfo_6558_, 0);
lean_inc(v_numParams_6739_);
v_numDiscrs_6740_ = lean_ctor_get(v_toMatcherInfo_6558_, 1);
lean_inc(v_numDiscrs_6740_);
v_altInfos_6741_ = lean_ctor_get(v_toMatcherInfo_6558_, 2);
lean_inc_ref(v_altInfos_6741_);
v_uElimPos_x3f_6742_ = lean_ctor_get(v_toMatcherInfo_6558_, 3);
lean_inc(v_uElimPos_x3f_6742_);
v_overlaps_6743_ = lean_ctor_get(v_toMatcherInfo_6558_, 5);
lean_inc_ref(v_overlaps_6743_);
lean_dec_ref(v_toMatcherInfo_6558_);
v_altInfos_6744_ = lean_ctor_get(v_splitterMatchInfo_6724_, 2);
v_isSharedCheck_6801_ = !lean_is_exclusive(v_splitterMatchInfo_6724_);
if (v_isSharedCheck_6801_ == 0)
{
lean_object* v_unused_6802_; lean_object* v_unused_6803_; lean_object* v_unused_6804_; lean_object* v_unused_6805_; lean_object* v_unused_6806_; 
v_unused_6802_ = lean_ctor_get(v_splitterMatchInfo_6724_, 5);
lean_dec(v_unused_6802_);
v_unused_6803_ = lean_ctor_get(v_splitterMatchInfo_6724_, 4);
lean_dec(v_unused_6803_);
v_unused_6804_ = lean_ctor_get(v_splitterMatchInfo_6724_, 3);
lean_dec(v_unused_6804_);
v_unused_6805_ = lean_ctor_get(v_splitterMatchInfo_6724_, 1);
lean_dec(v_unused_6805_);
v_unused_6806_ = lean_ctor_get(v_splitterMatchInfo_6724_, 0);
lean_dec(v_unused_6806_);
v___x_6746_ = v_splitterMatchInfo_6724_;
v_isShared_6747_ = v_isSharedCheck_6801_;
goto v_resetjp_6745_;
}
else
{
lean_inc(v_altInfos_6744_);
lean_dec(v_splitterMatchInfo_6724_);
v___x_6746_ = lean_box(0);
v_isShared_6747_ = v_isSharedCheck_6801_;
goto v_resetjp_6745_;
}
v_resetjp_6745_:
{
lean_object* v___x_6748_; lean_object* v___x_6749_; lean_object* v___x_6750_; lean_object* v___x_6751_; lean_object* v___x_6752_; lean_object* v___x_6753_; lean_object* v___x_6754_; lean_object* v___x_6755_; lean_object* v___x_6756_; lean_object* v___x_6758_; 
v___x_6748_ = lean_array_get_size(v_altInfos_6741_);
v___x_6749_ = lean_array_get_size(v_altInfos_6744_);
v___x_6750_ = lean_array_get_size(v_a_6720_);
v___x_6751_ = lean_array_get_size(v_a_6738_);
v___x_6752_ = l_Array_toSubarray___redArg(v_alts_6564_, v___x_6678_, v___x_6718_);
lean_inc_ref(v_altInfos_6741_);
v___x_6753_ = l_Array_toSubarray___redArg(v_altInfos_6741_, v___x_6678_, v___x_6748_);
v___x_6754_ = l_Array_toSubarray___redArg(v_altInfos_6744_, v___x_6678_, v___x_6749_);
v___x_6755_ = l_Array_toSubarray___redArg(v_a_6720_, v___x_6678_, v___x_6750_);
v___x_6756_ = l_Array_toSubarray___redArg(v_a_6738_, v___x_6678_, v___x_6751_);
if (v_isShared_6702_ == 0)
{
lean_ctor_set(v___x_6701_, 1, v___x_6756_);
lean_ctor_set(v___x_6701_, 0, v___x_6755_);
v___x_6758_ = v___x_6701_;
goto v_reusejp_6757_;
}
else
{
lean_object* v_reuseFailAlloc_6800_; 
v_reuseFailAlloc_6800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6800_, 0, v___x_6755_);
lean_ctor_set(v_reuseFailAlloc_6800_, 1, v___x_6756_);
v___x_6758_ = v_reuseFailAlloc_6800_;
goto v_reusejp_6757_;
}
v_reusejp_6757_:
{
lean_object* v___x_6760_; 
if (v_isShared_6698_ == 0)
{
lean_ctor_set(v___x_6697_, 1, v___x_6758_);
lean_ctor_set(v___x_6697_, 0, v___x_6754_);
v___x_6760_ = v___x_6697_;
goto v_reusejp_6759_;
}
else
{
lean_object* v_reuseFailAlloc_6799_; 
v_reuseFailAlloc_6799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6799_, 0, v___x_6754_);
lean_ctor_set(v_reuseFailAlloc_6799_, 1, v___x_6758_);
v___x_6760_ = v_reuseFailAlloc_6799_;
goto v_reusejp_6759_;
}
v_reusejp_6759_:
{
lean_object* v___x_6761_; lean_object* v___x_6762_; lean_object* v___x_6763_; lean_object* v___x_6764_; 
v___x_6761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6761_, 0, v___x_6753_);
lean_ctor_set(v___x_6761_, 1, v___x_6760_);
v___x_6762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6762_, 0, v___x_6752_);
lean_ctor_set(v___x_6762_, 1, v___x_6761_);
v___x_6763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6763_, 0, v_remaining_x27_6679_);
lean_ctor_set(v___x_6763_, 1, v___x_6762_);
v___x_6764_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v___x_6718_, v_onAlt_6549_, v_useSplitter_6545_, v_fst_6699_, v___y_6669_, v___x_6678_, v___x_6763_, v___y_6674_, v___y_6675_, v___y_6676_, v___y_6677_);
if (lean_obj_tag(v___x_6764_) == 0)
{
lean_object* v_a_6765_; lean_object* v_fst_6766_; lean_object* v___x_6767_; 
v_a_6765_ = lean_ctor_get(v___x_6764_, 0);
lean_inc(v_a_6765_);
lean_dec_ref_known(v___x_6764_, 1);
v_fst_6766_ = lean_ctor_get(v_a_6765_, 0);
lean_inc(v_fst_6766_);
lean_dec(v_a_6765_);
lean_inc(v___y_6677_);
lean_inc_ref(v___y_6676_);
lean_inc(v___y_6675_);
lean_inc_ref(v___y_6674_);
v___x_6767_ = lean_apply_6(v_onRemaining_6550_, v_remaining_6565_, v___y_6674_, v___y_6675_, v___y_6676_, v___y_6677_, lean_box(0));
if (lean_obj_tag(v___x_6767_) == 0)
{
lean_object* v_a_6768_; lean_object* v___x_6770_; uint8_t v_isShared_6771_; uint8_t v_isSharedCheck_6782_; 
v_a_6768_ = lean_ctor_get(v___x_6767_, 0);
v_isSharedCheck_6782_ = !lean_is_exclusive(v___x_6767_);
if (v_isSharedCheck_6782_ == 0)
{
v___x_6770_ = v___x_6767_;
v_isShared_6771_ = v_isSharedCheck_6782_;
goto v_resetjp_6769_;
}
else
{
lean_inc(v_a_6768_);
lean_dec(v___x_6767_);
v___x_6770_ = lean_box(0);
v_isShared_6771_ = v_isSharedCheck_6782_;
goto v_resetjp_6769_;
}
v_resetjp_6769_:
{
lean_object* v_remaining_x27_6772_; lean_object* v___x_6774_; 
v_remaining_x27_6772_ = l_Array_append___redArg(v_fst_6695_, v_a_6768_);
lean_dec(v_a_6768_);
if (v_isShared_6747_ == 0)
{
lean_ctor_set(v___x_6746_, 5, v_overlaps_6743_);
lean_ctor_set(v___x_6746_, 4, v___y_6671_);
lean_ctor_set(v___x_6746_, 3, v_uElimPos_x3f_6742_);
lean_ctor_set(v___x_6746_, 2, v_altInfos_6741_);
lean_ctor_set(v___x_6746_, 1, v_numDiscrs_6740_);
lean_ctor_set(v___x_6746_, 0, v_numParams_6739_);
v___x_6774_ = v___x_6746_;
goto v_reusejp_6773_;
}
else
{
lean_object* v_reuseFailAlloc_6781_; 
v_reuseFailAlloc_6781_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6781_, 0, v_numParams_6739_);
lean_ctor_set(v_reuseFailAlloc_6781_, 1, v_numDiscrs_6740_);
lean_ctor_set(v_reuseFailAlloc_6781_, 2, v_altInfos_6741_);
lean_ctor_set(v_reuseFailAlloc_6781_, 3, v_uElimPos_x3f_6742_);
lean_ctor_set(v_reuseFailAlloc_6781_, 4, v___y_6671_);
lean_ctor_set(v_reuseFailAlloc_6781_, 5, v_overlaps_6743_);
v___x_6774_ = v_reuseFailAlloc_6781_;
goto v_reusejp_6773_;
}
v_reusejp_6773_:
{
lean_object* v___x_6776_; 
if (v_isShared_6694_ == 0)
{
lean_ctor_set(v___x_6693_, 7, v_remaining_x27_6772_);
lean_ctor_set(v___x_6693_, 6, v_fst_6766_);
lean_ctor_set(v___x_6693_, 5, v___y_6672_);
lean_ctor_set(v___x_6693_, 4, v___y_6668_);
lean_ctor_set(v___x_6693_, 3, v___y_6670_);
lean_ctor_set(v___x_6693_, 2, v_matcherLevels_6673_);
lean_ctor_set(v___x_6693_, 1, v_splitterName_6723_);
lean_ctor_set(v___x_6693_, 0, v___x_6774_);
v___x_6776_ = v___x_6693_;
goto v_reusejp_6775_;
}
else
{
lean_object* v_reuseFailAlloc_6780_; 
v_reuseFailAlloc_6780_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_6780_, 0, v___x_6774_);
lean_ctor_set(v_reuseFailAlloc_6780_, 1, v_splitterName_6723_);
lean_ctor_set(v_reuseFailAlloc_6780_, 2, v_matcherLevels_6673_);
lean_ctor_set(v_reuseFailAlloc_6780_, 3, v___y_6670_);
lean_ctor_set(v_reuseFailAlloc_6780_, 4, v___y_6668_);
lean_ctor_set(v_reuseFailAlloc_6780_, 5, v___y_6672_);
lean_ctor_set(v_reuseFailAlloc_6780_, 6, v_fst_6766_);
lean_ctor_set(v_reuseFailAlloc_6780_, 7, v_remaining_x27_6772_);
v___x_6776_ = v_reuseFailAlloc_6780_;
goto v_reusejp_6775_;
}
v_reusejp_6775_:
{
lean_object* v___x_6778_; 
if (v_isShared_6771_ == 0)
{
lean_ctor_set(v___x_6770_, 0, v___x_6776_);
v___x_6778_ = v___x_6770_;
goto v_reusejp_6777_;
}
else
{
lean_object* v_reuseFailAlloc_6779_; 
v_reuseFailAlloc_6779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6779_, 0, v___x_6776_);
v___x_6778_ = v_reuseFailAlloc_6779_;
goto v_reusejp_6777_;
}
v_reusejp_6777_:
{
return v___x_6778_;
}
}
}
}
}
else
{
lean_object* v_a_6783_; lean_object* v___x_6785_; uint8_t v_isShared_6786_; uint8_t v_isSharedCheck_6790_; 
lean_dec(v_fst_6766_);
lean_del_object(v___x_6746_);
lean_dec_ref(v_overlaps_6743_);
lean_dec(v_uElimPos_x3f_6742_);
lean_dec_ref(v_altInfos_6741_);
lean_dec(v_numDiscrs_6740_);
lean_dec(v_numParams_6739_);
lean_dec(v_splitterName_6723_);
lean_dec(v_fst_6695_);
lean_del_object(v___x_6693_);
lean_dec_ref(v_matcherLevels_6673_);
lean_dec_ref(v___y_6672_);
lean_dec_ref(v___y_6671_);
lean_dec_ref(v___y_6670_);
lean_dec_ref(v___y_6668_);
v_a_6783_ = lean_ctor_get(v___x_6767_, 0);
v_isSharedCheck_6790_ = !lean_is_exclusive(v___x_6767_);
if (v_isSharedCheck_6790_ == 0)
{
v___x_6785_ = v___x_6767_;
v_isShared_6786_ = v_isSharedCheck_6790_;
goto v_resetjp_6784_;
}
else
{
lean_inc(v_a_6783_);
lean_dec(v___x_6767_);
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
lean_del_object(v___x_6746_);
lean_dec_ref(v_overlaps_6743_);
lean_dec(v_uElimPos_x3f_6742_);
lean_dec_ref(v_altInfos_6741_);
lean_dec(v_numDiscrs_6740_);
lean_dec(v_numParams_6739_);
lean_dec(v_splitterName_6723_);
lean_dec(v_fst_6695_);
lean_del_object(v___x_6693_);
lean_dec_ref(v_matcherLevels_6673_);
lean_dec_ref(v___y_6672_);
lean_dec_ref(v___y_6671_);
lean_dec_ref(v___y_6670_);
lean_dec_ref(v___y_6668_);
lean_dec_ref(v_remaining_6565_);
lean_dec_ref(v_onRemaining_6550_);
v_a_6791_ = lean_ctor_get(v___x_6764_, 0);
v_isSharedCheck_6798_ = !lean_is_exclusive(v___x_6764_);
if (v_isSharedCheck_6798_ == 0)
{
v___x_6793_ = v___x_6764_;
v_isShared_6794_ = v_isSharedCheck_6798_;
goto v_resetjp_6792_;
}
else
{
lean_inc(v_a_6791_);
lean_dec(v___x_6764_);
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
}
}
}
else
{
lean_object* v_a_6807_; lean_object* v___x_6809_; uint8_t v_isShared_6810_; uint8_t v_isSharedCheck_6814_; 
lean_dec_ref(v_splitterMatchInfo_6724_);
lean_dec(v_splitterName_6723_);
lean_dec(v_a_6720_);
lean_del_object(v___x_6701_);
lean_dec(v_fst_6699_);
lean_del_object(v___x_6697_);
lean_dec(v_fst_6695_);
lean_del_object(v___x_6693_);
lean_dec_ref(v_matcherLevels_6673_);
lean_dec_ref(v___y_6672_);
lean_dec_ref(v___y_6671_);
lean_dec_ref(v___y_6670_);
lean_dec(v___y_6669_);
lean_dec_ref(v___y_6668_);
lean_dec_ref(v_remaining_6565_);
lean_dec_ref(v_alts_6564_);
lean_dec_ref(v_toMatcherInfo_6558_);
lean_dec_ref(v_onRemaining_6550_);
lean_dec_ref(v_onAlt_6549_);
v_a_6807_ = lean_ctor_get(v___x_6737_, 0);
v_isSharedCheck_6814_ = !lean_is_exclusive(v___x_6737_);
if (v_isSharedCheck_6814_ == 0)
{
v___x_6809_ = v___x_6737_;
v_isShared_6810_ = v_isSharedCheck_6814_;
goto v_resetjp_6808_;
}
else
{
lean_inc(v_a_6807_);
lean_dec(v___x_6737_);
v___x_6809_ = lean_box(0);
v_isShared_6810_ = v_isSharedCheck_6814_;
goto v_resetjp_6808_;
}
v_resetjp_6808_:
{
lean_object* v___x_6812_; 
if (v_isShared_6810_ == 0)
{
v___x_6812_ = v___x_6809_;
goto v_reusejp_6811_;
}
else
{
lean_object* v_reuseFailAlloc_6813_; 
v_reuseFailAlloc_6813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6813_, 0, v_a_6807_);
v___x_6812_ = v_reuseFailAlloc_6813_;
goto v_reusejp_6811_;
}
v_reusejp_6811_:
{
return v___x_6812_;
}
}
}
}
else
{
lean_object* v_a_6815_; lean_object* v___x_6817_; uint8_t v_isShared_6818_; uint8_t v_isSharedCheck_6822_; 
lean_dec_ref(v_aux2_6728_);
lean_dec_ref(v_splitterMatchInfo_6724_);
lean_dec(v_splitterName_6723_);
lean_dec(v_a_6720_);
lean_del_object(v___x_6701_);
lean_dec(v_fst_6699_);
lean_del_object(v___x_6697_);
lean_dec(v_fst_6695_);
lean_del_object(v___x_6693_);
lean_dec_ref(v_matcherLevels_6673_);
lean_dec_ref(v___y_6672_);
lean_dec_ref(v___y_6671_);
lean_dec_ref(v___y_6670_);
lean_dec(v___y_6669_);
lean_dec_ref(v___y_6668_);
lean_dec_ref(v_remaining_6565_);
lean_dec_ref(v_alts_6564_);
lean_dec_ref(v_toMatcherInfo_6558_);
lean_dec_ref(v_onRemaining_6550_);
lean_dec_ref(v_onAlt_6549_);
v_a_6815_ = lean_ctor_get(v___x_6736_, 0);
v_isSharedCheck_6822_ = !lean_is_exclusive(v___x_6736_);
if (v_isSharedCheck_6822_ == 0)
{
v___x_6817_ = v___x_6736_;
v_isShared_6818_ = v_isSharedCheck_6822_;
goto v_resetjp_6816_;
}
else
{
lean_inc(v_a_6815_);
lean_dec(v___x_6736_);
v___x_6817_ = lean_box(0);
v_isShared_6818_ = v_isSharedCheck_6822_;
goto v_resetjp_6816_;
}
v_resetjp_6816_:
{
lean_object* v___x_6820_; 
if (v_isShared_6818_ == 0)
{
v___x_6820_ = v___x_6817_;
goto v_reusejp_6819_;
}
else
{
lean_object* v_reuseFailAlloc_6821_; 
v_reuseFailAlloc_6821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6821_, 0, v_a_6815_);
v___x_6820_ = v_reuseFailAlloc_6821_;
goto v_reusejp_6819_;
}
v_reusejp_6819_:
{
return v___x_6820_;
}
}
}
}
else
{
lean_object* v_a_6823_; lean_object* v___x_6825_; uint8_t v_isShared_6826_; uint8_t v_isSharedCheck_6830_; 
lean_dec(v_a_6720_);
lean_dec(v___x_6703_);
lean_del_object(v___x_6701_);
lean_dec(v_fst_6699_);
lean_del_object(v___x_6697_);
lean_dec(v_fst_6695_);
lean_del_object(v___x_6693_);
lean_dec_ref(v_matcherLevels_6673_);
lean_dec_ref(v___y_6672_);
lean_dec_ref(v___y_6671_);
lean_dec_ref(v___y_6670_);
lean_dec(v___y_6669_);
lean_dec_ref(v___y_6668_);
lean_dec_ref(v_remaining_6565_);
lean_dec_ref(v_alts_6564_);
lean_dec_ref(v_toMatcherInfo_6558_);
lean_dec_ref(v_onRemaining_6550_);
lean_dec_ref(v_onAlt_6549_);
v_a_6823_ = lean_ctor_get(v___x_6721_, 0);
v_isSharedCheck_6830_ = !lean_is_exclusive(v___x_6721_);
if (v_isSharedCheck_6830_ == 0)
{
v___x_6825_ = v___x_6721_;
v_isShared_6826_ = v_isSharedCheck_6830_;
goto v_resetjp_6824_;
}
else
{
lean_inc(v_a_6823_);
lean_dec(v___x_6721_);
v___x_6825_ = lean_box(0);
v_isShared_6826_ = v_isSharedCheck_6830_;
goto v_resetjp_6824_;
}
v_resetjp_6824_:
{
lean_object* v___x_6828_; 
if (v_isShared_6826_ == 0)
{
v___x_6828_ = v___x_6825_;
goto v_reusejp_6827_;
}
else
{
lean_object* v_reuseFailAlloc_6829_; 
v_reuseFailAlloc_6829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6829_, 0, v_a_6823_);
v___x_6828_ = v_reuseFailAlloc_6829_;
goto v_reusejp_6827_;
}
v_reusejp_6827_:
{
return v___x_6828_;
}
}
}
}
else
{
lean_object* v_a_6831_; lean_object* v___x_6833_; uint8_t v_isShared_6834_; uint8_t v_isSharedCheck_6838_; 
lean_dec(v___x_6703_);
lean_del_object(v___x_6701_);
lean_dec(v_fst_6699_);
lean_del_object(v___x_6697_);
lean_dec(v_fst_6695_);
lean_del_object(v___x_6693_);
lean_dec_ref(v_matcherLevels_6673_);
lean_dec_ref(v___y_6672_);
lean_dec_ref(v___y_6671_);
lean_dec_ref(v___y_6670_);
lean_dec(v___y_6669_);
lean_dec_ref(v___y_6668_);
lean_dec_ref(v_remaining_6565_);
lean_dec_ref(v_alts_6564_);
lean_dec(v_matcherName_6559_);
lean_dec_ref(v_toMatcherInfo_6558_);
lean_dec_ref(v_onRemaining_6550_);
lean_dec_ref(v_onAlt_6549_);
v_a_6831_ = lean_ctor_get(v___x_6719_, 0);
v_isSharedCheck_6838_ = !lean_is_exclusive(v___x_6719_);
if (v_isSharedCheck_6838_ == 0)
{
v___x_6833_ = v___x_6719_;
v_isShared_6834_ = v_isSharedCheck_6838_;
goto v_resetjp_6832_;
}
else
{
lean_inc(v_a_6831_);
lean_dec(v___x_6719_);
v___x_6833_ = lean_box(0);
v_isShared_6834_ = v_isSharedCheck_6838_;
goto v_resetjp_6832_;
}
v_resetjp_6832_:
{
lean_object* v___x_6836_; 
if (v_isShared_6834_ == 0)
{
v___x_6836_ = v___x_6833_;
goto v_reusejp_6835_;
}
else
{
lean_object* v_reuseFailAlloc_6837_; 
v_reuseFailAlloc_6837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6837_, 0, v_a_6831_);
v___x_6836_ = v_reuseFailAlloc_6837_;
goto v_reusejp_6835_;
}
v_reusejp_6835_:
{
return v___x_6836_;
}
}
}
}
else
{
lean_object* v_a_6839_; lean_object* v___x_6841_; uint8_t v_isShared_6842_; uint8_t v_isSharedCheck_6846_; 
lean_dec_ref(v_aux1_6707_);
lean_dec(v___x_6703_);
lean_del_object(v___x_6701_);
lean_dec(v_fst_6699_);
lean_del_object(v___x_6697_);
lean_dec(v_fst_6695_);
lean_del_object(v___x_6693_);
lean_dec_ref(v_matcherLevels_6673_);
lean_dec_ref(v___y_6672_);
lean_dec_ref(v___y_6671_);
lean_dec_ref(v___y_6670_);
lean_dec(v___y_6669_);
lean_dec_ref(v___y_6668_);
lean_dec_ref(v_remaining_6565_);
lean_dec_ref(v_alts_6564_);
lean_dec(v_matcherName_6559_);
lean_dec_ref(v_toMatcherInfo_6558_);
lean_dec_ref(v_onRemaining_6550_);
lean_dec_ref(v_onAlt_6549_);
v_a_6839_ = lean_ctor_get(v___x_6717_, 0);
v_isSharedCheck_6846_ = !lean_is_exclusive(v___x_6717_);
if (v_isSharedCheck_6846_ == 0)
{
v___x_6841_ = v___x_6717_;
v_isShared_6842_ = v_isSharedCheck_6846_;
goto v_resetjp_6840_;
}
else
{
lean_inc(v_a_6839_);
lean_dec(v___x_6717_);
v___x_6841_ = lean_box(0);
v_isShared_6842_ = v_isSharedCheck_6846_;
goto v_resetjp_6840_;
}
v_resetjp_6840_:
{
lean_object* v___x_6844_; 
if (v_isShared_6842_ == 0)
{
v___x_6844_ = v___x_6841_;
goto v_reusejp_6843_;
}
else
{
lean_object* v_reuseFailAlloc_6845_; 
v_reuseFailAlloc_6845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6845_, 0, v_a_6839_);
v___x_6844_ = v_reuseFailAlloc_6845_;
goto v_reusejp_6843_;
}
v_reusejp_6843_:
{
return v___x_6844_;
}
}
}
}
}
}
}
else
{
lean_object* v_fst_6860_; lean_object* v_fst_6861_; 
lean_dec(v___y_6669_);
v_fst_6860_ = lean_ctor_get(v_a_6688_, 0);
lean_inc(v_fst_6860_);
lean_dec(v_a_6688_);
v_fst_6861_ = lean_ctor_get(v_snd_6689_, 0);
lean_inc(v_fst_6861_);
lean_dec(v_snd_6689_);
v___y_6567_ = v___y_6676_;
v___y_6568_ = v_fst_6860_;
v___y_6569_ = v___y_6668_;
v___y_6570_ = v___x_6678_;
v___y_6571_ = v___y_6670_;
v___y_6572_ = v___y_6675_;
v___y_6573_ = v_matcherLevels_6673_;
v___y_6574_ = v_fst_6861_;
v___y_6575_ = v___y_6674_;
v___y_6576_ = v___y_6671_;
v___y_6577_ = v___y_6672_;
v___y_6578_ = v___y_6677_;
v___y_6579_ = v_remaining_x27_6679_;
goto v___jp_6566_;
}
}
}
else
{
lean_object* v_a_6862_; lean_object* v___x_6864_; uint8_t v_isShared_6865_; uint8_t v_isSharedCheck_6869_; 
lean_dec_ref(v_matcherLevels_6673_);
lean_dec_ref(v___y_6672_);
lean_dec_ref(v___y_6671_);
lean_dec_ref(v___y_6670_);
lean_dec(v___y_6669_);
lean_dec_ref(v___y_6668_);
lean_dec_ref(v_remaining_6565_);
lean_dec_ref(v_alts_6564_);
lean_dec(v_matcherName_6559_);
lean_dec_ref(v_toMatcherInfo_6558_);
lean_dec_ref(v_onRemaining_6550_);
lean_dec_ref(v_onAlt_6549_);
lean_dec_ref(v_matcherApp_6544_);
v_a_6862_ = lean_ctor_get(v___x_6687_, 0);
v_isSharedCheck_6869_ = !lean_is_exclusive(v___x_6687_);
if (v_isSharedCheck_6869_ == 0)
{
v___x_6864_ = v___x_6687_;
v_isShared_6865_ = v_isSharedCheck_6869_;
goto v_resetjp_6863_;
}
else
{
lean_inc(v_a_6862_);
lean_dec(v___x_6687_);
v___x_6864_ = lean_box(0);
v_isShared_6865_ = v_isSharedCheck_6869_;
goto v_resetjp_6863_;
}
v_resetjp_6863_:
{
lean_object* v___x_6867_; 
if (v_isShared_6865_ == 0)
{
v___x_6867_ = v___x_6864_;
goto v_reusejp_6866_;
}
else
{
lean_object* v_reuseFailAlloc_6868_; 
v_reuseFailAlloc_6868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6868_, 0, v_a_6862_);
v___x_6867_ = v_reuseFailAlloc_6868_;
goto v_reusejp_6866_;
}
v_reusejp_6866_:
{
return v___x_6867_;
}
}
}
}
v___jp_6870_:
{
size_t v_sz_6876_; size_t v___x_6877_; lean_object* v___x_6878_; 
v_sz_6876_ = lean_array_size(v_params_6561_);
v___x_6877_ = ((size_t)0ULL);
lean_inc_ref(v_params_6561_);
lean_inc_ref(v_onParams_6547_);
v___x_6878_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6547_, v_sz_6876_, v___x_6877_, v_params_6561_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_);
if (lean_obj_tag(v___x_6878_) == 0)
{
lean_object* v_a_6879_; size_t v_sz_6880_; lean_object* v___x_6881_; 
v_a_6879_ = lean_ctor_get(v___x_6878_, 0);
lean_inc(v_a_6879_);
lean_dec_ref_known(v___x_6878_, 1);
v_sz_6880_ = lean_array_size(v_discrs_6563_);
lean_inc_ref(v_discrs_6563_);
v___x_6881_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6547_, v_sz_6880_, v___x_6877_, v_discrs_6563_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_);
if (lean_obj_tag(v___x_6881_) == 0)
{
lean_object* v_a_6882_; lean_object* v___x_6883_; lean_object* v___x_6884_; lean_object* v___f_6885_; uint8_t v___x_6886_; lean_object* v___x_6887_; 
v_a_6882_ = lean_ctor_get(v___x_6881_, 0);
lean_inc_n(v_a_6882_, 2);
lean_dec_ref_known(v___x_6881_, 1);
v___x_6883_ = lean_box(v_addEqualities_6546_);
v___x_6884_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed__const__1));
lean_inc_ref(v_discrs_6563_);
lean_inc_ref(v_toMatcherInfo_6558_);
v___f_6885_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed), 13, 6);
lean_closure_set(v___f_6885_, 0, v_onMotive_6548_);
lean_closure_set(v___f_6885_, 1, v_toMatcherInfo_6558_);
lean_closure_set(v___f_6885_, 2, v_a_6882_);
lean_closure_set(v___f_6885_, 3, v___x_6883_);
lean_closure_set(v___f_6885_, 4, v___x_6884_);
lean_closure_set(v___f_6885_, 5, v_discrs_6563_);
v___x_6886_ = 0;
lean_inc_ref(v_motive_6562_);
v___x_6887_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_6562_, v___f_6885_, v___x_6886_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_);
if (lean_obj_tag(v___x_6887_) == 0)
{
lean_object* v_a_6888_; lean_object* v_snd_6889_; lean_object* v_snd_6890_; lean_object* v_uElimPos_x3f_6891_; 
v_a_6888_ = lean_ctor_get(v___x_6887_, 0);
lean_inc(v_a_6888_);
lean_dec_ref_known(v___x_6887_, 1);
v_snd_6889_ = lean_ctor_get(v_a_6888_, 1);
v_snd_6890_ = lean_ctor_get(v_snd_6889_, 1);
lean_inc(v_snd_6890_);
v_uElimPos_x3f_6891_ = lean_ctor_get(v_toMatcherInfo_6558_, 3);
if (lean_obj_tag(v_uElimPos_x3f_6891_) == 0)
{
lean_object* v_fst_6892_; lean_object* v_fst_6893_; lean_object* v_snd_6894_; 
v_fst_6892_ = lean_ctor_get(v_a_6888_, 0);
lean_inc(v_fst_6892_);
lean_dec(v_a_6888_);
v_fst_6893_ = lean_ctor_get(v_snd_6890_, 0);
lean_inc(v_fst_6893_);
v_snd_6894_ = lean_ctor_get(v_snd_6890_, 1);
lean_inc(v_snd_6894_);
lean_dec(v_snd_6890_);
lean_inc_ref(v_matcherLevels_6560_);
v___y_6666_ = v___x_6877_;
v___y_6667_ = v_fst_6893_;
v___y_6668_ = v_fst_6892_;
v___y_6669_ = v_numDiscrEqs_6871_;
v___y_6670_ = v_a_6879_;
v___y_6671_ = v_snd_6894_;
v___y_6672_ = v_a_6882_;
v_matcherLevels_6673_ = v_matcherLevels_6560_;
v___y_6674_ = v___y_6872_;
v___y_6675_ = v___y_6873_;
v___y_6676_ = v___y_6874_;
v___y_6677_ = v___y_6875_;
goto v___jp_6665_;
}
else
{
lean_object* v_fst_6895_; lean_object* v_fst_6896_; lean_object* v_fst_6897_; lean_object* v_snd_6898_; lean_object* v_val_6899_; lean_object* v___x_6900_; 
lean_inc(v_snd_6889_);
v_fst_6895_ = lean_ctor_get(v_a_6888_, 0);
lean_inc(v_fst_6895_);
lean_dec(v_a_6888_);
v_fst_6896_ = lean_ctor_get(v_snd_6889_, 0);
lean_inc(v_fst_6896_);
lean_dec(v_snd_6889_);
v_fst_6897_ = lean_ctor_get(v_snd_6890_, 0);
lean_inc(v_fst_6897_);
v_snd_6898_ = lean_ctor_get(v_snd_6890_, 1);
lean_inc(v_snd_6898_);
lean_dec(v_snd_6890_);
v_val_6899_ = lean_ctor_get(v_uElimPos_x3f_6891_, 0);
lean_inc_ref(v_matcherLevels_6560_);
v___x_6900_ = lean_array_set(v_matcherLevels_6560_, v_val_6899_, v_fst_6896_);
v___y_6666_ = v___x_6877_;
v___y_6667_ = v_fst_6897_;
v___y_6668_ = v_fst_6895_;
v___y_6669_ = v_numDiscrEqs_6871_;
v___y_6670_ = v_a_6879_;
v___y_6671_ = v_snd_6898_;
v___y_6672_ = v_a_6882_;
v_matcherLevels_6673_ = v___x_6900_;
v___y_6674_ = v___y_6872_;
v___y_6675_ = v___y_6873_;
v___y_6676_ = v___y_6874_;
v___y_6677_ = v___y_6875_;
goto v___jp_6665_;
}
}
else
{
lean_object* v_a_6901_; lean_object* v___x_6903_; uint8_t v_isShared_6904_; uint8_t v_isSharedCheck_6908_; 
lean_dec(v_a_6882_);
lean_dec(v_a_6879_);
lean_dec(v_numDiscrEqs_6871_);
lean_dec_ref(v_remaining_6565_);
lean_dec_ref(v_alts_6564_);
lean_dec(v_matcherName_6559_);
lean_dec_ref(v_toMatcherInfo_6558_);
lean_dec_ref(v_onRemaining_6550_);
lean_dec_ref(v_onAlt_6549_);
lean_dec_ref(v_matcherApp_6544_);
v_a_6901_ = lean_ctor_get(v___x_6887_, 0);
v_isSharedCheck_6908_ = !lean_is_exclusive(v___x_6887_);
if (v_isSharedCheck_6908_ == 0)
{
v___x_6903_ = v___x_6887_;
v_isShared_6904_ = v_isSharedCheck_6908_;
goto v_resetjp_6902_;
}
else
{
lean_inc(v_a_6901_);
lean_dec(v___x_6887_);
v___x_6903_ = lean_box(0);
v_isShared_6904_ = v_isSharedCheck_6908_;
goto v_resetjp_6902_;
}
v_resetjp_6902_:
{
lean_object* v___x_6906_; 
if (v_isShared_6904_ == 0)
{
v___x_6906_ = v___x_6903_;
goto v_reusejp_6905_;
}
else
{
lean_object* v_reuseFailAlloc_6907_; 
v_reuseFailAlloc_6907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6907_, 0, v_a_6901_);
v___x_6906_ = v_reuseFailAlloc_6907_;
goto v_reusejp_6905_;
}
v_reusejp_6905_:
{
return v___x_6906_;
}
}
}
}
else
{
lean_object* v_a_6909_; lean_object* v___x_6911_; uint8_t v_isShared_6912_; uint8_t v_isSharedCheck_6916_; 
lean_dec(v_a_6879_);
lean_dec(v_numDiscrEqs_6871_);
lean_dec_ref(v_remaining_6565_);
lean_dec_ref(v_alts_6564_);
lean_dec(v_matcherName_6559_);
lean_dec_ref(v_toMatcherInfo_6558_);
lean_dec_ref(v_onRemaining_6550_);
lean_dec_ref(v_onAlt_6549_);
lean_dec_ref(v_onMotive_6548_);
lean_dec_ref(v_matcherApp_6544_);
v_a_6909_ = lean_ctor_get(v___x_6881_, 0);
v_isSharedCheck_6916_ = !lean_is_exclusive(v___x_6881_);
if (v_isSharedCheck_6916_ == 0)
{
v___x_6911_ = v___x_6881_;
v_isShared_6912_ = v_isSharedCheck_6916_;
goto v_resetjp_6910_;
}
else
{
lean_inc(v_a_6909_);
lean_dec(v___x_6881_);
v___x_6911_ = lean_box(0);
v_isShared_6912_ = v_isSharedCheck_6916_;
goto v_resetjp_6910_;
}
v_resetjp_6910_:
{
lean_object* v___x_6914_; 
if (v_isShared_6912_ == 0)
{
v___x_6914_ = v___x_6911_;
goto v_reusejp_6913_;
}
else
{
lean_object* v_reuseFailAlloc_6915_; 
v_reuseFailAlloc_6915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6915_, 0, v_a_6909_);
v___x_6914_ = v_reuseFailAlloc_6915_;
goto v_reusejp_6913_;
}
v_reusejp_6913_:
{
return v___x_6914_;
}
}
}
}
else
{
lean_object* v_a_6917_; lean_object* v___x_6919_; uint8_t v_isShared_6920_; uint8_t v_isSharedCheck_6924_; 
lean_dec(v_numDiscrEqs_6871_);
lean_dec_ref(v_remaining_6565_);
lean_dec_ref(v_alts_6564_);
lean_dec(v_matcherName_6559_);
lean_dec_ref(v_toMatcherInfo_6558_);
lean_dec_ref(v_onRemaining_6550_);
lean_dec_ref(v_onAlt_6549_);
lean_dec_ref(v_onMotive_6548_);
lean_dec_ref(v_onParams_6547_);
lean_dec_ref(v_matcherApp_6544_);
v_a_6917_ = lean_ctor_get(v___x_6878_, 0);
v_isSharedCheck_6924_ = !lean_is_exclusive(v___x_6878_);
if (v_isSharedCheck_6924_ == 0)
{
v___x_6919_ = v___x_6878_;
v_isShared_6920_ = v_isSharedCheck_6924_;
goto v_resetjp_6918_;
}
else
{
lean_inc(v_a_6917_);
lean_dec(v___x_6878_);
v___x_6919_ = lean_box(0);
v_isShared_6920_ = v_isSharedCheck_6924_;
goto v_resetjp_6918_;
}
v_resetjp_6918_:
{
lean_object* v___x_6922_; 
if (v_isShared_6920_ == 0)
{
v___x_6922_ = v___x_6919_;
goto v_reusejp_6921_;
}
else
{
lean_object* v_reuseFailAlloc_6923_; 
v_reuseFailAlloc_6923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6923_, 0, v_a_6917_);
v___x_6922_ = v_reuseFailAlloc_6923_;
goto v_reusejp_6921_;
}
v_reusejp_6921_:
{
return v___x_6922_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed(lean_object* v_matcherApp_6944_, lean_object* v_useSplitter_6945_, lean_object* v_addEqualities_6946_, lean_object* v_onParams_6947_, lean_object* v_onMotive_6948_, lean_object* v_onAlt_6949_, lean_object* v_onRemaining_6950_, lean_object* v___y_6951_, lean_object* v___y_6952_, lean_object* v___y_6953_, lean_object* v___y_6954_, lean_object* v___y_6955_){
_start:
{
uint8_t v_useSplitter_boxed_6956_; uint8_t v_addEqualities_boxed_6957_; lean_object* v_res_6958_; 
v_useSplitter_boxed_6956_ = lean_unbox(v_useSplitter_6945_);
v_addEqualities_boxed_6957_ = lean_unbox(v_addEqualities_6946_);
v_res_6958_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(v_matcherApp_6944_, v_useSplitter_boxed_6956_, v_addEqualities_boxed_6957_, v_onParams_6947_, v_onMotive_6948_, v_onAlt_6949_, v_onRemaining_6950_, v___y_6951_, v___y_6952_, v___y_6953_, v___y_6954_);
lean_dec(v___y_6954_);
lean_dec_ref(v___y_6953_);
lean_dec(v___y_6952_);
lean_dec_ref(v___y_6951_);
return v_res_6958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType(lean_object* v_matcherApp_6964_, lean_object* v_a_6965_, lean_object* v_a_6966_, lean_object* v_a_6967_, lean_object* v_a_6968_){
_start:
{
lean_object* v_toMatcherInfo_6970_; lean_object* v_matcherName_6971_; lean_object* v_matcherLevels_6972_; lean_object* v_params_6973_; lean_object* v_alts_6974_; lean_object* v_remaining_6975_; lean_object* v___f_6976_; lean_object* v___f_6977_; lean_object* v_nExtra_6978_; uint8_t v___x_6979_; lean_object* v___f_6980_; uint8_t v___x_6981_; lean_object* v___x_6982_; lean_object* v___x_6983_; lean_object* v___f_6984_; lean_object* v___x_6985_; 
v_toMatcherInfo_6970_ = lean_ctor_get(v_matcherApp_6964_, 0);
v_matcherName_6971_ = lean_ctor_get(v_matcherApp_6964_, 1);
v_matcherLevels_6972_ = lean_ctor_get(v_matcherApp_6964_, 2);
v_params_6973_ = lean_ctor_get(v_matcherApp_6964_, 3);
v_alts_6974_ = lean_ctor_get(v_matcherApp_6964_, 6);
v_remaining_6975_ = lean_ctor_get(v_matcherApp_6964_, 7);
v___f_6976_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__0));
v___f_6977_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__1));
v_nExtra_6978_ = lean_array_get_size(v_remaining_6975_);
v___x_6979_ = 1;
v___f_6980_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__2));
v___x_6981_ = 0;
v___x_6982_ = lean_box(v___x_6981_);
v___x_6983_ = lean_box(v___x_6979_);
lean_inc_ref(v_matcherLevels_6972_);
lean_inc_ref(v_params_6973_);
lean_inc(v_matcherName_6971_);
lean_inc_ref(v_toMatcherInfo_6970_);
lean_inc_ref(v_alts_6974_);
v___f_6984_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed), 15, 8);
lean_closure_set(v___f_6984_, 0, v_nExtra_6978_);
lean_closure_set(v___f_6984_, 1, v___x_6982_);
lean_closure_set(v___f_6984_, 2, v___x_6983_);
lean_closure_set(v___f_6984_, 3, v_alts_6974_);
lean_closure_set(v___f_6984_, 4, v_toMatcherInfo_6970_);
lean_closure_set(v___f_6984_, 5, v_matcherName_6971_);
lean_closure_set(v___f_6984_, 6, v_params_6973_);
lean_closure_set(v___f_6984_, 7, v_matcherLevels_6972_);
v___x_6985_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(v_matcherApp_6964_, v___x_6979_, v___x_6981_, v___f_6976_, v___f_6984_, v___f_6980_, v___f_6977_, v_a_6965_, v_a_6966_, v_a_6967_, v_a_6968_);
return v___x_6985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___boxed(lean_object* v_matcherApp_6986_, lean_object* v_a_6987_, lean_object* v_a_6988_, lean_object* v_a_6989_, lean_object* v_a_6990_, lean_object* v_a_6991_){
_start:
{
lean_object* v_res_6992_; 
v_res_6992_ = l_Lean_Meta_MatcherApp_inferMatchType(v_matcherApp_6986_, v_a_6987_, v_a_6988_, v_a_6989_, v_a_6990_);
lean_dec(v_a_6990_);
lean_dec_ref(v_a_6989_);
lean_dec(v_a_6988_);
lean_dec_ref(v_a_6987_);
return v_res_6992_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(lean_object* v_a_6993_, lean_object* v_termAlt_6994_, lean_object* v_inst_6995_, lean_object* v_R_6996_, lean_object* v_a_6997_, lean_object* v_b_6998_, lean_object* v_c_6999_, lean_object* v___y_7000_, lean_object* v___y_7001_, lean_object* v___y_7002_, lean_object* v___y_7003_){
_start:
{
lean_object* v___x_7005_; 
v___x_7005_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_6993_, v_termAlt_6994_, v_a_6997_, v_b_6998_, v___y_7000_, v___y_7001_, v___y_7002_, v___y_7003_);
return v___x_7005_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___boxed(lean_object* v_a_7006_, lean_object* v_termAlt_7007_, lean_object* v_inst_7008_, lean_object* v_R_7009_, lean_object* v_a_7010_, lean_object* v_b_7011_, lean_object* v_c_7012_, lean_object* v___y_7013_, lean_object* v___y_7014_, lean_object* v___y_7015_, lean_object* v___y_7016_, lean_object* v___y_7017_){
_start:
{
lean_object* v_res_7018_; 
v_res_7018_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(v_a_7006_, v_termAlt_7007_, v_inst_7008_, v_R_7009_, v_a_7010_, v_b_7011_, v_c_7012_, v___y_7013_, v___y_7014_, v___y_7015_, v___y_7016_);
lean_dec(v___y_7016_);
lean_dec_ref(v___y_7015_);
lean_dec(v___y_7014_);
lean_dec_ref(v___y_7013_);
return v_res_7018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(lean_object* v_00_u03b1_7019_, lean_object* v_fvars_7020_, lean_object* v_names_7021_, lean_object* v_k_7022_, lean_object* v___y_7023_, lean_object* v___y_7024_, lean_object* v___y_7025_, lean_object* v___y_7026_){
_start:
{
lean_object* v___x_7028_; 
v___x_7028_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_fvars_7020_, v_names_7021_, v_k_7022_, v___y_7023_, v___y_7024_, v___y_7025_, v___y_7026_);
return v___x_7028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___boxed(lean_object* v_00_u03b1_7029_, lean_object* v_fvars_7030_, lean_object* v_names_7031_, lean_object* v_k_7032_, lean_object* v___y_7033_, lean_object* v___y_7034_, lean_object* v___y_7035_, lean_object* v___y_7036_, lean_object* v___y_7037_){
_start:
{
lean_object* v_res_7038_; 
v_res_7038_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(v_00_u03b1_7029_, v_fvars_7030_, v_names_7031_, v_k_7032_, v___y_7033_, v___y_7034_, v___y_7035_, v___y_7036_);
lean_dec(v___y_7036_);
lean_dec_ref(v___y_7035_);
lean_dec(v___y_7034_);
lean_dec_ref(v___y_7033_);
lean_dec_ref(v_names_7031_);
lean_dec_ref(v_fvars_7030_);
return v_res_7038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(lean_object* v_00_u03b1_7039_, lean_object* v_origAltType_7040_, lean_object* v_altInfo_7041_, lean_object* v_k_7042_, lean_object* v___y_7043_, lean_object* v___y_7044_, lean_object* v___y_7045_, lean_object* v___y_7046_){
_start:
{
lean_object* v___x_7048_; 
v___x_7048_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v_origAltType_7040_, v_altInfo_7041_, v_k_7042_, v___y_7043_, v___y_7044_, v___y_7045_, v___y_7046_);
return v___x_7048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___boxed(lean_object* v_00_u03b1_7049_, lean_object* v_origAltType_7050_, lean_object* v_altInfo_7051_, lean_object* v_k_7052_, lean_object* v___y_7053_, lean_object* v___y_7054_, lean_object* v___y_7055_, lean_object* v___y_7056_, lean_object* v___y_7057_){
_start:
{
lean_object* v_res_7058_; 
v_res_7058_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(v_00_u03b1_7049_, v_origAltType_7050_, v_altInfo_7051_, v_k_7052_, v___y_7053_, v___y_7054_, v___y_7055_, v___y_7056_);
lean_dec(v___y_7056_);
lean_dec_ref(v___y_7055_);
lean_dec(v___y_7054_);
lean_dec_ref(v___y_7053_);
return v_res_7058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(lean_object* v_declName_7059_, lean_object* v___y_7060_, lean_object* v___y_7061_, lean_object* v___y_7062_, lean_object* v___y_7063_){
_start:
{
lean_object* v___x_7065_; 
v___x_7065_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_declName_7059_, v___y_7063_);
return v___x_7065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___boxed(lean_object* v_declName_7066_, lean_object* v___y_7067_, lean_object* v___y_7068_, lean_object* v___y_7069_, lean_object* v___y_7070_, lean_object* v___y_7071_){
_start:
{
lean_object* v_res_7072_; 
v_res_7072_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(v_declName_7066_, v___y_7067_, v___y_7068_, v___y_7069_, v___y_7070_);
lean_dec(v___y_7070_);
lean_dec_ref(v___y_7069_);
lean_dec(v___y_7068_);
lean_dec_ref(v___y_7067_);
return v_res_7072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(size_t v_sz_7073_, size_t v_i_7074_, lean_object* v_bs_7075_, lean_object* v___y_7076_, lean_object* v___y_7077_, lean_object* v___y_7078_, lean_object* v___y_7079_){
_start:
{
lean_object* v___x_7081_; 
v___x_7081_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_7073_, v_i_7074_, v_bs_7075_, v___y_7076_, v___y_7078_, v___y_7079_);
return v___x_7081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___boxed(lean_object* v_sz_7082_, lean_object* v_i_7083_, lean_object* v_bs_7084_, lean_object* v___y_7085_, lean_object* v___y_7086_, lean_object* v___y_7087_, lean_object* v___y_7088_, lean_object* v___y_7089_){
_start:
{
size_t v_sz_boxed_7090_; size_t v_i_boxed_7091_; lean_object* v_res_7092_; 
v_sz_boxed_7090_ = lean_unbox_usize(v_sz_7082_);
lean_dec(v_sz_7082_);
v_i_boxed_7091_ = lean_unbox_usize(v_i_7083_);
lean_dec(v_i_7083_);
v_res_7092_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(v_sz_boxed_7090_, v_i_boxed_7091_, v_bs_7084_, v___y_7085_, v___y_7086_, v___y_7087_, v___y_7088_);
lean_dec(v___y_7088_);
lean_dec_ref(v___y_7087_);
lean_dec(v___y_7086_);
lean_dec_ref(v___y_7085_);
return v_res_7092_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(lean_object* v_upperBound_7093_, lean_object* v_onAlt_7094_, lean_object* v_extraEqualities_7095_, lean_object* v_inst_7096_, lean_object* v_R_7097_, lean_object* v_a_7098_, lean_object* v_b_7099_, lean_object* v_c_7100_, lean_object* v___y_7101_, lean_object* v___y_7102_, lean_object* v___y_7103_, lean_object* v___y_7104_){
_start:
{
lean_object* v___x_7106_; 
v___x_7106_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v_upperBound_7093_, v_onAlt_7094_, v_extraEqualities_7095_, v_a_7098_, v_b_7099_, v___y_7101_, v___y_7102_, v___y_7103_, v___y_7104_);
return v___x_7106_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___boxed(lean_object* v_upperBound_7107_, lean_object* v_onAlt_7108_, lean_object* v_extraEqualities_7109_, lean_object* v_inst_7110_, lean_object* v_R_7111_, lean_object* v_a_7112_, lean_object* v_b_7113_, lean_object* v_c_7114_, lean_object* v___y_7115_, lean_object* v___y_7116_, lean_object* v___y_7117_, lean_object* v___y_7118_, lean_object* v___y_7119_){
_start:
{
lean_object* v_res_7120_; 
v_res_7120_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(v_upperBound_7107_, v_onAlt_7108_, v_extraEqualities_7109_, v_inst_7110_, v_R_7111_, v_a_7112_, v_b_7113_, v_c_7114_, v___y_7115_, v___y_7116_, v___y_7117_, v___y_7118_);
lean_dec(v___y_7118_);
lean_dec_ref(v___y_7117_);
lean_dec(v___y_7116_);
lean_dec_ref(v___y_7115_);
lean_dec(v_upperBound_7107_);
return v_res_7120_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(lean_object* v_upperBound_7121_, lean_object* v_onAlt_7122_, uint8_t v_useSplitter_7123_, lean_object* v_extraEqualities_7124_, lean_object* v_numDiscrEqs_7125_, lean_object* v_inst_7126_, lean_object* v_R_7127_, lean_object* v_a_7128_, lean_object* v_b_7129_, lean_object* v_c_7130_, lean_object* v___y_7131_, lean_object* v___y_7132_, lean_object* v___y_7133_, lean_object* v___y_7134_){
_start:
{
lean_object* v___x_7136_; 
v___x_7136_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v_upperBound_7121_, v_onAlt_7122_, v_useSplitter_7123_, v_extraEqualities_7124_, v_numDiscrEqs_7125_, v_a_7128_, v_b_7129_, v___y_7131_, v___y_7132_, v___y_7133_, v___y_7134_);
return v___x_7136_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___boxed(lean_object* v_upperBound_7137_, lean_object* v_onAlt_7138_, lean_object* v_useSplitter_7139_, lean_object* v_extraEqualities_7140_, lean_object* v_numDiscrEqs_7141_, lean_object* v_inst_7142_, lean_object* v_R_7143_, lean_object* v_a_7144_, lean_object* v_b_7145_, lean_object* v_c_7146_, lean_object* v___y_7147_, lean_object* v___y_7148_, lean_object* v___y_7149_, lean_object* v___y_7150_, lean_object* v___y_7151_){
_start:
{
uint8_t v_useSplitter_boxed_7152_; lean_object* v_res_7153_; 
v_useSplitter_boxed_7152_ = lean_unbox(v_useSplitter_7139_);
v_res_7153_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(v_upperBound_7137_, v_onAlt_7138_, v_useSplitter_boxed_7152_, v_extraEqualities_7140_, v_numDiscrEqs_7141_, v_inst_7142_, v_R_7143_, v_a_7144_, v_b_7145_, v_c_7146_, v___y_7147_, v___y_7148_, v___y_7149_, v___y_7150_);
lean_dec(v___y_7150_);
lean_dec_ref(v___y_7149_);
lean_dec(v___y_7148_);
lean_dec_ref(v___y_7147_);
lean_dec(v_upperBound_7137_);
return v_res_7153_;
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
