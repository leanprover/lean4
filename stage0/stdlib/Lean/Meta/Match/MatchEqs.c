// Lean compiler output
// Module: Lean.Meta.Match.MatchEqs
// Imports: public import Lean.Meta.Match.Match public import Lean.Meta.Match.MatchEqsExt import Lean.Meta.Tactic.Refl import Lean.Meta.Tactic.Delta import Lean.Meta.Tactic.SplitIf import Lean.Meta.Tactic.CasesOnStuckLHS import Lean.Meta.Match.SimpH import Lean.Meta.Match.AltTelescopes import Lean.Meta.Match.NamedPatterns import Lean.Meta.SplitSparseCasesOn
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
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introSubstEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_deltaTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(lean_object*);
uint8_t lean_is_matcher(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Meta_Match_Overlaps_overlapping(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_simpH_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrowN(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_unfoldNamedPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_heqOfEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_splitIfTarget_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpIfTarget(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_splitSparseCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceSparseCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_casesOnStuckLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_contradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_modifyTargetEqLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
extern lean_object* l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
extern lean_object* l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
size_t lean_usize_shift_right(size_t, size_t);
extern lean_object* l_Lean_Meta_eqnThmSuffixBase;
lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_getNumEqsFromDiscrInfos(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Meta_Match_registerMatchEqns___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_withMkMatcherInput___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getMotivePos(lean_object*);
uint8_t l_Lean_Meta_Match_Overlaps_isEmpty(lean_object*);
lean_object* l_Lean_Meta_Match_isNamedPattern___boxed(lean_object*);
uint8_t l_Lean_Meta_Match_instBEqAltParamInfo_beq(lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
extern lean_object* l_Lean_Meta_Match_matchEqnsExt;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedConfigWithKey___private__1;
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_Meta_Match_congrEqn1ThmSuffix;
lean_object* l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* lean_private_to_user_name(lean_object*);
uint8_t l_Lean_Meta_isEqnReservedNameSuffix(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_registerReservedNamePredicate(lean_object*);
lean_object* l_Lean_registerReservedNameAction(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Could not find equation "};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__1;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__3;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " among "};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__5;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "expecting "};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__7;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = " equalities, but found type"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__8 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkAppDiscrEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkAppDiscrEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "substSomeVar failed"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elimOffset"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(15, 200, 217, 88, 39, 250, 32, 250)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__2_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__1 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "goal's target does not contain `Nat.elimOffset`"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__2 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "failed to generate equality theorems for `match` expression `"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`\n"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "spliIf failed"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "simpIf failed"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7;
static const lean_array_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8_value;
static const lean_closure_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_whnfCore___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__9 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchEqs"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__12 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Match"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__11 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__10 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__10_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__11_value),LEAN_SCALAR_PTR_LITERAL(250, 1, 225, 180, 135, 246, 184, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__12_value),LEAN_SCALAR_PTR_LITERAL(142, 18, 82, 91, 15, 164, 75, 57)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "proveCondEqThm.go "};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Match_proveCondEqThm___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "proveCondEqThm after subst"};
static const lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1;
static const lean_string_object l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "proveCondEqThm "};
static const lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Match_proveCondEqThm___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_proveCondEqThm___closed__0;
static lean_once_cell_t l_Lean_Meta_Match_proveCondEqThm___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_proveCondEqThm___closed__1;
static lean_once_cell_t l_Lean_Meta_Match_proveCondEqThm___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_proveCondEqThm___closed__2;
static lean_once_cell_t l_Lean_Meta_Match_proveCondEqThm___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_proveCondEqThm___closed__3;
static lean_once_cell_t l_Lean_Meta_Match_proveCondEqThm___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_proveCondEqThm___closed__4;
static const lean_array_object l_Lean_Meta_Match_proveCondEqThm___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Match_proveCondEqThm___closed__5 = (const lean_object*)&l_Lean_Meta_Match_proveCondEqThm___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0___boxed(lean_object**);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__1_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hs: "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__4_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Meta.Match.MatchEqs"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "_private.Lean.Meta.Match.MatchEqs.0.Lean.Meta.Match.getEquationsForImpl.go"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 237, .m_capacity = 237, .m_length = 236, .m_data = "assertion violation: matchInfo.altInfos == splitterAltInfos\n      -- This match statement does not need a splitter, we can use itself for that.\n      -- (We still have to generate a declaration to satisfy the realizable constant)\n      "};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__7;
static const lean_closure_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Match_isNamedPattern___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__8 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` is not a matcher function"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Match_getEquationsForImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "splitter"};
static const lean_object* l_Lean_Meta_Match_getEquationsForImpl___closed__0 = (const lean_object*)&l_Lean_Meta_Match_getEquationsForImpl___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Match_getEquationsForImpl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Match_getEquationsForImpl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 60, 9, 208, 120, 135, 115, 56)}};
static const lean_object* l_Lean_Meta_Match_getEquationsForImpl___closed__1 = (const lean_object*)&l_Lean_Meta_Match_getEquationsForImpl___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Match_getEquationsForImpl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Match_getEquationsForImpl___closed__2 = (const lean_object*)&l_Lean_Meta_Match_getEquationsForImpl___closed__2_value;
static const lean_string_object l_Lean_Meta_Match_getEquationsForImpl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "failed to retrieve match equations for `"};
static const lean_object* l_Lean_Meta_Match_getEquationsForImpl___closed__3 = (const lean_object*)&l_Lean_Meta_Match_getEquationsForImpl___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Match_getEquationsForImpl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_getEquationsForImpl___closed__4;
static const lean_string_object l_Lean_Meta_Match_getEquationsForImpl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "` after realization"};
static const lean_object* l_Lean_Meta_Match_getEquationsForImpl___closed__5 = (const lean_object*)&l_Lean_Meta_Match_getEquationsForImpl___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Match_getEquationsForImpl___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Match_getEquationsForImpl___closed__6;
LEAN_EXPORT lean_object* lean_get_match_equations_for(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getEquationsForImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "heq"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 249, 62, 128, 70, 197, 241, 171)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__1;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 77, .m_capacity = 77, .m_length = 76, .m_data = "_private.Lean.Meta.Match.MatchEqs.0.Lean.Meta.Match.genMatchCongrEqnsImpl.go"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "assertion violation: patterns.size == discrs.size\n        "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__1_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed(lean_object**);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___boxed(lean_object**);
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8_value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_congr_match_equations_for(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_genMatchCongrEqnsImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__10_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__11_value),LEAN_SCALAR_PTR_LITERAL(75, 7, 62, 187, 210, 164, 110, 59)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "MatchEqs"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__7_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(32, 108, 58, 118, 141, 255, 162, 173)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__7_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__7_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__8_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__7_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(89, 143, 139, 150, 26, 209, 69, 100)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__8_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__8_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__9_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__8_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(60, 19, 205, 36, 112, 108, 199, 19)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__9_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__9_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__10_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__9_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__10_value),LEAN_SCALAR_PTR_LITERAL(64, 18, 131, 232, 118, 16, 218, 224)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__10_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__10_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__11_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__10_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__11_value),LEAN_SCALAR_PTR_LITERAL(149, 136, 49, 102, 95, 126, 100, 58)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__11_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__11_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__12_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__12_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__12_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__13_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__11_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__12_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 148, 22, 51, 114, 213, 50, 138)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__13_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__13_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__14_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__14_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__14_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__15_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__13_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__14_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 135, 35, 122, 223, 37, 228, 228)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__15_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__15_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__16_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__15_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(32, 16, 217, 45, 230, 145, 50, 231)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__16_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__16_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__17_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__16_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__10_value),LEAN_SCALAR_PTR_LITERAL(140, 51, 94, 245, 163, 3, 190, 52)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__17_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__17_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__18_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__17_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__11_value),LEAN_SCALAR_PTR_LITERAL(81, 118, 58, 117, 110, 34, 2, 117)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__18_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__18_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__19_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__18_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(66, 96, 197, 5, 210, 40, 219, 253)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__19_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__19_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__21_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__21_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__21_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__23_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__23_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__23_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object*);
static const lean_array_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_mctx_10_; lean_object* v_lctx_11_; lean_object* v_options_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_mctx_10_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_10_);
lean_dec(v___x_9_);
v_lctx_11_ = lean_ctor_get(v___y_2_, 2);
v_options_12_ = lean_ctor_get(v___y_4_, 2);
lean_inc_ref(v_options_12_);
lean_inc_ref(v_lctx_11_);
v___x_13_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_13_, 0, v_env_8_);
lean_ctor_set(v___x_13_, 1, v_mctx_10_);
lean_ctor_set(v___x_13_, 2, v_lctx_11_);
lean_ctor_set(v___x_13_, 3, v_options_12_);
v___x_14_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v_msgData_1_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2___boxed(lean_object* v_msgData_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2(v_msgData_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(lean_object* v_msg_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_ref_29_; lean_object* v___x_30_; lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_39_; 
v_ref_29_ = lean_ctor_get(v___y_26_, 5);
v___x_30_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2(v_msg_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_39_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_37_; 
lean_inc(v_ref_29_);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v_ref_29_);
lean_ctor_set(v___x_35_, 1, v_a_31_);
if (v_isShared_34_ == 0)
{
lean_ctor_set_tag(v___x_33_, 1);
lean_ctor_set(v___x_33_, 0, v___x_35_);
v___x_37_ = v___x_33_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg___boxed(lean_object* v_msg_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v_msg_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(lean_object* v_a_47_, lean_object* v_a_48_){
_start:
{
if (lean_obj_tag(v_a_47_) == 0)
{
lean_object* v___x_49_; 
v___x_49_ = l_List_reverse___redArg(v_a_48_);
return v___x_49_;
}
else
{
lean_object* v_head_50_; lean_object* v_tail_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_60_; 
v_head_50_ = lean_ctor_get(v_a_47_, 0);
v_tail_51_ = lean_ctor_get(v_a_47_, 1);
v_isSharedCheck_60_ = !lean_is_exclusive(v_a_47_);
if (v_isSharedCheck_60_ == 0)
{
v___x_53_ = v_a_47_;
v_isShared_54_ = v_isSharedCheck_60_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_tail_51_);
lean_inc(v_head_50_);
lean_dec(v_a_47_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_60_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_55_; lean_object* v___x_57_; 
v___x_55_ = l_Lean_MessageData_ofExpr(v_head_50_);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 1, v_a_48_);
lean_ctor_set(v___x_53_, 0, v___x_55_);
v___x_57_ = v___x_53_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v___x_55_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v_a_48_);
v___x_57_ = v_reuseFailAlloc_59_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
v_a_47_ = v_tail_51_;
v_a_48_ = v___x_57_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__1(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__0));
v___x_66_ = l_Lean_stringToMessageData(v___x_65_);
return v___x_66_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__3(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_68_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__2));
v___x_69_ = l_Lean_stringToMessageData(v___x_68_);
return v___x_69_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__5(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__4));
v___x_72_ = l_Lean_stringToMessageData(v___x_71_);
return v___x_72_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__7(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__6));
v___x_75_ = l_Lean_stringToMessageData(v___x_74_);
return v___x_75_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__9(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__8));
v___x_78_ = l_Lean_stringToMessageData(v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go(lean_object* v_alt_79_, lean_object* v_heqs_80_, lean_object* v_numDiscrEqs_81_, lean_object* v_e_82_, lean_object* v_ty_83_, lean_object* v_i_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_){
_start:
{
uint8_t v___x_90_; 
v___x_90_ = lean_nat_dec_lt(v_i_84_, v_numDiscrEqs_81_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; 
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec_ref(v_ty_83_);
lean_dec(v_numDiscrEqs_81_);
lean_dec_ref(v_heqs_80_);
lean_dec_ref(v_alt_79_);
v___x_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_91_, 0, v_e_82_);
return v___x_91_;
}
else
{
if (lean_obj_tag(v_ty_83_) == 7)
{
lean_object* v_binderName_92_; lean_object* v_binderType_93_; lean_object* v_body_94_; lean_object* v___x_95_; size_t v_sz_96_; size_t v___x_97_; lean_object* v___x_98_; 
v_binderName_92_ = lean_ctor_get(v_ty_83_, 0);
lean_inc(v_binderName_92_);
v_binderType_93_ = lean_ctor_get(v_ty_83_, 1);
lean_inc_ref(v_binderType_93_);
v_body_94_ = lean_ctor_get(v_ty_83_, 2);
lean_inc_ref(v_body_94_);
lean_dec_ref(v_ty_83_);
v___x_95_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0___closed__0));
v_sz_96_ = lean_array_size(v_heqs_80_);
v___x_97_ = ((size_t)0ULL);
lean_inc(v_a_88_);
lean_inc_ref(v_a_87_);
lean_inc(v_a_86_);
lean_inc_ref(v_a_85_);
lean_inc_ref(v_heqs_80_);
lean_inc_ref(v_binderType_93_);
v___x_98_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0(v_binderType_93_, v_e_82_, v_body_94_, v_i_84_, v_alt_79_, v_heqs_80_, v_numDiscrEqs_81_, v_heqs_80_, v_sz_96_, v___x_97_, v___x_95_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
lean_dec_ref(v_body_94_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_130_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_130_ == 0)
{
v___x_101_ = v___x_98_;
v_isShared_102_ = v_isSharedCheck_130_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_dec(v___x_98_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_130_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v_fst_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_128_; 
v_fst_103_ = lean_ctor_get(v_a_99_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v_a_99_);
if (v_isSharedCheck_128_ == 0)
{
lean_object* v_unused_129_; 
v_unused_129_ = lean_ctor_get(v_a_99_, 1);
lean_dec(v_unused_129_);
v___x_105_ = v_a_99_;
v_isShared_106_ = v_isSharedCheck_128_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_fst_103_);
lean_dec(v_a_99_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_128_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
if (lean_obj_tag(v_fst_103_) == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
lean_del_object(v___x_101_);
v___x_107_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__1);
v___x_108_ = l_Lean_MessageData_ofName(v_binderName_92_);
if (v_isShared_106_ == 0)
{
lean_ctor_set_tag(v___x_105_, 7);
lean_ctor_set(v___x_105_, 1, v___x_108_);
lean_ctor_set(v___x_105_, 0, v___x_107_);
v___x_110_ = v___x_105_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v___x_108_);
v___x_110_ = v_reuseFailAlloc_123_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_111_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__3);
v___x_112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_110_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
v___x_113_ = l_Lean_MessageData_ofExpr(v_binderType_93_);
v___x_114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_112_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
v___x_115_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__5, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__5_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__5);
v___x_116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_114_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = lean_array_to_list(v_heqs_80_);
v___x_118_ = lean_box(0);
v___x_119_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_117_, v___x_118_);
v___x_120_ = l_Lean_MessageData_ofList(v___x_119_);
v___x_121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_116_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_121_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
return v___x_122_;
}
}
else
{
lean_object* v_val_124_; lean_object* v___x_126_; 
lean_del_object(v___x_105_);
lean_dec_ref(v_binderType_93_);
lean_dec(v_binderName_92_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec_ref(v_heqs_80_);
v_val_124_ = lean_ctor_get(v_fst_103_, 0);
lean_inc(v_val_124_);
lean_dec_ref(v_fst_103_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 0, v_val_124_);
v___x_126_ = v___x_101_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_val_124_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
}
else
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
lean_dec_ref(v_binderType_93_);
lean_dec(v_binderName_92_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec_ref(v_heqs_80_);
v_a_131_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_138_ == 0)
{
v___x_133_ = v___x_98_;
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_98_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_136_; 
if (v_isShared_134_ == 0)
{
v___x_136_ = v___x_133_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_a_131_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
else
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
lean_dec_ref(v_ty_83_);
lean_dec_ref(v_e_82_);
lean_dec_ref(v_heqs_80_);
v___x_139_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__7, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__7_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__7);
v___x_140_ = l_Nat_reprFast(v_numDiscrEqs_81_);
v___x_141_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
v___x_142_ = l_Lean_MessageData_ofFormat(v___x_141_);
v___x_143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_139_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
v___x_144_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__9, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__9_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__9);
v___x_145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_143_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
v___x_146_ = l_Lean_indentExpr(v_alt_79_);
v___x_147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_145_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
v___x_148_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_147_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0(lean_object* v_binderType_149_, lean_object* v_e_150_, lean_object* v_body_151_, lean_object* v_i_152_, lean_object* v_alt_153_, lean_object* v_heqs_154_, lean_object* v_numDiscrEqs_155_, lean_object* v_as_156_, size_t v_sz_157_, size_t v_i_158_, lean_object* v_b_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
uint8_t v___x_165_; 
v___x_165_ = lean_usize_dec_lt(v_i_158_, v_sz_157_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; 
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v_numDiscrEqs_155_);
lean_dec_ref(v_heqs_154_);
lean_dec_ref(v_alt_153_);
lean_dec_ref(v_e_150_);
lean_dec_ref(v_binderType_149_);
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v_b_159_);
return v___x_166_;
}
else
{
lean_object* v_a_167_; lean_object* v___x_168_; 
lean_dec_ref(v_b_159_);
v_a_167_ = lean_array_uget_borrowed(v_as_156_, v_i_158_);
lean_inc(v___y_163_);
lean_inc_ref(v___y_162_);
lean_inc(v___y_161_);
lean_inc_ref(v___y_160_);
lean_inc(v_a_167_);
v___x_168_ = lean_infer_type(v_a_167_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_169_; lean_object* v___x_170_; 
v_a_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_a_169_);
lean_dec_ref(v___x_168_);
lean_inc(v___y_163_);
lean_inc_ref(v___y_162_);
lean_inc(v___y_161_);
lean_inc_ref(v___y_160_);
lean_inc_ref(v_binderType_149_);
v___x_170_ = l_Lean_Meta_isExprDefEq(v_a_169_, v_binderType_149_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v_a_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v_a_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_a_171_);
lean_dec_ref(v___x_170_);
v___x_172_ = lean_box(0);
v___x_173_ = lean_unbox(v_a_171_);
lean_dec(v_a_171_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; size_t v___x_175_; size_t v___x_176_; 
v___x_174_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0___closed__0));
v___x_175_ = ((size_t)1ULL);
v___x_176_ = lean_usize_add(v_i_158_, v___x_175_);
v_i_158_ = v___x_176_;
v_b_159_ = v___x_174_;
goto _start;
}
else
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec_ref(v_binderType_149_);
lean_inc(v_a_167_);
v___x_178_ = l_Lean_Expr_app___override(v_e_150_, v_a_167_);
v___x_179_ = lean_expr_instantiate1(v_body_151_, v_a_167_);
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = lean_nat_add(v_i_152_, v___x_180_);
v___x_182_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go(v_alt_153_, v_heqs_154_, v_numDiscrEqs_155_, v___x_178_, v___x_179_, v___x_181_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
lean_dec(v___x_181_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_192_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_192_ == 0)
{
v___x_185_ = v___x_182_;
v_isShared_186_ = v_isSharedCheck_192_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_182_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_192_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_187_, 0, v_a_183_);
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v___x_172_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_188_);
v___x_190_ = v___x_185_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
else
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
v_a_193_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_182_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_182_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
}
else
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v_numDiscrEqs_155_);
lean_dec_ref(v_heqs_154_);
lean_dec_ref(v_alt_153_);
lean_dec_ref(v_e_150_);
lean_dec_ref(v_binderType_149_);
v_a_201_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_170_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_170_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
else
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_216_; 
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v_numDiscrEqs_155_);
lean_dec_ref(v_heqs_154_);
lean_dec_ref(v_alt_153_);
lean_dec_ref(v_e_150_);
lean_dec_ref(v_binderType_149_);
v_a_209_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_216_ == 0)
{
v___x_211_ = v___x_168_;
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_168_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_a_209_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0___boxed(lean_object* v_binderType_217_, lean_object* v_e_218_, lean_object* v_body_219_, lean_object* v_i_220_, lean_object* v_alt_221_, lean_object* v_heqs_222_, lean_object* v_numDiscrEqs_223_, lean_object* v_as_224_, lean_object* v_sz_225_, lean_object* v_i_226_, lean_object* v_b_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
size_t v_sz_boxed_233_; size_t v_i_boxed_234_; lean_object* v_res_235_; 
v_sz_boxed_233_ = lean_unbox_usize(v_sz_225_);
lean_dec(v_sz_225_);
v_i_boxed_234_ = lean_unbox_usize(v_i_226_);
lean_dec(v_i_226_);
v_res_235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0(v_binderType_217_, v_e_218_, v_body_219_, v_i_220_, v_alt_221_, v_heqs_222_, v_numDiscrEqs_223_, v_as_224_, v_sz_boxed_233_, v_i_boxed_234_, v_b_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
lean_dec_ref(v_as_224_);
lean_dec(v_i_220_);
lean_dec_ref(v_body_219_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___boxed(lean_object* v_alt_236_, lean_object* v_heqs_237_, lean_object* v_numDiscrEqs_238_, lean_object* v_e_239_, lean_object* v_ty_240_, lean_object* v_i_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go(v_alt_236_, v_heqs_237_, v_numDiscrEqs_238_, v_e_239_, v_ty_240_, v_i_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_);
lean_dec(v_i_241_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2(lean_object* v_00_u03b1_248_, lean_object* v_msg_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v_msg_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___boxed(lean_object* v_00_u03b1_256_, lean_object* v_msg_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2(v_00_u03b1_256_, v_msg_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkAppDiscrEqs(lean_object* v_alt_264_, lean_object* v_heqs_265_, lean_object* v_numDiscrEqs_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v___x_272_; 
lean_inc(v_a_270_);
lean_inc_ref(v_a_269_);
lean_inc(v_a_268_);
lean_inc_ref(v_a_267_);
lean_inc_ref(v_alt_264_);
v___x_272_ = lean_infer_type(v_alt_264_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_a_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v_a_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_a_273_);
lean_dec_ref(v___x_272_);
v___x_274_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alt_264_);
v___x_275_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go(v_alt_264_, v_heqs_265_, v_numDiscrEqs_266_, v_alt_264_, v_a_273_, v___x_274_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
return v___x_275_;
}
else
{
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec(v_a_268_);
lean_dec_ref(v_a_267_);
lean_dec(v_numDiscrEqs_266_);
lean_dec_ref(v_heqs_265_);
lean_dec_ref(v_alt_264_);
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkAppDiscrEqs___boxed(lean_object* v_alt_276_, lean_object* v_heqs_277_, lean_object* v_numDiscrEqs_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_Meta_Match_mkAppDiscrEqs(v_alt_276_, v_heqs_277_, v_numDiscrEqs_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_);
return v_res_284_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__0(lean_object* v_x_285_){
_start:
{
uint8_t v___x_286_; 
v___x_286_ = 0;
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__0___boxed(lean_object* v_x_287_){
_start:
{
uint8_t v_res_288_; lean_object* v_r_289_; 
v_res_288_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__0(v_x_287_);
lean_dec(v_x_287_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__1(lean_object* v_fvarId_290_, lean_object* v_x_291_){
_start:
{
uint8_t v___x_292_; 
v___x_292_ = l_Lean_instBEqFVarId_beq(v_fvarId_290_, v_x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__1___boxed(lean_object* v_fvarId_293_, lean_object* v_x_294_){
_start:
{
uint8_t v_res_295_; lean_object* v_r_296_; 
v_res_295_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__1(v_fvarId_293_, v_x_294_);
lean_dec(v_x_294_);
lean_dec(v_fvarId_293_);
v_r_296_ = lean_box(v_res_295_);
return v_r_296_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_298_ = lean_box(0);
v___x_299_ = lean_unsigned_to_nat(16u);
v___x_300_ = lean_mk_array(v___x_299_, v___x_298_);
return v___x_300_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_301_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__1, &l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__1);
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v___x_301_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(lean_object* v_e_304_, lean_object* v_fvarId_305_, lean_object* v___y_306_){
_start:
{
lean_object* v___x_308_; uint8_t v_fst_310_; lean_object* v_mctx_311_; lean_object* v___y_329_; lean_object* v_mctx_334_; lean_object* v___f_335_; lean_object* v___f_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_308_ = lean_st_ref_get(v___y_306_);
v_mctx_334_ = lean_ctor_get(v___x_308_, 0);
lean_inc_ref(v_mctx_334_);
lean_dec(v___x_308_);
v___f_335_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__0));
v___f_336_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_336_, 0, v_fvarId_305_);
v___x_337_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2);
lean_inc_ref(v_mctx_334_);
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v_mctx_334_);
v___x_339_ = l_Lean_Expr_hasFVar(v_e_304_);
if (v___x_339_ == 0)
{
uint8_t v___x_340_; 
v___x_340_ = l_Lean_Expr_hasMVar(v_e_304_);
if (v___x_340_ == 0)
{
lean_dec_ref(v___x_338_);
lean_dec_ref(v___f_336_);
lean_dec_ref(v_e_304_);
v_fst_310_ = v___x_340_;
v_mctx_311_ = v_mctx_334_;
goto v___jp_309_;
}
else
{
lean_object* v___x_341_; 
lean_dec_ref(v_mctx_334_);
v___x_341_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_336_, v___f_335_, v_e_304_, v___x_338_);
v___y_329_ = v___x_341_;
goto v___jp_328_;
}
}
else
{
lean_object* v___x_342_; 
lean_dec_ref(v_mctx_334_);
v___x_342_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_336_, v___f_335_, v_e_304_, v___x_338_);
v___y_329_ = v___x_342_;
goto v___jp_328_;
}
v___jp_309_:
{
lean_object* v___x_312_; lean_object* v_cache_313_; lean_object* v_zetaDeltaFVarIds_314_; lean_object* v_postponed_315_; lean_object* v_diag_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_326_; 
v___x_312_ = lean_st_ref_take(v___y_306_);
v_cache_313_ = lean_ctor_get(v___x_312_, 1);
v_zetaDeltaFVarIds_314_ = lean_ctor_get(v___x_312_, 2);
v_postponed_315_ = lean_ctor_get(v___x_312_, 3);
v_diag_316_ = lean_ctor_get(v___x_312_, 4);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_326_ == 0)
{
lean_object* v_unused_327_; 
v_unused_327_ = lean_ctor_get(v___x_312_, 0);
lean_dec(v_unused_327_);
v___x_318_ = v___x_312_;
v_isShared_319_ = v_isSharedCheck_326_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_diag_316_);
lean_inc(v_postponed_315_);
lean_inc(v_zetaDeltaFVarIds_314_);
lean_inc(v_cache_313_);
lean_dec(v___x_312_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_326_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v_mctx_311_);
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_mctx_311_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_cache_313_);
lean_ctor_set(v_reuseFailAlloc_325_, 2, v_zetaDeltaFVarIds_314_);
lean_ctor_set(v_reuseFailAlloc_325_, 3, v_postponed_315_);
lean_ctor_set(v_reuseFailAlloc_325_, 4, v_diag_316_);
v___x_321_ = v_reuseFailAlloc_325_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = lean_st_ref_set(v___y_306_, v___x_321_);
v___x_323_ = lean_box(v_fst_310_);
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
return v___x_324_;
}
}
}
v___jp_328_:
{
lean_object* v_snd_330_; lean_object* v_fst_331_; lean_object* v_mctx_332_; uint8_t v___x_333_; 
v_snd_330_ = lean_ctor_get(v___y_329_, 1);
lean_inc(v_snd_330_);
v_fst_331_ = lean_ctor_get(v___y_329_, 0);
lean_inc(v_fst_331_);
lean_dec_ref(v___y_329_);
v_mctx_332_ = lean_ctor_get(v_snd_330_, 1);
lean_inc_ref(v_mctx_332_);
lean_dec(v_snd_330_);
v___x_333_ = lean_unbox(v_fst_331_);
lean_dec(v_fst_331_);
v_fst_310_ = v___x_333_;
v_mctx_311_ = v_mctx_332_;
goto v___jp_309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___boxed(lean_object* v_e_343_, lean_object* v_fvarId_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_e_343_, v_fvarId_344_, v___y_345_);
lean_dec(v___y_345_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0(lean_object* v_e_348_, lean_object* v_fvarId_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_e_348_, v_fvarId_349_, v___y_351_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___boxed(lean_object* v_e_356_, lean_object* v_fvarId_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0(v_e_356_, v_fvarId_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg(lean_object* v_mvarId_364_, lean_object* v_x_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_364_, v_x_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_379_ == 0)
{
v___x_374_ = v___x_371_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_372_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
v_a_380_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_371_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_371_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg___boxed(lean_object* v_mvarId_388_, lean_object* v_x_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg(v_mvarId_388_, v_x_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2(lean_object* v_00_u03b1_396_, lean_object* v_mvarId_397_, lean_object* v_x_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg(v_mvarId_397_, v_x_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___boxed(lean_object* v_00_u03b1_405_, lean_object* v_mvarId_406_, lean_object* v_x_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2(v_00_u03b1_405_, v_mvarId_406_, v_x_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5(lean_object* v_mvarId_417_, lean_object* v_as_418_, size_t v_sz_419_, size_t v_i_420_, lean_object* v_b_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
uint8_t v___x_427_; 
v___x_427_ = lean_usize_dec_lt(v_i_420_, v_sz_419_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; 
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v_mvarId_417_);
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v_b_421_);
return v___x_428_;
}
else
{
lean_object* v_snd_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_531_; 
v_snd_429_ = lean_ctor_get(v_b_421_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v_b_421_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; 
v_unused_532_ = lean_ctor_get(v_b_421_, 0);
lean_dec(v_unused_532_);
v___x_431_ = v_b_421_;
v_isShared_432_ = v_isSharedCheck_531_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_snd_429_);
lean_dec(v_b_421_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_531_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v_a_435_; lean_object* v_a_442_; 
v___x_433_ = lean_box(0);
v_a_442_ = lean_array_uget(v_as_418_, v_i_420_);
if (lean_obj_tag(v_a_442_) == 0)
{
v_a_435_ = v_snd_429_;
goto v___jp_434_;
}
else
{
lean_object* v_val_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_530_; 
v_val_443_ = lean_ctor_get(v_a_442_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v_a_442_);
if (v_isSharedCheck_530_ == 0)
{
v___x_445_ = v_a_442_;
v_isShared_446_ = v_isSharedCheck_530_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_val_443_);
lean_dec(v_a_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_530_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = l_Lean_LocalDecl_type(v_val_443_);
lean_dec(v_val_443_);
lean_inc(v___y_425_);
lean_inc_ref(v___y_424_);
lean_inc(v___y_423_);
lean_inc_ref(v___y_422_);
v___x_448_ = l_Lean_Meta_matchEq_x3f(v___x_447_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_a_449_);
lean_dec_ref(v___x_448_);
v___x_450_ = lean_box(0);
v___x_451_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5___closed__0));
if (lean_obj_tag(v_a_449_) == 1)
{
lean_object* v_val_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_521_; 
v_val_452_ = lean_ctor_get(v_a_449_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v_a_449_);
if (v_isSharedCheck_521_ == 0)
{
v___x_454_ = v_a_449_;
v_isShared_455_ = v_isSharedCheck_521_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_val_452_);
lean_dec(v_a_449_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_521_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v_snd_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_519_; 
v_snd_456_ = lean_ctor_get(v_val_452_, 1);
v_isSharedCheck_519_ = !lean_is_exclusive(v_val_452_);
if (v_isSharedCheck_519_ == 0)
{
lean_object* v_unused_520_; 
v_unused_520_ = lean_ctor_get(v_val_452_, 0);
lean_dec(v_unused_520_);
v___x_458_ = v_val_452_;
v_isShared_459_ = v_isSharedCheck_519_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_snd_456_);
lean_dec(v_val_452_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_519_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v_fst_460_; lean_object* v_snd_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_518_; 
v_fst_460_ = lean_ctor_get(v_snd_456_, 0);
v_snd_461_ = lean_ctor_get(v_snd_456_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_snd_456_);
if (v_isSharedCheck_518_ == 0)
{
v___x_463_ = v_snd_456_;
v_isShared_464_ = v_isSharedCheck_518_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_snd_461_);
lean_inc(v_fst_460_);
lean_dec(v_snd_456_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_518_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
uint8_t v___x_465_; 
v___x_465_ = l_Lean_Expr_isFVar(v_fst_460_);
if (v___x_465_ == 0)
{
lean_del_object(v___x_463_);
lean_dec(v_snd_461_);
lean_dec(v_fst_460_);
lean_del_object(v___x_458_);
lean_del_object(v___x_454_);
lean_del_object(v___x_445_);
lean_dec(v_snd_429_);
v_a_435_ = v___x_451_;
goto v___jp_434_;
}
else
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = l_Lean_Expr_fvarId_x21(v_fst_460_);
lean_dec(v_fst_460_);
lean_inc(v___x_466_);
v___x_467_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_461_, v___x_466_, v___y_423_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; uint8_t v___x_469_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_a_468_);
lean_dec_ref(v___x_467_);
v___x_469_ = lean_unbox(v_a_468_);
lean_dec(v_a_468_);
if (v___x_469_ == 0)
{
if (v___x_465_ == 0)
{
lean_dec(v___x_466_);
lean_del_object(v___x_463_);
lean_del_object(v___x_458_);
lean_del_object(v___x_454_);
lean_del_object(v___x_445_);
lean_dec(v_snd_429_);
v_a_435_ = v___x_451_;
goto v___jp_434_;
}
else
{
lean_object* v___x_470_; 
lean_inc(v___y_425_);
lean_inc_ref(v___y_424_);
lean_inc(v___y_423_);
lean_inc_ref(v___y_422_);
lean_inc(v_mvarId_417_);
v___x_470_ = l_Lean_Meta_subst_x3f(v_mvarId_417_, v___x_466_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_501_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_501_ == 0)
{
v___x_473_ = v___x_470_;
v_isShared_474_ = v_isSharedCheck_501_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_470_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_501_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
if (lean_obj_tag(v_a_471_) == 0)
{
lean_del_object(v___x_473_);
lean_del_object(v___x_463_);
lean_del_object(v___x_458_);
lean_del_object(v___x_454_);
lean_del_object(v___x_445_);
lean_dec(v_snd_429_);
v_a_435_ = v___x_451_;
goto v___jp_434_;
}
else
{
lean_object* v_val_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_500_; 
lean_del_object(v___x_431_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v_mvarId_417_);
v_val_475_ = lean_ctor_get(v_a_471_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v_a_471_);
if (v_isSharedCheck_500_ == 0)
{
v___x_477_ = v_a_471_;
v_isShared_478_ = v_isSharedCheck_500_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_val_475_);
lean_dec(v_a_471_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_500_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_479_ = lean_unsigned_to_nat(1u);
v___x_480_ = lean_mk_empty_array_with_capacity(v___x_479_);
v___x_481_ = lean_array_push(v___x_480_, v_val_475_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v___x_481_);
v___x_483_ = v___x_477_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_481_);
v___x_483_ = v_reuseFailAlloc_499_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_485_; 
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 1, v___x_450_);
lean_ctor_set(v___x_463_, 0, v___x_483_);
v___x_485_ = v___x_463_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v___x_450_);
v___x_485_ = v_reuseFailAlloc_498_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_487_; 
if (v_isShared_446_ == 0)
{
lean_ctor_set_tag(v___x_445_, 0);
lean_ctor_set(v___x_445_, 0, v___x_485_);
v___x_487_ = v___x_445_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_485_);
v___x_487_ = v_reuseFailAlloc_497_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_489_; 
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_487_);
v___x_489_ = v___x_454_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_487_);
v___x_489_ = v_reuseFailAlloc_496_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_491_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 1, v_snd_429_);
lean_ctor_set(v___x_458_, 0, v___x_489_);
v___x_491_ = v___x_458_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_snd_429_);
v___x_491_ = v_reuseFailAlloc_495_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_493_; 
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___x_491_);
v___x_493_ = v___x_473_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
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
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
lean_del_object(v___x_463_);
lean_del_object(v___x_458_);
lean_del_object(v___x_454_);
lean_del_object(v___x_445_);
lean_del_object(v___x_431_);
lean_dec(v_snd_429_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v_mvarId_417_);
v_a_502_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_470_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_470_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
else
{
lean_dec(v___x_466_);
lean_del_object(v___x_463_);
lean_del_object(v___x_458_);
lean_del_object(v___x_454_);
lean_del_object(v___x_445_);
lean_dec(v_snd_429_);
v_a_435_ = v___x_451_;
goto v___jp_434_;
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec(v___x_466_);
lean_del_object(v___x_463_);
lean_del_object(v___x_458_);
lean_del_object(v___x_454_);
lean_del_object(v___x_445_);
lean_del_object(v___x_431_);
lean_dec(v_snd_429_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v_mvarId_417_);
v_a_510_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_467_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_467_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
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
lean_dec(v_a_449_);
lean_del_object(v___x_445_);
lean_dec(v_snd_429_);
v_a_435_ = v___x_451_;
goto v___jp_434_;
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_del_object(v___x_445_);
lean_del_object(v___x_431_);
lean_dec(v_snd_429_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v_mvarId_417_);
v_a_522_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_448_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_448_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
}
v___jp_434_:
{
lean_object* v___x_437_; 
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 1, v_a_435_);
lean_ctor_set(v___x_431_, 0, v___x_433_);
v___x_437_ = v___x_431_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_a_435_);
v___x_437_ = v_reuseFailAlloc_441_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
size_t v___x_438_; size_t v___x_439_; 
v___x_438_ = ((size_t)1ULL);
v___x_439_ = lean_usize_add(v_i_420_, v___x_438_);
v_i_420_ = v___x_439_;
v_b_421_ = v___x_437_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5___boxed(lean_object* v_mvarId_533_, lean_object* v_as_534_, lean_object* v_sz_535_, lean_object* v_i_536_, lean_object* v_b_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
size_t v_sz_boxed_543_; size_t v_i_boxed_544_; lean_object* v_res_545_; 
v_sz_boxed_543_ = lean_unbox_usize(v_sz_535_);
lean_dec(v_sz_535_);
v_i_boxed_544_ = lean_unbox_usize(v_i_536_);
lean_dec(v_i_536_);
v_res_545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5(v_mvarId_533_, v_as_534_, v_sz_boxed_543_, v_i_boxed_544_, v_b_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
lean_dec_ref(v_as_534_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4(lean_object* v_mvarId_546_, lean_object* v_as_547_, size_t v_sz_548_, size_t v_i_549_, lean_object* v_b_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
uint8_t v___x_556_; 
v___x_556_ = lean_usize_dec_lt(v_i_549_, v_sz_548_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; 
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v_mvarId_546_);
v___x_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_557_, 0, v_b_550_);
return v___x_557_;
}
else
{
lean_object* v_snd_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_660_; 
v_snd_558_ = lean_ctor_get(v_b_550_, 1);
v_isSharedCheck_660_ = !lean_is_exclusive(v_b_550_);
if (v_isSharedCheck_660_ == 0)
{
lean_object* v_unused_661_; 
v_unused_661_ = lean_ctor_get(v_b_550_, 0);
lean_dec(v_unused_661_);
v___x_560_ = v_b_550_;
v_isShared_561_ = v_isSharedCheck_660_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_snd_558_);
lean_dec(v_b_550_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_660_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; lean_object* v_a_564_; lean_object* v_a_571_; 
v___x_562_ = lean_box(0);
v_a_571_ = lean_array_uget(v_as_547_, v_i_549_);
if (lean_obj_tag(v_a_571_) == 0)
{
v_a_564_ = v_snd_558_;
goto v___jp_563_;
}
else
{
lean_object* v_val_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_659_; 
v_val_572_ = lean_ctor_get(v_a_571_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v_a_571_);
if (v_isSharedCheck_659_ == 0)
{
v___x_574_ = v_a_571_;
v_isShared_575_ = v_isSharedCheck_659_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_val_572_);
lean_dec(v_a_571_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_659_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = l_Lean_LocalDecl_type(v_val_572_);
lean_dec(v_val_572_);
lean_inc(v___y_554_);
lean_inc_ref(v___y_553_);
lean_inc(v___y_552_);
lean_inc_ref(v___y_551_);
v___x_577_ = l_Lean_Meta_matchEq_x3f(v___x_576_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v_a_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v_a_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_a_578_);
lean_dec_ref(v___x_577_);
v___x_579_ = lean_box(0);
v___x_580_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5___closed__0));
if (lean_obj_tag(v_a_578_) == 1)
{
lean_object* v_val_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_650_; 
v_val_581_ = lean_ctor_get(v_a_578_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v_a_578_);
if (v_isSharedCheck_650_ == 0)
{
v___x_583_ = v_a_578_;
v_isShared_584_ = v_isSharedCheck_650_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_val_581_);
lean_dec(v_a_578_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_650_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v_snd_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_648_; 
v_snd_585_ = lean_ctor_get(v_val_581_, 1);
v_isSharedCheck_648_ = !lean_is_exclusive(v_val_581_);
if (v_isSharedCheck_648_ == 0)
{
lean_object* v_unused_649_; 
v_unused_649_ = lean_ctor_get(v_val_581_, 0);
lean_dec(v_unused_649_);
v___x_587_ = v_val_581_;
v_isShared_588_ = v_isSharedCheck_648_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_snd_585_);
lean_dec(v_val_581_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_648_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v_fst_589_; lean_object* v_snd_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_647_; 
v_fst_589_ = lean_ctor_get(v_snd_585_, 0);
v_snd_590_ = lean_ctor_get(v_snd_585_, 1);
v_isSharedCheck_647_ = !lean_is_exclusive(v_snd_585_);
if (v_isSharedCheck_647_ == 0)
{
v___x_592_ = v_snd_585_;
v_isShared_593_ = v_isSharedCheck_647_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_snd_590_);
lean_inc(v_fst_589_);
lean_dec(v_snd_585_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_647_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
uint8_t v___x_594_; 
v___x_594_ = l_Lean_Expr_isFVar(v_fst_589_);
if (v___x_594_ == 0)
{
lean_del_object(v___x_592_);
lean_dec(v_snd_590_);
lean_dec(v_fst_589_);
lean_del_object(v___x_587_);
lean_del_object(v___x_583_);
lean_del_object(v___x_574_);
lean_dec(v_snd_558_);
v_a_564_ = v___x_580_;
goto v___jp_563_;
}
else
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = l_Lean_Expr_fvarId_x21(v_fst_589_);
lean_dec(v_fst_589_);
lean_inc(v___x_595_);
v___x_596_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_590_, v___x_595_, v___y_552_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; uint8_t v___x_598_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_597_);
lean_dec_ref(v___x_596_);
v___x_598_ = lean_unbox(v_a_597_);
lean_dec(v_a_597_);
if (v___x_598_ == 0)
{
if (v___x_594_ == 0)
{
lean_dec(v___x_595_);
lean_del_object(v___x_592_);
lean_del_object(v___x_587_);
lean_del_object(v___x_583_);
lean_del_object(v___x_574_);
lean_dec(v_snd_558_);
v_a_564_ = v___x_580_;
goto v___jp_563_;
}
else
{
lean_object* v___x_599_; 
lean_inc(v___y_554_);
lean_inc_ref(v___y_553_);
lean_inc(v___y_552_);
lean_inc_ref(v___y_551_);
lean_inc(v_mvarId_546_);
v___x_599_ = l_Lean_Meta_subst_x3f(v_mvarId_546_, v___x_595_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_630_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_630_ == 0)
{
v___x_602_ = v___x_599_;
v_isShared_603_ = v_isSharedCheck_630_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_630_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
if (lean_obj_tag(v_a_600_) == 0)
{
lean_del_object(v___x_602_);
lean_del_object(v___x_592_);
lean_del_object(v___x_587_);
lean_del_object(v___x_583_);
lean_del_object(v___x_574_);
lean_dec(v_snd_558_);
v_a_564_ = v___x_580_;
goto v___jp_563_;
}
else
{
lean_object* v_val_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_629_; 
lean_del_object(v___x_560_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v_mvarId_546_);
v_val_604_ = lean_ctor_get(v_a_600_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v_a_600_);
if (v_isSharedCheck_629_ == 0)
{
v___x_606_ = v_a_600_;
v_isShared_607_ = v_isSharedCheck_629_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_val_604_);
lean_dec(v_a_600_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_629_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_612_; 
v___x_608_ = lean_unsigned_to_nat(1u);
v___x_609_ = lean_mk_empty_array_with_capacity(v___x_608_);
v___x_610_ = lean_array_push(v___x_609_, v_val_604_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_610_);
v___x_612_ = v___x_606_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_628_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_614_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 1, v___x_579_);
lean_ctor_set(v___x_592_, 0, v___x_612_);
v___x_614_ = v___x_592_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v___x_579_);
v___x_614_ = v_reuseFailAlloc_627_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_616_; 
if (v_isShared_575_ == 0)
{
lean_ctor_set_tag(v___x_574_, 0);
lean_ctor_set(v___x_574_, 0, v___x_614_);
v___x_616_ = v___x_574_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_626_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_618_; 
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_616_);
v___x_618_ = v___x_583_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_616_);
v___x_618_ = v_reuseFailAlloc_625_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
lean_object* v___x_620_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v_snd_558_);
lean_ctor_set(v___x_587_, 0, v___x_618_);
v___x_620_ = v___x_587_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_618_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_snd_558_);
v___x_620_ = v_reuseFailAlloc_624_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_622_; 
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_620_);
v___x_622_ = v___x_602_;
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
}
}
}
}
}
}
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_del_object(v___x_592_);
lean_del_object(v___x_587_);
lean_del_object(v___x_583_);
lean_del_object(v___x_574_);
lean_del_object(v___x_560_);
lean_dec(v_snd_558_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v_mvarId_546_);
v_a_631_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_599_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_599_);
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
lean_dec(v___x_595_);
lean_del_object(v___x_592_);
lean_del_object(v___x_587_);
lean_del_object(v___x_583_);
lean_del_object(v___x_574_);
lean_dec(v_snd_558_);
v_a_564_ = v___x_580_;
goto v___jp_563_;
}
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec(v___x_595_);
lean_del_object(v___x_592_);
lean_del_object(v___x_587_);
lean_del_object(v___x_583_);
lean_del_object(v___x_574_);
lean_del_object(v___x_560_);
lean_dec(v_snd_558_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v_mvarId_546_);
v_a_639_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_596_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_596_);
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
}
}
}
}
else
{
lean_dec(v_a_578_);
lean_del_object(v___x_574_);
lean_dec(v_snd_558_);
v_a_564_ = v___x_580_;
goto v___jp_563_;
}
}
else
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_del_object(v___x_574_);
lean_del_object(v___x_560_);
lean_dec(v_snd_558_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v_mvarId_546_);
v_a_651_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_577_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_577_);
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
v___jp_563_:
{
lean_object* v___x_566_; 
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 1, v_a_564_);
lean_ctor_set(v___x_560_, 0, v___x_562_);
v___x_566_ = v___x_560_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_a_564_);
v___x_566_ = v_reuseFailAlloc_570_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
size_t v___x_567_; size_t v___x_568_; lean_object* v___x_569_; 
v___x_567_ = ((size_t)1ULL);
v___x_568_ = lean_usize_add(v_i_549_, v___x_567_);
v___x_569_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5(v_mvarId_546_, v_as_547_, v_sz_548_, v___x_568_, v___x_566_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
return v___x_569_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4___boxed(lean_object* v_mvarId_662_, lean_object* v_as_663_, lean_object* v_sz_664_, lean_object* v_i_665_, lean_object* v_b_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
size_t v_sz_boxed_672_; size_t v_i_boxed_673_; lean_object* v_res_674_; 
v_sz_boxed_672_ = lean_unbox_usize(v_sz_664_);
lean_dec(v_sz_664_);
v_i_boxed_673_ = lean_unbox_usize(v_i_665_);
lean_dec(v_i_665_);
v_res_674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4(v_mvarId_662_, v_as_663_, v_sz_boxed_672_, v_i_boxed_673_, v_b_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
lean_dec_ref(v_as_663_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(lean_object* v_mvarId_675_, lean_object* v_inh_676_, lean_object* v_n_677_, lean_object* v_b_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
if (lean_obj_tag(v_n_677_) == 0)
{
lean_object* v_cs_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_718_; 
v_cs_684_ = lean_ctor_get(v_n_677_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v_n_677_);
if (v_isSharedCheck_718_ == 0)
{
v___x_686_ = v_n_677_;
v_isShared_687_ = v_isSharedCheck_718_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_cs_684_);
lean_dec(v_n_677_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_718_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_689_; size_t v_sz_690_; size_t v___x_691_; lean_object* v___x_692_; 
v___x_688_ = lean_box(0);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set(v___x_689_, 1, v_b_678_);
v_sz_690_ = lean_array_size(v_cs_684_);
v___x_691_ = ((size_t)0ULL);
v___x_692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(v_mvarId_675_, v_inh_676_, v_cs_684_, v_sz_690_, v___x_691_, v___x_689_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec_ref(v_cs_684_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_709_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_709_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_709_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_709_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v_fst_697_; 
v_fst_697_ = lean_ctor_get(v_a_693_, 0);
if (lean_obj_tag(v_fst_697_) == 0)
{
lean_object* v_snd_698_; lean_object* v___x_700_; 
v_snd_698_ = lean_ctor_get(v_a_693_, 1);
lean_inc(v_snd_698_);
lean_dec(v_a_693_);
if (v_isShared_687_ == 0)
{
lean_ctor_set_tag(v___x_686_, 1);
lean_ctor_set(v___x_686_, 0, v_snd_698_);
v___x_700_ = v___x_686_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_snd_698_);
v___x_700_ = v_reuseFailAlloc_704_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_702_; 
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_700_);
v___x_702_ = v___x_695_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
else
{
lean_object* v_val_705_; lean_object* v___x_707_; 
lean_inc_ref(v_fst_697_);
lean_dec(v_a_693_);
lean_del_object(v___x_686_);
v_val_705_ = lean_ctor_get(v_fst_697_, 0);
lean_inc(v_val_705_);
lean_dec_ref(v_fst_697_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v_val_705_);
v___x_707_ = v___x_695_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_val_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_del_object(v___x_686_);
v_a_710_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_692_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_692_);
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
lean_object* v_vs_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_753_; 
v_vs_719_ = lean_ctor_get(v_n_677_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v_n_677_);
if (v_isSharedCheck_753_ == 0)
{
v___x_721_ = v_n_677_;
v_isShared_722_ = v_isSharedCheck_753_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_vs_719_);
lean_dec(v_n_677_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_753_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; lean_object* v___x_724_; size_t v_sz_725_; size_t v___x_726_; lean_object* v___x_727_; 
v___x_723_ = lean_box(0);
v___x_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
lean_ctor_set(v___x_724_, 1, v_b_678_);
v_sz_725_ = lean_array_size(v_vs_719_);
v___x_726_ = ((size_t)0ULL);
v___x_727_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4(v_mvarId_675_, v_vs_719_, v_sz_725_, v___x_726_, v___x_724_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec_ref(v_vs_719_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_744_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_744_ == 0)
{
v___x_730_ = v___x_727_;
v_isShared_731_ = v_isSharedCheck_744_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_727_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_744_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v_fst_732_; 
v_fst_732_ = lean_ctor_get(v_a_728_, 0);
if (lean_obj_tag(v_fst_732_) == 0)
{
lean_object* v_snd_733_; lean_object* v___x_735_; 
v_snd_733_ = lean_ctor_get(v_a_728_, 1);
lean_inc(v_snd_733_);
lean_dec(v_a_728_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v_snd_733_);
v___x_735_ = v___x_721_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_snd_733_);
v___x_735_ = v_reuseFailAlloc_739_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_737_; 
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_735_);
v___x_737_ = v___x_730_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
else
{
lean_object* v_val_740_; lean_object* v___x_742_; 
lean_inc_ref(v_fst_732_);
lean_dec(v_a_728_);
lean_del_object(v___x_721_);
v_val_740_ = lean_ctor_get(v_fst_732_, 0);
lean_inc(v_val_740_);
lean_dec_ref(v_fst_732_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v_val_740_);
v___x_742_ = v___x_730_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_val_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_del_object(v___x_721_);
v_a_745_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_727_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_727_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(lean_object* v_mvarId_754_, lean_object* v_inh_755_, lean_object* v_as_756_, size_t v_sz_757_, size_t v_i_758_, lean_object* v_b_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
uint8_t v___x_765_; 
v___x_765_ = lean_usize_dec_lt(v_i_758_, v_sz_757_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; 
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v_mvarId_754_);
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v_b_759_);
return v___x_766_;
}
else
{
lean_object* v_snd_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_801_; 
v_snd_767_ = lean_ctor_get(v_b_759_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v_b_759_);
if (v_isSharedCheck_801_ == 0)
{
lean_object* v_unused_802_; 
v_unused_802_ = lean_ctor_get(v_b_759_, 0);
lean_dec(v_unused_802_);
v___x_769_ = v_b_759_;
v_isShared_770_ = v_isSharedCheck_801_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_snd_767_);
lean_dec(v_b_759_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_801_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v_a_771_; lean_object* v___x_772_; 
v_a_771_ = lean_array_uget_borrowed(v_as_756_, v_i_758_);
lean_inc(v___y_763_);
lean_inc_ref(v___y_762_);
lean_inc(v___y_761_);
lean_inc_ref(v___y_760_);
lean_inc(v_snd_767_);
lean_inc(v_a_771_);
lean_inc(v_mvarId_754_);
v___x_772_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_mvarId_754_, v_inh_755_, v_a_771_, v_snd_767_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_792_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_792_ == 0)
{
v___x_775_ = v___x_772_;
v_isShared_776_ = v_isSharedCheck_792_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_772_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_792_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
if (lean_obj_tag(v_a_773_) == 0)
{
lean_object* v___x_777_; lean_object* v___x_779_; 
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v_mvarId_754_);
v___x_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_777_, 0, v_a_773_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_777_);
v___x_779_ = v___x_769_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_snd_767_);
v___x_779_ = v_reuseFailAlloc_783_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v___x_781_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v___x_779_);
v___x_781_ = v___x_775_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_785_; lean_object* v___x_787_; 
lean_del_object(v___x_775_);
lean_dec(v_snd_767_);
v_a_784_ = lean_ctor_get(v_a_773_, 0);
lean_inc(v_a_784_);
lean_dec_ref(v_a_773_);
v___x_785_ = lean_box(0);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 1, v_a_784_);
lean_ctor_set(v___x_769_, 0, v___x_785_);
v___x_787_ = v___x_769_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_a_784_);
v___x_787_ = v_reuseFailAlloc_791_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
size_t v___x_788_; size_t v___x_789_; 
v___x_788_ = ((size_t)1ULL);
v___x_789_ = lean_usize_add(v_i_758_, v___x_788_);
v_i_758_ = v___x_789_;
v_b_759_ = v___x_787_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
lean_del_object(v___x_769_);
lean_dec(v_snd_767_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v_mvarId_754_);
v_a_793_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_772_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_772_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3___boxed(lean_object* v_mvarId_803_, lean_object* v_inh_804_, lean_object* v_as_805_, lean_object* v_sz_806_, lean_object* v_i_807_, lean_object* v_b_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
size_t v_sz_boxed_814_; size_t v_i_boxed_815_; lean_object* v_res_816_; 
v_sz_boxed_814_ = lean_unbox_usize(v_sz_806_);
lean_dec(v_sz_806_);
v_i_boxed_815_ = lean_unbox_usize(v_i_807_);
lean_dec(v_i_807_);
v_res_816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(v_mvarId_803_, v_inh_804_, v_as_805_, v_sz_boxed_814_, v_i_boxed_815_, v_b_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
lean_dec_ref(v_as_805_);
lean_dec_ref(v_inh_804_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1___boxed(lean_object* v_mvarId_817_, lean_object* v_inh_818_, lean_object* v_n_819_, lean_object* v_b_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_mvarId_817_, v_inh_818_, v_n_819_, v_b_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
lean_dec_ref(v_inh_818_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(lean_object* v_mvarId_830_, lean_object* v_as_831_, size_t v_sz_832_, size_t v_i_833_, lean_object* v_b_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
uint8_t v___x_840_; 
v___x_840_ = lean_usize_dec_lt(v_i_833_, v_sz_832_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; 
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v_mvarId_830_);
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v_b_834_);
return v___x_841_;
}
else
{
lean_object* v_snd_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_937_; 
v_snd_842_ = lean_ctor_get(v_b_834_, 1);
v_isSharedCheck_937_ = !lean_is_exclusive(v_b_834_);
if (v_isSharedCheck_937_ == 0)
{
lean_object* v_unused_938_; 
v_unused_938_ = lean_ctor_get(v_b_834_, 0);
lean_dec(v_unused_938_);
v___x_844_ = v_b_834_;
v_isShared_845_ = v_isSharedCheck_937_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_snd_842_);
lean_dec(v_b_834_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_937_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v_a_848_; lean_object* v_a_855_; 
v___x_846_ = lean_box(0);
v_a_855_ = lean_array_uget_borrowed(v_as_831_, v_i_833_);
if (lean_obj_tag(v_a_855_) == 0)
{
v_a_848_ = v_snd_842_;
goto v___jp_847_;
}
else
{
lean_object* v_val_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v_val_856_ = lean_ctor_get(v_a_855_, 0);
v___x_857_ = l_Lean_LocalDecl_type(v_val_856_);
lean_inc(v___y_838_);
lean_inc_ref(v___y_837_);
lean_inc(v___y_836_);
lean_inc_ref(v___y_835_);
v___x_858_ = l_Lean_Meta_matchEq_x3f(v___x_857_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref(v___x_858_);
v___x_860_ = lean_box(0);
v___x_861_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___closed__0));
if (lean_obj_tag(v_a_859_) == 1)
{
lean_object* v_val_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_928_; 
v_val_862_ = lean_ctor_get(v_a_859_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v_a_859_);
if (v_isSharedCheck_928_ == 0)
{
v___x_864_ = v_a_859_;
v_isShared_865_ = v_isSharedCheck_928_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_val_862_);
lean_dec(v_a_859_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_928_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v_snd_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_926_; 
v_snd_866_ = lean_ctor_get(v_val_862_, 1);
v_isSharedCheck_926_ = !lean_is_exclusive(v_val_862_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; 
v_unused_927_ = lean_ctor_get(v_val_862_, 0);
lean_dec(v_unused_927_);
v___x_868_ = v_val_862_;
v_isShared_869_ = v_isSharedCheck_926_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_snd_866_);
lean_dec(v_val_862_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_926_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v_fst_870_; lean_object* v_snd_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_925_; 
v_fst_870_ = lean_ctor_get(v_snd_866_, 0);
v_snd_871_ = lean_ctor_get(v_snd_866_, 1);
v_isSharedCheck_925_ = !lean_is_exclusive(v_snd_866_);
if (v_isSharedCheck_925_ == 0)
{
v___x_873_ = v_snd_866_;
v_isShared_874_ = v_isSharedCheck_925_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_snd_871_);
lean_inc(v_fst_870_);
lean_dec(v_snd_866_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_925_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
uint8_t v___x_875_; 
v___x_875_ = l_Lean_Expr_isFVar(v_fst_870_);
if (v___x_875_ == 0)
{
lean_del_object(v___x_873_);
lean_dec(v_snd_871_);
lean_dec(v_fst_870_);
lean_del_object(v___x_868_);
lean_del_object(v___x_864_);
lean_dec(v_snd_842_);
v_a_848_ = v___x_861_;
goto v___jp_847_;
}
else
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = l_Lean_Expr_fvarId_x21(v_fst_870_);
lean_dec(v_fst_870_);
lean_inc(v___x_876_);
v___x_877_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_871_, v___x_876_, v___y_836_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; uint8_t v___x_879_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref(v___x_877_);
v___x_879_ = lean_unbox(v_a_878_);
lean_dec(v_a_878_);
if (v___x_879_ == 0)
{
if (v___x_875_ == 0)
{
lean_dec(v___x_876_);
lean_del_object(v___x_873_);
lean_del_object(v___x_868_);
lean_del_object(v___x_864_);
lean_dec(v_snd_842_);
v_a_848_ = v___x_861_;
goto v___jp_847_;
}
else
{
lean_object* v___x_880_; 
lean_inc(v___y_838_);
lean_inc_ref(v___y_837_);
lean_inc(v___y_836_);
lean_inc_ref(v___y_835_);
lean_inc(v_mvarId_830_);
v___x_880_ = l_Lean_Meta_subst_x3f(v_mvarId_830_, v___x_876_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_908_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_908_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_908_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_908_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
if (lean_obj_tag(v_a_881_) == 0)
{
lean_del_object(v___x_883_);
lean_del_object(v___x_873_);
lean_del_object(v___x_868_);
lean_del_object(v___x_864_);
lean_dec(v_snd_842_);
v_a_848_ = v___x_861_;
goto v___jp_847_;
}
else
{
lean_object* v_val_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_907_; 
lean_del_object(v___x_844_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v_mvarId_830_);
v_val_885_ = lean_ctor_get(v_a_881_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v_a_881_);
if (v_isSharedCheck_907_ == 0)
{
v___x_887_ = v_a_881_;
v_isShared_888_ = v_isSharedCheck_907_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_val_885_);
lean_dec(v_a_881_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_907_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_889_ = lean_unsigned_to_nat(1u);
v___x_890_ = lean_mk_empty_array_with_capacity(v___x_889_);
v___x_891_ = lean_array_push(v___x_890_, v_val_885_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_891_);
v___x_893_ = v___x_887_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_906_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_895_; 
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 1, v___x_860_);
lean_ctor_set(v___x_873_, 0, v___x_893_);
v___x_895_ = v___x_873_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v___x_860_);
v___x_895_ = v_reuseFailAlloc_905_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
lean_object* v___x_897_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_895_);
v___x_897_ = v___x_864_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_895_);
v___x_897_ = v_reuseFailAlloc_904_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_899_; 
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 1, v_snd_842_);
lean_ctor_set(v___x_868_, 0, v___x_897_);
v___x_899_ = v___x_868_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_snd_842_);
v___x_899_ = v_reuseFailAlloc_903_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_901_; 
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_899_);
v___x_901_ = v___x_883_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
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
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
lean_del_object(v___x_873_);
lean_del_object(v___x_868_);
lean_del_object(v___x_864_);
lean_del_object(v___x_844_);
lean_dec(v_snd_842_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v_mvarId_830_);
v_a_909_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_880_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_880_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
else
{
lean_dec(v___x_876_);
lean_del_object(v___x_873_);
lean_del_object(v___x_868_);
lean_del_object(v___x_864_);
lean_dec(v_snd_842_);
v_a_848_ = v___x_861_;
goto v___jp_847_;
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec(v___x_876_);
lean_del_object(v___x_873_);
lean_del_object(v___x_868_);
lean_del_object(v___x_864_);
lean_del_object(v___x_844_);
lean_dec(v_snd_842_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v_mvarId_830_);
v_a_917_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_877_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_877_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
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
lean_dec(v_a_859_);
lean_dec(v_snd_842_);
v_a_848_ = v___x_861_;
goto v___jp_847_;
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
lean_del_object(v___x_844_);
lean_dec(v_snd_842_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v_mvarId_830_);
v_a_929_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_858_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_858_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
v___jp_847_:
{
lean_object* v___x_850_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v_a_848_);
lean_ctor_set(v___x_844_, 0, v___x_846_);
v___x_850_ = v___x_844_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_a_848_);
v___x_850_ = v_reuseFailAlloc_854_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
size_t v___x_851_; size_t v___x_852_; 
v___x_851_ = ((size_t)1ULL);
v___x_852_ = lean_usize_add(v_i_833_, v___x_851_);
v_i_833_ = v___x_852_;
v_b_834_ = v___x_850_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___boxed(lean_object* v_mvarId_939_, lean_object* v_as_940_, lean_object* v_sz_941_, lean_object* v_i_942_, lean_object* v_b_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
size_t v_sz_boxed_949_; size_t v_i_boxed_950_; lean_object* v_res_951_; 
v_sz_boxed_949_ = lean_unbox_usize(v_sz_941_);
lean_dec(v_sz_941_);
v_i_boxed_950_ = lean_unbox_usize(v_i_942_);
lean_dec(v_i_942_);
v_res_951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(v_mvarId_939_, v_as_940_, v_sz_boxed_949_, v_i_boxed_950_, v_b_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec_ref(v_as_940_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(lean_object* v_mvarId_952_, lean_object* v_as_953_, size_t v_sz_954_, size_t v_i_955_, lean_object* v_b_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
uint8_t v___x_962_; 
v___x_962_ = lean_usize_dec_lt(v_i_955_, v_sz_954_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; 
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v_mvarId_952_);
v___x_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_963_, 0, v_b_956_);
return v___x_963_;
}
else
{
lean_object* v_snd_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_1059_; 
v_snd_964_ = lean_ctor_get(v_b_956_, 1);
v_isSharedCheck_1059_ = !lean_is_exclusive(v_b_956_);
if (v_isSharedCheck_1059_ == 0)
{
lean_object* v_unused_1060_; 
v_unused_1060_ = lean_ctor_get(v_b_956_, 0);
lean_dec(v_unused_1060_);
v___x_966_ = v_b_956_;
v_isShared_967_ = v_isSharedCheck_1059_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_snd_964_);
lean_dec(v_b_956_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_1059_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_968_; lean_object* v_a_970_; lean_object* v_a_977_; 
v___x_968_ = lean_box(0);
v_a_977_ = lean_array_uget_borrowed(v_as_953_, v_i_955_);
if (lean_obj_tag(v_a_977_) == 0)
{
v_a_970_ = v_snd_964_;
goto v___jp_969_;
}
else
{
lean_object* v_val_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v_val_978_ = lean_ctor_get(v_a_977_, 0);
v___x_979_ = l_Lean_LocalDecl_type(v_val_978_);
lean_inc(v___y_960_);
lean_inc_ref(v___y_959_);
lean_inc(v___y_958_);
lean_inc_ref(v___y_957_);
v___x_980_ = l_Lean_Meta_matchEq_x3f(v___x_979_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref(v___x_980_);
v___x_982_ = lean_box(0);
v___x_983_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___closed__0));
if (lean_obj_tag(v_a_981_) == 1)
{
lean_object* v_val_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_1050_; 
v_val_984_ = lean_ctor_get(v_a_981_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_a_981_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_986_ = v_a_981_;
v_isShared_987_ = v_isSharedCheck_1050_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_val_984_);
lean_dec(v_a_981_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_1050_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v_snd_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1048_; 
v_snd_988_ = lean_ctor_get(v_val_984_, 1);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_val_984_);
if (v_isSharedCheck_1048_ == 0)
{
lean_object* v_unused_1049_; 
v_unused_1049_ = lean_ctor_get(v_val_984_, 0);
lean_dec(v_unused_1049_);
v___x_990_ = v_val_984_;
v_isShared_991_ = v_isSharedCheck_1048_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_snd_988_);
lean_dec(v_val_984_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1048_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v_fst_992_; lean_object* v_snd_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1047_; 
v_fst_992_ = lean_ctor_get(v_snd_988_, 0);
v_snd_993_ = lean_ctor_get(v_snd_988_, 1);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_snd_988_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_995_ = v_snd_988_;
v_isShared_996_ = v_isSharedCheck_1047_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_snd_993_);
lean_inc(v_fst_992_);
lean_dec(v_snd_988_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1047_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
uint8_t v___x_997_; 
v___x_997_ = l_Lean_Expr_isFVar(v_fst_992_);
if (v___x_997_ == 0)
{
lean_del_object(v___x_995_);
lean_dec(v_snd_993_);
lean_dec(v_fst_992_);
lean_del_object(v___x_990_);
lean_del_object(v___x_986_);
lean_dec(v_snd_964_);
v_a_970_ = v___x_983_;
goto v___jp_969_;
}
else
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = l_Lean_Expr_fvarId_x21(v_fst_992_);
lean_dec(v_fst_992_);
lean_inc(v___x_998_);
v___x_999_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_993_, v___x_998_, v___y_958_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; uint8_t v___x_1001_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref(v___x_999_);
v___x_1001_ = lean_unbox(v_a_1000_);
lean_dec(v_a_1000_);
if (v___x_1001_ == 0)
{
if (v___x_997_ == 0)
{
lean_dec(v___x_998_);
lean_del_object(v___x_995_);
lean_del_object(v___x_990_);
lean_del_object(v___x_986_);
lean_dec(v_snd_964_);
v_a_970_ = v___x_983_;
goto v___jp_969_;
}
else
{
lean_object* v___x_1002_; 
lean_inc(v___y_960_);
lean_inc_ref(v___y_959_);
lean_inc(v___y_958_);
lean_inc_ref(v___y_957_);
lean_inc(v_mvarId_952_);
v___x_1002_ = l_Lean_Meta_subst_x3f(v_mvarId_952_, v___x_998_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1030_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1030_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1030_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
if (lean_obj_tag(v_a_1003_) == 0)
{
lean_del_object(v___x_1005_);
lean_del_object(v___x_995_);
lean_del_object(v___x_990_);
lean_del_object(v___x_986_);
lean_dec(v_snd_964_);
v_a_970_ = v___x_983_;
goto v___jp_969_;
}
else
{
lean_object* v_val_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1029_; 
lean_del_object(v___x_966_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v_mvarId_952_);
v_val_1007_ = lean_ctor_get(v_a_1003_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_a_1003_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1009_ = v_a_1003_;
v_isShared_1010_ = v_isSharedCheck_1029_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_val_1007_);
lean_dec(v_a_1003_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1029_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1011_ = lean_unsigned_to_nat(1u);
v___x_1012_ = lean_mk_empty_array_with_capacity(v___x_1011_);
v___x_1013_ = lean_array_push(v___x_1012_, v_val_1007_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1013_);
v___x_1015_ = v___x_1009_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1017_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 1, v___x_982_);
lean_ctor_set(v___x_995_, 0, v___x_1015_);
v___x_1017_ = v___x_995_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v___x_982_);
v___x_1017_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1019_; 
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v___x_1017_);
v___x_1019_ = v___x_986_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1021_; 
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 1, v_snd_964_);
lean_ctor_set(v___x_990_, 0, v___x_1019_);
v___x_1021_ = v___x_990_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1019_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_snd_964_);
v___x_1021_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1023_; 
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1021_);
v___x_1023_ = v___x_1005_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
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
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_del_object(v___x_995_);
lean_del_object(v___x_990_);
lean_del_object(v___x_986_);
lean_del_object(v___x_966_);
lean_dec(v_snd_964_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v_mvarId_952_);
v_a_1031_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1002_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1002_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
else
{
lean_dec(v___x_998_);
lean_del_object(v___x_995_);
lean_del_object(v___x_990_);
lean_del_object(v___x_986_);
lean_dec(v_snd_964_);
v_a_970_ = v___x_983_;
goto v___jp_969_;
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec(v___x_998_);
lean_del_object(v___x_995_);
lean_del_object(v___x_990_);
lean_del_object(v___x_986_);
lean_del_object(v___x_966_);
lean_dec(v_snd_964_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v_mvarId_952_);
v_a_1039_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_999_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_999_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
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
lean_dec(v_a_981_);
lean_dec(v_snd_964_);
v_a_970_ = v___x_983_;
goto v___jp_969_;
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_del_object(v___x_966_);
lean_dec(v_snd_964_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v_mvarId_952_);
v_a_1051_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_980_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_980_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
v___jp_969_:
{
lean_object* v___x_972_; 
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 1, v_a_970_);
lean_ctor_set(v___x_966_, 0, v___x_968_);
v___x_972_ = v___x_966_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_a_970_);
v___x_972_ = v_reuseFailAlloc_976_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
size_t v___x_973_; size_t v___x_974_; lean_object* v___x_975_; 
v___x_973_ = ((size_t)1ULL);
v___x_974_ = lean_usize_add(v_i_955_, v___x_973_);
v___x_975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(v_mvarId_952_, v_as_953_, v_sz_954_, v___x_974_, v___x_972_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
return v___x_975_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2___boxed(lean_object* v_mvarId_1061_, lean_object* v_as_1062_, lean_object* v_sz_1063_, lean_object* v_i_1064_, lean_object* v_b_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
size_t v_sz_boxed_1071_; size_t v_i_boxed_1072_; lean_object* v_res_1073_; 
v_sz_boxed_1071_ = lean_unbox_usize(v_sz_1063_);
lean_dec(v_sz_1063_);
v_i_boxed_1072_ = lean_unbox_usize(v_i_1064_);
lean_dec(v_i_1064_);
v_res_1073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(v_mvarId_1061_, v_as_1062_, v_sz_boxed_1071_, v_i_boxed_1072_, v_b_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec_ref(v_as_1062_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(lean_object* v_mvarId_1074_, lean_object* v_t_1075_, lean_object* v_init_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_root_1082_; lean_object* v_tail_1083_; lean_object* v___x_1084_; 
v_root_1082_ = lean_ctor_get(v_t_1075_, 0);
lean_inc_ref(v_root_1082_);
v_tail_1083_ = lean_ctor_get(v_t_1075_, 1);
lean_inc_ref(v_tail_1083_);
lean_dec_ref(v_t_1075_);
lean_inc(v___y_1080_);
lean_inc_ref(v___y_1079_);
lean_inc(v___y_1078_);
lean_inc_ref(v___y_1077_);
lean_inc_ref(v_init_1076_);
lean_inc(v_mvarId_1074_);
v___x_1084_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_mvarId_1074_, v_init_1076_, v_root_1082_, v_init_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
lean_dec_ref(v_init_1076_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1121_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1121_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1121_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
if (lean_obj_tag(v_a_1085_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1091_; 
lean_dec_ref(v_tail_1083_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v_mvarId_1074_);
v_a_1089_ = lean_ctor_get(v_a_1085_, 0);
lean_inc(v_a_1089_);
lean_dec_ref(v_a_1085_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v_a_1089_);
v___x_1091_ = v___x_1087_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; size_t v_sz_1096_; size_t v___x_1097_; lean_object* v___x_1098_; 
lean_del_object(v___x_1087_);
v_a_1093_ = lean_ctor_get(v_a_1085_, 0);
lean_inc(v_a_1093_);
lean_dec_ref(v_a_1085_);
v___x_1094_ = lean_box(0);
v___x_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
lean_ctor_set(v___x_1095_, 1, v_a_1093_);
v_sz_1096_ = lean_array_size(v_tail_1083_);
v___x_1097_ = ((size_t)0ULL);
v___x_1098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(v_mvarId_1074_, v_tail_1083_, v_sz_1096_, v___x_1097_, v___x_1095_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
lean_dec_ref(v_tail_1083_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1112_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1101_ = v___x_1098_;
v_isShared_1102_ = v_isSharedCheck_1112_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1098_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1112_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v_fst_1103_; 
v_fst_1103_ = lean_ctor_get(v_a_1099_, 0);
if (lean_obj_tag(v_fst_1103_) == 0)
{
lean_object* v_snd_1104_; lean_object* v___x_1106_; 
v_snd_1104_ = lean_ctor_get(v_a_1099_, 1);
lean_inc(v_snd_1104_);
lean_dec(v_a_1099_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v_snd_1104_);
v___x_1106_ = v___x_1101_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_snd_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
else
{
lean_object* v_val_1108_; lean_object* v___x_1110_; 
lean_inc_ref(v_fst_1103_);
lean_dec(v_a_1099_);
v_val_1108_ = lean_ctor_get(v_fst_1103_, 0);
lean_inc(v_val_1108_);
lean_dec_ref(v_fst_1103_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v_val_1108_);
v___x_1110_ = v___x_1101_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_val_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
v_a_1113_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1098_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1098_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_dec_ref(v_tail_1083_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v_mvarId_1074_);
v_a_1122_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1084_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1084_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1___boxed(lean_object* v_mvarId_1130_, lean_object* v_t_1131_, lean_object* v_init_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(v_mvarId_1130_, v_t_1131_, v_init_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
return v_res_1138_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__1));
v___x_1144_ = l_Lean_stringToMessageData(v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0(lean_object* v_mvarId_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_lctx_1151_; lean_object* v_decls_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v_lctx_1151_ = lean_ctor_get(v___y_1146_, 2);
v_decls_1152_ = lean_ctor_get(v_lctx_1151_, 1);
v___x_1153_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__0));
lean_inc(v___y_1149_);
lean_inc_ref(v___y_1148_);
lean_inc(v___y_1147_);
lean_inc_ref(v___y_1146_);
lean_inc_ref(v_decls_1152_);
v___x_1154_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(v_mvarId_1145_, v_decls_1152_, v___x_1153_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1166_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1166_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1166_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v_fst_1159_; 
v_fst_1159_ = lean_ctor_get(v_a_1155_, 0);
lean_inc(v_fst_1159_);
lean_dec(v_a_1155_);
if (lean_obj_tag(v_fst_1159_) == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_del_object(v___x_1157_);
v___x_1160_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2);
v___x_1161_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1160_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
return v___x_1161_;
}
else
{
lean_object* v_val_1162_; lean_object* v___x_1164_; 
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
v_val_1162_ = lean_ctor_get(v_fst_1159_, 0);
lean_inc(v_val_1162_);
lean_dec_ref(v_fst_1159_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v_val_1162_);
v___x_1164_ = v___x_1157_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_val_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
v_a_1167_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1154_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1154_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___boxed(lean_object* v_mvarId_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0(v_mvarId_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(lean_object* v_mvarId_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v___f_1188_; lean_object* v___x_1189_; 
lean_inc(v_mvarId_1182_);
v___f_1188_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1188_, 0, v_mvarId_1182_);
v___x_1189_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg(v_mvarId_1182_, v___f_1188_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___boxed(lean_object* v_mvarId_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(v_mvarId_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
return v_res_1196_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0(lean_object* v_x_1202_){
_start:
{
lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__2));
v___x_1204_ = lean_name_eq(v_x_1202_, v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___boxed(lean_object* v_x_1205_){
_start:
{
uint8_t v_res_1206_; lean_object* v_r_1207_; 
v_res_1206_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0(v_x_1205_);
lean_dec(v_x_1205_);
v_r_1207_ = lean_box(v_res_1206_);
return v_r_1207_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1(lean_object* v_e_1208_){
_start:
{
lean_object* v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__2));
v___x_1210_ = l_Lean_Expr_isConstOf(v_e_1208_, v___x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1___boxed(lean_object* v_e_1211_){
_start:
{
uint8_t v_res_1212_; lean_object* v_r_1213_; 
v_res_1212_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1(v_e_1211_);
lean_dec_ref(v_e_1211_);
v_r_1213_ = lean_box(v_res_1212_);
return v_r_1213_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__2));
v___x_1218_ = l_Lean_stringToMessageData(v___x_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(lean_object* v_mvarId_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v___x_1225_; 
lean_inc(v_mvarId_1219_);
v___x_1225_ = l_Lean_MVarId_getType(v_mvarId_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v___f_1227_; lean_object* v___f_1228_; lean_object* v___x_1229_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1226_);
lean_dec_ref(v___x_1225_);
v___f_1227_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__0));
v___f_1228_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__1));
v___x_1229_ = lean_find_expr(v___f_1228_, v_a_1226_);
lean_dec(v_a_1226_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec(v_mvarId_1219_);
v___x_1230_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3);
v___x_1231_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1230_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
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
lean_object* v___x_1240_; 
lean_dec_ref(v___x_1229_);
v___x_1240_ = l_Lean_MVarId_deltaTarget(v_mvarId_1219_, v___f_1227_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_);
return v___x_1240_;
}
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_mvarId_1219_);
v_a_1241_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1225_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1225_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___boxed(lean_object* v_mvarId_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(v_mvarId_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___redArg(lean_object* v_cls_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_options_1262_; uint8_t v_hasTrace_1263_; 
v_options_1262_ = lean_ctor_get(v___y_1260_, 2);
v_hasTrace_1263_ = lean_ctor_get_uint8(v_options_1262_, sizeof(void*)*1);
if (v_hasTrace_1263_ == 0)
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
lean_dec(v_cls_1259_);
v___x_1264_ = lean_box(v_hasTrace_1263_);
v___x_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
return v___x_1265_;
}
else
{
lean_object* v_inheritedTraceOptions_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v_inheritedTraceOptions_1266_ = lean_ctor_get(v___y_1260_, 13);
v___x_1267_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___redArg___closed__1));
v___x_1268_ = l_Lean_Name_append(v___x_1267_, v_cls_1259_);
v___x_1269_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1266_, v_options_1262_, v___x_1268_);
lean_dec(v___x_1268_);
v___x_1270_ = lean_box(v___x_1269_);
v___x_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
return v___x_1271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___redArg___boxed(lean_object* v_cls_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___redArg(v_cls_1272_, v___y_1273_);
lean_dec_ref(v___y_1273_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(lean_object* v_cls_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___redArg(v_cls_1276_, v___y_1279_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___boxed(lean_object* v_cls_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v_cls_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
return v_res_1289_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = l_Lean_maxRecDepthErrorMessage;
v___x_1296_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
return v___x_1296_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__3);
v___x_1298_ = l_Lean_MessageData_ofFormat(v___x_1297_);
return v___x_1298_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__4);
v___x_1300_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__2));
v___x_1301_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
lean_ctor_set(v___x_1301_, 1, v___x_1299_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg(lean_object* v_ref_1302_){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1304_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___closed__5);
v___x_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1305_, 0, v_ref_1302_);
lean_ctor_set(v___x_1305_, 1, v___x_1304_);
v___x_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg___boxed(lean_object* v_ref_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg(v_ref_1307_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3(lean_object* v_00_u03b1_1310_, lean_object* v_ref_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg(v_ref_1311_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___boxed(lean_object* v_00_u03b1_1318_, lean_object* v_ref_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3(v_00_u03b1_1318_, v_ref_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(lean_object* v_a_1326_, lean_object* v_____r_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1333_ = lean_unsigned_to_nat(1u);
v___x_1334_ = lean_mk_empty_array_with_capacity(v___x_1333_);
v___x_1335_ = lean_array_push(v___x_1334_, v_a_1326_);
v___x_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0___boxed(lean_object* v_a_1337_, lean_object* v_____r_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1337_, v_____r_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
return v_res_1344_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1345_; double v___x_1346_; 
v___x_1345_ = lean_unsigned_to_nat(0u);
v___x_1346_ = lean_float_of_nat(v___x_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(lean_object* v_cls_1350_, lean_object* v_msg_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v_ref_1357_; lean_object* v___x_1358_; lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1403_; 
v_ref_1357_ = lean_ctor_get(v___y_1354_, 5);
v___x_1358_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2(v_msg_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1361_ = v___x_1358_;
v_isShared_1362_ = v_isSharedCheck_1403_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1358_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1403_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; lean_object* v_traceState_1364_; lean_object* v_env_1365_; lean_object* v_nextMacroScope_1366_; lean_object* v_ngen_1367_; lean_object* v_auxDeclNGen_1368_; lean_object* v_cache_1369_; lean_object* v_messages_1370_; lean_object* v_infoState_1371_; lean_object* v_snapshotTasks_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1402_; 
v___x_1363_ = lean_st_ref_take(v___y_1355_);
v_traceState_1364_ = lean_ctor_get(v___x_1363_, 4);
v_env_1365_ = lean_ctor_get(v___x_1363_, 0);
v_nextMacroScope_1366_ = lean_ctor_get(v___x_1363_, 1);
v_ngen_1367_ = lean_ctor_get(v___x_1363_, 2);
v_auxDeclNGen_1368_ = lean_ctor_get(v___x_1363_, 3);
v_cache_1369_ = lean_ctor_get(v___x_1363_, 5);
v_messages_1370_ = lean_ctor_get(v___x_1363_, 6);
v_infoState_1371_ = lean_ctor_get(v___x_1363_, 7);
v_snapshotTasks_1372_ = lean_ctor_get(v___x_1363_, 8);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1374_ = v___x_1363_;
v_isShared_1375_ = v_isSharedCheck_1402_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_snapshotTasks_1372_);
lean_inc(v_infoState_1371_);
lean_inc(v_messages_1370_);
lean_inc(v_cache_1369_);
lean_inc(v_traceState_1364_);
lean_inc(v_auxDeclNGen_1368_);
lean_inc(v_ngen_1367_);
lean_inc(v_nextMacroScope_1366_);
lean_inc(v_env_1365_);
lean_dec(v___x_1363_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1402_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
uint64_t v_tid_1376_; lean_object* v_traces_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1401_; 
v_tid_1376_ = lean_ctor_get_uint64(v_traceState_1364_, sizeof(void*)*1);
v_traces_1377_ = lean_ctor_get(v_traceState_1364_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_traceState_1364_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1379_ = v_traceState_1364_;
v_isShared_1380_ = v_isSharedCheck_1401_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_traces_1377_);
lean_dec(v_traceState_1364_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1401_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; double v___x_1382_; uint8_t v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
v___x_1381_ = lean_box(0);
v___x_1382_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___closed__0);
v___x_1383_ = 0;
v___x_1384_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___closed__1));
v___x_1385_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1385_, 0, v_cls_1350_);
lean_ctor_set(v___x_1385_, 1, v___x_1381_);
lean_ctor_set(v___x_1385_, 2, v___x_1384_);
lean_ctor_set_float(v___x_1385_, sizeof(void*)*3, v___x_1382_);
lean_ctor_set_float(v___x_1385_, sizeof(void*)*3 + 8, v___x_1382_);
lean_ctor_set_uint8(v___x_1385_, sizeof(void*)*3 + 16, v___x_1383_);
v___x_1386_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___closed__2));
v___x_1387_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1385_);
lean_ctor_set(v___x_1387_, 1, v_a_1359_);
lean_ctor_set(v___x_1387_, 2, v___x_1386_);
lean_inc(v_ref_1357_);
v___x_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1388_, 0, v_ref_1357_);
lean_ctor_set(v___x_1388_, 1, v___x_1387_);
v___x_1389_ = l_Lean_PersistentArray_push___redArg(v_traces_1377_, v___x_1388_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v___x_1389_);
v___x_1391_ = v___x_1379_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1389_);
lean_ctor_set_uint64(v_reuseFailAlloc_1400_, sizeof(void*)*1, v_tid_1376_);
v___x_1391_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
lean_object* v___x_1393_; 
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 4, v___x_1391_);
v___x_1393_ = v___x_1374_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_env_1365_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_nextMacroScope_1366_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v_ngen_1367_);
lean_ctor_set(v_reuseFailAlloc_1399_, 3, v_auxDeclNGen_1368_);
lean_ctor_set(v_reuseFailAlloc_1399_, 4, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1399_, 5, v_cache_1369_);
lean_ctor_set(v_reuseFailAlloc_1399_, 6, v_messages_1370_);
lean_ctor_set(v_reuseFailAlloc_1399_, 7, v_infoState_1371_);
lean_ctor_set(v_reuseFailAlloc_1399_, 8, v_snapshotTasks_1372_);
v___x_1393_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1394_ = lean_st_ref_set(v___y_1355_, v___x_1393_);
v___x_1395_ = lean_box(0);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v___x_1395_);
v___x_1397_ = v___x_1361_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___boxed(lean_object* v_cls_1404_, lean_object* v_msg_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(v_cls_1404_, v_msg_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
return v_res_1411_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__0));
v___x_1414_ = l_Lean_stringToMessageData(v___x_1413_);
return v___x_1414_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3(void){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__2));
v___x_1417_ = l_Lean_stringToMessageData(v___x_1416_);
return v___x_1417_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5(void){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__4));
v___x_1420_ = l_Lean_stringToMessageData(v___x_1419_);
return v___x_1420_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7(void){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__6));
v___x_1423_ = l_Lean_stringToMessageData(v___x_1422_);
return v___x_1423_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__15(void){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14));
v___x_1436_ = l_Lean_stringToMessageData(v___x_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(lean_object* v_matchDeclName_1437_, lean_object* v_mvarId_1438_, lean_object* v_depth_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_){
_start:
{
lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v_a_1450_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; uint8_t v___y_1487_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; uint8_t v___y_1512_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v_a_1536_; uint8_t v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; uint8_t v___y_1548_; lean_object* v___y_1583_; uint8_t v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v_a_1590_; uint8_t v___y_1594_; lean_object* v___y_1595_; lean_object* v___y_1596_; lean_object* v___y_1597_; lean_object* v___y_1598_; lean_object* v___y_1599_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1605_; lean_object* v___y_1606_; uint8_t v___y_1607_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; uint8_t v___y_1613_; uint8_t v___y_1637_; lean_object* v___y_1638_; lean_object* v___y_1639_; lean_object* v___y_1640_; lean_object* v___y_1641_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; uint8_t v___y_1645_; uint8_t v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; uint8_t v___y_1670_; lean_object* v___y_1687_; uint8_t v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; uint8_t v___y_1695_; uint8_t v___y_1713_; lean_object* v___y_1714_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; uint8_t v___y_1721_; uint8_t v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; uint8_t v___y_1750_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v_fileName_1801_; lean_object* v_fileMap_1802_; lean_object* v_options_1803_; lean_object* v_currRecDepth_1804_; lean_object* v_maxRecDepth_1805_; lean_object* v_ref_1806_; lean_object* v_currNamespace_1807_; lean_object* v_openDecls_1808_; lean_object* v_initHeartbeats_1809_; lean_object* v_maxHeartbeats_1810_; lean_object* v_quotContext_1811_; lean_object* v_currMacroScope_1812_; uint8_t v_diag_1813_; lean_object* v_cancelTk_x3f_1814_; uint8_t v_suppressElabErrors_1815_; lean_object* v_inheritedTraceOptions_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1843_; 
v_fileName_1801_ = lean_ctor_get(v_a_1442_, 0);
v_fileMap_1802_ = lean_ctor_get(v_a_1442_, 1);
v_options_1803_ = lean_ctor_get(v_a_1442_, 2);
v_currRecDepth_1804_ = lean_ctor_get(v_a_1442_, 3);
v_maxRecDepth_1805_ = lean_ctor_get(v_a_1442_, 4);
v_ref_1806_ = lean_ctor_get(v_a_1442_, 5);
v_currNamespace_1807_ = lean_ctor_get(v_a_1442_, 6);
v_openDecls_1808_ = lean_ctor_get(v_a_1442_, 7);
v_initHeartbeats_1809_ = lean_ctor_get(v_a_1442_, 8);
v_maxHeartbeats_1810_ = lean_ctor_get(v_a_1442_, 9);
v_quotContext_1811_ = lean_ctor_get(v_a_1442_, 10);
v_currMacroScope_1812_ = lean_ctor_get(v_a_1442_, 11);
v_diag_1813_ = lean_ctor_get_uint8(v_a_1442_, sizeof(void*)*14);
v_cancelTk_x3f_1814_ = lean_ctor_get(v_a_1442_, 12);
v_suppressElabErrors_1815_ = lean_ctor_get_uint8(v_a_1442_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1816_ = lean_ctor_get(v_a_1442_, 13);
v_isSharedCheck_1843_ = !lean_is_exclusive(v_a_1442_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1818_ = v_a_1442_;
v_isShared_1819_ = v_isSharedCheck_1843_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_inheritedTraceOptions_1816_);
lean_inc(v_cancelTk_x3f_1814_);
lean_inc(v_currMacroScope_1812_);
lean_inc(v_quotContext_1811_);
lean_inc(v_maxHeartbeats_1810_);
lean_inc(v_initHeartbeats_1809_);
lean_inc(v_openDecls_1808_);
lean_inc(v_currNamespace_1807_);
lean_inc(v_ref_1806_);
lean_inc(v_maxRecDepth_1805_);
lean_inc(v_currRecDepth_1804_);
lean_inc(v_options_1803_);
lean_inc(v_fileMap_1802_);
lean_inc(v_fileName_1801_);
lean_dec(v_a_1442_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1843_;
goto v_resetjp_1817_;
}
v___jp_1445_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
v___x_1451_ = lean_unsigned_to_nat(0u);
v___x_1452_ = lean_array_get_size(v_a_1450_);
v___x_1453_ = lean_box(0);
v___x_1454_ = lean_nat_dec_lt(v___x_1451_, v___x_1452_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; 
lean_dec_ref(v_a_1450_);
lean_dec_ref(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec(v_matchDeclName_1437_);
v___x_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1453_);
return v___x_1455_;
}
else
{
uint8_t v___x_1456_; 
v___x_1456_ = lean_nat_dec_le(v___x_1452_, v___x_1452_);
if (v___x_1456_ == 0)
{
if (v___x_1454_ == 0)
{
lean_object* v___x_1457_; 
lean_dec_ref(v_a_1450_);
lean_dec_ref(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec(v_matchDeclName_1437_);
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1453_);
return v___x_1457_;
}
else
{
size_t v___x_1458_; size_t v___x_1459_; lean_object* v___x_1460_; 
v___x_1458_ = ((size_t)0ULL);
v___x_1459_ = lean_usize_of_nat(v___x_1452_);
v___x_1460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1439_, v_matchDeclName_1437_, v_a_1450_, v___x_1458_, v___x_1459_, v___x_1453_, v___y_1449_, v___y_1446_, v___y_1448_, v___y_1447_);
lean_dec_ref(v_a_1450_);
return v___x_1460_;
}
}
else
{
size_t v___x_1461_; size_t v___x_1462_; lean_object* v___x_1463_; 
v___x_1461_ = ((size_t)0ULL);
v___x_1462_ = lean_usize_of_nat(v___x_1452_);
v___x_1463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1439_, v_matchDeclName_1437_, v_a_1450_, v___x_1461_, v___x_1462_, v___x_1453_, v___y_1449_, v___y_1446_, v___y_1448_, v___y_1447_);
lean_dec_ref(v_a_1450_);
return v___x_1463_;
}
}
}
v___jp_1464_:
{
if (lean_obj_tag(v___y_1469_) == 0)
{
lean_object* v_a_1470_; 
v_a_1470_ = lean_ctor_get(v___y_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref(v___y_1469_);
v___y_1446_ = v___y_1465_;
v___y_1447_ = v___y_1467_;
v___y_1448_ = v___y_1466_;
v___y_1449_ = v___y_1468_;
v_a_1450_ = v_a_1470_;
goto v___jp_1445_;
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec(v_matchDeclName_1437_);
v_a_1471_ = lean_ctor_get(v___y_1469_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___y_1469_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___y_1469_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___y_1469_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
v___jp_1479_:
{
if (v___y_1487_ == 0)
{
lean_object* v___x_1488_; 
lean_dec_ref(v___y_1481_);
v___x_1488_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1482_, v___y_1480_, v___y_1485_);
lean_dec_ref(v___y_1482_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1502_; 
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1502_ == 0)
{
lean_object* v_unused_1503_; 
v_unused_1503_ = lean_ctor_get(v___x_1488_, 0);
lean_dec(v_unused_1503_);
v___x_1490_ = v___x_1488_;
v_isShared_1491_ = v_isSharedCheck_1502_;
goto v_resetjp_1489_;
}
else
{
lean_dec(v___x_1488_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1502_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1498_; 
v___x_1492_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1);
lean_inc(v_matchDeclName_1437_);
v___x_1493_ = l_Lean_MessageData_ofName(v_matchDeclName_1437_);
v___x_1494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1492_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
v___x_1495_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3);
v___x_1496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1494_);
lean_ctor_set(v___x_1496_, 1, v___x_1495_);
if (v_isShared_1491_ == 0)
{
lean_ctor_set_tag(v___x_1490_, 1);
lean_ctor_set(v___x_1490_, 0, v___y_1483_);
v___x_1498_ = v___x_1490_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___y_1483_);
v___x_1498_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1496_);
lean_ctor_set(v___x_1499_, 1, v___x_1498_);
v___x_1500_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1499_, v___y_1486_, v___y_1480_, v___y_1484_, v___y_1485_);
v___y_1465_ = v___y_1480_;
v___y_1466_ = v___y_1484_;
v___y_1467_ = v___y_1485_;
v___y_1468_ = v___y_1486_;
v___y_1469_ = v___x_1500_;
goto v___jp_1464_;
}
}
}
else
{
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec(v___y_1480_);
lean_dec(v_matchDeclName_1437_);
return v___x_1488_;
}
}
else
{
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
v___y_1465_ = v___y_1480_;
v___y_1466_ = v___y_1484_;
v___y_1467_ = v___y_1485_;
v___y_1468_ = v___y_1486_;
v___y_1469_ = v___y_1481_;
goto v___jp_1464_;
}
}
v___jp_1504_:
{
if (v___y_1512_ == 0)
{
lean_object* v___x_1513_; 
lean_dec_ref(v___y_1507_);
v___x_1513_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1505_, v___y_1506_, v___y_1510_);
lean_dec_ref(v___y_1505_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v___x_1514_; 
lean_dec_ref(v___x_1513_);
v___x_1514_ = l_Lean_Meta_saveState___redArg(v___y_1506_, v___y_1510_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1516_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref(v___x_1514_);
lean_inc(v___y_1510_);
lean_inc_ref(v___y_1509_);
lean_inc(v___y_1506_);
lean_inc_ref(v___y_1511_);
lean_inc(v___y_1508_);
v___x_1516_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(v___y_1508_, v___y_1511_, v___y_1506_, v___y_1509_, v___y_1510_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_dec(v_a_1515_);
lean_dec(v___y_1508_);
v___y_1465_ = v___y_1506_;
v___y_1466_ = v___y_1509_;
v___y_1467_ = v___y_1510_;
v___y_1468_ = v___y_1511_;
v___y_1469_ = v___x_1516_;
goto v___jp_1464_;
}
else
{
lean_object* v_a_1517_; uint8_t v___x_1518_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
v___x_1518_ = l_Lean_Exception_isInterrupt(v_a_1517_);
if (v___x_1518_ == 0)
{
uint8_t v___x_1519_; 
v___x_1519_ = l_Lean_Exception_isRuntime(v_a_1517_);
v___y_1480_ = v___y_1506_;
v___y_1481_ = v___x_1516_;
v___y_1482_ = v_a_1515_;
v___y_1483_ = v___y_1508_;
v___y_1484_ = v___y_1509_;
v___y_1485_ = v___y_1510_;
v___y_1486_ = v___y_1511_;
v___y_1487_ = v___x_1519_;
goto v___jp_1479_;
}
else
{
lean_dec(v_a_1517_);
v___y_1480_ = v___y_1506_;
v___y_1481_ = v___x_1516_;
v___y_1482_ = v_a_1515_;
v___y_1483_ = v___y_1508_;
v___y_1484_ = v___y_1509_;
v___y_1485_ = v___y_1510_;
v___y_1486_ = v___y_1511_;
v___y_1487_ = v___x_1518_;
goto v___jp_1479_;
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec(v___y_1506_);
lean_dec(v_matchDeclName_1437_);
v_a_1520_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1514_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1514_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
else
{
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec(v___y_1506_);
lean_dec(v_matchDeclName_1437_);
return v___x_1513_;
}
}
else
{
lean_object* v___x_1528_; 
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v_matchDeclName_1437_);
v___x_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1528_, 0, v___y_1507_);
return v___x_1528_;
}
}
v___jp_1529_:
{
uint8_t v___x_1537_; 
v___x_1537_ = l_Lean_Exception_isInterrupt(v_a_1536_);
if (v___x_1537_ == 0)
{
uint8_t v___x_1538_; 
lean_inc_ref(v_a_1536_);
v___x_1538_ = l_Lean_Exception_isRuntime(v_a_1536_);
v___y_1505_ = v___y_1530_;
v___y_1506_ = v___y_1531_;
v___y_1507_ = v_a_1536_;
v___y_1508_ = v___y_1532_;
v___y_1509_ = v___y_1534_;
v___y_1510_ = v___y_1533_;
v___y_1511_ = v___y_1535_;
v___y_1512_ = v___x_1538_;
goto v___jp_1504_;
}
else
{
v___y_1505_ = v___y_1530_;
v___y_1506_ = v___y_1531_;
v___y_1507_ = v_a_1536_;
v___y_1508_ = v___y_1532_;
v___y_1509_ = v___y_1534_;
v___y_1510_ = v___y_1533_;
v___y_1511_ = v___y_1535_;
v___y_1512_ = v___x_1537_;
goto v___jp_1504_;
}
}
v___jp_1539_:
{
if (v___y_1548_ == 0)
{
lean_object* v___x_1549_; 
lean_dec_ref(v___y_1542_);
v___x_1549_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1544_, v___y_1541_, v___y_1546_);
lean_dec_ref(v___y_1544_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v___x_1550_; 
lean_dec_ref(v___x_1549_);
v___x_1550_ = l_Lean_Meta_saveState___redArg(v___y_1541_, v___y_1546_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref(v___x_1550_);
v___x_1552_ = lean_box(0);
lean_inc(v___y_1546_);
lean_inc_ref(v___y_1545_);
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1547_);
lean_inc(v___y_1543_);
v___x_1553_ = l_Lean_Meta_splitIfTarget_x3f(v___y_1543_, v___x_1552_, v___y_1540_, v___y_1547_, v___y_1541_, v___y_1545_, v___y_1546_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref(v___x_1553_);
if (lean_obj_tag(v_a_1554_) == 1)
{
lean_object* v_val_1555_; lean_object* v_fst_1556_; lean_object* v_snd_1557_; lean_object* v_mvarId_1558_; lean_object* v_fvarId_1559_; lean_object* v___x_1560_; 
v_val_1555_ = lean_ctor_get(v_a_1554_, 0);
lean_inc(v_val_1555_);
lean_dec_ref(v_a_1554_);
v_fst_1556_ = lean_ctor_get(v_val_1555_, 0);
lean_inc(v_fst_1556_);
v_snd_1557_ = lean_ctor_get(v_val_1555_, 1);
lean_inc(v_snd_1557_);
lean_dec(v_val_1555_);
v_mvarId_1558_ = lean_ctor_get(v_fst_1556_, 0);
lean_inc(v_mvarId_1558_);
v_fvarId_1559_ = lean_ctor_get(v_fst_1556_, 1);
lean_inc(v_fvarId_1559_);
lean_dec(v_fst_1556_);
lean_inc(v___y_1546_);
lean_inc_ref(v___y_1545_);
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1547_);
v___x_1560_ = l_Lean_Meta_trySubst(v_mvarId_1558_, v_fvarId_1559_, v___y_1547_, v___y_1541_, v___y_1545_, v___y_1546_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v_mvarId_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
lean_dec(v_a_1551_);
lean_dec(v___y_1543_);
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref(v___x_1560_);
v_mvarId_1562_ = lean_ctor_get(v_snd_1557_, 0);
lean_inc(v_mvarId_1562_);
lean_dec(v_snd_1557_);
v___x_1563_ = lean_unsigned_to_nat(2u);
v___x_1564_ = lean_mk_empty_array_with_capacity(v___x_1563_);
v___x_1565_ = lean_array_push(v___x_1564_, v_a_1561_);
v___x_1566_ = lean_array_push(v___x_1565_, v_mvarId_1562_);
v___y_1446_ = v___y_1541_;
v___y_1447_ = v___y_1546_;
v___y_1448_ = v___y_1545_;
v___y_1449_ = v___y_1547_;
v_a_1450_ = v___x_1566_;
goto v___jp_1445_;
}
else
{
lean_object* v_a_1567_; 
lean_dec(v_snd_1557_);
v_a_1567_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1567_);
lean_dec_ref(v___x_1560_);
v___y_1530_ = v_a_1551_;
v___y_1531_ = v___y_1541_;
v___y_1532_ = v___y_1543_;
v___y_1533_ = v___y_1546_;
v___y_1534_ = v___y_1545_;
v___y_1535_ = v___y_1547_;
v_a_1536_ = v_a_1567_;
goto v___jp_1529_;
}
}
else
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
lean_dec(v_a_1554_);
v___x_1568_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5);
v___x_1569_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1568_, v___y_1547_, v___y_1541_, v___y_1545_, v___y_1546_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; 
lean_dec(v_a_1551_);
lean_dec(v___y_1543_);
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref(v___x_1569_);
v___y_1446_ = v___y_1541_;
v___y_1447_ = v___y_1546_;
v___y_1448_ = v___y_1545_;
v___y_1449_ = v___y_1547_;
v_a_1450_ = v_a_1570_;
goto v___jp_1445_;
}
else
{
lean_object* v_a_1571_; 
v_a_1571_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1571_);
lean_dec_ref(v___x_1569_);
v___y_1530_ = v_a_1551_;
v___y_1531_ = v___y_1541_;
v___y_1532_ = v___y_1543_;
v___y_1533_ = v___y_1546_;
v___y_1534_ = v___y_1545_;
v___y_1535_ = v___y_1547_;
v_a_1536_ = v_a_1571_;
goto v___jp_1529_;
}
}
}
else
{
lean_object* v_a_1572_; 
v_a_1572_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1572_);
lean_dec_ref(v___x_1553_);
v___y_1530_ = v_a_1551_;
v___y_1531_ = v___y_1541_;
v___y_1532_ = v___y_1543_;
v___y_1533_ = v___y_1546_;
v___y_1534_ = v___y_1545_;
v___y_1535_ = v___y_1547_;
v_a_1536_ = v_a_1572_;
goto v___jp_1529_;
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec_ref(v___y_1547_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec(v___y_1543_);
lean_dec(v___y_1541_);
lean_dec(v_matchDeclName_1437_);
v_a_1573_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1550_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1550_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
else
{
lean_dec_ref(v___y_1547_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec(v___y_1543_);
lean_dec(v___y_1541_);
lean_dec(v_matchDeclName_1437_);
return v___x_1549_;
}
}
else
{
lean_object* v___x_1581_; 
lean_dec_ref(v___y_1547_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec(v___y_1541_);
lean_dec(v_matchDeclName_1437_);
v___x_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1581_, 0, v___y_1542_);
return v___x_1581_;
}
}
v___jp_1582_:
{
uint8_t v___x_1591_; 
v___x_1591_ = l_Lean_Exception_isInterrupt(v_a_1590_);
if (v___x_1591_ == 0)
{
uint8_t v___x_1592_; 
lean_inc_ref(v_a_1590_);
v___x_1592_ = l_Lean_Exception_isRuntime(v_a_1590_);
v___y_1540_ = v___y_1584_;
v___y_1541_ = v___y_1583_;
v___y_1542_ = v_a_1590_;
v___y_1543_ = v___y_1585_;
v___y_1544_ = v___y_1586_;
v___y_1545_ = v___y_1588_;
v___y_1546_ = v___y_1587_;
v___y_1547_ = v___y_1589_;
v___y_1548_ = v___x_1592_;
goto v___jp_1539_;
}
else
{
v___y_1540_ = v___y_1584_;
v___y_1541_ = v___y_1583_;
v___y_1542_ = v_a_1590_;
v___y_1543_ = v___y_1585_;
v___y_1544_ = v___y_1586_;
v___y_1545_ = v___y_1588_;
v___y_1546_ = v___y_1587_;
v___y_1547_ = v___y_1589_;
v___y_1548_ = v___x_1591_;
goto v___jp_1539_;
}
}
v___jp_1593_:
{
if (lean_obj_tag(v___y_1601_) == 0)
{
lean_object* v_a_1602_; 
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
v_a_1602_ = lean_ctor_get(v___y_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref(v___y_1601_);
v___y_1446_ = v___y_1595_;
v___y_1447_ = v___y_1599_;
v___y_1448_ = v___y_1598_;
v___y_1449_ = v___y_1600_;
v_a_1450_ = v_a_1602_;
goto v___jp_1445_;
}
else
{
lean_object* v_a_1603_; 
v_a_1603_ = lean_ctor_get(v___y_1601_, 0);
lean_inc(v_a_1603_);
lean_dec_ref(v___y_1601_);
v___y_1583_ = v___y_1595_;
v___y_1584_ = v___y_1594_;
v___y_1585_ = v___y_1596_;
v___y_1586_ = v___y_1597_;
v___y_1587_ = v___y_1599_;
v___y_1588_ = v___y_1598_;
v___y_1589_ = v___y_1600_;
v_a_1590_ = v_a_1603_;
goto v___jp_1582_;
}
}
v___jp_1604_:
{
if (v___y_1613_ == 0)
{
lean_object* v___x_1614_; 
lean_dec_ref(v___y_1605_);
v___x_1614_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1606_, v___y_1608_, v___y_1611_);
lean_dec_ref(v___y_1606_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v___x_1615_; 
lean_dec_ref(v___x_1614_);
v___x_1615_ = l_Lean_Meta_saveState___redArg(v___y_1608_, v___y_1611_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1617_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_a_1616_);
lean_dec_ref(v___x_1615_);
lean_inc(v___y_1611_);
lean_inc_ref(v___y_1610_);
lean_inc(v___y_1608_);
lean_inc_ref(v___y_1612_);
lean_inc(v___y_1609_);
v___x_1617_ = l_Lean_Meta_simpIfTarget(v___y_1609_, v___y_1607_, v___y_1607_, v___y_1612_, v___y_1608_, v___y_1610_, v___y_1611_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; uint8_t v___x_1619_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1618_);
lean_dec_ref(v___x_1617_);
v___x_1619_ = l_Lean_instBEqMVarId_beq(v_a_1618_, v___y_1609_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = lean_box(0);
v___x_1621_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1618_, v___x_1620_, v___y_1612_, v___y_1608_, v___y_1610_, v___y_1611_);
v___y_1594_ = v___y_1607_;
v___y_1595_ = v___y_1608_;
v___y_1596_ = v___y_1609_;
v___y_1597_ = v_a_1616_;
v___y_1598_ = v___y_1610_;
v___y_1599_ = v___y_1611_;
v___y_1600_ = v___y_1612_;
v___y_1601_ = v___x_1621_;
goto v___jp_1593_;
}
else
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7);
v___x_1623_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1622_, v___y_1612_, v___y_1608_, v___y_1610_, v___y_1611_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1625_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1624_);
lean_dec_ref(v___x_1623_);
v___x_1625_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1618_, v_a_1624_, v___y_1612_, v___y_1608_, v___y_1610_, v___y_1611_);
v___y_1594_ = v___y_1607_;
v___y_1595_ = v___y_1608_;
v___y_1596_ = v___y_1609_;
v___y_1597_ = v_a_1616_;
v___y_1598_ = v___y_1610_;
v___y_1599_ = v___y_1611_;
v___y_1600_ = v___y_1612_;
v___y_1601_ = v___x_1625_;
goto v___jp_1593_;
}
else
{
lean_object* v_a_1626_; 
lean_dec(v_a_1618_);
v_a_1626_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1626_);
lean_dec_ref(v___x_1623_);
v___y_1583_ = v___y_1608_;
v___y_1584_ = v___y_1607_;
v___y_1585_ = v___y_1609_;
v___y_1586_ = v_a_1616_;
v___y_1587_ = v___y_1611_;
v___y_1588_ = v___y_1610_;
v___y_1589_ = v___y_1612_;
v_a_1590_ = v_a_1626_;
goto v___jp_1582_;
}
}
}
else
{
lean_object* v_a_1627_; 
v_a_1627_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1627_);
lean_dec_ref(v___x_1617_);
v___y_1583_ = v___y_1608_;
v___y_1584_ = v___y_1607_;
v___y_1585_ = v___y_1609_;
v___y_1586_ = v_a_1616_;
v___y_1587_ = v___y_1611_;
v___y_1588_ = v___y_1610_;
v___y_1589_ = v___y_1612_;
v_a_1590_ = v_a_1627_;
goto v___jp_1582_;
}
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
lean_dec_ref(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec(v_matchDeclName_1437_);
v_a_1628_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1615_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1615_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
else
{
lean_dec_ref(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec(v_matchDeclName_1437_);
return v___x_1614_;
}
}
else
{
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1606_);
v___y_1465_ = v___y_1608_;
v___y_1466_ = v___y_1610_;
v___y_1467_ = v___y_1611_;
v___y_1468_ = v___y_1612_;
v___y_1469_ = v___y_1605_;
goto v___jp_1464_;
}
}
v___jp_1636_:
{
if (v___y_1645_ == 0)
{
lean_object* v___x_1646_; 
lean_dec_ref(v___y_1640_);
v___x_1646_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1644_, v___y_1638_, v___y_1642_);
lean_dec_ref(v___y_1644_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v___x_1647_; 
lean_dec_ref(v___x_1646_);
v___x_1647_ = l_Lean_Meta_saveState___redArg(v___y_1638_, v___y_1642_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; lean_object* v___x_1649_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref(v___x_1647_);
lean_inc(v___y_1642_);
lean_inc_ref(v___y_1641_);
lean_inc(v___y_1638_);
lean_inc_ref(v___y_1643_);
lean_inc(v___y_1639_);
v___x_1649_ = l_Lean_Meta_splitSparseCasesOn(v___y_1639_, v___y_1643_, v___y_1638_, v___y_1641_, v___y_1642_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_dec(v_a_1648_);
lean_dec(v___y_1639_);
v___y_1465_ = v___y_1638_;
v___y_1466_ = v___y_1641_;
v___y_1467_ = v___y_1642_;
v___y_1468_ = v___y_1643_;
v___y_1469_ = v___x_1649_;
goto v___jp_1464_;
}
else
{
lean_object* v_a_1650_; uint8_t v___x_1651_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_a_1650_);
v___x_1651_ = l_Lean_Exception_isInterrupt(v_a_1650_);
if (v___x_1651_ == 0)
{
uint8_t v___x_1652_; 
v___x_1652_ = l_Lean_Exception_isRuntime(v_a_1650_);
v___y_1605_ = v___x_1649_;
v___y_1606_ = v_a_1648_;
v___y_1607_ = v___y_1637_;
v___y_1608_ = v___y_1638_;
v___y_1609_ = v___y_1639_;
v___y_1610_ = v___y_1641_;
v___y_1611_ = v___y_1642_;
v___y_1612_ = v___y_1643_;
v___y_1613_ = v___x_1652_;
goto v___jp_1604_;
}
else
{
lean_dec(v_a_1650_);
v___y_1605_ = v___x_1649_;
v___y_1606_ = v_a_1648_;
v___y_1607_ = v___y_1637_;
v___y_1608_ = v___y_1638_;
v___y_1609_ = v___y_1639_;
v___y_1610_ = v___y_1641_;
v___y_1611_ = v___y_1642_;
v___y_1612_ = v___y_1643_;
v___y_1613_ = v___x_1651_;
goto v___jp_1604_;
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1660_; 
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec(v_matchDeclName_1437_);
v_a_1653_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1655_ = v___x_1647_;
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1647_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1660_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
else
{
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec(v_matchDeclName_1437_);
return v___x_1646_;
}
}
else
{
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1639_);
v___y_1465_ = v___y_1638_;
v___y_1466_ = v___y_1641_;
v___y_1467_ = v___y_1642_;
v___y_1468_ = v___y_1643_;
v___y_1469_ = v___y_1640_;
goto v___jp_1464_;
}
}
v___jp_1661_:
{
if (v___y_1670_ == 0)
{
lean_object* v___x_1671_; 
lean_dec_ref(v___y_1667_);
v___x_1671_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1669_, v___y_1663_, v___y_1666_);
lean_dec_ref(v___y_1669_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v___x_1672_; 
lean_dec_ref(v___x_1671_);
v___x_1672_ = l_Lean_Meta_saveState___redArg(v___y_1663_, v___y_1666_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1674_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_a_1673_);
lean_dec_ref(v___x_1672_);
lean_inc(v___y_1666_);
lean_inc_ref(v___y_1665_);
lean_inc(v___y_1663_);
lean_inc_ref(v___y_1668_);
lean_inc(v___y_1664_);
v___x_1674_ = l_Lean_Meta_reduceSparseCasesOn(v___y_1664_, v___y_1668_, v___y_1663_, v___y_1665_, v___y_1666_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_dec(v_a_1673_);
lean_dec(v___y_1664_);
v___y_1465_ = v___y_1663_;
v___y_1466_ = v___y_1665_;
v___y_1467_ = v___y_1666_;
v___y_1468_ = v___y_1668_;
v___y_1469_ = v___x_1674_;
goto v___jp_1464_;
}
else
{
lean_object* v_a_1675_; uint8_t v___x_1676_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_a_1675_);
v___x_1676_ = l_Lean_Exception_isInterrupt(v_a_1675_);
if (v___x_1676_ == 0)
{
uint8_t v___x_1677_; 
v___x_1677_ = l_Lean_Exception_isRuntime(v_a_1675_);
v___y_1637_ = v___y_1662_;
v___y_1638_ = v___y_1663_;
v___y_1639_ = v___y_1664_;
v___y_1640_ = v___x_1674_;
v___y_1641_ = v___y_1665_;
v___y_1642_ = v___y_1666_;
v___y_1643_ = v___y_1668_;
v___y_1644_ = v_a_1673_;
v___y_1645_ = v___x_1677_;
goto v___jp_1636_;
}
else
{
lean_dec(v_a_1675_);
v___y_1637_ = v___y_1662_;
v___y_1638_ = v___y_1663_;
v___y_1639_ = v___y_1664_;
v___y_1640_ = v___x_1674_;
v___y_1641_ = v___y_1665_;
v___y_1642_ = v___y_1666_;
v___y_1643_ = v___y_1668_;
v___y_1644_ = v_a_1673_;
v___y_1645_ = v___x_1676_;
goto v___jp_1636_;
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec(v_matchDeclName_1437_);
v_a_1678_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1672_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1672_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
else
{
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec(v_matchDeclName_1437_);
return v___x_1671_;
}
}
else
{
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1664_);
v___y_1465_ = v___y_1663_;
v___y_1466_ = v___y_1665_;
v___y_1467_ = v___y_1666_;
v___y_1468_ = v___y_1668_;
v___y_1469_ = v___y_1667_;
goto v___jp_1464_;
}
}
v___jp_1686_:
{
if (v___y_1695_ == 0)
{
lean_object* v___x_1696_; 
lean_dec_ref(v___y_1687_);
v___x_1696_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1690_, v___y_1689_, v___y_1693_);
lean_dec_ref(v___y_1690_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v___x_1697_; 
lean_dec_ref(v___x_1696_);
v___x_1697_ = l_Lean_Meta_saveState___redArg(v___y_1689_, v___y_1693_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1699_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc(v_a_1698_);
lean_dec_ref(v___x_1697_);
lean_inc(v___y_1693_);
lean_inc_ref(v___y_1692_);
lean_inc(v___y_1689_);
lean_inc_ref(v___y_1694_);
lean_inc(v___y_1691_);
v___x_1699_ = l_Lean_Meta_casesOnStuckLHS(v___y_1691_, v___y_1694_, v___y_1689_, v___y_1692_, v___y_1693_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_dec(v_a_1698_);
lean_dec(v___y_1691_);
v___y_1465_ = v___y_1689_;
v___y_1466_ = v___y_1692_;
v___y_1467_ = v___y_1693_;
v___y_1468_ = v___y_1694_;
v___y_1469_ = v___x_1699_;
goto v___jp_1464_;
}
else
{
lean_object* v_a_1700_; uint8_t v___x_1701_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_a_1700_);
v___x_1701_ = l_Lean_Exception_isInterrupt(v_a_1700_);
if (v___x_1701_ == 0)
{
uint8_t v___x_1702_; 
v___x_1702_ = l_Lean_Exception_isRuntime(v_a_1700_);
v___y_1662_ = v___y_1688_;
v___y_1663_ = v___y_1689_;
v___y_1664_ = v___y_1691_;
v___y_1665_ = v___y_1692_;
v___y_1666_ = v___y_1693_;
v___y_1667_ = v___x_1699_;
v___y_1668_ = v___y_1694_;
v___y_1669_ = v_a_1698_;
v___y_1670_ = v___x_1702_;
goto v___jp_1661_;
}
else
{
lean_dec(v_a_1700_);
v___y_1662_ = v___y_1688_;
v___y_1663_ = v___y_1689_;
v___y_1664_ = v___y_1691_;
v___y_1665_ = v___y_1692_;
v___y_1666_ = v___y_1693_;
v___y_1667_ = v___x_1699_;
v___y_1668_ = v___y_1694_;
v___y_1669_ = v_a_1698_;
v___y_1670_ = v___x_1701_;
goto v___jp_1661_;
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec(v___y_1689_);
lean_dec(v_matchDeclName_1437_);
v_a_1703_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1697_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1697_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
else
{
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec(v___y_1689_);
lean_dec(v_matchDeclName_1437_);
return v___x_1696_;
}
}
else
{
lean_object* v___x_1711_; 
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec(v_matchDeclName_1437_);
v___x_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1711_, 0, v___y_1687_);
return v___x_1711_;
}
}
v___jp_1712_:
{
if (v___y_1721_ == 0)
{
lean_object* v___x_1722_; 
lean_dec_ref(v___y_1717_);
v___x_1722_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1716_, v___y_1714_, v___y_1719_);
lean_dec_ref(v___y_1716_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v___x_1723_; 
lean_dec_ref(v___x_1722_);
v___x_1723_ = l_Lean_Meta_saveState___redArg(v___y_1714_, v___y_1719_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1725_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1724_);
lean_dec_ref(v___x_1723_);
lean_inc(v___y_1719_);
lean_inc_ref(v___y_1718_);
lean_inc(v___y_1714_);
lean_inc_ref(v___y_1720_);
lean_inc(v___y_1715_);
v___x_1725_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(v___y_1715_, v___y_1720_, v___y_1714_, v___y_1718_, v___y_1719_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
lean_dec(v_a_1724_);
lean_dec(v___y_1715_);
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1726_);
lean_dec_ref(v___x_1725_);
v___x_1727_ = lean_unsigned_to_nat(1u);
v___x_1728_ = lean_mk_empty_array_with_capacity(v___x_1727_);
v___x_1729_ = lean_array_push(v___x_1728_, v_a_1726_);
v___y_1446_ = v___y_1714_;
v___y_1447_ = v___y_1719_;
v___y_1448_ = v___y_1718_;
v___y_1449_ = v___y_1720_;
v_a_1450_ = v___x_1729_;
goto v___jp_1445_;
}
else
{
lean_object* v_a_1730_; uint8_t v___x_1731_; 
v_a_1730_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1730_);
lean_dec_ref(v___x_1725_);
v___x_1731_ = l_Lean_Exception_isInterrupt(v_a_1730_);
if (v___x_1731_ == 0)
{
uint8_t v___x_1732_; 
lean_inc(v_a_1730_);
v___x_1732_ = l_Lean_Exception_isRuntime(v_a_1730_);
v___y_1687_ = v_a_1730_;
v___y_1688_ = v___y_1713_;
v___y_1689_ = v___y_1714_;
v___y_1690_ = v_a_1724_;
v___y_1691_ = v___y_1715_;
v___y_1692_ = v___y_1718_;
v___y_1693_ = v___y_1719_;
v___y_1694_ = v___y_1720_;
v___y_1695_ = v___x_1732_;
goto v___jp_1686_;
}
else
{
v___y_1687_ = v_a_1730_;
v___y_1688_ = v___y_1713_;
v___y_1689_ = v___y_1714_;
v___y_1690_ = v_a_1724_;
v___y_1691_ = v___y_1715_;
v___y_1692_ = v___y_1718_;
v___y_1693_ = v___y_1719_;
v___y_1694_ = v___y_1720_;
v___y_1695_ = v___x_1731_;
goto v___jp_1686_;
}
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec(v_matchDeclName_1437_);
v_a_1733_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1723_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1723_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
else
{
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec(v_matchDeclName_1437_);
return v___x_1722_;
}
}
else
{
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec_ref(v___y_1716_);
lean_dec(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec(v_matchDeclName_1437_);
return v___y_1717_;
}
}
v___jp_1741_:
{
if (v___y_1750_ == 0)
{
lean_object* v___x_1751_; 
lean_dec_ref(v___y_1745_);
v___x_1751_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1744_, v___y_1743_, v___y_1748_);
lean_dec_ref(v___y_1744_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_dec_ref(v___x_1751_);
v___x_1752_ = lean_unsigned_to_nat(16u);
v___x_1753_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*1, v___y_1742_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*1 + 1, v___y_1742_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*1 + 2, v___y_1742_);
v___x_1754_ = l_Lean_Meta_saveState___redArg(v___y_1743_, v___y_1748_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1756_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref(v___x_1754_);
lean_inc(v___y_1748_);
lean_inc_ref(v___y_1747_);
lean_inc(v___y_1743_);
lean_inc_ref(v___y_1749_);
lean_inc(v___y_1746_);
v___x_1756_ = l_Lean_MVarId_contradiction(v___y_1746_, v___x_1753_, v___y_1749_, v___y_1743_, v___y_1747_, v___y_1748_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v___x_1757_; 
lean_dec_ref(v___x_1756_);
lean_dec(v_a_1755_);
lean_dec(v___y_1746_);
v___x_1757_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___y_1446_ = v___y_1743_;
v___y_1447_ = v___y_1748_;
v___y_1448_ = v___y_1747_;
v___y_1449_ = v___y_1749_;
v_a_1450_ = v___x_1757_;
goto v___jp_1445_;
}
else
{
lean_object* v_a_1758_; uint8_t v___x_1759_; 
v_a_1758_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_a_1758_);
v___x_1759_ = l_Lean_Exception_isInterrupt(v_a_1758_);
if (v___x_1759_ == 0)
{
uint8_t v___x_1760_; 
v___x_1760_ = l_Lean_Exception_isRuntime(v_a_1758_);
v___y_1713_ = v___y_1742_;
v___y_1714_ = v___y_1743_;
v___y_1715_ = v___y_1746_;
v___y_1716_ = v_a_1755_;
v___y_1717_ = v___x_1756_;
v___y_1718_ = v___y_1747_;
v___y_1719_ = v___y_1748_;
v___y_1720_ = v___y_1749_;
v___y_1721_ = v___x_1760_;
goto v___jp_1712_;
}
else
{
lean_dec(v_a_1758_);
v___y_1713_ = v___y_1742_;
v___y_1714_ = v___y_1743_;
v___y_1715_ = v___y_1746_;
v___y_1716_ = v_a_1755_;
v___y_1717_ = v___x_1756_;
v___y_1718_ = v___y_1747_;
v___y_1719_ = v___y_1748_;
v___y_1720_ = v___y_1749_;
v___y_1721_ = v___x_1759_;
goto v___jp_1712_;
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec_ref(v___x_1753_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec(v___y_1743_);
lean_dec(v_matchDeclName_1437_);
v_a_1761_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1754_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1754_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
else
{
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec(v___y_1743_);
lean_dec(v_matchDeclName_1437_);
return v___x_1751_;
}
}
else
{
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec(v_matchDeclName_1437_);
return v___y_1745_;
}
}
v___jp_1769_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__9));
lean_inc(v___y_1773_);
lean_inc_ref(v___y_1772_);
lean_inc(v___y_1771_);
lean_inc_ref(v___y_1770_);
v___x_1775_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_1438_, v___x_1774_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1777_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1776_);
lean_dec_ref(v___x_1775_);
v___x_1777_ = l_Lean_Meta_saveState___redArg(v___y_1771_, v___y_1773_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; uint8_t v___x_1779_; lean_object* v___x_1780_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_a_1778_);
lean_dec_ref(v___x_1777_);
v___x_1779_ = 1;
lean_inc(v___y_1773_);
lean_inc_ref(v___y_1772_);
lean_inc(v___y_1771_);
lean_inc_ref(v___y_1770_);
lean_inc(v_a_1776_);
v___x_1780_ = l_Lean_MVarId_refl(v_a_1776_, v___x_1779_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v___x_1781_; 
lean_dec_ref(v___x_1780_);
lean_dec(v_a_1778_);
lean_dec(v_a_1776_);
v___x_1781_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___y_1446_ = v___y_1771_;
v___y_1447_ = v___y_1773_;
v___y_1448_ = v___y_1772_;
v___y_1449_ = v___y_1770_;
v_a_1450_ = v___x_1781_;
goto v___jp_1445_;
}
else
{
lean_object* v_a_1782_; uint8_t v___x_1783_; 
v_a_1782_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_a_1782_);
v___x_1783_ = l_Lean_Exception_isInterrupt(v_a_1782_);
if (v___x_1783_ == 0)
{
uint8_t v___x_1784_; 
v___x_1784_ = l_Lean_Exception_isRuntime(v_a_1782_);
v___y_1742_ = v___x_1779_;
v___y_1743_ = v___y_1771_;
v___y_1744_ = v_a_1778_;
v___y_1745_ = v___x_1780_;
v___y_1746_ = v_a_1776_;
v___y_1747_ = v___y_1772_;
v___y_1748_ = v___y_1773_;
v___y_1749_ = v___y_1770_;
v___y_1750_ = v___x_1784_;
goto v___jp_1741_;
}
else
{
lean_dec(v_a_1782_);
v___y_1742_ = v___x_1779_;
v___y_1743_ = v___y_1771_;
v___y_1744_ = v_a_1778_;
v___y_1745_ = v___x_1780_;
v___y_1746_ = v_a_1776_;
v___y_1747_ = v___y_1772_;
v___y_1748_ = v___y_1773_;
v___y_1749_ = v___y_1770_;
v___y_1750_ = v___x_1783_;
goto v___jp_1741_;
}
}
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec(v_a_1776_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v_matchDeclName_1437_);
v_a_1785_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1777_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1777_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v_matchDeclName_1437_);
v_a_1793_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1775_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1775_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
v_resetjp_1817_:
{
uint8_t v___x_1820_; 
v___x_1820_ = lean_nat_dec_eq(v_currRecDepth_1804_, v_maxRecDepth_1805_);
if (v___x_1820_ == 0)
{
lean_object* v_cls_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1825_; 
v_cls_1821_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_1822_ = lean_unsigned_to_nat(1u);
v___x_1823_ = lean_nat_add(v_currRecDepth_1804_, v___x_1822_);
lean_dec(v_currRecDepth_1804_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 3, v___x_1823_);
v___x_1825_ = v___x_1818_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_fileName_1801_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_fileMap_1802_);
lean_ctor_set(v_reuseFailAlloc_1841_, 2, v_options_1803_);
lean_ctor_set(v_reuseFailAlloc_1841_, 3, v___x_1823_);
lean_ctor_set(v_reuseFailAlloc_1841_, 4, v_maxRecDepth_1805_);
lean_ctor_set(v_reuseFailAlloc_1841_, 5, v_ref_1806_);
lean_ctor_set(v_reuseFailAlloc_1841_, 6, v_currNamespace_1807_);
lean_ctor_set(v_reuseFailAlloc_1841_, 7, v_openDecls_1808_);
lean_ctor_set(v_reuseFailAlloc_1841_, 8, v_initHeartbeats_1809_);
lean_ctor_set(v_reuseFailAlloc_1841_, 9, v_maxHeartbeats_1810_);
lean_ctor_set(v_reuseFailAlloc_1841_, 10, v_quotContext_1811_);
lean_ctor_set(v_reuseFailAlloc_1841_, 11, v_currMacroScope_1812_);
lean_ctor_set(v_reuseFailAlloc_1841_, 12, v_cancelTk_x3f_1814_);
lean_ctor_set(v_reuseFailAlloc_1841_, 13, v_inheritedTraceOptions_1816_);
lean_ctor_set_uint8(v_reuseFailAlloc_1841_, sizeof(void*)*14, v_diag_1813_);
lean_ctor_set_uint8(v_reuseFailAlloc_1841_, sizeof(void*)*14 + 1, v_suppressElabErrors_1815_);
v___x_1825_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___redArg(v_cls_1821_, v___x_1825_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; uint8_t v___x_1828_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_a_1827_);
lean_dec_ref(v___x_1826_);
v___x_1828_ = lean_unbox(v_a_1827_);
lean_dec(v_a_1827_);
if (v___x_1828_ == 0)
{
v___y_1770_ = v_a_1440_;
v___y_1771_ = v_a_1441_;
v___y_1772_ = v___x_1825_;
v___y_1773_ = v_a_1443_;
goto v___jp_1769_;
}
else
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1829_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__15, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__15_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__15);
lean_inc(v_mvarId_1438_);
v___x_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1830_, 0, v_mvarId_1438_);
v___x_1831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1829_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v___x_1832_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(v_cls_1821_, v___x_1831_, v_a_1440_, v_a_1441_, v___x_1825_, v_a_1443_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_dec_ref(v___x_1832_);
v___y_1770_ = v_a_1440_;
v___y_1771_ = v_a_1441_;
v___y_1772_ = v___x_1825_;
v___y_1773_ = v_a_1443_;
goto v___jp_1769_;
}
else
{
lean_dec_ref(v___x_1825_);
lean_dec(v_a_1443_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_mvarId_1438_);
lean_dec(v_matchDeclName_1437_);
return v___x_1832_;
}
}
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
lean_dec_ref(v___x_1825_);
lean_dec(v_a_1443_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_mvarId_1438_);
lean_dec(v_matchDeclName_1437_);
v_a_1833_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1826_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1826_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
}
else
{
lean_object* v___x_1842_; 
lean_del_object(v___x_1818_);
lean_dec_ref(v_inheritedTraceOptions_1816_);
lean_dec(v_cancelTk_x3f_1814_);
lean_dec(v_currMacroScope_1812_);
lean_dec(v_quotContext_1811_);
lean_dec(v_maxHeartbeats_1810_);
lean_dec(v_initHeartbeats_1809_);
lean_dec(v_openDecls_1808_);
lean_dec(v_currNamespace_1807_);
lean_dec(v_maxRecDepth_1805_);
lean_dec(v_currRecDepth_1804_);
lean_dec_ref(v_options_1803_);
lean_dec_ref(v_fileMap_1802_);
lean_dec_ref(v_fileName_1801_);
lean_dec(v_a_1443_);
lean_dec(v_a_1441_);
lean_dec_ref(v_a_1440_);
lean_dec(v_mvarId_1438_);
lean_dec(v_matchDeclName_1437_);
v___x_1842_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__3___redArg(v_ref_1806_);
return v___x_1842_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(lean_object* v_depth_1844_, lean_object* v_matchDeclName_1845_, lean_object* v_as_1846_, size_t v_i_1847_, size_t v_stop_1848_, lean_object* v_b_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
uint8_t v___x_1855_; 
v___x_1855_ = lean_usize_dec_eq(v_i_1847_, v_stop_1848_);
if (v___x_1855_ == 0)
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1856_ = lean_array_uget_borrowed(v_as_1846_, v_i_1847_);
v___x_1857_ = lean_unsigned_to_nat(1u);
v___x_1858_ = lean_nat_add(v_depth_1844_, v___x_1857_);
lean_inc(v___y_1853_);
lean_inc_ref(v___y_1852_);
lean_inc(v___y_1851_);
lean_inc_ref(v___y_1850_);
lean_inc(v___x_1856_);
lean_inc(v_matchDeclName_1845_);
v___x_1859_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1845_, v___x_1856_, v___x_1858_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
lean_dec(v___x_1858_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; size_t v___x_1861_; size_t v___x_1862_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_a_1860_);
lean_dec_ref(v___x_1859_);
v___x_1861_ = ((size_t)1ULL);
v___x_1862_ = lean_usize_add(v_i_1847_, v___x_1861_);
v_i_1847_ = v___x_1862_;
v_b_1849_ = v_a_1860_;
goto _start;
}
else
{
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v_matchDeclName_1845_);
return v___x_1859_;
}
}
else
{
lean_object* v___x_1864_; 
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v_matchDeclName_1845_);
v___x_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1864_, 0, v_b_1849_);
return v___x_1864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0___boxed(lean_object* v_depth_1865_, lean_object* v_matchDeclName_1866_, lean_object* v_as_1867_, lean_object* v_i_1868_, lean_object* v_stop_1869_, lean_object* v_b_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
size_t v_i_boxed_1876_; size_t v_stop_boxed_1877_; lean_object* v_res_1878_; 
v_i_boxed_1876_ = lean_unbox_usize(v_i_1868_);
lean_dec(v_i_1868_);
v_stop_boxed_1877_ = lean_unbox_usize(v_stop_1869_);
lean_dec(v_stop_1869_);
v_res_1878_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1865_, v_matchDeclName_1866_, v_as_1867_, v_i_boxed_1876_, v_stop_boxed_1877_, v_b_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec_ref(v_as_1867_);
lean_dec(v_depth_1865_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___boxed(lean_object* v_matchDeclName_1879_, lean_object* v_mvarId_1880_, lean_object* v_depth_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1879_, v_mvarId_1880_, v_depth_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
lean_dec(v_depth_1881_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(lean_object* v_e_1888_, lean_object* v___y_1889_){
_start:
{
uint8_t v___x_1891_; 
v___x_1891_ = l_Lean_Expr_hasMVar(v_e_1888_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; 
v___x_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1892_, 0, v_e_1888_);
return v___x_1892_;
}
else
{
lean_object* v___x_1893_; lean_object* v_mctx_1894_; lean_object* v___x_1895_; lean_object* v_fst_1896_; lean_object* v_snd_1897_; lean_object* v___x_1898_; lean_object* v_cache_1899_; lean_object* v_zetaDeltaFVarIds_1900_; lean_object* v_postponed_1901_; lean_object* v_diag_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1911_; 
v___x_1893_ = lean_st_ref_get(v___y_1889_);
v_mctx_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc_ref(v_mctx_1894_);
lean_dec(v___x_1893_);
v___x_1895_ = l_Lean_instantiateMVarsCore(v_mctx_1894_, v_e_1888_);
v_fst_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_fst_1896_);
v_snd_1897_ = lean_ctor_get(v___x_1895_, 1);
lean_inc(v_snd_1897_);
lean_dec_ref(v___x_1895_);
v___x_1898_ = lean_st_ref_take(v___y_1889_);
v_cache_1899_ = lean_ctor_get(v___x_1898_, 1);
v_zetaDeltaFVarIds_1900_ = lean_ctor_get(v___x_1898_, 2);
v_postponed_1901_ = lean_ctor_get(v___x_1898_, 3);
v_diag_1902_ = lean_ctor_get(v___x_1898_, 4);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1911_ == 0)
{
lean_object* v_unused_1912_; 
v_unused_1912_ = lean_ctor_get(v___x_1898_, 0);
lean_dec(v_unused_1912_);
v___x_1904_ = v___x_1898_;
v_isShared_1905_ = v_isSharedCheck_1911_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_diag_1902_);
lean_inc(v_postponed_1901_);
lean_inc(v_zetaDeltaFVarIds_1900_);
lean_inc(v_cache_1899_);
lean_dec(v___x_1898_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1911_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v_snd_1897_);
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_snd_1897_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_cache_1899_);
lean_ctor_set(v_reuseFailAlloc_1910_, 2, v_zetaDeltaFVarIds_1900_);
lean_ctor_set(v_reuseFailAlloc_1910_, 3, v_postponed_1901_);
lean_ctor_set(v_reuseFailAlloc_1910_, 4, v_diag_1902_);
v___x_1907_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = lean_st_ref_set(v___y_1889_, v___x_1907_);
v___x_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1909_, 0, v_fst_1896_);
return v___x_1909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg___boxed(lean_object* v_e_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v_res_1916_; 
v_res_1916_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1913_, v___y_1914_);
lean_dec(v___y_1914_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(lean_object* v_e_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1917_, v___y_1919_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___boxed(lean_object* v_e_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(v_e_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(lean_object* v_lctx_1931_, lean_object* v_localInsts_1932_, lean_object* v_x_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v___x_1939_; 
v___x_1939_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1931_, v_localInsts_1932_, v_x_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1939_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1939_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
v_a_1948_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1939_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1939_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg___boxed(lean_object* v_lctx_1956_, lean_object* v_localInsts_1957_, lean_object* v_x_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1956_, v_localInsts_1957_, v_x_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(lean_object* v_00_u03b1_1965_, lean_object* v_lctx_1966_, lean_object* v_localInsts_1967_, lean_object* v_x_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1966_, v_localInsts_1967_, v_x_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___boxed(lean_object* v_00_u03b1_1975_, lean_object* v_lctx_1976_, lean_object* v_localInsts_1977_, lean_object* v_x_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(v_00_u03b1_1975_, v_lctx_1976_, v_localInsts_1977_, v_x_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
return v_res_1984_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_proveCondEqThm___lam__0(lean_object* v_matchDeclName_1985_, lean_object* v_x_1986_){
_start:
{
uint8_t v___x_1987_; 
v___x_1987_ = lean_name_eq(v_x_1986_, v_matchDeclName_1985_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed(lean_object* v_matchDeclName_1988_, lean_object* v_x_1989_){
_start:
{
uint8_t v_res_1990_; lean_object* v_r_1991_; 
v_res_1990_ = l_Lean_Meta_Match_proveCondEqThm___lam__0(v_matchDeclName_1988_, v_x_1989_);
lean_dec(v_x_1989_);
lean_dec(v_matchDeclName_1988_);
v_r_1991_ = lean_box(v_res_1990_);
return v_r_1991_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(lean_object* v_upperBound_1992_, lean_object* v_a_1993_, lean_object* v_b_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
uint8_t v___x_2000_; 
v___x_2000_ = lean_nat_dec_lt(v_a_1993_, v_upperBound_1992_);
if (v___x_2000_ == 0)
{
lean_object* v___x_2001_; 
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v_a_1993_);
v___x_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2001_, 0, v_b_1994_);
return v___x_2001_;
}
else
{
uint8_t v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = 0;
lean_inc(v___y_1998_);
lean_inc_ref(v___y_1997_);
lean_inc(v___y_1996_);
lean_inc_ref(v___y_1995_);
v___x_2003_ = l_Lean_Meta_introSubstEq(v_b_1994_, v___x_2002_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v_snd_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref(v___x_2003_);
v_snd_2005_ = lean_ctor_get(v_a_2004_, 1);
lean_inc(v_snd_2005_);
lean_dec(v_a_2004_);
v___x_2006_ = lean_unsigned_to_nat(1u);
v___x_2007_ = lean_nat_add(v_a_1993_, v___x_2006_);
lean_dec(v_a_1993_);
v_a_1993_ = v___x_2007_;
v_b_1994_ = v_snd_2005_;
goto _start;
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v_a_1993_);
v_a_2009_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_2003_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_2003_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg___boxed(lean_object* v_upperBound_2017_, lean_object* v_a_2018_, lean_object* v_b_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_2017_, v_a_2018_, v_b_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
lean_dec(v_upperBound_2017_);
return v_res_2025_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__0));
v___x_2028_ = l_Lean_stringToMessageData(v___x_2027_);
return v___x_2028_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__2));
v___x_2031_ = l_Lean_stringToMessageData(v___x_2030_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1(lean_object* v_type_2032_, lean_object* v___f_2033_, lean_object* v_matchDeclName_2034_, lean_object* v___x_2035_, uint8_t v___x_2036_, lean_object* v_heqPos_2037_, lean_object* v_heqNum_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v___x_2044_; lean_object* v_a_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2044_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_type_2032_, v___y_2040_);
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2045_);
lean_dec_ref(v___x_2044_);
v___x_2046_ = lean_box(0);
lean_inc_ref(v___y_2039_);
v___x_2047_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2045_, v___x_2046_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2196_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2050_ = v___x_2047_;
v_isShared_2051_ = v_isSharedCheck_2196_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2047_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2196_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2058_; uint8_t v___y_2059_; lean_object* v_mvarId_2094_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___x_2116_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___x_2174_; lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2195_; 
v___x_2116_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_2174_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___redArg(v___x_2116_, v___y_2041_);
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2177_ = v___x_2174_;
v_isShared_2178_ = v_isSharedCheck_2195_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2174_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2195_;
goto v_resetjp_2176_;
}
v___jp_2052_:
{
if (v___y_2059_ == 0)
{
lean_object* v___x_2060_; 
lean_dec_ref(v___y_2058_);
lean_del_object(v___x_2050_);
lean_inc(v___y_2054_);
lean_inc_ref(v___y_2053_);
lean_inc(v___y_2056_);
lean_inc_ref(v___y_2057_);
v___x_2060_ = l_Lean_MVarId_deltaTarget(v___y_2055_, v___f_2033_, v___y_2057_, v___y_2056_, v___y_2053_, v___y_2054_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v___x_2062_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2061_);
lean_dec_ref(v___x_2060_);
lean_inc(v___y_2054_);
lean_inc_ref(v___y_2053_);
lean_inc(v___y_2056_);
lean_inc_ref(v___y_2057_);
v___x_2062_ = l_Lean_MVarId_heqOfEq(v_a_2061_, v___y_2057_, v___y_2056_, v___y_2053_, v___y_2054_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2064_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2063_);
lean_dec_ref(v___x_2062_);
lean_inc(v___y_2056_);
v___x_2064_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_2034_, v_a_2063_, v___x_2035_, v___y_2057_, v___y_2056_, v___y_2053_, v___y_2054_);
lean_dec(v___x_2035_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v___x_2065_; 
lean_dec_ref(v___x_2064_);
v___x_2065_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_2048_, v___y_2056_);
lean_dec(v___y_2056_);
return v___x_2065_;
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec(v___y_2056_);
lean_dec(v_a_2048_);
v_a_2066_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2064_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2064_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec(v_a_2048_);
lean_dec(v___x_2035_);
lean_dec(v_matchDeclName_2034_);
v_a_2074_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2062_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2062_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec(v_a_2048_);
lean_dec(v___x_2035_);
lean_dec(v_matchDeclName_2034_);
v_a_2082_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2060_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2060_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
else
{
lean_object* v___x_2091_; 
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec(v_a_2048_);
lean_dec(v___x_2035_);
lean_dec(v_matchDeclName_2034_);
lean_dec_ref(v___f_2033_);
if (v_isShared_2051_ == 0)
{
lean_ctor_set_tag(v___x_2050_, 1);
lean_ctor_set(v___x_2050_, 0, v___y_2058_);
v___x_2091_ = v___x_2050_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___y_2058_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
v___jp_2093_:
{
lean_object* v___x_2099_; 
lean_inc(v___y_2098_);
lean_inc_ref(v___y_2097_);
lean_inc(v___y_2096_);
lean_inc_ref(v___y_2095_);
v___x_2099_ = l_Lean_MVarId_intros(v_mvarId_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v_snd_2101_; uint8_t v___x_2102_; lean_object* v___x_2103_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref(v___x_2099_);
v_snd_2101_ = lean_ctor_get(v_a_2100_, 1);
lean_inc(v_snd_2101_);
lean_dec(v_a_2100_);
v___x_2102_ = 1;
lean_inc(v___y_2098_);
lean_inc_ref(v___y_2097_);
lean_inc(v___y_2096_);
lean_inc_ref(v___y_2095_);
lean_inc(v_snd_2101_);
v___x_2103_ = l_Lean_MVarId_refl(v_snd_2101_, v___x_2102_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v___x_2104_; 
lean_dec_ref(v___x_2103_);
lean_dec(v_snd_2101_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec_ref(v___y_2095_);
lean_del_object(v___x_2050_);
lean_dec(v___x_2035_);
lean_dec(v_matchDeclName_2034_);
lean_dec_ref(v___f_2033_);
v___x_2104_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_2048_, v___y_2096_);
lean_dec(v___y_2096_);
return v___x_2104_;
}
else
{
lean_object* v_a_2105_; uint8_t v___x_2106_; 
v_a_2105_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2105_);
lean_dec_ref(v___x_2103_);
v___x_2106_ = l_Lean_Exception_isInterrupt(v_a_2105_);
if (v___x_2106_ == 0)
{
uint8_t v___x_2107_; 
lean_inc(v_a_2105_);
v___x_2107_ = l_Lean_Exception_isRuntime(v_a_2105_);
v___y_2053_ = v___y_2097_;
v___y_2054_ = v___y_2098_;
v___y_2055_ = v_snd_2101_;
v___y_2056_ = v___y_2096_;
v___y_2057_ = v___y_2095_;
v___y_2058_ = v_a_2105_;
v___y_2059_ = v___x_2107_;
goto v___jp_2052_;
}
else
{
v___y_2053_ = v___y_2097_;
v___y_2054_ = v___y_2098_;
v___y_2055_ = v_snd_2101_;
v___y_2056_ = v___y_2096_;
v___y_2057_ = v___y_2095_;
v___y_2058_ = v_a_2105_;
v___y_2059_ = v___x_2106_;
goto v___jp_2052_;
}
}
}
else
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_del_object(v___x_2050_);
lean_dec(v_a_2048_);
lean_dec(v___x_2035_);
lean_dec(v_matchDeclName_2034_);
lean_dec_ref(v___f_2033_);
v_a_2108_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2099_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2099_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2108_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
v___jp_2117_:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Lean_Expr_mvarId_x21(v_a_2048_);
if (v___x_2036_ == 0)
{
lean_dec(v_heqPos_2037_);
v_mvarId_2094_ = v___x_2122_;
v___y_2095_ = v___y_2118_;
v___y_2096_ = v___y_2119_;
v___y_2097_ = v___y_2120_;
v___y_2098_ = v___y_2121_;
goto v___jp_2093_;
}
else
{
lean_object* v___x_2123_; uint8_t v___x_2124_; lean_object* v___x_2125_; 
v___x_2123_ = lean_box(0);
v___x_2124_ = 0;
lean_inc(v___y_2121_);
lean_inc_ref(v___y_2120_);
lean_inc(v___y_2119_);
lean_inc_ref(v___y_2118_);
v___x_2125_ = l_Lean_Meta_introNCore(v___x_2122_, v_heqPos_2037_, v___x_2123_, v___x_2124_, v___x_2124_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v_snd_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2164_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref(v___x_2125_);
v_snd_2127_ = lean_ctor_get(v_a_2126_, 1);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_a_2126_);
if (v_isSharedCheck_2164_ == 0)
{
lean_object* v_unused_2165_; 
v_unused_2165_ = lean_ctor_get(v_a_2126_, 0);
lean_dec(v_unused_2165_);
v___x_2129_ = v_a_2126_;
v_isShared_2130_ = v_isSharedCheck_2164_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_snd_2127_);
lean_dec(v_a_2126_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2164_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2131_; 
lean_inc(v___y_2121_);
lean_inc_ref(v___y_2120_);
lean_inc(v___y_2119_);
lean_inc_ref(v___y_2118_);
lean_inc(v___x_2035_);
v___x_2131_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_heqNum_2038_, v___x_2035_, v_snd_2127_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v___x_2133_; lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2155_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref(v___x_2131_);
v___x_2133_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___redArg(v___x_2116_, v___y_2120_);
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2155_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2155_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
uint8_t v___x_2138_; 
v___x_2138_ = lean_unbox(v_a_2134_);
lean_dec(v_a_2134_);
if (v___x_2138_ == 0)
{
lean_del_object(v___x_2136_);
lean_del_object(v___x_2129_);
v_mvarId_2094_ = v_a_2132_;
v___y_2095_ = v___y_2118_;
v___y_2096_ = v___y_2119_;
v___y_2097_ = v___y_2120_;
v___y_2098_ = v___y_2121_;
goto v___jp_2093_;
}
else
{
lean_object* v___x_2139_; lean_object* v___x_2141_; 
v___x_2139_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1);
lean_inc(v_a_2132_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set_tag(v___x_2136_, 1);
lean_ctor_set(v___x_2136_, 0, v_a_2132_);
v___x_2141_ = v___x_2136_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2132_);
v___x_2141_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
lean_object* v___x_2143_; 
if (v_isShared_2130_ == 0)
{
lean_ctor_set_tag(v___x_2129_, 7);
lean_ctor_set(v___x_2129_, 1, v___x_2141_);
lean_ctor_set(v___x_2129_, 0, v___x_2139_);
v___x_2143_ = v___x_2129_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2139_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(v___x_2116_, v___x_2143_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_dec_ref(v___x_2144_);
v_mvarId_2094_ = v_a_2132_;
v___y_2095_ = v___y_2118_;
v___y_2096_ = v___y_2119_;
v___y_2097_ = v___y_2120_;
v___y_2098_ = v___y_2121_;
goto v___jp_2093_;
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec(v_a_2132_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_del_object(v___x_2050_);
lean_dec(v_a_2048_);
lean_dec(v___x_2035_);
lean_dec(v_matchDeclName_2034_);
lean_dec_ref(v___f_2033_);
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2144_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2144_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
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
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_del_object(v___x_2129_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_del_object(v___x_2050_);
lean_dec(v_a_2048_);
lean_dec(v___x_2035_);
lean_dec(v_matchDeclName_2034_);
lean_dec_ref(v___f_2033_);
v_a_2156_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2131_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2131_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
else
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_del_object(v___x_2050_);
lean_dec(v_a_2048_);
lean_dec(v___x_2035_);
lean_dec(v_matchDeclName_2034_);
lean_dec_ref(v___f_2033_);
v_a_2166_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2168_ = v___x_2125_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2125_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2166_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
}
v_resetjp_2176_:
{
uint8_t v___x_2179_; 
v___x_2179_ = lean_unbox(v_a_2175_);
lean_dec(v_a_2175_);
if (v___x_2179_ == 0)
{
lean_del_object(v___x_2177_);
v___y_2118_ = v___y_2039_;
v___y_2119_ = v___y_2040_;
v___y_2120_ = v___y_2041_;
v___y_2121_ = v___y_2042_;
goto v___jp_2117_;
}
else
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2183_; 
v___x_2180_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3);
v___x_2181_ = l_Lean_Expr_mvarId_x21(v_a_2048_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set_tag(v___x_2177_, 1);
lean_ctor_set(v___x_2177_, 0, v___x_2181_);
v___x_2183_ = v___x_2177_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2181_);
v___x_2183_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2180_);
lean_ctor_set(v___x_2184_, 1, v___x_2183_);
v___x_2185_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(v___x_2116_, v___x_2184_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_dec_ref(v___x_2185_);
v___y_2118_ = v___y_2039_;
v___y_2119_ = v___y_2040_;
v___y_2120_ = v___y_2041_;
v___y_2121_ = v___y_2042_;
goto v___jp_2117_;
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_del_object(v___x_2050_);
lean_dec(v_a_2048_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v_heqPos_2037_);
lean_dec(v___x_2035_);
lean_dec(v_matchDeclName_2034_);
lean_dec_ref(v___f_2033_);
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2185_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2185_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
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
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v_heqPos_2037_);
lean_dec(v___x_2035_);
lean_dec(v_matchDeclName_2034_);
lean_dec_ref(v___f_2033_);
return v___x_2047_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed(lean_object* v_type_2197_, lean_object* v___f_2198_, lean_object* v_matchDeclName_2199_, lean_object* v___x_2200_, lean_object* v___x_2201_, lean_object* v_heqPos_2202_, lean_object* v_heqNum_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
uint8_t v___x_5180__boxed_2209_; lean_object* v_res_2210_; 
v___x_5180__boxed_2209_ = lean_unbox(v___x_2201_);
v_res_2210_ = l_Lean_Meta_Match_proveCondEqThm___lam__1(v_type_2197_, v___f_2198_, v_matchDeclName_2199_, v___x_2200_, v___x_5180__boxed_2209_, v_heqPos_2202_, v_heqNum_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
lean_dec(v_heqNum_2203_);
return v_res_2210_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__0(void){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2211_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__1(void){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__0, &l_Lean_Meta_Match_proveCondEqThm___closed__0_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__0);
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
return v___x_2213_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__2(void){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2214_ = lean_unsigned_to_nat(32u);
v___x_2215_ = lean_mk_empty_array_with_capacity(v___x_2214_);
v___x_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
return v___x_2216_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__3(void){
_start:
{
size_t v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2217_ = ((size_t)5ULL);
v___x_2218_ = lean_unsigned_to_nat(0u);
v___x_2219_ = lean_unsigned_to_nat(32u);
v___x_2220_ = lean_mk_empty_array_with_capacity(v___x_2219_);
v___x_2221_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__2, &l_Lean_Meta_Match_proveCondEqThm___closed__2_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__2);
v___x_2222_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
lean_ctor_set(v___x_2222_, 1, v___x_2220_);
lean_ctor_set(v___x_2222_, 2, v___x_2218_);
lean_ctor_set(v___x_2222_, 3, v___x_2218_);
lean_ctor_set_usize(v___x_2222_, 4, v___x_2217_);
return v___x_2222_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__4(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2223_ = lean_box(1);
v___x_2224_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_2225_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_2226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
lean_ctor_set(v___x_2226_, 1, v___x_2224_);
lean_ctor_set(v___x_2226_, 2, v___x_2223_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm(lean_object* v_matchDeclName_2229_, lean_object* v_type_2230_, lean_object* v_heqPos_2231_, lean_object* v_heqNum_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_){
_start:
{
lean_object* v___f_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; uint8_t v___x_2242_; lean_object* v___x_2243_; lean_object* v___f_2244_; lean_object* v___x_2245_; 
lean_inc(v_matchDeclName_2229_);
v___f_2238_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2238_, 0, v_matchDeclName_2229_);
v___x_2239_ = lean_unsigned_to_nat(0u);
v___x_2240_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_2241_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___closed__5));
v___x_2242_ = lean_nat_dec_lt(v___x_2239_, v_heqNum_2232_);
v___x_2243_ = lean_box(v___x_2242_);
v___f_2244_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed), 12, 7);
lean_closure_set(v___f_2244_, 0, v_type_2230_);
lean_closure_set(v___f_2244_, 1, v___f_2238_);
lean_closure_set(v___f_2244_, 2, v_matchDeclName_2229_);
lean_closure_set(v___f_2244_, 3, v___x_2239_);
lean_closure_set(v___f_2244_, 4, v___x_2243_);
lean_closure_set(v___f_2244_, 5, v_heqPos_2231_);
lean_closure_set(v___f_2244_, 6, v_heqNum_2232_);
v___x_2245_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v___x_2240_, v___x_2241_, v___f_2244_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___boxed(lean_object* v_matchDeclName_2246_, lean_object* v_type_2247_, lean_object* v_heqPos_2248_, lean_object* v_heqNum_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2246_, v_type_2247_, v_heqPos_2248_, v_heqNum_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(lean_object* v_upperBound_2256_, lean_object* v_inst_2257_, lean_object* v_R_2258_, lean_object* v_a_2259_, lean_object* v_b_2260_, lean_object* v_c_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_2256_, v_a_2259_, v_b_2260_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___boxed(lean_object* v_upperBound_2268_, lean_object* v_inst_2269_, lean_object* v_R_2270_, lean_object* v_a_2271_, lean_object* v_b_2272_, lean_object* v_c_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(v_upperBound_2268_, v_inst_2269_, v_R_2270_, v_a_2271_, v_b_2272_, v_c_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
lean_dec(v_upperBound_2268_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(lean_object* v_k_2280_, lean_object* v_b_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v___x_2287_; 
v___x_2287_ = lean_apply_6(v_k_2280_, v_b_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, lean_box(0));
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_2288_, lean_object* v_b_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(v_k_2288_, v_b_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(lean_object* v_name_2296_, uint8_t v_bi_2297_, lean_object* v_type_2298_, lean_object* v_k_2299_, uint8_t v_kind_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v___f_2306_; lean_object* v___x_2307_; 
v___f_2306_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2306_, 0, v_k_2299_);
v___x_2307_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2296_, v_bi_2297_, v_type_2298_, v___f_2306_, v_kind_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2307_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2307_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
v_a_2316_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2307_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2307_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___boxed(lean_object* v_name_2324_, lean_object* v_bi_2325_, lean_object* v_type_2326_, lean_object* v_k_2327_, lean_object* v_kind_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
uint8_t v_bi_boxed_2334_; uint8_t v_kind_boxed_2335_; lean_object* v_res_2336_; 
v_bi_boxed_2334_ = lean_unbox(v_bi_2325_);
v_kind_boxed_2335_ = lean_unbox(v_kind_2328_);
v_res_2336_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_name_2324_, v_bi_boxed_2334_, v_type_2326_, v_k_2327_, v_kind_boxed_2335_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(lean_object* v_00_u03b1_2337_, lean_object* v_name_2338_, uint8_t v_bi_2339_, lean_object* v_type_2340_, lean_object* v_k_2341_, uint8_t v_kind_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_name_2338_, v_bi_2339_, v_type_2340_, v_k_2341_, v_kind_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___boxed(lean_object* v_00_u03b1_2349_, lean_object* v_name_2350_, lean_object* v_bi_2351_, lean_object* v_type_2352_, lean_object* v_k_2353_, lean_object* v_kind_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
uint8_t v_bi_boxed_2360_; uint8_t v_kind_boxed_2361_; lean_object* v_res_2362_; 
v_bi_boxed_2360_ = lean_unbox(v_bi_2351_);
v_kind_boxed_2361_ = lean_unbox(v_kind_2354_);
v_res_2362_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(v_00_u03b1_2349_, v_name_2350_, v_bi_boxed_2360_, v_type_2352_, v_k_2353_, v_kind_boxed_2361_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed(lean_object* v_i_2363_, lean_object* v_altsNew_2364_, lean_object* v_discrs_2365_, lean_object* v_patterns_2366_, lean_object* v_alts_2367_, lean_object* v_k_2368_, lean_object* v_altNew_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(v_i_2363_, v_altsNew_2364_, v_discrs_2365_, v_patterns_2366_, v_alts_2367_, v_k_2368_, v_altNew_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
lean_dec(v_i_2363_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(lean_object* v_discrs_2376_, lean_object* v_patterns_2377_, lean_object* v_alts_2378_, lean_object* v_k_2379_, lean_object* v_i_2380_, lean_object* v_altsNew_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_){
_start:
{
lean_object* v___x_2387_; uint8_t v___x_2388_; 
v___x_2387_ = lean_array_get_size(v_alts_2378_);
v___x_2388_ = lean_nat_dec_lt(v_i_2380_, v___x_2387_);
if (v___x_2388_ == 0)
{
lean_object* v___x_2389_; 
lean_dec(v_i_2380_);
lean_dec_ref(v_alts_2378_);
lean_dec_ref(v_patterns_2377_);
lean_dec_ref(v_discrs_2376_);
v___x_2389_ = lean_apply_6(v_k_2379_, v_altsNew_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, lean_box(0));
return v___x_2389_;
}
else
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = lean_array_fget_borrowed(v_alts_2378_, v_i_2380_);
lean_inc_ref(v_a_2382_);
v___x_2391_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_2390_, v_a_2382_, v_a_2384_, v_a_2385_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v___f_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; uint8_t v___x_2397_; uint8_t v___x_2398_; lean_object* v___x_2399_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
lean_dec_ref(v___x_2391_);
lean_inc_ref(v_patterns_2377_);
lean_inc_ref(v_discrs_2376_);
v___f_2393_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_2393_, 0, v_i_2380_);
lean_closure_set(v___f_2393_, 1, v_altsNew_2381_);
lean_closure_set(v___f_2393_, 2, v_discrs_2376_);
lean_closure_set(v___f_2393_, 3, v_patterns_2377_);
lean_closure_set(v___f_2393_, 4, v_alts_2378_);
lean_closure_set(v___f_2393_, 5, v_k_2379_);
v___x_2394_ = l_Lean_LocalDecl_type(v_a_2392_);
v___x_2395_ = l_Lean_Expr_replaceFVars(v___x_2394_, v_discrs_2376_, v_patterns_2377_);
lean_dec_ref(v_patterns_2377_);
lean_dec_ref(v_discrs_2376_);
lean_dec_ref(v___x_2394_);
v___x_2396_ = l_Lean_LocalDecl_userName(v_a_2392_);
v___x_2397_ = l_Lean_LocalDecl_binderInfo(v_a_2392_);
lean_dec(v_a_2392_);
v___x_2398_ = 0;
v___x_2399_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v___x_2396_, v___x_2397_, v___x_2395_, v___f_2393_, v___x_2398_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_);
return v___x_2399_;
}
else
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2407_; 
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
lean_dec(v_a_2383_);
lean_dec_ref(v_a_2382_);
lean_dec_ref(v_altsNew_2381_);
lean_dec(v_i_2380_);
lean_dec_ref(v_k_2379_);
lean_dec_ref(v_alts_2378_);
lean_dec_ref(v_patterns_2377_);
lean_dec_ref(v_discrs_2376_);
v_a_2400_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2402_ = v___x_2391_;
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2391_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2403_ == 0)
{
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(lean_object* v_i_2408_, lean_object* v_altsNew_2409_, lean_object* v_discrs_2410_, lean_object* v_patterns_2411_, lean_object* v_alts_2412_, lean_object* v_k_2413_, lean_object* v_altNew_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2420_ = lean_unsigned_to_nat(1u);
v___x_2421_ = lean_nat_add(v_i_2408_, v___x_2420_);
v___x_2422_ = lean_array_push(v_altsNew_2409_, v_altNew_2414_);
v___x_2423_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2410_, v_patterns_2411_, v_alts_2412_, v_k_2413_, v___x_2421_, v___x_2422_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___boxed(lean_object* v_discrs_2424_, lean_object* v_patterns_2425_, lean_object* v_alts_2426_, lean_object* v_k_2427_, lean_object* v_i_2428_, lean_object* v_altsNew_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2424_, v_patterns_2425_, v_alts_2426_, v_k_2427_, v_i_2428_, v_altsNew_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(lean_object* v_00_u03b1_2436_, lean_object* v_discrs_2437_, lean_object* v_patterns_2438_, lean_object* v_alts_2439_, lean_object* v_k_2440_, lean_object* v_i_2441_, lean_object* v_altsNew_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2437_, v_patterns_2438_, v_alts_2439_, v_k_2440_, v_i_2441_, v_altsNew_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___boxed(lean_object* v_00_u03b1_2449_, lean_object* v_discrs_2450_, lean_object* v_patterns_2451_, lean_object* v_alts_2452_, lean_object* v_k_2453_, lean_object* v_i_2454_, lean_object* v_altsNew_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(v_00_u03b1_2449_, v_discrs_2450_, v_patterns_2451_, v_alts_2452_, v_k_2453_, v_i_2454_, v_altsNew_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(lean_object* v_numDiscrEqs_2464_, lean_object* v_discrs_2465_, lean_object* v_patterns_2466_, lean_object* v_alts_2467_, lean_object* v_k_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_){
_start:
{
lean_object* v___x_2474_; uint8_t v___x_2475_; 
v___x_2474_ = lean_unsigned_to_nat(0u);
v___x_2475_ = lean_nat_dec_eq(v_numDiscrEqs_2464_, v___x_2474_);
if (v___x_2475_ == 0)
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_2477_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2465_, v_patterns_2466_, v_alts_2467_, v_k_2468_, v___x_2474_, v___x_2476_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_);
return v___x_2477_;
}
else
{
lean_object* v___x_2478_; 
lean_dec_ref(v_patterns_2466_);
lean_dec_ref(v_discrs_2465_);
v___x_2478_ = lean_apply_6(v_k_2468_, v_alts_2467_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, lean_box(0));
return v___x_2478_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___boxed(lean_object* v_numDiscrEqs_2479_, lean_object* v_discrs_2480_, lean_object* v_patterns_2481_, lean_object* v_alts_2482_, lean_object* v_k_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v_numDiscrEqs_2479_, v_discrs_2480_, v_patterns_2481_, v_alts_2482_, v_k_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_);
lean_dec(v_numDiscrEqs_2479_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(lean_object* v_00_u03b1_2490_, lean_object* v_numDiscrEqs_2491_, lean_object* v_discrs_2492_, lean_object* v_patterns_2493_, lean_object* v_alts_2494_, lean_object* v_k_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_){
_start:
{
lean_object* v___x_2501_; 
v___x_2501_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v_numDiscrEqs_2491_, v_discrs_2492_, v_patterns_2493_, v_alts_2494_, v_k_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___boxed(lean_object* v_00_u03b1_2502_, lean_object* v_numDiscrEqs_2503_, lean_object* v_discrs_2504_, lean_object* v_patterns_2505_, lean_object* v_alts_2506_, lean_object* v_k_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(v_00_u03b1_2502_, v_numDiscrEqs_2503_, v_discrs_2504_, v_patterns_2505_, v_alts_2506_, v_k_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_);
lean_dec(v_numDiscrEqs_2503_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(lean_object* v_declName_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v___x_2517_; lean_object* v_env_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2517_ = lean_st_ref_get(v___y_2515_);
v_env_2518_ = lean_ctor_get(v___x_2517_, 0);
lean_inc_ref(v_env_2518_);
lean_dec(v___x_2517_);
v___x_2519_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2518_, v_declName_2514_);
v___x_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg___boxed(lean_object* v_declName_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_declName_2521_, v___y_2522_);
lean_dec(v___y_2522_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(lean_object* v_declName_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v___x_2531_; 
v___x_2531_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_declName_2525_, v___y_2529_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___boxed(lean_object* v_declName_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(v_declName_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(lean_object* v_msg_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v___f_2546_; lean_object* v___x_13891__overap_2547_; lean_object* v___x_2548_; 
v___f_2546_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_13891__overap_2547_ = lean_panic_fn(v___f_2546_, v_msg_2540_);
v___x_2548_ = lean_apply_5(v___x_13891__overap_2547_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, lean_box(0));
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___boxed(lean_object* v_msg_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v_msg_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(lean_object* v_k_2556_, lean_object* v_b_2557_, lean_object* v_c_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v___x_2564_; 
v___x_2564_ = lean_apply_7(v_k_2556_, v_b_2557_, v_c_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, lean_box(0));
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed(lean_object* v_k_2565_, lean_object* v_b_2566_, lean_object* v_c_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(v_k_2565_, v_b_2566_, v_c_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(lean_object* v_type_2574_, lean_object* v_k_2575_, uint8_t v_cleanupAnnotations_2576_, uint8_t v_whnfType_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v___f_2583_; lean_object* v___x_2584_; 
v___f_2583_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2583_, 0, v_k_2575_);
v___x_2584_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2574_, v___f_2583_, v_cleanupAnnotations_2576_, v_whnfType_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2584_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2584_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
v_a_2593_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v___x_2584_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2584_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___boxed(lean_object* v_type_2601_, lean_object* v_k_2602_, lean_object* v_cleanupAnnotations_2603_, lean_object* v_whnfType_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2610_; uint8_t v_whnfType_boxed_2611_; lean_object* v_res_2612_; 
v_cleanupAnnotations_boxed_2610_ = lean_unbox(v_cleanupAnnotations_2603_);
v_whnfType_boxed_2611_ = lean_unbox(v_whnfType_2604_);
v_res_2612_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v_type_2601_, v_k_2602_, v_cleanupAnnotations_boxed_2610_, v_whnfType_boxed_2611_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(lean_object* v_00_u03b1_2613_, lean_object* v_type_2614_, lean_object* v_k_2615_, uint8_t v_cleanupAnnotations_2616_, uint8_t v_whnfType_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v_type_2614_, v_k_2615_, v_cleanupAnnotations_2616_, v_whnfType_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___boxed(lean_object* v_00_u03b1_2624_, lean_object* v_type_2625_, lean_object* v_k_2626_, lean_object* v_cleanupAnnotations_2627_, lean_object* v_whnfType_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2634_; uint8_t v_whnfType_boxed_2635_; lean_object* v_res_2636_; 
v_cleanupAnnotations_boxed_2634_ = lean_unbox(v_cleanupAnnotations_2627_);
v_whnfType_boxed_2635_ = lean_unbox(v_whnfType_2628_);
v_res_2636_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(v_00_u03b1_2624_, v_type_2625_, v_k_2626_, v_cleanupAnnotations_boxed_2634_, v_whnfType_boxed_2635_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(lean_object* v_overlaps_2637_, lean_object* v_splitterName_2638_, lean_object* v_matcherInput_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
lean_object* v_matchType_2645_; lean_object* v_discrInfos_2646_; lean_object* v_lhss_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2667_; 
v_matchType_2645_ = lean_ctor_get(v_matcherInput_2639_, 1);
v_discrInfos_2646_ = lean_ctor_get(v_matcherInput_2639_, 2);
v_lhss_2647_ = lean_ctor_get(v_matcherInput_2639_, 3);
v_isSharedCheck_2667_ = !lean_is_exclusive(v_matcherInput_2639_);
if (v_isSharedCheck_2667_ == 0)
{
lean_object* v_unused_2668_; lean_object* v_unused_2669_; 
v_unused_2668_ = lean_ctor_get(v_matcherInput_2639_, 4);
lean_dec(v_unused_2668_);
v_unused_2669_ = lean_ctor_get(v_matcherInput_2639_, 0);
lean_dec(v_unused_2669_);
v___x_2649_ = v_matcherInput_2639_;
v_isShared_2650_ = v_isSharedCheck_2667_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_lhss_2647_);
lean_inc(v_discrInfos_2646_);
lean_inc(v_matchType_2645_);
lean_dec(v_matcherInput_2639_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2667_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2651_; lean_object* v___x_2653_; 
v___x_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2651_, 0, v_overlaps_2637_);
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 4, v___x_2651_);
lean_ctor_set(v___x_2649_, 0, v_splitterName_2638_);
v___x_2653_ = v___x_2649_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_splitterName_2638_);
lean_ctor_set(v_reuseFailAlloc_2666_, 1, v_matchType_2645_);
lean_ctor_set(v_reuseFailAlloc_2666_, 2, v_discrInfos_2646_);
lean_ctor_set(v_reuseFailAlloc_2666_, 3, v_lhss_2647_);
lean_ctor_set(v_reuseFailAlloc_2666_, 4, v___x_2651_);
v___x_2653_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
lean_object* v___x_2654_; 
lean_inc(v___y_2643_);
lean_inc_ref(v___y_2642_);
lean_inc(v___y_2641_);
lean_inc_ref(v___y_2640_);
v___x_2654_ = l_Lean_Meta_Match_mkMatcher(v___x_2653_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; lean_object* v_addMatcher_2656_; lean_object* v___x_2657_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
lean_dec_ref(v___x_2654_);
v_addMatcher_2656_ = lean_ctor_get(v_a_2655_, 3);
lean_inc_ref(v_addMatcher_2656_);
lean_dec(v_a_2655_);
v___x_2657_ = lean_apply_5(v_addMatcher_2656_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, lean_box(0));
return v___x_2657_;
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
v_a_2658_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2654_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2654_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2658_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed(lean_object* v_overlaps_2670_, lean_object* v_splitterName_2671_, lean_object* v_matcherInput_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(v_overlaps_2670_, v_splitterName_2671_, v_matcherInput_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
return v_res_2678_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(lean_object* v_xs_2679_, lean_object* v_ys_2680_, lean_object* v_x_2681_){
_start:
{
lean_object* v_zero_2682_; uint8_t v_isZero_2683_; 
v_zero_2682_ = lean_unsigned_to_nat(0u);
v_isZero_2683_ = lean_nat_dec_eq(v_x_2681_, v_zero_2682_);
if (v_isZero_2683_ == 1)
{
lean_dec(v_x_2681_);
return v_isZero_2683_;
}
else
{
lean_object* v_one_2684_; lean_object* v_n_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; uint8_t v___x_2688_; 
v_one_2684_ = lean_unsigned_to_nat(1u);
v_n_2685_ = lean_nat_sub(v_x_2681_, v_one_2684_);
lean_dec(v_x_2681_);
v___x_2686_ = lean_array_fget_borrowed(v_xs_2679_, v_n_2685_);
v___x_2687_ = lean_array_fget_borrowed(v_ys_2680_, v_n_2685_);
v___x_2688_ = l_Lean_Meta_Match_instBEqAltParamInfo_beq(v___x_2686_, v___x_2687_);
if (v___x_2688_ == 0)
{
lean_dec(v_n_2685_);
return v___x_2688_;
}
else
{
v_x_2681_ = v_n_2685_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg___boxed(lean_object* v_xs_2690_, lean_object* v_ys_2691_, lean_object* v_x_2692_){
_start:
{
uint8_t v_res_2693_; lean_object* v_r_2694_; 
v_res_2693_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_2690_, v_ys_2691_, v_x_2692_);
lean_dec_ref(v_ys_2691_);
lean_dec_ref(v_xs_2690_);
v_r_2694_ = lean_box(v_res_2693_);
return v_r_2694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(lean_object* v_a_2695_, lean_object* v_b_2696_){
_start:
{
lean_object* v_array_2697_; lean_object* v_start_2698_; lean_object* v_stop_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2712_; 
v_array_2697_ = lean_ctor_get(v_a_2695_, 0);
v_start_2698_ = lean_ctor_get(v_a_2695_, 1);
v_stop_2699_ = lean_ctor_get(v_a_2695_, 2);
v_isSharedCheck_2712_ = !lean_is_exclusive(v_a_2695_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2701_ = v_a_2695_;
v_isShared_2702_ = v_isSharedCheck_2712_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_stop_2699_);
lean_inc(v_start_2698_);
lean_inc(v_array_2697_);
lean_dec(v_a_2695_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2712_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
uint8_t v___x_2703_; 
v___x_2703_ = lean_nat_dec_lt(v_start_2698_, v_stop_2699_);
if (v___x_2703_ == 0)
{
lean_del_object(v___x_2701_);
lean_dec(v_stop_2699_);
lean_dec(v_start_2698_);
lean_dec_ref(v_array_2697_);
return v_b_2696_;
}
else
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2707_; 
v___x_2704_ = lean_unsigned_to_nat(1u);
v___x_2705_ = lean_nat_add(v_start_2698_, v___x_2704_);
lean_inc_ref(v_array_2697_);
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 1, v___x_2705_);
v___x_2707_ = v___x_2701_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_array_2697_);
lean_ctor_set(v_reuseFailAlloc_2711_, 1, v___x_2705_);
lean_ctor_set(v_reuseFailAlloc_2711_, 2, v_stop_2699_);
v___x_2707_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2708_ = lean_array_fget(v_array_2697_, v_start_2698_);
lean_dec(v_start_2698_);
lean_dec_ref(v_array_2697_);
v___x_2709_ = lean_array_push(v_b_2696_, v___x_2708_);
v_a_2695_ = v___x_2707_;
v_b_2696_ = v___x_2709_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(lean_object* v_as_2713_, size_t v_sz_2714_, size_t v_i_2715_, lean_object* v_b_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
uint8_t v___x_2722_; 
v___x_2722_ = lean_usize_dec_lt(v_i_2715_, v_sz_2714_);
if (v___x_2722_ == 0)
{
lean_object* v___x_2723_; 
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
v___x_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2723_, 0, v_b_2716_);
return v___x_2723_;
}
else
{
lean_object* v_snd_2724_; lean_object* v_fst_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2777_; 
v_snd_2724_ = lean_ctor_get(v_b_2716_, 1);
v_fst_2725_ = lean_ctor_get(v_b_2716_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v_b_2716_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2727_ = v_b_2716_;
v_isShared_2728_ = v_isSharedCheck_2777_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_snd_2724_);
lean_inc(v_fst_2725_);
lean_dec(v_b_2716_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2777_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v_array_2729_; lean_object* v_start_2730_; lean_object* v_stop_2731_; uint8_t v___x_2732_; 
v_array_2729_ = lean_ctor_get(v_snd_2724_, 0);
v_start_2730_ = lean_ctor_get(v_snd_2724_, 1);
v_stop_2731_ = lean_ctor_get(v_snd_2724_, 2);
v___x_2732_ = lean_nat_dec_lt(v_start_2730_, v_stop_2731_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2734_; 
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
if (v_isShared_2728_ == 0)
{
v___x_2734_ = v___x_2727_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_fst_2725_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v_snd_2724_);
v___x_2734_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
lean_object* v___x_2735_; 
v___x_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2734_);
return v___x_2735_;
}
}
else
{
lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2773_; 
lean_inc(v_stop_2731_);
lean_inc(v_start_2730_);
lean_inc_ref(v_array_2729_);
v_isSharedCheck_2773_ = !lean_is_exclusive(v_snd_2724_);
if (v_isSharedCheck_2773_ == 0)
{
lean_object* v_unused_2774_; lean_object* v_unused_2775_; lean_object* v_unused_2776_; 
v_unused_2774_ = lean_ctor_get(v_snd_2724_, 2);
lean_dec(v_unused_2774_);
v_unused_2775_ = lean_ctor_get(v_snd_2724_, 1);
lean_dec(v_unused_2775_);
v_unused_2776_ = lean_ctor_get(v_snd_2724_, 0);
lean_dec(v_unused_2776_);
v___x_2738_ = v_snd_2724_;
v_isShared_2739_ = v_isSharedCheck_2773_;
goto v_resetjp_2737_;
}
else
{
lean_dec(v_snd_2724_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2773_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v_a_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v_a_2740_ = lean_array_uget_borrowed(v_as_2713_, v_i_2715_);
v___x_2741_ = lean_array_fget_borrowed(v_array_2729_, v_start_2730_);
lean_inc(v___y_2720_);
lean_inc_ref(v___y_2719_);
lean_inc(v___y_2718_);
lean_inc_ref(v___y_2717_);
lean_inc(v___x_2741_);
lean_inc(v_a_2740_);
v___x_2742_ = l_Lean_Meta_mkEqHEq(v_a_2740_, v___x_2741_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2744_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_a_2743_);
lean_dec_ref(v___x_2742_);
lean_inc(v___y_2720_);
lean_inc_ref(v___y_2719_);
v___x_2744_ = l_Lean_mkArrow(v_a_2743_, v_fst_2725_, v___y_2719_, v___y_2720_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2749_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2745_);
lean_dec_ref(v___x_2744_);
v___x_2746_ = lean_unsigned_to_nat(1u);
v___x_2747_ = lean_nat_add(v_start_2730_, v___x_2746_);
lean_dec(v_start_2730_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 1, v___x_2747_);
v___x_2749_ = v___x_2738_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_array_2729_);
lean_ctor_set(v_reuseFailAlloc_2756_, 1, v___x_2747_);
lean_ctor_set(v_reuseFailAlloc_2756_, 2, v_stop_2731_);
v___x_2749_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
lean_object* v___x_2751_; 
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 1, v___x_2749_);
lean_ctor_set(v___x_2727_, 0, v_a_2745_);
v___x_2751_ = v___x_2727_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2745_);
lean_ctor_set(v_reuseFailAlloc_2755_, 1, v___x_2749_);
v___x_2751_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
size_t v___x_2752_; size_t v___x_2753_; 
v___x_2752_ = ((size_t)1ULL);
v___x_2753_ = lean_usize_add(v_i_2715_, v___x_2752_);
v_i_2715_ = v___x_2753_;
v_b_2716_ = v___x_2751_;
goto _start;
}
}
}
else
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2764_; 
lean_del_object(v___x_2738_);
lean_dec(v_stop_2731_);
lean_dec(v_start_2730_);
lean_dec_ref(v_array_2729_);
lean_del_object(v___x_2727_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
v_a_2757_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2759_ = v___x_2744_;
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2744_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2764_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2762_; 
if (v_isShared_2760_ == 0)
{
v___x_2762_ = v___x_2759_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_a_2757_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
lean_del_object(v___x_2738_);
lean_dec(v_stop_2731_);
lean_dec(v_start_2730_);
lean_dec_ref(v_array_2729_);
lean_del_object(v___x_2727_);
lean_dec(v_fst_2725_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
v_a_2765_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2742_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2742_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7___boxed(lean_object* v_as_2778_, lean_object* v_sz_2779_, lean_object* v_i_2780_, lean_object* v_b_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
size_t v_sz_boxed_2787_; size_t v_i_boxed_2788_; lean_object* v_res_2789_; 
v_sz_boxed_2787_ = lean_unbox_usize(v_sz_2779_);
lean_dec(v_sz_2779_);
v_i_boxed_2788_ = lean_unbox_usize(v_i_2780_);
lean_dec(v_i_2780_);
v_res_2789_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v_as_2778_, v_sz_boxed_2787_, v_i_boxed_2788_, v_b_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
lean_dec_ref(v_as_2778_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(lean_object* v___x_2790_, lean_object* v___x_2791_, lean_object* v_as_2792_, size_t v_sz_2793_, size_t v_i_2794_, lean_object* v_b_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
uint8_t v___x_2801_; 
v___x_2801_ = lean_usize_dec_lt(v_i_2794_, v_sz_2793_);
if (v___x_2801_ == 0)
{
lean_object* v___x_2802_; 
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
v___x_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2802_, 0, v_b_2795_);
return v___x_2802_;
}
else
{
lean_object* v___x_2803_; lean_object* v_a_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2803_ = l_Lean_instInhabitedExpr;
v_a_2804_ = lean_array_uget_borrowed(v_as_2792_, v_i_2794_);
v___x_2805_ = lean_array_get_borrowed(v___x_2803_, v___x_2790_, v_a_2804_);
lean_inc(v___y_2799_);
lean_inc_ref(v___y_2798_);
lean_inc(v___y_2797_);
lean_inc_ref(v___y_2796_);
lean_inc(v___x_2805_);
v___x_2806_ = l_Lean_Meta_instantiateForall(v___x_2805_, v___x_2791_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref(v___x_2806_);
v___x_2808_ = lean_array_get_size(v___x_2791_);
lean_inc(v___y_2799_);
lean_inc_ref(v___y_2798_);
lean_inc(v___y_2797_);
lean_inc_ref(v___y_2796_);
v___x_2809_ = l_Lean_Meta_Match_simpH_x3f(v_a_2807_, v___x_2808_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v_a_2810_; lean_object* v_a_2812_; 
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_a_2810_);
lean_dec_ref(v___x_2809_);
if (lean_obj_tag(v_a_2810_) == 1)
{
lean_object* v_val_2816_; lean_object* v___x_2817_; 
v_val_2816_ = lean_ctor_get(v_a_2810_, 0);
lean_inc(v_val_2816_);
lean_dec_ref(v_a_2810_);
v___x_2817_ = lean_array_push(v_b_2795_, v_val_2816_);
v_a_2812_ = v___x_2817_;
goto v___jp_2811_;
}
else
{
lean_dec(v_a_2810_);
v_a_2812_ = v_b_2795_;
goto v___jp_2811_;
}
v___jp_2811_:
{
size_t v___x_2813_; size_t v___x_2814_; 
v___x_2813_ = ((size_t)1ULL);
v___x_2814_ = lean_usize_add(v_i_2794_, v___x_2813_);
v_i_2794_ = v___x_2814_;
v_b_2795_ = v_a_2812_;
goto _start;
}
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec_ref(v_b_2795_);
v_a_2818_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2809_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2809_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec_ref(v_b_2795_);
v_a_2826_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2806_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2806_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5___boxed(lean_object* v___x_2834_, lean_object* v___x_2835_, lean_object* v_as_2836_, lean_object* v_sz_2837_, lean_object* v_i_2838_, lean_object* v_b_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
size_t v_sz_boxed_2845_; size_t v_i_boxed_2846_; lean_object* v_res_2847_; 
v_sz_boxed_2845_ = lean_unbox_usize(v_sz_2837_);
lean_dec(v_sz_2837_);
v_i_boxed_2846_ = lean_unbox_usize(v_i_2838_);
lean_dec(v_i_2838_);
v_res_2847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(v___x_2834_, v___x_2835_, v_as_2836_, v_sz_boxed_2845_, v_i_boxed_2846_, v_b_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
lean_dec_ref(v_as_2836_);
lean_dec_ref(v___x_2835_);
lean_dec_ref(v___x_2834_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(lean_object* v___x_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v___x_2851_, lean_object* v___x_2852_, lean_object* v___x_2853_, lean_object* v___x_2854_, lean_object* v___x_2855_, lean_object* v_rhsArgs_2856_, lean_object* v_a_2857_, lean_object* v_ys_2858_, uint8_t v___x_2859_, uint8_t v___x_2860_, uint8_t v___x_2861_, lean_object* v_matchDeclName_2862_, lean_object* v___x_2863_, lean_object* v___x_2864_, lean_object* v___x_2865_, lean_object* v___x_2866_, lean_object* v___x_2867_, lean_object* v_argMask_2868_, lean_object* v_a_2869_, lean_object* v_alts_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2876_ = lean_array_get_borrowed(v___x_2848_, v_alts_2870_, v_a_2849_);
v___x_2877_ = l_Lean_ConstantInfo_name(v_a_2850_);
v___x_2878_ = l_Lean_mkConst(v___x_2877_, v___x_2851_);
v___x_2879_ = l_Subarray_copy___redArg(v___x_2852_);
v___x_2880_ = lean_mk_empty_array_with_capacity(v___x_2853_);
v___x_2881_ = lean_array_push(v___x_2880_, v___x_2854_);
v___x_2882_ = l_Array_append___redArg(v___x_2879_, v___x_2881_);
lean_dec_ref(v___x_2881_);
lean_inc_ref(v___x_2882_);
v___x_2883_ = l_Array_append___redArg(v___x_2882_, v___x_2855_);
v___x_2884_ = l_Array_append___redArg(v___x_2883_, v_alts_2870_);
v___x_2885_ = l_Lean_mkAppN(v___x_2878_, v___x_2884_);
lean_dec_ref(v___x_2884_);
lean_inc(v___x_2876_);
v___x_2886_ = l_Lean_mkAppN(v___x_2876_, v_rhsArgs_2856_);
lean_inc(v___y_2874_);
lean_inc_ref(v___y_2873_);
lean_inc(v___y_2872_);
lean_inc_ref(v___y_2871_);
v___x_2887_ = l_Lean_Meta_mkEq(v___x_2885_, v___x_2886_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v___x_2889_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref(v___x_2887_);
lean_inc(v___y_2874_);
lean_inc_ref(v___y_2873_);
v___x_2889_ = l_Lean_mkArrowN(v_a_2857_, v_a_2888_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc(v_a_2890_);
lean_dec_ref(v___x_2889_);
v___x_2891_ = l_Array_append___redArg(v___x_2882_, v_ys_2858_);
v___x_2892_ = l_Array_append___redArg(v___x_2891_, v_alts_2870_);
v___x_2893_ = l_Lean_Meta_mkForallFVars(v___x_2892_, v_a_2890_, v___x_2859_, v___x_2860_, v___x_2860_, v___x_2861_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
lean_dec_ref(v___x_2892_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2895_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_a_2894_);
lean_dec_ref(v___x_2893_);
lean_inc(v___y_2874_);
lean_inc_ref(v___y_2873_);
lean_inc(v___y_2872_);
lean_inc_ref(v___y_2871_);
v___x_2895_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_2894_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2896_; lean_object* v___x_2897_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
lean_inc(v_a_2896_);
lean_dec_ref(v___x_2895_);
lean_inc(v___y_2874_);
lean_inc_ref(v___y_2873_);
lean_inc(v___x_2863_);
lean_inc(v_a_2896_);
v___x_2897_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2862_, v_a_2896_, v___x_2863_, v___x_2863_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_a_2898_);
lean_dec_ref(v___x_2897_);
lean_inc(v___x_2864_);
v___x_2899_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2864_);
lean_ctor_set(v___x_2899_, 1, v___x_2865_);
lean_ctor_set(v___x_2899_, 2, v_a_2896_);
v___x_2900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2864_);
lean_ctor_set(v___x_2900_, 1, v___x_2866_);
v___x_2901_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2899_);
lean_ctor_set(v___x_2901_, 1, v_a_2898_);
lean_ctor_set(v___x_2901_, 2, v___x_2900_);
v___x_2902_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2901_);
v___x_2903_ = l_Lean_addDecl(v___x_2902_, v___x_2859_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2912_; 
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2912_ == 0)
{
lean_object* v_unused_2913_; 
v_unused_2913_ = lean_ctor_get(v___x_2903_, 0);
lean_dec(v_unused_2913_);
v___x_2905_ = v___x_2903_;
v_isShared_2906_ = v_isSharedCheck_2912_;
goto v_resetjp_2904_;
}
else
{
lean_dec(v___x_2903_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2912_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2910_; 
v___x_2907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2867_);
lean_ctor_set(v___x_2907_, 1, v_argMask_2868_);
v___x_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2908_, 0, v_a_2869_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 0, v___x_2908_);
v___x_2910_ = v___x_2905_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2908_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec_ref(v_a_2869_);
lean_dec_ref(v_argMask_2868_);
lean_dec_ref(v___x_2867_);
v_a_2914_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2903_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2903_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_dec(v_a_2896_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec_ref(v_a_2869_);
lean_dec_ref(v_argMask_2868_);
lean_dec_ref(v___x_2867_);
lean_dec(v___x_2866_);
lean_dec(v___x_2865_);
lean_dec(v___x_2864_);
v_a_2922_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2897_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2897_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
else
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec_ref(v_a_2869_);
lean_dec_ref(v_argMask_2868_);
lean_dec_ref(v___x_2867_);
lean_dec(v___x_2866_);
lean_dec(v___x_2865_);
lean_dec(v___x_2864_);
lean_dec(v___x_2863_);
lean_dec(v_matchDeclName_2862_);
v_a_2930_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2895_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2895_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
else
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec_ref(v_a_2869_);
lean_dec_ref(v_argMask_2868_);
lean_dec_ref(v___x_2867_);
lean_dec(v___x_2866_);
lean_dec(v___x_2865_);
lean_dec(v___x_2864_);
lean_dec(v___x_2863_);
lean_dec(v_matchDeclName_2862_);
v_a_2938_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2940_ = v___x_2893_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2893_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2943_; 
if (v_isShared_2941_ == 0)
{
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2938_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
}
else
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2953_; 
lean_dec_ref(v___x_2882_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec_ref(v_a_2869_);
lean_dec_ref(v_argMask_2868_);
lean_dec_ref(v___x_2867_);
lean_dec(v___x_2866_);
lean_dec(v___x_2865_);
lean_dec(v___x_2864_);
lean_dec(v___x_2863_);
lean_dec(v_matchDeclName_2862_);
v_a_2946_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2948_ = v___x_2889_;
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2889_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2946_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
}
else
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
lean_dec_ref(v___x_2882_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec_ref(v_a_2869_);
lean_dec_ref(v_argMask_2868_);
lean_dec_ref(v___x_2867_);
lean_dec(v___x_2866_);
lean_dec(v___x_2865_);
lean_dec(v___x_2864_);
lean_dec(v___x_2863_);
lean_dec(v_matchDeclName_2862_);
v_a_2954_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2956_ = v___x_2887_;
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2887_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_2962_ = _args[0];
lean_object* v_a_2963_ = _args[1];
lean_object* v_a_2964_ = _args[2];
lean_object* v___x_2965_ = _args[3];
lean_object* v___x_2966_ = _args[4];
lean_object* v___x_2967_ = _args[5];
lean_object* v___x_2968_ = _args[6];
lean_object* v___x_2969_ = _args[7];
lean_object* v_rhsArgs_2970_ = _args[8];
lean_object* v_a_2971_ = _args[9];
lean_object* v_ys_2972_ = _args[10];
lean_object* v___x_2973_ = _args[11];
lean_object* v___x_2974_ = _args[12];
lean_object* v___x_2975_ = _args[13];
lean_object* v_matchDeclName_2976_ = _args[14];
lean_object* v___x_2977_ = _args[15];
lean_object* v___x_2978_ = _args[16];
lean_object* v___x_2979_ = _args[17];
lean_object* v___x_2980_ = _args[18];
lean_object* v___x_2981_ = _args[19];
lean_object* v_argMask_2982_ = _args[20];
lean_object* v_a_2983_ = _args[21];
lean_object* v_alts_2984_ = _args[22];
lean_object* v___y_2985_ = _args[23];
lean_object* v___y_2986_ = _args[24];
lean_object* v___y_2987_ = _args[25];
lean_object* v___y_2988_ = _args[26];
lean_object* v___y_2989_ = _args[27];
_start:
{
uint8_t v___x_18132__boxed_2990_; uint8_t v___x_18133__boxed_2991_; uint8_t v___x_18134__boxed_2992_; lean_object* v_res_2993_; 
v___x_18132__boxed_2990_ = lean_unbox(v___x_2973_);
v___x_18133__boxed_2991_ = lean_unbox(v___x_2974_);
v___x_18134__boxed_2992_ = lean_unbox(v___x_2975_);
v_res_2993_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(v___x_2962_, v_a_2963_, v_a_2964_, v___x_2965_, v___x_2966_, v___x_2967_, v___x_2968_, v___x_2969_, v_rhsArgs_2970_, v_a_2971_, v_ys_2972_, v___x_18132__boxed_2990_, v___x_18133__boxed_2991_, v___x_18134__boxed_2992_, v_matchDeclName_2976_, v___x_2977_, v___x_2978_, v___x_2979_, v___x_2980_, v___x_2981_, v_argMask_2982_, v_a_2983_, v_alts_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_);
lean_dec_ref(v_alts_2984_);
lean_dec_ref(v_ys_2972_);
lean_dec_ref(v_a_2971_);
lean_dec_ref(v_rhsArgs_2970_);
lean_dec_ref(v___x_2969_);
lean_dec(v___x_2967_);
lean_dec_ref(v_a_2964_);
lean_dec(v_a_2963_);
return v_res_2993_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2994_; lean_object* v_dummy_2995_; 
v___x_2994_ = lean_box(0);
v_dummy_2995_ = l_Lean_Expr_sort___override(v___x_2994_);
return v_dummy_2995_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_2999_ = lean_box(0);
v___x_3000_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__2));
v___x_3001_ = l_Lean_mkConst(v___x_3000_, v___x_2999_);
return v___x_3001_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3003_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__4));
v___x_3004_ = l_Lean_stringToMessageData(v___x_3003_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(lean_object* v___x_3005_, lean_object* v_overlaps_3006_, lean_object* v_a_3007_, lean_object* v_fst_3008_, lean_object* v___x_3009_, lean_object* v___x_3010_, lean_object* v___x_3011_, uint8_t v___x_3012_, lean_object* v___x_3013_, lean_object* v_a_3014_, lean_object* v___x_3015_, lean_object* v___x_3016_, lean_object* v___x_3017_, lean_object* v_matchDeclName_3018_, lean_object* v___x_3019_, lean_object* v___x_3020_, lean_object* v___x_3021_, lean_object* v___x_3022_, lean_object* v___x_3023_, lean_object* v_ys_3024_, lean_object* v___eqs_3025_, lean_object* v_rhsArgs_3026_, lean_object* v_argMask_3027_, lean_object* v_altResultType_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
lean_object* v_dummy_3034_; lean_object* v_nargs_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; size_t v_sz_3040_; size_t v___x_3041_; lean_object* v___x_3042_; 
v_dummy_3034_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_3035_ = l_Lean_Expr_getAppNumArgs(v_altResultType_3028_);
lean_inc(v_nargs_3035_);
v___x_3036_ = lean_mk_array(v_nargs_3035_, v_dummy_3034_);
v___x_3037_ = lean_nat_sub(v_nargs_3035_, v___x_3005_);
lean_dec(v_nargs_3035_);
v___x_3038_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_altResultType_3028_, v___x_3036_, v___x_3037_);
v___x_3039_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_3006_, v_a_3007_);
v_sz_3040_ = lean_array_size(v___x_3039_);
v___x_3041_ = ((size_t)0ULL);
lean_inc(v___y_3032_);
lean_inc_ref(v___y_3031_);
lean_inc(v___y_3030_);
lean_inc_ref(v___y_3029_);
lean_inc_ref(v___x_3009_);
v___x_3042_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(v_fst_3008_, v___x_3038_, v___x_3039_, v_sz_3040_, v___x_3041_, v___x_3009_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_);
lean_dec_ref(v___x_3039_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; uint8_t v___y_3049_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; uint8_t v___y_3097_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3043_);
lean_dec_ref(v___x_3042_);
v___x_3108_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_3109_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___redArg(v___x_3108_, v___y_3031_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; uint8_t v___x_3111_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
lean_inc(v_a_3110_);
lean_dec_ref(v___x_3109_);
v___x_3111_ = lean_unbox(v_a_3110_);
lean_dec(v_a_3110_);
if (v___x_3111_ == 0)
{
v___y_3100_ = v___y_3029_;
v___y_3101_ = v___y_3030_;
v___y_3102_ = v___y_3031_;
v___y_3103_ = v___y_3032_;
goto v___jp_3099_;
}
else
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3112_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_3043_);
v___x_3113_ = lean_array_to_list(v_a_3043_);
v___x_3114_ = lean_box(0);
v___x_3115_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_3113_, v___x_3114_);
v___x_3116_ = l_Lean_MessageData_ofList(v___x_3115_);
v___x_3117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3112_);
lean_ctor_set(v___x_3117_, 1, v___x_3116_);
v___x_3118_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(v___x_3108_, v___x_3117_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_dec_ref(v___x_3118_);
v___y_3100_ = v___y_3029_;
v___y_3101_ = v___y_3030_;
v___y_3102_ = v___y_3031_;
v___y_3103_ = v___y_3032_;
goto v___jp_3099_;
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec(v_a_3043_);
lean_dec_ref(v___x_3038_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec_ref(v_argMask_3027_);
lean_dec_ref(v_rhsArgs_3026_);
lean_dec_ref(v_ys_3024_);
lean_dec_ref(v___x_3022_);
lean_dec(v___x_3021_);
lean_dec(v___x_3020_);
lean_dec(v___x_3019_);
lean_dec(v_matchDeclName_3018_);
lean_dec_ref(v___x_3017_);
lean_dec_ref(v___x_3016_);
lean_dec(v___x_3015_);
lean_dec_ref(v_a_3014_);
lean_dec_ref(v___x_3013_);
lean_dec_ref(v___x_3011_);
lean_dec(v___x_3010_);
lean_dec_ref(v___x_3009_);
lean_dec(v_a_3007_);
lean_dec(v___x_3005_);
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3118_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3118_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
lean_dec(v_a_3043_);
lean_dec_ref(v___x_3038_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec_ref(v_argMask_3027_);
lean_dec_ref(v_rhsArgs_3026_);
lean_dec_ref(v_ys_3024_);
lean_dec_ref(v___x_3022_);
lean_dec(v___x_3021_);
lean_dec(v___x_3020_);
lean_dec(v___x_3019_);
lean_dec(v_matchDeclName_3018_);
lean_dec_ref(v___x_3017_);
lean_dec_ref(v___x_3016_);
lean_dec(v___x_3015_);
lean_dec_ref(v_a_3014_);
lean_dec_ref(v___x_3013_);
lean_dec_ref(v___x_3011_);
lean_dec(v___x_3010_);
lean_dec_ref(v___x_3009_);
lean_dec(v_a_3007_);
lean_dec(v___x_3005_);
v_a_3127_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_3109_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3109_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
v___jp_3044_:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; size_t v_sz_3057_; lean_object* v___x_3058_; 
v___x_3050_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
lean_inc_ref(v___x_3038_);
v___x_3051_ = l_Array_reverse___redArg(v___x_3038_);
v___x_3052_ = lean_array_get_size(v___x_3051_);
lean_inc(v___x_3010_);
v___x_3053_ = l_Array_toSubarray___redArg(v___x_3051_, v___x_3010_, v___x_3052_);
lean_inc_ref(v___x_3011_);
v___x_3054_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_3011_, v___x_3009_);
v___x_3055_ = l_Array_reverse___redArg(v___x_3054_);
v___x_3056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3050_);
lean_ctor_set(v___x_3056_, 1, v___x_3053_);
v_sz_3057_ = lean_array_size(v___x_3055_);
lean_inc(v___y_3048_);
lean_inc_ref(v___y_3045_);
lean_inc(v___y_3046_);
lean_inc_ref(v___y_3047_);
v___x_3058_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_3055_, v_sz_3057_, v___x_3041_, v___x_3056_, v___y_3047_, v___y_3046_, v___y_3045_, v___y_3048_);
lean_dec_ref(v___x_3055_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v_fst_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; uint8_t v___x_3063_; uint8_t v___x_3064_; lean_object* v___x_3065_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref(v___x_3058_);
v_fst_3060_ = lean_ctor_get(v_a_3059_, 0);
lean_inc(v_fst_3060_);
lean_dec(v_a_3059_);
v___x_3061_ = l_Subarray_copy___redArg(v___x_3011_);
lean_inc_ref(v___x_3061_);
v___x_3062_ = l_Array_append___redArg(v___x_3061_, v_ys_3024_);
v___x_3063_ = 0;
v___x_3064_ = 1;
v___x_3065_ = l_Lean_Meta_mkForallFVars(v___x_3062_, v_fst_3060_, v___x_3063_, v___x_3012_, v___x_3012_, v___x_3064_, v___y_3047_, v___y_3046_, v___y_3045_, v___y_3048_);
lean_dec_ref(v___x_3062_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v_a_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___f_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
lean_inc(v_a_3066_);
lean_dec_ref(v___x_3065_);
v___x_3067_ = lean_array_get_size(v_ys_3024_);
v___x_3068_ = lean_array_get_size(v_a_3043_);
v___x_3069_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3069_, 0, v___x_3067_);
lean_ctor_set(v___x_3069_, 1, v___x_3068_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*2, v___y_3049_);
v___x_3070_ = lean_box(v___x_3063_);
v___x_3071_ = lean_box(v___x_3012_);
v___x_3072_ = lean_box(v___x_3064_);
lean_inc_ref(v___x_3038_);
v___f_3073_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0___boxed), 28, 22);
lean_closure_set(v___f_3073_, 0, v___x_3013_);
lean_closure_set(v___f_3073_, 1, v_a_3007_);
lean_closure_set(v___f_3073_, 2, v_a_3014_);
lean_closure_set(v___f_3073_, 3, v___x_3015_);
lean_closure_set(v___f_3073_, 4, v___x_3016_);
lean_closure_set(v___f_3073_, 5, v___x_3005_);
lean_closure_set(v___f_3073_, 6, v___x_3017_);
lean_closure_set(v___f_3073_, 7, v___x_3038_);
lean_closure_set(v___f_3073_, 8, v_rhsArgs_3026_);
lean_closure_set(v___f_3073_, 9, v_a_3043_);
lean_closure_set(v___f_3073_, 10, v_ys_3024_);
lean_closure_set(v___f_3073_, 11, v___x_3070_);
lean_closure_set(v___f_3073_, 12, v___x_3071_);
lean_closure_set(v___f_3073_, 13, v___x_3072_);
lean_closure_set(v___f_3073_, 14, v_matchDeclName_3018_);
lean_closure_set(v___f_3073_, 15, v___x_3010_);
lean_closure_set(v___f_3073_, 16, v___x_3019_);
lean_closure_set(v___f_3073_, 17, v___x_3020_);
lean_closure_set(v___f_3073_, 18, v___x_3021_);
lean_closure_set(v___f_3073_, 19, v___x_3069_);
lean_closure_set(v___f_3073_, 20, v_argMask_3027_);
lean_closure_set(v___f_3073_, 21, v_a_3066_);
v___x_3074_ = l_Subarray_copy___redArg(v___x_3022_);
v___x_3075_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v___x_3023_, v___x_3061_, v___x_3038_, v___x_3074_, v___f_3073_, v___y_3047_, v___y_3046_, v___y_3045_, v___y_3048_);
return v___x_3075_;
}
else
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_dec_ref(v___x_3061_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3045_);
lean_dec(v_a_3043_);
lean_dec_ref(v___x_3038_);
lean_dec_ref(v_argMask_3027_);
lean_dec_ref(v_rhsArgs_3026_);
lean_dec_ref(v_ys_3024_);
lean_dec_ref(v___x_3022_);
lean_dec(v___x_3021_);
lean_dec(v___x_3020_);
lean_dec(v___x_3019_);
lean_dec(v_matchDeclName_3018_);
lean_dec_ref(v___x_3017_);
lean_dec_ref(v___x_3016_);
lean_dec(v___x_3015_);
lean_dec_ref(v_a_3014_);
lean_dec_ref(v___x_3013_);
lean_dec(v___x_3010_);
lean_dec(v_a_3007_);
lean_dec(v___x_3005_);
v_a_3076_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_3065_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3065_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3045_);
lean_dec(v_a_3043_);
lean_dec_ref(v___x_3038_);
lean_dec_ref(v_argMask_3027_);
lean_dec_ref(v_rhsArgs_3026_);
lean_dec_ref(v_ys_3024_);
lean_dec_ref(v___x_3022_);
lean_dec(v___x_3021_);
lean_dec(v___x_3020_);
lean_dec(v___x_3019_);
lean_dec(v_matchDeclName_3018_);
lean_dec_ref(v___x_3017_);
lean_dec_ref(v___x_3016_);
lean_dec(v___x_3015_);
lean_dec_ref(v_a_3014_);
lean_dec_ref(v___x_3013_);
lean_dec_ref(v___x_3011_);
lean_dec(v___x_3010_);
lean_dec(v_a_3007_);
lean_dec(v___x_3005_);
v_a_3084_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3058_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3058_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
v___jp_3092_:
{
if (v___y_3097_ == 0)
{
v___y_3045_ = v___y_3093_;
v___y_3046_ = v___y_3094_;
v___y_3047_ = v___y_3095_;
v___y_3048_ = v___y_3096_;
v___y_3049_ = v___y_3097_;
goto v___jp_3044_;
}
else
{
uint8_t v___x_3098_; 
v___x_3098_ = lean_nat_dec_eq(v___x_3023_, v___x_3010_);
v___y_3045_ = v___y_3093_;
v___y_3046_ = v___y_3094_;
v___y_3047_ = v___y_3095_;
v___y_3048_ = v___y_3096_;
v___y_3049_ = v___x_3098_;
goto v___jp_3044_;
}
}
v___jp_3099_:
{
lean_object* v___x_3104_; uint8_t v___x_3105_; 
v___x_3104_ = lean_array_get_size(v_ys_3024_);
v___x_3105_ = lean_nat_dec_eq(v___x_3104_, v___x_3010_);
if (v___x_3105_ == 0)
{
v___y_3093_ = v___y_3102_;
v___y_3094_ = v___y_3101_;
v___y_3095_ = v___y_3100_;
v___y_3096_ = v___y_3103_;
v___y_3097_ = v___x_3105_;
goto v___jp_3092_;
}
else
{
lean_object* v___x_3106_; uint8_t v___x_3107_; 
v___x_3106_ = lean_array_get_size(v_a_3043_);
v___x_3107_ = lean_nat_dec_eq(v___x_3106_, v___x_3010_);
v___y_3093_ = v___y_3102_;
v___y_3094_ = v___y_3101_;
v___y_3095_ = v___y_3100_;
v___y_3096_ = v___y_3103_;
v___y_3097_ = v___x_3107_;
goto v___jp_3092_;
}
}
}
else
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3142_; 
lean_dec_ref(v___x_3038_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec_ref(v_argMask_3027_);
lean_dec_ref(v_rhsArgs_3026_);
lean_dec_ref(v_ys_3024_);
lean_dec_ref(v___x_3022_);
lean_dec(v___x_3021_);
lean_dec(v___x_3020_);
lean_dec(v___x_3019_);
lean_dec(v_matchDeclName_3018_);
lean_dec_ref(v___x_3017_);
lean_dec_ref(v___x_3016_);
lean_dec(v___x_3015_);
lean_dec_ref(v_a_3014_);
lean_dec_ref(v___x_3013_);
lean_dec_ref(v___x_3011_);
lean_dec(v___x_3010_);
lean_dec_ref(v___x_3009_);
lean_dec(v_a_3007_);
lean_dec(v___x_3005_);
v_a_3135_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3137_ = v___x_3042_;
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v___x_3042_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3135_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_3143_ = _args[0];
lean_object* v_overlaps_3144_ = _args[1];
lean_object* v_a_3145_ = _args[2];
lean_object* v_fst_3146_ = _args[3];
lean_object* v___x_3147_ = _args[4];
lean_object* v___x_3148_ = _args[5];
lean_object* v___x_3149_ = _args[6];
lean_object* v___x_3150_ = _args[7];
lean_object* v___x_3151_ = _args[8];
lean_object* v_a_3152_ = _args[9];
lean_object* v___x_3153_ = _args[10];
lean_object* v___x_3154_ = _args[11];
lean_object* v___x_3155_ = _args[12];
lean_object* v_matchDeclName_3156_ = _args[13];
lean_object* v___x_3157_ = _args[14];
lean_object* v___x_3158_ = _args[15];
lean_object* v___x_3159_ = _args[16];
lean_object* v___x_3160_ = _args[17];
lean_object* v___x_3161_ = _args[18];
lean_object* v_ys_3162_ = _args[19];
lean_object* v___eqs_3163_ = _args[20];
lean_object* v_rhsArgs_3164_ = _args[21];
lean_object* v_argMask_3165_ = _args[22];
lean_object* v_altResultType_3166_ = _args[23];
lean_object* v___y_3167_ = _args[24];
lean_object* v___y_3168_ = _args[25];
lean_object* v___y_3169_ = _args[26];
lean_object* v___y_3170_ = _args[27];
lean_object* v___y_3171_ = _args[28];
_start:
{
uint8_t v___x_18394__boxed_3172_; lean_object* v_res_3173_; 
v___x_18394__boxed_3172_ = lean_unbox(v___x_3150_);
v_res_3173_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(v___x_3143_, v_overlaps_3144_, v_a_3145_, v_fst_3146_, v___x_3147_, v___x_3148_, v___x_3149_, v___x_18394__boxed_3172_, v___x_3151_, v_a_3152_, v___x_3153_, v___x_3154_, v___x_3155_, v_matchDeclName_3156_, v___x_3157_, v___x_3158_, v___x_3159_, v___x_3160_, v___x_3161_, v_ys_3162_, v___eqs_3163_, v_rhsArgs_3164_, v_argMask_3165_, v_altResultType_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
lean_dec_ref(v___eqs_3163_);
lean_dec(v___x_3161_);
lean_dec(v_fst_3146_);
lean_dec_ref(v_overlaps_3144_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(lean_object* v_upperBound_3174_, lean_object* v_val_3175_, lean_object* v_baseName_3176_, lean_object* v___x_3177_, lean_object* v_a_3178_, lean_object* v___x_3179_, lean_object* v___x_3180_, lean_object* v___x_3181_, lean_object* v_matchDeclName_3182_, lean_object* v___x_3183_, lean_object* v___x_3184_, lean_object* v___x_3185_, lean_object* v_a_3186_, lean_object* v_b_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_){
_start:
{
uint8_t v___x_3193_; 
v___x_3193_ = lean_nat_dec_lt(v_a_3186_, v_upperBound_3174_);
if (v___x_3193_ == 0)
{
lean_object* v___x_3194_; 
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v_a_3186_);
lean_dec(v___x_3185_);
lean_dec_ref(v___x_3184_);
lean_dec(v___x_3183_);
lean_dec(v_matchDeclName_3182_);
lean_dec_ref(v___x_3181_);
lean_dec_ref(v___x_3180_);
lean_dec(v___x_3179_);
lean_dec_ref(v_a_3178_);
lean_dec_ref(v___x_3177_);
lean_dec(v_baseName_3176_);
lean_dec_ref(v_val_3175_);
v___x_3194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3194_, 0, v_b_3187_);
return v___x_3194_;
}
else
{
lean_object* v_snd_3195_; lean_object* v_snd_3196_; lean_object* v_snd_3197_; lean_object* v_fst_3198_; lean_object* v_fst_3199_; lean_object* v_fst_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3283_; 
v_snd_3195_ = lean_ctor_get(v_b_3187_, 1);
lean_inc(v_snd_3195_);
v_snd_3196_ = lean_ctor_get(v_snd_3195_, 1);
lean_inc(v_snd_3196_);
v_snd_3197_ = lean_ctor_get(v_snd_3196_, 1);
lean_inc(v_snd_3197_);
v_fst_3198_ = lean_ctor_get(v_b_3187_, 0);
lean_inc(v_fst_3198_);
lean_dec_ref(v_b_3187_);
v_fst_3199_ = lean_ctor_get(v_snd_3195_, 0);
lean_inc(v_fst_3199_);
lean_dec(v_snd_3195_);
v_fst_3200_ = lean_ctor_get(v_snd_3196_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v_snd_3196_);
if (v_isSharedCheck_3283_ == 0)
{
lean_object* v_unused_3284_; 
v_unused_3284_ = lean_ctor_get(v_snd_3196_, 1);
lean_dec(v_unused_3284_);
v___x_3202_ = v_snd_3196_;
v_isShared_3203_ = v_isSharedCheck_3283_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_fst_3200_);
lean_dec(v_snd_3196_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3283_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v_fst_3204_; lean_object* v_snd_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3282_; 
v_fst_3204_ = lean_ctor_get(v_snd_3197_, 0);
v_snd_3205_ = lean_ctor_get(v_snd_3197_, 1);
v_isSharedCheck_3282_ = !lean_is_exclusive(v_snd_3197_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3207_ = v_snd_3197_;
v_isShared_3208_ = v_isSharedCheck_3282_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_snd_3205_);
lean_inc(v_fst_3204_);
lean_dec(v_snd_3197_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3282_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v_altInfos_3209_; lean_object* v_overlaps_3210_; lean_object* v_start_3211_; lean_object* v_stop_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___f_3224_; lean_object* v___x_3225_; lean_object* v___y_3227_; lean_object* v___x_3278_; uint8_t v___x_3279_; 
v_altInfos_3209_ = lean_ctor_get(v_val_3175_, 2);
v_overlaps_3210_ = lean_ctor_get(v_val_3175_, 5);
v_start_3211_ = lean_ctor_get(v___x_3184_, 1);
v_stop_3212_ = lean_ctor_get(v___x_3184_, 2);
v___x_3213_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_3214_ = l_Lean_instInhabitedExpr;
v___x_3215_ = lean_unsigned_to_nat(0u);
v___x_3216_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_3217_ = lean_box(0);
v___x_3218_ = lean_unsigned_to_nat(1u);
v___x_3219_ = lean_array_get_borrowed(v___x_3213_, v_altInfos_3209_, v_a_3186_);
v___x_3220_ = l_Lean_Meta_eqnThmSuffixBase;
lean_inc(v_baseName_3176_);
v___x_3221_ = l_Lean_Name_str___override(v_baseName_3176_, v___x_3220_);
lean_inc(v_fst_3200_);
v___x_3222_ = lean_name_append_index_after(v___x_3221_, v_fst_3200_);
v___x_3223_ = lean_box(v___x_3193_);
lean_inc(v___x_3185_);
lean_inc_ref(v___x_3184_);
lean_inc(v___x_3183_);
lean_inc(v___x_3222_);
lean_inc(v_matchDeclName_3182_);
lean_inc_ref(v___x_3181_);
lean_inc_ref(v___x_3180_);
lean_inc(v___x_3179_);
lean_inc_ref(v_a_3178_);
lean_inc_ref(v___x_3177_);
lean_inc(v_fst_3199_);
lean_inc(v_a_3186_);
lean_inc_ref(v_overlaps_3210_);
v___f_3224_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed), 29, 19);
lean_closure_set(v___f_3224_, 0, v___x_3218_);
lean_closure_set(v___f_3224_, 1, v_overlaps_3210_);
lean_closure_set(v___f_3224_, 2, v_a_3186_);
lean_closure_set(v___f_3224_, 3, v_fst_3199_);
lean_closure_set(v___f_3224_, 4, v___x_3216_);
lean_closure_set(v___f_3224_, 5, v___x_3215_);
lean_closure_set(v___f_3224_, 6, v___x_3177_);
lean_closure_set(v___f_3224_, 7, v___x_3223_);
lean_closure_set(v___f_3224_, 8, v___x_3214_);
lean_closure_set(v___f_3224_, 9, v_a_3178_);
lean_closure_set(v___f_3224_, 10, v___x_3179_);
lean_closure_set(v___f_3224_, 11, v___x_3180_);
lean_closure_set(v___f_3224_, 12, v___x_3181_);
lean_closure_set(v___f_3224_, 13, v_matchDeclName_3182_);
lean_closure_set(v___f_3224_, 14, v___x_3222_);
lean_closure_set(v___f_3224_, 15, v___x_3183_);
lean_closure_set(v___f_3224_, 16, v___x_3217_);
lean_closure_set(v___f_3224_, 17, v___x_3184_);
lean_closure_set(v___f_3224_, 18, v___x_3185_);
v___x_3225_ = lean_array_push(v_fst_3198_, v___x_3222_);
v___x_3278_ = lean_nat_sub(v_stop_3212_, v_start_3211_);
v___x_3279_ = lean_nat_dec_lt(v_a_3186_, v___x_3278_);
lean_dec(v___x_3278_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3280_; 
v___x_3280_ = l_outOfBounds___redArg(v___x_3214_);
v___y_3227_ = v___x_3280_;
goto v___jp_3226_;
}
else
{
lean_object* v___x_3281_; 
v___x_3281_ = l_Subarray_get___redArg(v___x_3184_, v_a_3186_);
v___y_3227_ = v___x_3281_;
goto v___jp_3226_;
}
v___jp_3226_:
{
lean_object* v___x_3228_; 
lean_inc(v___y_3191_);
lean_inc_ref(v___y_3190_);
lean_inc(v___y_3189_);
lean_inc_ref(v___y_3188_);
v___x_3228_ = lean_infer_type(v___y_3227_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3229_; lean_object* v___x_3230_; 
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_a_3229_);
lean_dec_ref(v___x_3228_);
lean_inc(v___y_3191_);
lean_inc_ref(v___y_3190_);
lean_inc(v___y_3189_);
lean_inc_ref(v___y_3188_);
lean_inc(v___x_3185_);
lean_inc(v___x_3219_);
v___x_3230_ = l_Lean_Meta_Match_forallAltTelescope___redArg(v_a_3229_, v___x_3219_, v___x_3185_, v___f_3224_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; lean_object* v_snd_3232_; lean_object* v_fst_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3261_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3231_);
lean_dec_ref(v___x_3230_);
v_snd_3232_ = lean_ctor_get(v_a_3231_, 1);
v_fst_3233_ = lean_ctor_get(v_a_3231_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v_a_3231_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3235_ = v_a_3231_;
v_isShared_3236_ = v_isSharedCheck_3261_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_snd_3232_);
lean_inc(v_fst_3233_);
lean_dec(v_a_3231_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3261_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v_fst_3237_; lean_object* v_snd_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3260_; 
v_fst_3237_ = lean_ctor_get(v_snd_3232_, 0);
v_snd_3238_ = lean_ctor_get(v_snd_3232_, 1);
v_isSharedCheck_3260_ = !lean_is_exclusive(v_snd_3232_);
if (v_isSharedCheck_3260_ == 0)
{
v___x_3240_ = v_snd_3232_;
v_isShared_3241_ = v_isSharedCheck_3260_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_snd_3238_);
lean_inc(v_fst_3237_);
lean_dec(v_snd_3232_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3260_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3247_; 
v___x_3242_ = lean_array_push(v_fst_3199_, v_fst_3233_);
v___x_3243_ = lean_array_push(v_fst_3204_, v_fst_3237_);
v___x_3244_ = lean_array_push(v_snd_3205_, v_snd_3238_);
v___x_3245_ = lean_nat_add(v_fst_3200_, v___x_3218_);
lean_dec(v_fst_3200_);
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 1, v___x_3244_);
lean_ctor_set(v___x_3240_, 0, v___x_3243_);
v___x_3247_ = v___x_3240_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v___x_3243_);
lean_ctor_set(v_reuseFailAlloc_3259_, 1, v___x_3244_);
v___x_3247_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
lean_object* v___x_3249_; 
if (v_isShared_3236_ == 0)
{
lean_ctor_set(v___x_3235_, 1, v___x_3247_);
lean_ctor_set(v___x_3235_, 0, v___x_3245_);
v___x_3249_ = v___x_3235_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3245_);
lean_ctor_set(v_reuseFailAlloc_3258_, 1, v___x_3247_);
v___x_3249_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
lean_object* v___x_3251_; 
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 1, v___x_3249_);
lean_ctor_set(v___x_3207_, 0, v___x_3242_);
v___x_3251_ = v___x_3207_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v___x_3242_);
lean_ctor_set(v_reuseFailAlloc_3257_, 1, v___x_3249_);
v___x_3251_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
lean_object* v___x_3253_; 
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 1, v___x_3251_);
lean_ctor_set(v___x_3202_, 0, v___x_3225_);
v___x_3253_ = v___x_3202_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3225_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v___x_3251_);
v___x_3253_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
lean_object* v___x_3254_; 
v___x_3254_ = lean_nat_add(v_a_3186_, v___x_3218_);
lean_dec(v_a_3186_);
v_a_3186_ = v___x_3254_;
v_b_3187_ = v___x_3253_;
goto _start;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3269_; 
lean_dec_ref(v___x_3225_);
lean_del_object(v___x_3207_);
lean_dec(v_snd_3205_);
lean_dec(v_fst_3204_);
lean_del_object(v___x_3202_);
lean_dec(v_fst_3200_);
lean_dec(v_fst_3199_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v_a_3186_);
lean_dec(v___x_3185_);
lean_dec_ref(v___x_3184_);
lean_dec(v___x_3183_);
lean_dec(v_matchDeclName_3182_);
lean_dec_ref(v___x_3181_);
lean_dec_ref(v___x_3180_);
lean_dec(v___x_3179_);
lean_dec_ref(v_a_3178_);
lean_dec_ref(v___x_3177_);
lean_dec(v_baseName_3176_);
lean_dec_ref(v_val_3175_);
v_a_3262_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3264_ = v___x_3230_;
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3230_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3267_; 
if (v_isShared_3265_ == 0)
{
v___x_3267_ = v___x_3264_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3262_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
}
}
else
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
lean_dec_ref(v___x_3225_);
lean_dec_ref(v___f_3224_);
lean_del_object(v___x_3207_);
lean_dec(v_snd_3205_);
lean_dec(v_fst_3204_);
lean_del_object(v___x_3202_);
lean_dec(v_fst_3200_);
lean_dec(v_fst_3199_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v_a_3186_);
lean_dec(v___x_3185_);
lean_dec_ref(v___x_3184_);
lean_dec(v___x_3183_);
lean_dec(v_matchDeclName_3182_);
lean_dec_ref(v___x_3181_);
lean_dec_ref(v___x_3180_);
lean_dec(v___x_3179_);
lean_dec_ref(v_a_3178_);
lean_dec_ref(v___x_3177_);
lean_dec(v_baseName_3176_);
lean_dec_ref(v_val_3175_);
v_a_3270_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3272_ = v___x_3228_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3228_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3275_; 
if (v_isShared_3273_ == 0)
{
v___x_3275_ = v___x_3272_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_3285_ = _args[0];
lean_object* v_val_3286_ = _args[1];
lean_object* v_baseName_3287_ = _args[2];
lean_object* v___x_3288_ = _args[3];
lean_object* v_a_3289_ = _args[4];
lean_object* v___x_3290_ = _args[5];
lean_object* v___x_3291_ = _args[6];
lean_object* v___x_3292_ = _args[7];
lean_object* v_matchDeclName_3293_ = _args[8];
lean_object* v___x_3294_ = _args[9];
lean_object* v___x_3295_ = _args[10];
lean_object* v___x_3296_ = _args[11];
lean_object* v_a_3297_ = _args[12];
lean_object* v_b_3298_ = _args[13];
lean_object* v___y_3299_ = _args[14];
lean_object* v___y_3300_ = _args[15];
lean_object* v___y_3301_ = _args[16];
lean_object* v___y_3302_ = _args[17];
lean_object* v___y_3303_ = _args[18];
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3285_, v_val_3286_, v_baseName_3287_, v___x_3288_, v_a_3289_, v___x_3290_, v___x_3291_, v___x_3292_, v_matchDeclName_3293_, v___x_3294_, v___x_3295_, v___x_3296_, v_a_3297_, v_b_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
lean_dec(v_upperBound_3285_);
return v_res_3304_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3308_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__2));
v___x_3309_ = lean_unsigned_to_nat(6u);
v___x_3310_ = lean_unsigned_to_nat(232u);
v___x_3311_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__1));
v___x_3312_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_3313_ = l_mkPanicMessageWithDecl(v___x_3312_, v___x_3311_, v___x_3310_, v___x_3309_, v___x_3308_);
return v___x_3313_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__4(void){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3314_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___x_3315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3314_);
lean_ctor_set(v___x_3315_, 1, v___x_3314_);
return v___x_3315_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3316_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__4, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__4_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__4);
v___x_3317_ = lean_unsigned_to_nat(1u);
v___x_3318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3317_);
lean_ctor_set(v___x_3318_, 1, v___x_3316_);
return v___x_3318_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__6(void){
_start:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3319_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__5, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__5_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__5);
v___x_3320_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___x_3321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3320_);
lean_ctor_set(v___x_3321_, 1, v___x_3319_);
return v___x_3321_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__7(void){
_start:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3322_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__6, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__6_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__6);
v___x_3323_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___x_3324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
lean_ctor_set(v___x_3324_, 1, v___x_3322_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(lean_object* v_splitterName_3326_, lean_object* v_matchDeclName_3327_, lean_object* v_numParams_3328_, lean_object* v_val_3329_, lean_object* v___x_3330_, lean_object* v_numDiscrs_3331_, lean_object* v_baseName_3332_, lean_object* v_a_3333_, lean_object* v___x_3334_, lean_object* v___x_3335_, lean_object* v___x_3336_, lean_object* v_uElimPos_x3f_3337_, lean_object* v_discrInfos_3338_, lean_object* v_overlaps_3339_, lean_object* v___f_3340_, lean_object* v___x_3341_, lean_object* v_altInfos_3342_, lean_object* v_xs_3343_, lean_object* v___matchResultType_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; uint8_t v___y_3362_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v_lower_3370_; lean_object* v_upper_3371_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; uint8_t v___x_3426_; 
v___x_3364_ = lean_box(0);
v___x_3365_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3328_);
lean_inc_ref(v_xs_3343_);
v___x_3366_ = l_Array_toSubarray___redArg(v_xs_3343_, v___x_3365_, v_numParams_3328_);
v___x_3367_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_3329_);
v___x_3368_ = lean_array_get(v___x_3330_, v_xs_3343_, v___x_3367_);
lean_dec(v___x_3367_);
v___x_3423_ = lean_array_get_size(v_xs_3343_);
v___x_3424_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_3329_);
v___x_3425_ = lean_nat_sub(v___x_3423_, v___x_3424_);
lean_dec(v___x_3424_);
v___x_3426_ = lean_nat_dec_le(v___x_3425_, v___x_3365_);
if (v___x_3426_ == 0)
{
v_lower_3370_ = v___x_3425_;
v_upper_3371_ = v___x_3423_;
goto v___jp_3369_;
}
else
{
lean_dec(v___x_3425_);
v_lower_3370_ = v___x_3365_;
v_upper_3371_ = v___x_3423_;
goto v___jp_3369_;
}
v___jp_3350_:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3351_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3);
v___x_3352_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v___x_3351_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
return v___x_3352_;
}
v___jp_3353_:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3356_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3356_, 0, v___y_3354_);
lean_ctor_set(v___x_3356_, 1, v_splitterName_3326_);
lean_ctor_set(v___x_3356_, 2, v___y_3355_);
v___x_3357_ = l_Lean_Meta_Match_registerMatchEqns___redArg(v_matchDeclName_3327_, v___x_3356_, v___y_3348_);
lean_dec(v___y_3348_);
return v___x_3357_;
}
v___jp_3358_:
{
lean_object* v___x_3363_; 
lean_inc(v___y_3348_);
lean_inc(v_matchDeclName_3327_);
v___x_3363_ = l_Lean_Meta_Match_withMkMatcherInput___redArg(v_matchDeclName_3327_, v___y_3362_, v___y_3361_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_dec_ref(v___x_3363_);
v___y_3354_ = v___y_3359_;
v___y_3355_ = v___y_3360_;
goto v___jp_3353_;
}
else
{
lean_dec_ref(v___y_3360_);
lean_dec(v___y_3359_);
lean_dec(v___y_3348_);
lean_dec(v_matchDeclName_3327_);
lean_dec(v_splitterName_3326_);
return v___x_3363_;
}
}
v___jp_3369_:
{
lean_object* v___x_3372_; lean_object* v_start_3373_; lean_object* v_stop_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
lean_inc_ref(v_xs_3343_);
v___x_3372_ = l_Array_toSubarray___redArg(v_xs_3343_, v_lower_3370_, v_upper_3371_);
v_start_3373_ = lean_ctor_get(v___x_3372_, 1);
lean_inc(v_start_3373_);
v_stop_3374_ = lean_ctor_get(v___x_3372_, 2);
lean_inc(v_stop_3374_);
v___x_3375_ = lean_unsigned_to_nat(1u);
v___x_3376_ = lean_nat_add(v_numParams_3328_, v___x_3375_);
v___x_3377_ = lean_nat_add(v___x_3376_, v_numDiscrs_3331_);
v___x_3378_ = lean_nat_sub(v_stop_3374_, v_start_3373_);
lean_dec(v_start_3373_);
lean_dec(v_stop_3374_);
v___x_3379_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__7, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__7_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__7);
v___x_3380_ = l_Array_toSubarray___redArg(v_xs_3343_, v___x_3376_, v___x_3377_);
lean_inc(v___y_3348_);
lean_inc_ref(v___y_3347_);
lean_inc(v___y_3346_);
lean_inc_ref(v___y_3345_);
lean_inc(v___x_3335_);
lean_inc(v_matchDeclName_3327_);
lean_inc(v___x_3334_);
v___x_3381_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v___x_3378_, v_val_3329_, v_baseName_3332_, v___x_3380_, v_a_3333_, v___x_3334_, v___x_3366_, v___x_3368_, v_matchDeclName_3327_, v___x_3335_, v___x_3372_, v___x_3336_, v___x_3365_, v___x_3379_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
lean_dec(v___x_3378_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v_snd_3383_; lean_object* v_snd_3384_; lean_object* v_snd_3385_; lean_object* v_fst_3386_; lean_object* v_fst_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3413_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3382_);
lean_dec_ref(v___x_3381_);
v_snd_3383_ = lean_ctor_get(v_a_3382_, 1);
v_snd_3384_ = lean_ctor_get(v_snd_3383_, 1);
v_snd_3385_ = lean_ctor_get(v_snd_3384_, 1);
lean_inc(v_snd_3385_);
v_fst_3386_ = lean_ctor_get(v_a_3382_, 0);
lean_inc(v_fst_3386_);
lean_dec(v_a_3382_);
v_fst_3387_ = lean_ctor_get(v_snd_3385_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v_snd_3385_);
if (v_isSharedCheck_3413_ == 0)
{
lean_object* v_unused_3414_; 
v_unused_3414_ = lean_ctor_get(v_snd_3385_, 1);
lean_dec(v_unused_3414_);
v___x_3389_ = v_snd_3385_;
v_isShared_3390_ = v_isSharedCheck_3413_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_fst_3387_);
lean_dec(v_snd_3385_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3413_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3391_; uint8_t v___x_3392_; 
lean_inc_ref(v_overlaps_3339_);
lean_inc(v_fst_3387_);
v___x_3391_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3391_, 0, v_numParams_3328_);
lean_ctor_set(v___x_3391_, 1, v_numDiscrs_3331_);
lean_ctor_set(v___x_3391_, 2, v_fst_3387_);
lean_ctor_set(v___x_3391_, 3, v_uElimPos_x3f_3337_);
lean_ctor_set(v___x_3391_, 4, v_discrInfos_3338_);
lean_ctor_set(v___x_3391_, 5, v_overlaps_3339_);
v___x_3392_ = l_Lean_Meta_Match_Overlaps_isEmpty(v_overlaps_3339_);
lean_dec_ref(v_overlaps_3339_);
if (v___x_3392_ == 0)
{
uint8_t v___x_3393_; 
lean_del_object(v___x_3389_);
lean_dec(v_fst_3387_);
lean_dec_ref(v___x_3341_);
lean_dec(v___x_3335_);
lean_dec(v___x_3334_);
v___x_3393_ = 1;
v___y_3359_ = v_fst_3386_;
v___y_3360_ = v___x_3391_;
v___y_3361_ = v___f_3340_;
v___y_3362_ = v___x_3393_;
goto v___jp_3358_;
}
else
{
lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3394_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__8));
v___x_3395_ = lean_find_expr(v___x_3394_, v___x_3341_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v___x_3396_; lean_object* v___x_3397_; uint8_t v___x_3398_; 
lean_dec_ref(v___f_3340_);
v___x_3396_ = lean_array_get_size(v_altInfos_3342_);
v___x_3397_ = lean_array_get_size(v_fst_3387_);
v___x_3398_ = lean_nat_dec_eq(v___x_3396_, v___x_3397_);
if (v___x_3398_ == 0)
{
lean_dec_ref(v___x_3391_);
lean_del_object(v___x_3389_);
lean_dec(v_fst_3387_);
lean_dec(v_fst_3386_);
lean_dec_ref(v___x_3341_);
lean_dec(v___x_3335_);
lean_dec(v___x_3334_);
lean_dec(v_matchDeclName_3327_);
lean_dec(v_splitterName_3326_);
goto v___jp_3350_;
}
else
{
uint8_t v___x_3399_; 
v___x_3399_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_altInfos_3342_, v_fst_3387_, v___x_3396_);
lean_dec(v_fst_3387_);
if (v___x_3399_ == 0)
{
lean_dec_ref(v___x_3391_);
lean_del_object(v___x_3389_);
lean_dec(v_fst_3386_);
lean_dec_ref(v___x_3341_);
lean_dec(v___x_3335_);
lean_dec(v___x_3334_);
lean_dec(v_matchDeclName_3327_);
lean_dec(v_splitterName_3326_);
goto v___jp_3350_;
}
else
{
uint8_t v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; uint8_t v___x_3404_; lean_object* v___x_3406_; 
v___x_3400_ = 0;
lean_inc(v_splitterName_3326_);
v___x_3401_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3401_, 0, v_splitterName_3326_);
lean_ctor_set(v___x_3401_, 1, v___x_3335_);
lean_ctor_set(v___x_3401_, 2, v___x_3341_);
lean_inc(v_matchDeclName_3327_);
v___x_3402_ = l_Lean_mkConst(v_matchDeclName_3327_, v___x_3334_);
v___x_3403_ = lean_box(1);
v___x_3404_ = 1;
lean_inc(v_splitterName_3326_);
if (v_isShared_3390_ == 0)
{
lean_ctor_set_tag(v___x_3389_, 1);
lean_ctor_set(v___x_3389_, 1, v___x_3364_);
lean_ctor_set(v___x_3389_, 0, v_splitterName_3326_);
v___x_3406_ = v___x_3389_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_splitterName_3326_);
lean_ctor_set(v_reuseFailAlloc_3412_, 1, v___x_3364_);
v___x_3406_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
v___x_3407_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3407_, 0, v___x_3401_);
lean_ctor_set(v___x_3407_, 1, v___x_3402_);
lean_ctor_set(v___x_3407_, 2, v___x_3403_);
lean_ctor_set(v___x_3407_, 3, v___x_3406_);
lean_ctor_set_uint8(v___x_3407_, sizeof(void*)*4, v___x_3404_);
v___x_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3407_);
lean_inc(v___y_3348_);
lean_inc_ref(v___y_3347_);
v___x_3409_ = l_Lean_addAndCompile(v___x_3408_, v___x_3400_, v___y_3347_, v___y_3348_);
if (lean_obj_tag(v___x_3409_) == 0)
{
uint8_t v___x_3410_; lean_object* v___x_3411_; 
lean_dec_ref(v___x_3409_);
v___x_3410_ = 0;
lean_inc(v_splitterName_3326_);
v___x_3411_ = l_Lean_Meta_setInlineAttribute(v_splitterName_3326_, v___x_3410_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_dec_ref(v___x_3411_);
v___y_3354_ = v_fst_3386_;
v___y_3355_ = v___x_3391_;
goto v___jp_3353_;
}
else
{
lean_dec_ref(v___x_3391_);
lean_dec(v_fst_3386_);
lean_dec(v___y_3348_);
lean_dec(v_matchDeclName_3327_);
lean_dec(v_splitterName_3326_);
return v___x_3411_;
}
}
else
{
lean_dec_ref(v___x_3391_);
lean_dec(v_fst_3386_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec(v_matchDeclName_3327_);
lean_dec(v_splitterName_3326_);
return v___x_3409_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3395_);
lean_del_object(v___x_3389_);
lean_dec(v_fst_3387_);
lean_dec_ref(v___x_3341_);
lean_dec(v___x_3335_);
lean_dec(v___x_3334_);
v___y_3359_ = v_fst_3386_;
v___y_3360_ = v___x_3391_;
v___y_3361_ = v___f_3340_;
v___y_3362_ = v___x_3392_;
goto v___jp_3358_;
}
}
}
}
else
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec_ref(v___x_3341_);
lean_dec_ref(v___f_3340_);
lean_dec_ref(v_overlaps_3339_);
lean_dec_ref(v_discrInfos_3338_);
lean_dec(v_uElimPos_x3f_3337_);
lean_dec(v___x_3335_);
lean_dec(v___x_3334_);
lean_dec(v_numDiscrs_3331_);
lean_dec(v_numParams_3328_);
lean_dec(v_matchDeclName_3327_);
lean_dec(v_splitterName_3326_);
v_a_3415_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___x_3381_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3381_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed(lean_object** _args){
lean_object* v_splitterName_3427_ = _args[0];
lean_object* v_matchDeclName_3428_ = _args[1];
lean_object* v_numParams_3429_ = _args[2];
lean_object* v_val_3430_ = _args[3];
lean_object* v___x_3431_ = _args[4];
lean_object* v_numDiscrs_3432_ = _args[5];
lean_object* v_baseName_3433_ = _args[6];
lean_object* v_a_3434_ = _args[7];
lean_object* v___x_3435_ = _args[8];
lean_object* v___x_3436_ = _args[9];
lean_object* v___x_3437_ = _args[10];
lean_object* v_uElimPos_x3f_3438_ = _args[11];
lean_object* v_discrInfos_3439_ = _args[12];
lean_object* v_overlaps_3440_ = _args[13];
lean_object* v___f_3441_ = _args[14];
lean_object* v___x_3442_ = _args[15];
lean_object* v_altInfos_3443_ = _args[16];
lean_object* v_xs_3444_ = _args[17];
lean_object* v___matchResultType_3445_ = _args[18];
lean_object* v___y_3446_ = _args[19];
lean_object* v___y_3447_ = _args[20];
lean_object* v___y_3448_ = _args[21];
lean_object* v___y_3449_ = _args[22];
lean_object* v___y_3450_ = _args[23];
_start:
{
lean_object* v_res_3451_; 
v_res_3451_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(v_splitterName_3427_, v_matchDeclName_3428_, v_numParams_3429_, v_val_3430_, v___x_3431_, v_numDiscrs_3432_, v_baseName_3433_, v_a_3434_, v___x_3435_, v___x_3436_, v___x_3437_, v_uElimPos_x3f_3438_, v_discrInfos_3439_, v_overlaps_3440_, v___f_3441_, v___x_3442_, v_altInfos_3443_, v_xs_3444_, v___matchResultType_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
lean_dec_ref(v___matchResultType_3445_);
lean_dec_ref(v_altInfos_3443_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(lean_object* v_a_3452_, lean_object* v_a_3453_){
_start:
{
if (lean_obj_tag(v_a_3452_) == 0)
{
lean_object* v___x_3454_; 
v___x_3454_ = l_List_reverse___redArg(v_a_3453_);
return v___x_3454_;
}
else
{
lean_object* v_head_3455_; lean_object* v_tail_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3465_; 
v_head_3455_ = lean_ctor_get(v_a_3452_, 0);
v_tail_3456_ = lean_ctor_get(v_a_3452_, 1);
v_isSharedCheck_3465_ = !lean_is_exclusive(v_a_3452_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3458_ = v_a_3452_;
v_isShared_3459_ = v_isSharedCheck_3465_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_tail_3456_);
lean_inc(v_head_3455_);
lean_dec(v_a_3452_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3465_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3460_; lean_object* v___x_3462_; 
v___x_3460_ = l_Lean_mkLevelParam(v_head_3455_);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 1, v_a_3453_);
lean_ctor_set(v___x_3458_, 0, v___x_3460_);
v___x_3462_ = v___x_3458_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3460_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_a_3453_);
v___x_3462_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
v_a_3452_ = v_tail_3456_;
v_a_3453_ = v___x_3462_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_3466_; 
v___x_3466_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3466_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3467_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_3468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3467_);
return v___x_3468_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3469_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_3470_ = lean_unsigned_to_nat(0u);
v___x_3471_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
lean_ctor_set(v___x_3471_, 1, v___x_3470_);
lean_ctor_set(v___x_3471_, 2, v___x_3470_);
lean_ctor_set(v___x_3471_, 3, v___x_3469_);
lean_ctor_set(v___x_3471_, 4, v___x_3469_);
lean_ctor_set(v___x_3471_, 5, v___x_3469_);
lean_ctor_set(v___x_3471_, 6, v___x_3469_);
lean_ctor_set(v___x_3471_, 7, v___x_3469_);
lean_ctor_set(v___x_3471_, 8, v___x_3469_);
return v___x_3471_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3472_ = lean_box(1);
v___x_3473_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_3474_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_3475_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
lean_ctor_set(v___x_3475_, 1, v___x_3473_);
lean_ctor_set(v___x_3475_, 2, v___x_3472_);
return v___x_3475_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3477_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4));
v___x_3478_ = l_Lean_stringToMessageData(v___x_3477_);
return v___x_3478_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3480_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_3481_ = l_Lean_stringToMessageData(v___x_3480_);
return v___x_3481_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3483_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_3484_ = l_Lean_stringToMessageData(v___x_3483_);
return v___x_3484_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3486_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_3487_ = l_Lean_stringToMessageData(v___x_3486_);
return v___x_3487_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3489_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_3490_ = l_Lean_stringToMessageData(v___x_3489_);
return v___x_3490_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3492_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_3493_ = l_Lean_stringToMessageData(v___x_3492_);
return v___x_3493_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3495_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_3496_ = l_Lean_stringToMessageData(v___x_3495_);
return v___x_3496_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_3497_, lean_object* v_declHint_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v___x_3501_; lean_object* v_env_3502_; uint8_t v___x_3503_; 
v___x_3501_ = lean_st_ref_get(v___y_3499_);
v_env_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc_ref(v_env_3502_);
lean_dec(v___x_3501_);
v___x_3503_ = l_Lean_Name_isAnonymous(v_declHint_3498_);
if (v___x_3503_ == 0)
{
uint8_t v_isExporting_3504_; 
v_isExporting_3504_ = lean_ctor_get_uint8(v_env_3502_, sizeof(void*)*8);
if (v_isExporting_3504_ == 0)
{
lean_object* v___x_3505_; 
lean_dec_ref(v_env_3502_);
lean_dec(v_declHint_3498_);
v___x_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3505_, 0, v_msg_3497_);
return v___x_3505_;
}
else
{
lean_object* v___x_3506_; uint8_t v___x_3507_; 
lean_inc_ref(v_env_3502_);
v___x_3506_ = l_Lean_Environment_setExporting(v_env_3502_, v___x_3503_);
lean_inc(v_declHint_3498_);
lean_inc_ref(v___x_3506_);
v___x_3507_ = l_Lean_Environment_contains(v___x_3506_, v_declHint_3498_, v_isExporting_3504_);
if (v___x_3507_ == 0)
{
lean_object* v___x_3508_; 
lean_dec_ref(v___x_3506_);
lean_dec_ref(v_env_3502_);
lean_dec(v_declHint_3498_);
v___x_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3508_, 0, v_msg_3497_);
return v___x_3508_;
}
else
{
lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v_c_3514_; lean_object* v___x_3515_; 
v___x_3509_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_3510_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_3511_ = l_Lean_Options_empty;
v___x_3512_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3512_, 0, v___x_3506_);
lean_ctor_set(v___x_3512_, 1, v___x_3509_);
lean_ctor_set(v___x_3512_, 2, v___x_3510_);
lean_ctor_set(v___x_3512_, 3, v___x_3511_);
lean_inc(v_declHint_3498_);
v___x_3513_ = l_Lean_MessageData_ofConstName(v_declHint_3498_, v___x_3503_);
v_c_3514_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3514_, 0, v___x_3512_);
lean_ctor_set(v_c_3514_, 1, v___x_3513_);
v___x_3515_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3502_, v_declHint_3498_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
lean_dec_ref(v_env_3502_);
lean_dec(v_declHint_3498_);
v___x_3516_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_3517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3516_);
lean_ctor_set(v___x_3517_, 1, v_c_3514_);
v___x_3518_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_3519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3517_);
lean_ctor_set(v___x_3519_, 1, v___x_3518_);
v___x_3520_ = l_Lean_MessageData_note(v___x_3519_);
v___x_3521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3521_, 0, v_msg_3497_);
lean_ctor_set(v___x_3521_, 1, v___x_3520_);
v___x_3522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3521_);
return v___x_3522_;
}
else
{
lean_object* v_val_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3558_; 
v_val_3523_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3525_ = v___x_3515_;
v_isShared_3526_ = v_isSharedCheck_3558_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_val_3523_);
lean_dec(v___x_3515_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3558_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v_mod_3530_; uint8_t v___x_3531_; 
v___x_3527_ = lean_box(0);
v___x_3528_ = l_Lean_Environment_header(v_env_3502_);
lean_dec_ref(v_env_3502_);
v___x_3529_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3528_);
v_mod_3530_ = lean_array_get(v___x_3527_, v___x_3529_, v_val_3523_);
lean_dec(v_val_3523_);
lean_dec_ref(v___x_3529_);
v___x_3531_ = l_Lean_isPrivateName(v_declHint_3498_);
lean_dec(v_declHint_3498_);
if (v___x_3531_ == 0)
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3543_; 
v___x_3532_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_3533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3532_);
lean_ctor_set(v___x_3533_, 1, v_c_3514_);
v___x_3534_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_3535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3533_);
lean_ctor_set(v___x_3535_, 1, v___x_3534_);
v___x_3536_ = l_Lean_MessageData_ofName(v_mod_3530_);
v___x_3537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3535_);
lean_ctor_set(v___x_3537_, 1, v___x_3536_);
v___x_3538_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_3539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3537_);
lean_ctor_set(v___x_3539_, 1, v___x_3538_);
v___x_3540_ = l_Lean_MessageData_note(v___x_3539_);
v___x_3541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3541_, 0, v_msg_3497_);
lean_ctor_set(v___x_3541_, 1, v___x_3540_);
if (v_isShared_3526_ == 0)
{
lean_ctor_set_tag(v___x_3525_, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3541_);
v___x_3543_ = v___x_3525_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v___x_3541_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
else
{
lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3556_; 
v___x_3545_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_3546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3545_);
lean_ctor_set(v___x_3546_, 1, v_c_3514_);
v___x_3547_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_3548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3546_);
lean_ctor_set(v___x_3548_, 1, v___x_3547_);
v___x_3549_ = l_Lean_MessageData_ofName(v_mod_3530_);
v___x_3550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3548_);
lean_ctor_set(v___x_3550_, 1, v___x_3549_);
v___x_3551_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_3552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3550_);
lean_ctor_set(v___x_3552_, 1, v___x_3551_);
v___x_3553_ = l_Lean_MessageData_note(v___x_3552_);
v___x_3554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3554_, 0, v_msg_3497_);
lean_ctor_set(v___x_3554_, 1, v___x_3553_);
if (v_isShared_3526_ == 0)
{
lean_ctor_set_tag(v___x_3525_, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3554_);
v___x_3556_ = v___x_3525_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3554_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3559_; 
lean_dec_ref(v_env_3502_);
lean_dec(v_declHint_3498_);
v___x_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3559_, 0, v_msg_3497_);
return v___x_3559_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_3560_, lean_object* v_declHint_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
lean_object* v_res_3564_; 
v_res_3564_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3560_, v_declHint_3561_, v___y_3562_);
lean_dec(v___y_3562_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(lean_object* v_msg_3565_, lean_object* v_declHint_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_){
_start:
{
lean_object* v___x_3572_; lean_object* v_a_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3582_; 
v___x_3572_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3565_, v_declHint_3566_, v___y_3570_);
v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3575_ = v___x_3572_;
v_isShared_3576_ = v_isSharedCheck_3582_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_a_3573_);
lean_dec(v___x_3572_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3582_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3580_; 
v___x_3577_ = l_Lean_unknownIdentifierMessageTag;
v___x_3578_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
lean_ctor_set(v___x_3578_, 1, v_a_3573_);
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 0, v___x_3578_);
v___x_3580_ = v___x_3575_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v___x_3578_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12___boxed(lean_object* v_msg_3583_, lean_object* v_declHint_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
lean_object* v_res_3590_; 
v_res_3590_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3583_, v_declHint_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
return v_res_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(lean_object* v_ref_3591_, lean_object* v_msg_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_){
_start:
{
lean_object* v_fileName_3598_; lean_object* v_fileMap_3599_; lean_object* v_options_3600_; lean_object* v_currRecDepth_3601_; lean_object* v_maxRecDepth_3602_; lean_object* v_ref_3603_; lean_object* v_currNamespace_3604_; lean_object* v_openDecls_3605_; lean_object* v_initHeartbeats_3606_; lean_object* v_maxHeartbeats_3607_; lean_object* v_quotContext_3608_; lean_object* v_currMacroScope_3609_; uint8_t v_diag_3610_; lean_object* v_cancelTk_x3f_3611_; uint8_t v_suppressElabErrors_3612_; lean_object* v_inheritedTraceOptions_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3622_; 
v_fileName_3598_ = lean_ctor_get(v___y_3595_, 0);
v_fileMap_3599_ = lean_ctor_get(v___y_3595_, 1);
v_options_3600_ = lean_ctor_get(v___y_3595_, 2);
v_currRecDepth_3601_ = lean_ctor_get(v___y_3595_, 3);
v_maxRecDepth_3602_ = lean_ctor_get(v___y_3595_, 4);
v_ref_3603_ = lean_ctor_get(v___y_3595_, 5);
v_currNamespace_3604_ = lean_ctor_get(v___y_3595_, 6);
v_openDecls_3605_ = lean_ctor_get(v___y_3595_, 7);
v_initHeartbeats_3606_ = lean_ctor_get(v___y_3595_, 8);
v_maxHeartbeats_3607_ = lean_ctor_get(v___y_3595_, 9);
v_quotContext_3608_ = lean_ctor_get(v___y_3595_, 10);
v_currMacroScope_3609_ = lean_ctor_get(v___y_3595_, 11);
v_diag_3610_ = lean_ctor_get_uint8(v___y_3595_, sizeof(void*)*14);
v_cancelTk_x3f_3611_ = lean_ctor_get(v___y_3595_, 12);
v_suppressElabErrors_3612_ = lean_ctor_get_uint8(v___y_3595_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3613_ = lean_ctor_get(v___y_3595_, 13);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___y_3595_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3615_ = v___y_3595_;
v_isShared_3616_ = v_isSharedCheck_3622_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_inheritedTraceOptions_3613_);
lean_inc(v_cancelTk_x3f_3611_);
lean_inc(v_currMacroScope_3609_);
lean_inc(v_quotContext_3608_);
lean_inc(v_maxHeartbeats_3607_);
lean_inc(v_initHeartbeats_3606_);
lean_inc(v_openDecls_3605_);
lean_inc(v_currNamespace_3604_);
lean_inc(v_ref_3603_);
lean_inc(v_maxRecDepth_3602_);
lean_inc(v_currRecDepth_3601_);
lean_inc(v_options_3600_);
lean_inc(v_fileMap_3599_);
lean_inc(v_fileName_3598_);
lean_dec(v___y_3595_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3622_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v_ref_3617_; lean_object* v___x_3619_; 
v_ref_3617_ = l_Lean_replaceRef(v_ref_3591_, v_ref_3603_);
lean_dec(v_ref_3603_);
if (v_isShared_3616_ == 0)
{
lean_ctor_set(v___x_3615_, 5, v_ref_3617_);
v___x_3619_ = v___x_3615_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_fileName_3598_);
lean_ctor_set(v_reuseFailAlloc_3621_, 1, v_fileMap_3599_);
lean_ctor_set(v_reuseFailAlloc_3621_, 2, v_options_3600_);
lean_ctor_set(v_reuseFailAlloc_3621_, 3, v_currRecDepth_3601_);
lean_ctor_set(v_reuseFailAlloc_3621_, 4, v_maxRecDepth_3602_);
lean_ctor_set(v_reuseFailAlloc_3621_, 5, v_ref_3617_);
lean_ctor_set(v_reuseFailAlloc_3621_, 6, v_currNamespace_3604_);
lean_ctor_set(v_reuseFailAlloc_3621_, 7, v_openDecls_3605_);
lean_ctor_set(v_reuseFailAlloc_3621_, 8, v_initHeartbeats_3606_);
lean_ctor_set(v_reuseFailAlloc_3621_, 9, v_maxHeartbeats_3607_);
lean_ctor_set(v_reuseFailAlloc_3621_, 10, v_quotContext_3608_);
lean_ctor_set(v_reuseFailAlloc_3621_, 11, v_currMacroScope_3609_);
lean_ctor_set(v_reuseFailAlloc_3621_, 12, v_cancelTk_x3f_3611_);
lean_ctor_set(v_reuseFailAlloc_3621_, 13, v_inheritedTraceOptions_3613_);
lean_ctor_set_uint8(v_reuseFailAlloc_3621_, sizeof(void*)*14, v_diag_3610_);
lean_ctor_set_uint8(v_reuseFailAlloc_3621_, sizeof(void*)*14 + 1, v_suppressElabErrors_3612_);
v___x_3619_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
lean_object* v___x_3620_; 
v___x_3620_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v_msg_3592_, v___y_3593_, v___y_3594_, v___x_3619_, v___y_3596_);
lean_dec_ref(v___x_3619_);
return v___x_3620_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg___boxed(lean_object* v_ref_3623_, lean_object* v_msg_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
lean_object* v_res_3630_; 
v_res_3630_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3623_, v_msg_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
lean_dec(v___y_3628_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec(v_ref_3623_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(lean_object* v_ref_3631_, lean_object* v_msg_3632_, lean_object* v_declHint_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v___x_3639_; lean_object* v_a_3640_; lean_object* v___x_3641_; 
v___x_3639_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3632_, v_declHint_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
lean_inc(v_a_3640_);
lean_dec_ref(v___x_3639_);
v___x_3641_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3631_, v_a_3640_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object* v_ref_3642_, lean_object* v_msg_3643_, lean_object* v_declHint_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3642_, v_msg_3643_, v_declHint_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
lean_dec(v___y_3648_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec(v_ref_3642_);
return v_res_3650_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3652_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_3653_ = l_Lean_stringToMessageData(v___x_3652_);
return v___x_3653_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3655_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_3656_ = l_Lean_stringToMessageData(v___x_3655_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_3657_, lean_object* v_constName_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
lean_object* v___x_3664_; uint8_t v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3664_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_3665_ = 0;
lean_inc(v_constName_3658_);
v___x_3666_ = l_Lean_MessageData_ofConstName(v_constName_3658_, v___x_3665_);
v___x_3667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3664_);
lean_ctor_set(v___x_3667_, 1, v___x_3666_);
v___x_3668_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3667_);
lean_ctor_set(v___x_3669_, 1, v___x_3668_);
v___x_3670_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3657_, v___x_3669_, v_constName_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_3671_, lean_object* v_constName_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
lean_object* v_res_3678_; 
v_res_3678_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3671_, v_constName_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_);
lean_dec(v___y_3676_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v_ref_3671_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(lean_object* v_constName_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_){
_start:
{
lean_object* v_ref_3685_; lean_object* v___x_3686_; 
v_ref_3685_ = lean_ctor_get(v___y_3682_, 5);
lean_inc(v_ref_3685_);
v___x_3686_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3685_, v_constName_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_);
lean_dec(v_ref_3685_);
return v___x_3686_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_){
_start:
{
lean_object* v_res_3693_; 
v_res_3693_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
lean_dec(v___y_3691_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(lean_object* v_constName_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v___x_3700_; lean_object* v_env_3701_; uint8_t v___x_3702_; lean_object* v___x_3703_; 
v___x_3700_ = lean_st_ref_get(v___y_3698_);
v_env_3701_ = lean_ctor_get(v___x_3700_, 0);
lean_inc_ref(v_env_3701_);
lean_dec(v___x_3700_);
v___x_3702_ = 0;
lean_inc(v_constName_3694_);
v___x_3703_ = l_Lean_Environment_find_x3f(v_env_3701_, v_constName_3694_, v___x_3702_);
if (lean_obj_tag(v___x_3703_) == 0)
{
lean_object* v___x_3704_; 
v___x_3704_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
return v___x_3704_;
}
else
{
lean_object* v_val_3705_; lean_object* v___x_3707_; uint8_t v_isShared_3708_; uint8_t v_isSharedCheck_3712_; 
lean_dec_ref(v___y_3697_);
lean_dec(v_constName_3694_);
v_val_3705_ = lean_ctor_get(v___x_3703_, 0);
v_isSharedCheck_3712_ = !lean_is_exclusive(v___x_3703_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3707_ = v___x_3703_;
v_isShared_3708_ = v_isSharedCheck_3712_;
goto v_resetjp_3706_;
}
else
{
lean_inc(v_val_3705_);
lean_dec(v___x_3703_);
v___x_3707_ = lean_box(0);
v_isShared_3708_ = v_isSharedCheck_3712_;
goto v_resetjp_3706_;
}
v_resetjp_3706_:
{
lean_object* v___x_3710_; 
if (v_isShared_3708_ == 0)
{
lean_ctor_set_tag(v___x_3707_, 0);
v___x_3710_ = v___x_3707_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_val_3705_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0___boxed(lean_object* v_constName_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
lean_object* v_res_3719_; 
v_res_3719_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_constName_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
lean_dec(v___y_3717_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
return v_res_3719_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1(void){
_start:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3721_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__0));
v___x_3722_ = l_Lean_stringToMessageData(v___x_3721_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(lean_object* v_matchDeclName_3723_, lean_object* v_baseName_3724_, lean_object* v_splitterName_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_){
_start:
{
lean_object* v___x_3731_; uint8_t v_foApprox_3732_; uint8_t v_ctxApprox_3733_; uint8_t v_quasiPatternApprox_3734_; uint8_t v_constApprox_3735_; uint8_t v_isDefEqStuckEx_3736_; uint8_t v_unificationHints_3737_; uint8_t v_proofIrrelevance_3738_; uint8_t v_assignSyntheticOpaque_3739_; uint8_t v_offsetCnstrs_3740_; uint8_t v_transparency_3741_; uint8_t v_univApprox_3742_; uint8_t v_iota_3743_; uint8_t v_beta_3744_; uint8_t v_proj_3745_; uint8_t v_zeta_3746_; uint8_t v_zetaDelta_3747_; uint8_t v_zetaUnused_3748_; uint8_t v_zetaHave_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3812_; 
v___x_3731_ = l_Lean_Meta_Context_config(v_a_3726_);
v_foApprox_3732_ = lean_ctor_get_uint8(v___x_3731_, 0);
v_ctxApprox_3733_ = lean_ctor_get_uint8(v___x_3731_, 1);
v_quasiPatternApprox_3734_ = lean_ctor_get_uint8(v___x_3731_, 2);
v_constApprox_3735_ = lean_ctor_get_uint8(v___x_3731_, 3);
v_isDefEqStuckEx_3736_ = lean_ctor_get_uint8(v___x_3731_, 4);
v_unificationHints_3737_ = lean_ctor_get_uint8(v___x_3731_, 5);
v_proofIrrelevance_3738_ = lean_ctor_get_uint8(v___x_3731_, 6);
v_assignSyntheticOpaque_3739_ = lean_ctor_get_uint8(v___x_3731_, 7);
v_offsetCnstrs_3740_ = lean_ctor_get_uint8(v___x_3731_, 8);
v_transparency_3741_ = lean_ctor_get_uint8(v___x_3731_, 9);
v_univApprox_3742_ = lean_ctor_get_uint8(v___x_3731_, 11);
v_iota_3743_ = lean_ctor_get_uint8(v___x_3731_, 12);
v_beta_3744_ = lean_ctor_get_uint8(v___x_3731_, 13);
v_proj_3745_ = lean_ctor_get_uint8(v___x_3731_, 14);
v_zeta_3746_ = lean_ctor_get_uint8(v___x_3731_, 15);
v_zetaDelta_3747_ = lean_ctor_get_uint8(v___x_3731_, 16);
v_zetaUnused_3748_ = lean_ctor_get_uint8(v___x_3731_, 17);
v_zetaHave_3749_ = lean_ctor_get_uint8(v___x_3731_, 18);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3751_ = v___x_3731_;
v_isShared_3752_ = v_isSharedCheck_3812_;
goto v_resetjp_3750_;
}
else
{
lean_dec(v___x_3731_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3812_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
uint8_t v_trackZetaDelta_3753_; lean_object* v_zetaDeltaSet_3754_; lean_object* v_lctx_3755_; lean_object* v_localInstances_3756_; lean_object* v_defEqCtx_x3f_3757_; lean_object* v_synthPendingDepth_3758_; lean_object* v_canUnfold_x3f_3759_; uint8_t v_univApprox_3760_; uint8_t v_inTypeClassResolution_3761_; uint8_t v_cacheInferType_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3810_; 
v_trackZetaDelta_3753_ = lean_ctor_get_uint8(v_a_3726_, sizeof(void*)*7);
v_zetaDeltaSet_3754_ = lean_ctor_get(v_a_3726_, 1);
v_lctx_3755_ = lean_ctor_get(v_a_3726_, 2);
v_localInstances_3756_ = lean_ctor_get(v_a_3726_, 3);
v_defEqCtx_x3f_3757_ = lean_ctor_get(v_a_3726_, 4);
v_synthPendingDepth_3758_ = lean_ctor_get(v_a_3726_, 5);
v_canUnfold_x3f_3759_ = lean_ctor_get(v_a_3726_, 6);
v_univApprox_3760_ = lean_ctor_get_uint8(v_a_3726_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3761_ = lean_ctor_get_uint8(v_a_3726_, sizeof(void*)*7 + 2);
v_cacheInferType_3762_ = lean_ctor_get_uint8(v_a_3726_, sizeof(void*)*7 + 3);
v_isSharedCheck_3810_ = !lean_is_exclusive(v_a_3726_);
if (v_isSharedCheck_3810_ == 0)
{
lean_object* v_unused_3811_; 
v_unused_3811_ = lean_ctor_get(v_a_3726_, 0);
lean_dec(v_unused_3811_);
v___x_3764_ = v_a_3726_;
v_isShared_3765_ = v_isSharedCheck_3810_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_canUnfold_x3f_3759_);
lean_inc(v_synthPendingDepth_3758_);
lean_inc(v_defEqCtx_x3f_3757_);
lean_inc(v_localInstances_3756_);
lean_inc(v_lctx_3755_);
lean_inc(v_zetaDeltaSet_3754_);
lean_dec(v_a_3726_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3810_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
uint8_t v___x_3766_; lean_object* v___x_3768_; 
v___x_3766_ = 2;
if (v_isShared_3752_ == 0)
{
v___x_3768_ = v___x_3751_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3809_, 0, v_foApprox_3732_);
lean_ctor_set_uint8(v_reuseFailAlloc_3809_, 1, v_ctxApprox_3733_);
lean_ctor_set_uint8(v_reuseFailAlloc_3809_, 2, v_quasiPatternApprox_3734_);
lean_ctor_set_uint8(v_reuseFailAlloc_3809_, 3, v_constApprox_3735_);
lean_ctor_set_uint8(v_reuseFailAlloc_3809_, 4, v_isDefEqStuckEx_3736_);
lean_ctor_set_uint8(v_reuseFailAlloc_3809_, 5, v_unificationHints_3737_);
lean_ctor_set_uint8(v_reuseFailAlloc_3809_, 6, v_proofIrrelevance_3738_);
lean_ctor_set_uint8(v_reuseFailAlloc_3809_, 7, v_assignSyntheticOpaque_3739_);
lean_ctor_set_uint8(v_reuseFailAlloc_3809_, 8, v_offsetCnstrs_3740_);
lean_ctor_set_uint8(v_reuseFailAlloc_3809_, 9, v_transparency_3741_);
lean_ctor_set_uint8(v_reuseFailAlloc_3809_, 11, v_univApprox_3742_);
lean_ctor_set_uint8(v_reuseFailAlloc_3809_, 12, v_iota_3743_);
lean_ctor_set_uint8(v_reuseFailAlloc_3809_, 13, v_beta_3744_);
lean_ctor_set_uint8(v_reuseFailAlloc_3809_, 14, v_proj_3745_);
lean_ctor_set_uint8(v_reuseFailAlloc_3809_, 15, v_zeta_3746_);
lean_ctor_set_uint8(v_reuseFailAlloc_3809_, 16, v_zetaDelta_3747_);
lean_ctor_set_uint8(v_reuseFailAlloc_3809_, 17, v_zetaUnused_3748_);
lean_ctor_set_uint8(v_reuseFailAlloc_3809_, 18, v_zetaHave_3749_);
v___x_3768_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
uint64_t v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3772_; 
lean_ctor_set_uint8(v___x_3768_, 10, v___x_3766_);
v___x_3769_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3768_);
v___x_3770_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3770_, 0, v___x_3768_);
lean_ctor_set_uint64(v___x_3770_, sizeof(void*)*1, v___x_3769_);
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 0, v___x_3770_);
v___x_3772_ = v___x_3764_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3770_);
lean_ctor_set(v_reuseFailAlloc_3808_, 1, v_zetaDeltaSet_3754_);
lean_ctor_set(v_reuseFailAlloc_3808_, 2, v_lctx_3755_);
lean_ctor_set(v_reuseFailAlloc_3808_, 3, v_localInstances_3756_);
lean_ctor_set(v_reuseFailAlloc_3808_, 4, v_defEqCtx_x3f_3757_);
lean_ctor_set(v_reuseFailAlloc_3808_, 5, v_synthPendingDepth_3758_);
lean_ctor_set(v_reuseFailAlloc_3808_, 6, v_canUnfold_x3f_3759_);
lean_ctor_set_uint8(v_reuseFailAlloc_3808_, sizeof(void*)*7, v_trackZetaDelta_3753_);
lean_ctor_set_uint8(v_reuseFailAlloc_3808_, sizeof(void*)*7 + 1, v_univApprox_3760_);
lean_ctor_set_uint8(v_reuseFailAlloc_3808_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3761_);
lean_ctor_set_uint8(v_reuseFailAlloc_3808_, sizeof(void*)*7 + 3, v_cacheInferType_3762_);
v___x_3772_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
lean_object* v___x_3773_; 
lean_inc_ref(v_a_3728_);
lean_inc(v_matchDeclName_3723_);
v___x_3773_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_3723_, v___x_3772_, v_a_3727_, v_a_3728_, v_a_3729_);
if (lean_obj_tag(v___x_3773_) == 0)
{
lean_object* v_a_3774_; lean_object* v___x_3775_; lean_object* v_a_3776_; 
v_a_3774_ = lean_ctor_get(v___x_3773_, 0);
lean_inc(v_a_3774_);
lean_dec_ref(v___x_3773_);
lean_inc(v_matchDeclName_3723_);
v___x_3775_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_3723_, v_a_3729_);
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
lean_inc(v_a_3776_);
lean_dec_ref(v___x_3775_);
if (lean_obj_tag(v_a_3776_) == 1)
{
lean_object* v_val_3777_; lean_object* v_numParams_3778_; lean_object* v_numDiscrs_3779_; lean_object* v_altInfos_3780_; lean_object* v_uElimPos_x3f_3781_; lean_object* v_discrInfos_3782_; lean_object* v_overlaps_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___f_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___f_3791_; uint8_t v___x_3792_; lean_object* v___x_3793_; 
v_val_3777_ = lean_ctor_get(v_a_3776_, 0);
lean_inc(v_val_3777_);
lean_dec_ref(v_a_3776_);
v_numParams_3778_ = lean_ctor_get(v_val_3777_, 0);
lean_inc(v_numParams_3778_);
v_numDiscrs_3779_ = lean_ctor_get(v_val_3777_, 1);
lean_inc(v_numDiscrs_3779_);
v_altInfos_3780_ = lean_ctor_get(v_val_3777_, 2);
lean_inc_ref(v_altInfos_3780_);
v_uElimPos_x3f_3781_ = lean_ctor_get(v_val_3777_, 3);
lean_inc(v_uElimPos_x3f_3781_);
v_discrInfos_3782_ = lean_ctor_get(v_val_3777_, 4);
lean_inc_ref(v_discrInfos_3782_);
v_overlaps_3783_ = lean_ctor_get(v_val_3777_, 5);
lean_inc_ref(v_overlaps_3783_);
v___x_3784_ = l_Lean_instInhabitedExpr;
v___x_3785_ = l_Lean_ConstantInfo_levelParams(v_a_3774_);
v___x_3786_ = lean_box(0);
lean_inc(v___x_3785_);
v___x_3787_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(v___x_3785_, v___x_3786_);
lean_inc(v_splitterName_3725_);
lean_inc_ref(v_overlaps_3783_);
v___f_3788_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3788_, 0, v_overlaps_3783_);
lean_closure_set(v___f_3788_, 1, v_splitterName_3725_);
v___x_3789_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_discrInfos_3782_);
v___x_3790_ = l_Lean_ConstantInfo_type(v_a_3774_);
lean_inc_ref(v___x_3790_);
v___f_3791_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed), 24, 17);
lean_closure_set(v___f_3791_, 0, v_splitterName_3725_);
lean_closure_set(v___f_3791_, 1, v_matchDeclName_3723_);
lean_closure_set(v___f_3791_, 2, v_numParams_3778_);
lean_closure_set(v___f_3791_, 3, v_val_3777_);
lean_closure_set(v___f_3791_, 4, v___x_3784_);
lean_closure_set(v___f_3791_, 5, v_numDiscrs_3779_);
lean_closure_set(v___f_3791_, 6, v_baseName_3724_);
lean_closure_set(v___f_3791_, 7, v_a_3774_);
lean_closure_set(v___f_3791_, 8, v___x_3787_);
lean_closure_set(v___f_3791_, 9, v___x_3785_);
lean_closure_set(v___f_3791_, 10, v___x_3789_);
lean_closure_set(v___f_3791_, 11, v_uElimPos_x3f_3781_);
lean_closure_set(v___f_3791_, 12, v_discrInfos_3782_);
lean_closure_set(v___f_3791_, 13, v_overlaps_3783_);
lean_closure_set(v___f_3791_, 14, v___f_3788_);
lean_closure_set(v___f_3791_, 15, v___x_3790_);
lean_closure_set(v___f_3791_, 16, v_altInfos_3780_);
v___x_3792_ = 0;
v___x_3793_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_3790_, v___f_3791_, v___x_3792_, v___x_3792_, v___x_3772_, v_a_3727_, v_a_3728_, v_a_3729_);
return v___x_3793_;
}
else
{
lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
lean_dec(v_a_3776_);
lean_dec(v_a_3774_);
lean_dec(v_splitterName_3725_);
lean_dec(v_baseName_3724_);
v___x_3794_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3795_ = l_Lean_MessageData_ofName(v_matchDeclName_3723_);
v___x_3796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3794_);
lean_ctor_set(v___x_3796_, 1, v___x_3795_);
v___x_3797_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_3798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3796_);
lean_ctor_set(v___x_3798_, 1, v___x_3797_);
v___x_3799_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_3798_, v___x_3772_, v_a_3727_, v_a_3728_, v_a_3729_);
lean_dec(v_a_3729_);
lean_dec_ref(v_a_3728_);
lean_dec(v_a_3727_);
lean_dec_ref(v___x_3772_);
return v___x_3799_;
}
}
else
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3807_; 
lean_dec_ref(v___x_3772_);
lean_dec(v_a_3729_);
lean_dec_ref(v_a_3728_);
lean_dec(v_a_3727_);
lean_dec(v_splitterName_3725_);
lean_dec(v_baseName_3724_);
lean_dec(v_matchDeclName_3723_);
v_a_3800_ = lean_ctor_get(v___x_3773_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3773_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3802_ = v___x_3773_;
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___x_3773_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_a_3800_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed(lean_object* v_matchDeclName_3813_, lean_object* v_baseName_3814_, lean_object* v_splitterName_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_){
_start:
{
lean_object* v_res_3821_; 
v_res_3821_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(v_matchDeclName_3813_, v_baseName_3814_, v_splitterName_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_);
return v_res_3821_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(lean_object* v_xs_3822_, lean_object* v_ys_3823_, lean_object* v_hsz_3824_, lean_object* v_x_3825_, lean_object* v_x_3826_){
_start:
{
uint8_t v___x_3827_; 
v___x_3827_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_3822_, v_ys_3823_, v_x_3825_);
return v___x_3827_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___boxed(lean_object* v_xs_3828_, lean_object* v_ys_3829_, lean_object* v_hsz_3830_, lean_object* v_x_3831_, lean_object* v_x_3832_){
_start:
{
uint8_t v_res_3833_; lean_object* v_r_3834_; 
v_res_3833_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(v_xs_3828_, v_ys_3829_, v_hsz_3830_, v_x_3831_, v_x_3832_);
lean_dec_ref(v_ys_3829_);
lean_dec_ref(v_xs_3828_);
v_r_3834_ = lean_box(v_res_3833_);
return v_r_3834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6(lean_object* v_inst_3835_, lean_object* v_R_3836_, lean_object* v_a_3837_, lean_object* v_b_3838_){
_start:
{
lean_object* v___x_3839_; 
v___x_3839_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v_a_3837_, v_b_3838_);
return v___x_3839_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(lean_object* v_upperBound_3840_, lean_object* v_val_3841_, lean_object* v_baseName_3842_, lean_object* v___x_3843_, lean_object* v_a_3844_, lean_object* v___x_3845_, lean_object* v___x_3846_, lean_object* v___x_3847_, lean_object* v_matchDeclName_3848_, lean_object* v___x_3849_, lean_object* v___x_3850_, lean_object* v___x_3851_, lean_object* v_inst_3852_, lean_object* v_R_3853_, lean_object* v_a_3854_, lean_object* v_b_3855_, lean_object* v_c_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_){
_start:
{
lean_object* v___x_3862_; 
v___x_3862_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3840_, v_val_3841_, v_baseName_3842_, v___x_3843_, v_a_3844_, v___x_3845_, v___x_3846_, v___x_3847_, v_matchDeclName_3848_, v___x_3849_, v___x_3850_, v___x_3851_, v_a_3854_, v_b_3855_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
return v___x_3862_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_3863_ = _args[0];
lean_object* v_val_3864_ = _args[1];
lean_object* v_baseName_3865_ = _args[2];
lean_object* v___x_3866_ = _args[3];
lean_object* v_a_3867_ = _args[4];
lean_object* v___x_3868_ = _args[5];
lean_object* v___x_3869_ = _args[6];
lean_object* v___x_3870_ = _args[7];
lean_object* v_matchDeclName_3871_ = _args[8];
lean_object* v___x_3872_ = _args[9];
lean_object* v___x_3873_ = _args[10];
lean_object* v___x_3874_ = _args[11];
lean_object* v_inst_3875_ = _args[12];
lean_object* v_R_3876_ = _args[13];
lean_object* v_a_3877_ = _args[14];
lean_object* v_b_3878_ = _args[15];
lean_object* v_c_3879_ = _args[16];
lean_object* v___y_3880_ = _args[17];
lean_object* v___y_3881_ = _args[18];
lean_object* v___y_3882_ = _args[19];
lean_object* v___y_3883_ = _args[20];
lean_object* v___y_3884_ = _args[21];
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(v_upperBound_3863_, v_val_3864_, v_baseName_3865_, v___x_3866_, v_a_3867_, v___x_3868_, v___x_3869_, v___x_3870_, v_matchDeclName_3871_, v___x_3872_, v___x_3873_, v___x_3874_, v_inst_3875_, v_R_3876_, v_a_3877_, v_b_3878_, v_c_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
lean_dec(v_upperBound_3863_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(lean_object* v_00_u03b1_3886_, lean_object* v_constName_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_){
_start:
{
lean_object* v___x_3893_; 
v___x_3893_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_);
return v___x_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3894_, lean_object* v_constName_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(v_00_u03b1_3894_, v_constName_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_);
lean_dec(v___y_3899_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_3902_, lean_object* v_ref_3903_, lean_object* v_constName_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_){
_start:
{
lean_object* v___x_3910_; 
v___x_3910_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3903_, v_constName_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
return v___x_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_3911_, lean_object* v_ref_3912_, lean_object* v_constName_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_){
_start:
{
lean_object* v_res_3919_; 
v_res_3919_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(v_00_u03b1_3911_, v_ref_3912_, v_constName_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
lean_dec(v___y_3917_);
lean_dec(v___y_3915_);
lean_dec_ref(v___y_3914_);
lean_dec(v_ref_3912_);
return v_res_3919_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(lean_object* v_00_u03b1_3920_, lean_object* v_ref_3921_, lean_object* v_msg_3922_, lean_object* v_declHint_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_){
_start:
{
lean_object* v___x_3929_; 
v___x_3929_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3921_, v_msg_3922_, v_declHint_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_);
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___boxed(lean_object* v_00_u03b1_3930_, lean_object* v_ref_3931_, lean_object* v_msg_3932_, lean_object* v_declHint_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(v_00_u03b1_3930_, v_ref_3931_, v_msg_3932_, v_declHint_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_);
lean_dec(v___y_3937_);
lean_dec(v___y_3935_);
lean_dec_ref(v___y_3934_);
lean_dec(v_ref_3931_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(lean_object* v_msg_3940_, lean_object* v_declHint_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
lean_object* v___x_3947_; 
v___x_3947_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3940_, v_declHint_3941_, v___y_3945_);
return v___x_3947_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_3948_, lean_object* v_declHint_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(v_msg_3948_, v_declHint_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(lean_object* v_00_u03b1_3956_, lean_object* v_ref_3957_, lean_object* v_msg_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_){
_start:
{
lean_object* v___x_3964_; 
v___x_3964_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3957_, v_msg_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___boxed(lean_object* v_00_u03b1_3965_, lean_object* v_ref_3966_, lean_object* v_msg_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_){
_start:
{
lean_object* v_res_3973_; 
v_res_3973_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(v_00_u03b1_3965_, v_ref_3966_, v_msg_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_);
lean_dec(v___y_3971_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
lean_dec(v_ref_3966_);
return v_res_3973_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3974_, lean_object* v_vals_3975_, lean_object* v_i_3976_, lean_object* v_k_3977_){
_start:
{
lean_object* v___x_3978_; uint8_t v___x_3979_; 
v___x_3978_ = lean_array_get_size(v_keys_3974_);
v___x_3979_ = lean_nat_dec_lt(v_i_3976_, v___x_3978_);
if (v___x_3979_ == 0)
{
lean_object* v___x_3980_; 
lean_dec(v_i_3976_);
v___x_3980_ = lean_box(0);
return v___x_3980_;
}
else
{
lean_object* v_k_x27_3981_; uint8_t v___x_3982_; 
v_k_x27_3981_ = lean_array_fget_borrowed(v_keys_3974_, v_i_3976_);
v___x_3982_ = lean_name_eq(v_k_3977_, v_k_x27_3981_);
if (v___x_3982_ == 0)
{
lean_object* v___x_3983_; lean_object* v___x_3984_; 
v___x_3983_ = lean_unsigned_to_nat(1u);
v___x_3984_ = lean_nat_add(v_i_3976_, v___x_3983_);
lean_dec(v_i_3976_);
v_i_3976_ = v___x_3984_;
goto _start;
}
else
{
lean_object* v___x_3986_; lean_object* v___x_3987_; 
v___x_3986_ = lean_array_fget_borrowed(v_vals_3975_, v_i_3976_);
lean_dec(v_i_3976_);
lean_inc(v___x_3986_);
v___x_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3987_, 0, v___x_3986_);
return v___x_3987_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3988_, lean_object* v_vals_3989_, lean_object* v_i_3990_, lean_object* v_k_3991_){
_start:
{
lean_object* v_res_3992_; 
v_res_3992_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_3988_, v_vals_3989_, v_i_3990_, v_k_3991_);
lean_dec(v_k_3991_);
lean_dec_ref(v_vals_3989_);
lean_dec_ref(v_keys_3988_);
return v_res_3992_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_3993_; size_t v___x_3994_; size_t v___x_3995_; 
v___x_3993_ = ((size_t)5ULL);
v___x_3994_ = ((size_t)1ULL);
v___x_3995_ = lean_usize_shift_left(v___x_3994_, v___x_3993_);
return v___x_3995_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_3996_; size_t v___x_3997_; size_t v___x_3998_; 
v___x_3996_ = ((size_t)1ULL);
v___x_3997_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__0);
v___x_3998_ = lean_usize_sub(v___x_3997_, v___x_3996_);
return v___x_3998_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(lean_object* v_x_3999_, size_t v_x_4000_, lean_object* v_x_4001_){
_start:
{
if (lean_obj_tag(v_x_3999_) == 0)
{
lean_object* v_es_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4023_; 
v_es_4002_ = lean_ctor_get(v_x_3999_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v_x_3999_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4004_ = v_x_3999_;
v_isShared_4005_ = v_isSharedCheck_4023_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_es_4002_);
lean_dec(v_x_3999_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4023_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4006_; size_t v___x_4007_; size_t v___x_4008_; size_t v___x_4009_; lean_object* v_j_4010_; lean_object* v___x_4011_; 
v___x_4006_ = lean_box(2);
v___x_4007_ = ((size_t)5ULL);
v___x_4008_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___closed__1);
v___x_4009_ = lean_usize_land(v_x_4000_, v___x_4008_);
v_j_4010_ = lean_usize_to_nat(v___x_4009_);
v___x_4011_ = lean_array_get(v___x_4006_, v_es_4002_, v_j_4010_);
lean_dec(v_j_4010_);
lean_dec_ref(v_es_4002_);
switch(lean_obj_tag(v___x_4011_))
{
case 0:
{
lean_object* v_key_4012_; lean_object* v_val_4013_; uint8_t v___x_4014_; 
v_key_4012_ = lean_ctor_get(v___x_4011_, 0);
lean_inc(v_key_4012_);
v_val_4013_ = lean_ctor_get(v___x_4011_, 1);
lean_inc(v_val_4013_);
lean_dec_ref(v___x_4011_);
v___x_4014_ = lean_name_eq(v_x_4001_, v_key_4012_);
lean_dec(v_key_4012_);
if (v___x_4014_ == 0)
{
lean_object* v___x_4015_; 
lean_dec(v_val_4013_);
lean_del_object(v___x_4004_);
v___x_4015_ = lean_box(0);
return v___x_4015_;
}
else
{
lean_object* v___x_4017_; 
if (v_isShared_4005_ == 0)
{
lean_ctor_set_tag(v___x_4004_, 1);
lean_ctor_set(v___x_4004_, 0, v_val_4013_);
v___x_4017_ = v___x_4004_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_val_4013_);
v___x_4017_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
return v___x_4017_;
}
}
}
case 1:
{
lean_object* v_node_4019_; size_t v___x_4020_; 
lean_del_object(v___x_4004_);
v_node_4019_ = lean_ctor_get(v___x_4011_, 0);
lean_inc(v_node_4019_);
lean_dec_ref(v___x_4011_);
v___x_4020_ = lean_usize_shift_right(v_x_4000_, v___x_4007_);
v_x_3999_ = v_node_4019_;
v_x_4000_ = v___x_4020_;
goto _start;
}
default: 
{
lean_object* v___x_4022_; 
lean_del_object(v___x_4004_);
v___x_4022_ = lean_box(0);
return v___x_4022_;
}
}
}
}
else
{
lean_object* v_ks_4024_; lean_object* v_vs_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; 
v_ks_4024_ = lean_ctor_get(v_x_3999_, 0);
lean_inc_ref(v_ks_4024_);
v_vs_4025_ = lean_ctor_get(v_x_3999_, 1);
lean_inc_ref(v_vs_4025_);
lean_dec_ref(v_x_3999_);
v___x_4026_ = lean_unsigned_to_nat(0u);
v___x_4027_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_ks_4024_, v_vs_4025_, v___x_4026_, v_x_4001_);
lean_dec_ref(v_vs_4025_);
lean_dec_ref(v_ks_4024_);
return v___x_4027_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_4028_, lean_object* v_x_4029_, lean_object* v_x_4030_){
_start:
{
size_t v_x_750__boxed_4031_; lean_object* v_res_4032_; 
v_x_750__boxed_4031_ = lean_unbox_usize(v_x_4029_);
lean_dec(v_x_4029_);
v_res_4032_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_4028_, v_x_750__boxed_4031_, v_x_4030_);
lean_dec(v_x_4030_);
return v_res_4032_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4033_; uint64_t v___x_4034_; 
v___x_4033_ = lean_unsigned_to_nat(1723u);
v___x_4034_ = lean_uint64_of_nat(v___x_4033_);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(lean_object* v_x_4035_, lean_object* v_x_4036_){
_start:
{
uint64_t v___y_4038_; 
if (lean_obj_tag(v_x_4036_) == 0)
{
uint64_t v___x_4041_; 
v___x_4041_ = lean_uint64_once(&l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___closed__0);
v___y_4038_ = v___x_4041_;
goto v___jp_4037_;
}
else
{
uint64_t v_hash_4042_; 
v_hash_4042_ = lean_ctor_get_uint64(v_x_4036_, sizeof(void*)*2);
v___y_4038_ = v_hash_4042_;
goto v___jp_4037_;
}
v___jp_4037_:
{
size_t v___x_4039_; lean_object* v___x_4040_; 
v___x_4039_ = lean_uint64_to_usize(v___y_4038_);
v___x_4040_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_4035_, v___x_4039_, v_x_4036_);
return v___x_4040_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___boxed(lean_object* v_x_4043_, lean_object* v_x_4044_){
_start:
{
lean_object* v_res_4045_; 
v_res_4045_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_4043_, v_x_4044_);
lean_dec(v_x_4044_);
return v_res_4045_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4(void){
_start:
{
lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4052_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__3));
v___x_4053_ = l_Lean_stringToMessageData(v___x_4052_);
return v___x_4053_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6(void){
_start:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; 
v___x_4055_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__5));
v___x_4056_ = l_Lean_stringToMessageData(v___x_4055_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* lean_get_match_equations_for(lean_object* v_matchDeclName_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_){
_start:
{
lean_object* v___x_4063_; lean_object* v_env_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
v___x_4063_ = lean_st_ref_get(v_a_4061_);
v_env_4064_ = lean_ctor_get(v___x_4063_, 0);
lean_inc_ref(v_env_4064_);
lean_dec(v___x_4063_);
lean_inc(v_matchDeclName_4057_);
v___x_4065_ = l_Lean_mkPrivateName(v_env_4064_, v_matchDeclName_4057_);
lean_dec_ref(v_env_4064_);
v___x_4066_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__1));
lean_inc(v___x_4065_);
v___x_4067_ = l_Lean_Name_append(v___x_4065_, v___x_4066_);
lean_inc(v___x_4067_);
lean_inc(v_matchDeclName_4057_);
v___x_4068_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed), 8, 3);
lean_closure_set(v___x_4068_, 0, v_matchDeclName_4057_);
lean_closure_set(v___x_4068_, 1, v___x_4065_);
lean_closure_set(v___x_4068_, 2, v___x_4067_);
lean_inc(v_a_4061_);
lean_inc_ref(v_a_4060_);
lean_inc(v_a_4059_);
lean_inc_ref(v_a_4058_);
lean_inc(v___x_4067_);
lean_inc(v_matchDeclName_4057_);
v___x_4069_ = l_Lean_Meta_realizeConst(v_matchDeclName_4057_, v___x_4067_, v___x_4068_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_);
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4098_; 
v_isSharedCheck_4098_ = !lean_is_exclusive(v___x_4069_);
if (v_isSharedCheck_4098_ == 0)
{
lean_object* v_unused_4099_; 
v_unused_4099_ = lean_ctor_get(v___x_4069_, 0);
lean_dec(v_unused_4099_);
v___x_4071_ = v___x_4069_;
v_isShared_4072_ = v_isSharedCheck_4098_;
goto v_resetjp_4070_;
}
else
{
lean_dec(v___x_4069_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4098_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4073_; lean_object* v_env_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v_map_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4096_; 
v___x_4073_ = lean_st_ref_get(v_a_4061_);
v_env_4074_ = lean_ctor_get(v___x_4073_, 0);
lean_inc_ref(v_env_4074_);
lean_dec(v___x_4073_);
v___x_4075_ = l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
v___x_4076_ = l_Lean_Meta_Match_matchEqnsExt;
v___x_4077_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__2));
v___x_4078_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4075_, v___x_4076_, v_env_4074_, v___x_4077_, v___x_4067_);
v_map_4079_ = lean_ctor_get(v___x_4078_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4078_);
if (v_isSharedCheck_4096_ == 0)
{
lean_object* v_unused_4097_; 
v_unused_4097_ = lean_ctor_get(v___x_4078_, 1);
lean_dec(v_unused_4097_);
v___x_4081_ = v___x_4078_;
v_isShared_4082_ = v_isSharedCheck_4096_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_map_4079_);
lean_dec(v___x_4078_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4096_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4083_; 
v___x_4083_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_map_4079_, v_matchDeclName_4057_);
if (lean_obj_tag(v___x_4083_) == 0)
{
lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4087_; 
lean_del_object(v___x_4071_);
v___x_4084_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__4, &l_Lean_Meta_Match_getEquationsForImpl___closed__4_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4);
v___x_4085_ = l_Lean_MessageData_ofName(v_matchDeclName_4057_);
if (v_isShared_4082_ == 0)
{
lean_ctor_set_tag(v___x_4081_, 7);
lean_ctor_set(v___x_4081_, 1, v___x_4085_);
lean_ctor_set(v___x_4081_, 0, v___x_4084_);
v___x_4087_ = v___x_4081_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4084_);
lean_ctor_set(v_reuseFailAlloc_4091_, 1, v___x_4085_);
v___x_4087_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4088_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__6, &l_Lean_Meta_Match_getEquationsForImpl___closed__6_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6);
v___x_4089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4087_);
lean_ctor_set(v___x_4089_, 1, v___x_4088_);
v___x_4090_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_4089_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_);
lean_dec(v_a_4061_);
lean_dec_ref(v_a_4060_);
lean_dec(v_a_4059_);
lean_dec_ref(v_a_4058_);
return v___x_4090_;
}
}
else
{
lean_object* v_val_4092_; lean_object* v___x_4094_; 
lean_del_object(v___x_4081_);
lean_dec(v_a_4061_);
lean_dec_ref(v_a_4060_);
lean_dec(v_a_4059_);
lean_dec_ref(v_a_4058_);
lean_dec(v_matchDeclName_4057_);
v_val_4092_ = lean_ctor_get(v___x_4083_, 0);
lean_inc(v_val_4092_);
lean_dec_ref(v___x_4083_);
if (v_isShared_4072_ == 0)
{
lean_ctor_set(v___x_4071_, 0, v_val_4092_);
v___x_4094_ = v___x_4071_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_val_4092_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
}
}
}
else
{
lean_object* v_a_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4107_; 
lean_dec(v___x_4067_);
lean_dec(v_a_4061_);
lean_dec_ref(v_a_4060_);
lean_dec(v_a_4059_);
lean_dec_ref(v_a_4058_);
lean_dec(v_matchDeclName_4057_);
v_a_4100_ = lean_ctor_get(v___x_4069_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4069_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4102_ = v___x_4069_;
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_a_4100_);
lean_dec(v___x_4069_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4105_; 
if (v_isShared_4103_ == 0)
{
v___x_4105_ = v___x_4102_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_a_4100_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
return v___x_4105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getEquationsForImpl___boxed(lean_object* v_matchDeclName_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_){
_start:
{
lean_object* v_res_4114_; 
v_res_4114_ = lean_get_match_equations_for(v_matchDeclName_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_);
return v_res_4114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(lean_object* v_00_u03b2_4115_, lean_object* v_x_4116_, lean_object* v_x_4117_){
_start:
{
lean_object* v___x_4118_; 
v___x_4118_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_4116_, v_x_4117_);
return v___x_4118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___boxed(lean_object* v_00_u03b2_4119_, lean_object* v_x_4120_, lean_object* v_x_4121_){
_start:
{
lean_object* v_res_4122_; 
v_res_4122_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(v_00_u03b2_4119_, v_x_4120_, v_x_4121_);
lean_dec(v_x_4121_);
return v_res_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(lean_object* v_00_u03b2_4123_, lean_object* v_x_4124_, size_t v_x_4125_, lean_object* v_x_4126_){
_start:
{
lean_object* v___x_4127_; 
v___x_4127_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_4124_, v_x_4125_, v_x_4126_);
return v___x_4127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4128_, lean_object* v_x_4129_, lean_object* v_x_4130_, lean_object* v_x_4131_){
_start:
{
size_t v_x_978__boxed_4132_; lean_object* v_res_4133_; 
v_x_978__boxed_4132_ = lean_unbox_usize(v_x_4130_);
lean_dec(v_x_4130_);
v_res_4133_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(v_00_u03b2_4128_, v_x_4129_, v_x_978__boxed_4132_, v_x_4131_);
lean_dec(v_x_4131_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4134_, lean_object* v_keys_4135_, lean_object* v_vals_4136_, lean_object* v_heq_4137_, lean_object* v_i_4138_, lean_object* v_k_4139_){
_start:
{
lean_object* v___x_4140_; 
v___x_4140_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_4135_, v_vals_4136_, v_i_4138_, v_k_4139_);
return v___x_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4141_, lean_object* v_keys_4142_, lean_object* v_vals_4143_, lean_object* v_heq_4144_, lean_object* v_i_4145_, lean_object* v_k_4146_){
_start:
{
lean_object* v_res_4147_; 
v_res_4147_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(v_00_u03b2_4141_, v_keys_4142_, v_vals_4143_, v_heq_4144_, v_i_4145_, v_k_4146_);
lean_dec(v_k_4146_);
lean_dec_ref(v_vals_4143_);
lean_dec_ref(v_keys_4142_);
return v_res_4147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(lean_object* v_type_4148_, lean_object* v_k_4149_, uint8_t v_cleanupAnnotations_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_){
_start:
{
lean_object* v___f_4156_; uint8_t v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; 
v___f_4156_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4156_, 0, v_k_4149_);
v___x_4157_ = 0;
v___x_4158_ = lean_box(0);
v___x_4159_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_4157_, v___x_4158_, v_type_4148_, v___f_4156_, v_cleanupAnnotations_4150_, v___x_4157_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_object* v_a_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4167_; 
v_a_4160_ = lean_ctor_get(v___x_4159_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_4159_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4162_ = v___x_4159_;
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_a_4160_);
lean_dec(v___x_4159_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___x_4165_; 
if (v_isShared_4163_ == 0)
{
v___x_4165_ = v___x_4162_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v_a_4160_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
return v___x_4165_;
}
}
}
else
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4175_; 
v_a_4168_ = lean_ctor_get(v___x_4159_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4159_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4170_ = v___x_4159_;
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4159_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4173_; 
if (v_isShared_4171_ == 0)
{
v___x_4173_ = v___x_4170_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_a_4168_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg___boxed(lean_object* v_type_4176_, lean_object* v_k_4177_, lean_object* v_cleanupAnnotations_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4184_; lean_object* v_res_4185_; 
v_cleanupAnnotations_boxed_4184_ = lean_unbox(v_cleanupAnnotations_4178_);
v_res_4185_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4176_, v_k_4177_, v_cleanupAnnotations_boxed_4184_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_);
return v_res_4185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(lean_object* v_00_u03b1_4186_, lean_object* v_type_4187_, lean_object* v_k_4188_, uint8_t v_cleanupAnnotations_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
lean_object* v___x_4195_; 
v___x_4195_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4187_, v_k_4188_, v_cleanupAnnotations_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
return v___x_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4196_, lean_object* v_type_4197_, lean_object* v_k_4198_, lean_object* v_cleanupAnnotations_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4205_; lean_object* v_res_4206_; 
v_cleanupAnnotations_boxed_4205_ = lean_unbox(v_cleanupAnnotations_4199_);
v_res_4206_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(v_00_u03b1_4196_, v_type_4197_, v_k_4198_, v_cleanupAnnotations_boxed_4205_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
return v_res_4206_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(lean_object* v_msg_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_){
_start:
{
lean_object* v___f_4213_; lean_object* v___x_19501__overap_4214_; lean_object* v___x_4215_; 
v___f_4213_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_19501__overap_4214_ = lean_panic_fn(v___f_4213_, v_msg_4207_);
v___x_4215_ = lean_apply_5(v___x_19501__overap_4214_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, lean_box(0));
return v___x_4215_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1___boxed(lean_object* v_msg_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v_msg_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(lean_object* v_c_4223_){
_start:
{
uint8_t v_foApprox_4224_; uint8_t v_ctxApprox_4225_; uint8_t v_quasiPatternApprox_4226_; uint8_t v_constApprox_4227_; uint8_t v_isDefEqStuckEx_4228_; uint8_t v_unificationHints_4229_; uint8_t v_proofIrrelevance_4230_; uint8_t v_assignSyntheticOpaque_4231_; uint8_t v_offsetCnstrs_4232_; uint8_t v_transparency_4233_; uint8_t v_univApprox_4234_; uint8_t v_iota_4235_; uint8_t v_beta_4236_; uint8_t v_proj_4237_; uint8_t v_zeta_4238_; uint8_t v_zetaDelta_4239_; uint8_t v_zetaUnused_4240_; uint8_t v_zetaHave_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4249_; 
v_foApprox_4224_ = lean_ctor_get_uint8(v_c_4223_, 0);
v_ctxApprox_4225_ = lean_ctor_get_uint8(v_c_4223_, 1);
v_quasiPatternApprox_4226_ = lean_ctor_get_uint8(v_c_4223_, 2);
v_constApprox_4227_ = lean_ctor_get_uint8(v_c_4223_, 3);
v_isDefEqStuckEx_4228_ = lean_ctor_get_uint8(v_c_4223_, 4);
v_unificationHints_4229_ = lean_ctor_get_uint8(v_c_4223_, 5);
v_proofIrrelevance_4230_ = lean_ctor_get_uint8(v_c_4223_, 6);
v_assignSyntheticOpaque_4231_ = lean_ctor_get_uint8(v_c_4223_, 7);
v_offsetCnstrs_4232_ = lean_ctor_get_uint8(v_c_4223_, 8);
v_transparency_4233_ = lean_ctor_get_uint8(v_c_4223_, 9);
v_univApprox_4234_ = lean_ctor_get_uint8(v_c_4223_, 11);
v_iota_4235_ = lean_ctor_get_uint8(v_c_4223_, 12);
v_beta_4236_ = lean_ctor_get_uint8(v_c_4223_, 13);
v_proj_4237_ = lean_ctor_get_uint8(v_c_4223_, 14);
v_zeta_4238_ = lean_ctor_get_uint8(v_c_4223_, 15);
v_zetaDelta_4239_ = lean_ctor_get_uint8(v_c_4223_, 16);
v_zetaUnused_4240_ = lean_ctor_get_uint8(v_c_4223_, 17);
v_zetaHave_4241_ = lean_ctor_get_uint8(v_c_4223_, 18);
v_isSharedCheck_4249_ = !lean_is_exclusive(v_c_4223_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4243_ = v_c_4223_;
v_isShared_4244_ = v_isSharedCheck_4249_;
goto v_resetjp_4242_;
}
else
{
lean_dec(v_c_4223_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4249_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
uint8_t v___x_4245_; lean_object* v___x_4247_; 
v___x_4245_ = 2;
if (v_isShared_4244_ == 0)
{
v___x_4247_ = v___x_4243_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4248_, 0, v_foApprox_4224_);
lean_ctor_set_uint8(v_reuseFailAlloc_4248_, 1, v_ctxApprox_4225_);
lean_ctor_set_uint8(v_reuseFailAlloc_4248_, 2, v_quasiPatternApprox_4226_);
lean_ctor_set_uint8(v_reuseFailAlloc_4248_, 3, v_constApprox_4227_);
lean_ctor_set_uint8(v_reuseFailAlloc_4248_, 4, v_isDefEqStuckEx_4228_);
lean_ctor_set_uint8(v_reuseFailAlloc_4248_, 5, v_unificationHints_4229_);
lean_ctor_set_uint8(v_reuseFailAlloc_4248_, 6, v_proofIrrelevance_4230_);
lean_ctor_set_uint8(v_reuseFailAlloc_4248_, 7, v_assignSyntheticOpaque_4231_);
lean_ctor_set_uint8(v_reuseFailAlloc_4248_, 8, v_offsetCnstrs_4232_);
lean_ctor_set_uint8(v_reuseFailAlloc_4248_, 9, v_transparency_4233_);
lean_ctor_set_uint8(v_reuseFailAlloc_4248_, 11, v_univApprox_4234_);
lean_ctor_set_uint8(v_reuseFailAlloc_4248_, 12, v_iota_4235_);
lean_ctor_set_uint8(v_reuseFailAlloc_4248_, 13, v_beta_4236_);
lean_ctor_set_uint8(v_reuseFailAlloc_4248_, 14, v_proj_4237_);
lean_ctor_set_uint8(v_reuseFailAlloc_4248_, 15, v_zeta_4238_);
lean_ctor_set_uint8(v_reuseFailAlloc_4248_, 16, v_zetaDelta_4239_);
lean_ctor_set_uint8(v_reuseFailAlloc_4248_, 17, v_zetaUnused_4240_);
lean_ctor_set_uint8(v_reuseFailAlloc_4248_, 18, v_zetaHave_4241_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
lean_ctor_set_uint8(v___x_4247_, 10, v___x_4245_);
return v___x_4247_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(lean_object* v_x_4250_, lean_object* v_t_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_){
_start:
{
lean_object* v_dummy_4257_; lean_object* v_nargs_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; 
v_dummy_4257_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_4258_ = l_Lean_Expr_getAppNumArgs(v_t_4251_);
lean_inc(v_nargs_4258_);
v___x_4259_ = lean_mk_array(v_nargs_4258_, v_dummy_4257_);
v___x_4260_ = lean_unsigned_to_nat(1u);
v___x_4261_ = lean_nat_sub(v_nargs_4258_, v___x_4260_);
lean_dec(v_nargs_4258_);
v___x_4262_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_t_4251_, v___x_4259_, v___x_4261_);
v___x_4263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4263_, 0, v___x_4262_);
return v___x_4263_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0___boxed(lean_object* v_x_4264_, lean_object* v_t_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_){
_start:
{
lean_object* v_res_4271_; 
v_res_4271_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(v_x_4264_, v_t_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_);
lean_dec(v___y_4269_);
lean_dec_ref(v___y_4268_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec_ref(v_x_4264_);
return v_res_4271_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(lean_object* v_a_4275_, lean_object* v_b_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_){
_start:
{
lean_object* v_array_4282_; lean_object* v_start_4283_; lean_object* v_stop_4284_; lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4342_; 
v_array_4282_ = lean_ctor_get(v_a_4275_, 0);
v_start_4283_ = lean_ctor_get(v_a_4275_, 1);
v_stop_4284_ = lean_ctor_get(v_a_4275_, 2);
v_isSharedCheck_4342_ = !lean_is_exclusive(v_a_4275_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4286_ = v_a_4275_;
v_isShared_4287_ = v_isSharedCheck_4342_;
goto v_resetjp_4285_;
}
else
{
lean_inc(v_stop_4284_);
lean_inc(v_start_4283_);
lean_inc(v_array_4282_);
lean_dec(v_a_4275_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4342_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
uint8_t v___x_4288_; 
v___x_4288_ = lean_nat_dec_lt(v_start_4283_, v_stop_4284_);
if (v___x_4288_ == 0)
{
lean_object* v___x_4289_; 
lean_del_object(v___x_4286_);
lean_dec(v_stop_4284_);
lean_dec(v_start_4283_);
lean_dec_ref(v_array_4282_);
lean_dec(v___y_4280_);
lean_dec_ref(v___y_4279_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4277_);
v___x_4289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4289_, 0, v_b_4276_);
return v___x_4289_;
}
else
{
lean_object* v_snd_4290_; lean_object* v_fst_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4341_; 
v_snd_4290_ = lean_ctor_get(v_b_4276_, 1);
v_fst_4291_ = lean_ctor_get(v_b_4276_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v_b_4276_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4293_ = v_b_4276_;
v_isShared_4294_ = v_isSharedCheck_4341_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_snd_4290_);
lean_inc(v_fst_4291_);
lean_dec(v_b_4276_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4341_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v_array_4295_; lean_object* v_start_4296_; lean_object* v_stop_4297_; uint8_t v___x_4298_; 
v_array_4295_ = lean_ctor_get(v_snd_4290_, 0);
v_start_4296_ = lean_ctor_get(v_snd_4290_, 1);
v_stop_4297_ = lean_ctor_get(v_snd_4290_, 2);
v___x_4298_ = lean_nat_dec_lt(v_start_4296_, v_stop_4297_);
if (v___x_4298_ == 0)
{
lean_object* v___x_4300_; 
lean_del_object(v___x_4286_);
lean_dec(v_stop_4284_);
lean_dec(v_start_4283_);
lean_dec_ref(v_array_4282_);
lean_dec(v___y_4280_);
lean_dec_ref(v___y_4279_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4277_);
if (v_isShared_4294_ == 0)
{
v___x_4300_ = v___x_4293_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4302_; 
v_reuseFailAlloc_4302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4302_, 0, v_fst_4291_);
lean_ctor_set(v_reuseFailAlloc_4302_, 1, v_snd_4290_);
v___x_4300_ = v_reuseFailAlloc_4302_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
lean_object* v___x_4301_; 
v___x_4301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4301_, 0, v___x_4300_);
return v___x_4301_;
}
}
else
{
lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4337_; 
lean_inc(v_stop_4297_);
lean_inc(v_start_4296_);
lean_inc_ref(v_array_4295_);
v_isSharedCheck_4337_ = !lean_is_exclusive(v_snd_4290_);
if (v_isSharedCheck_4337_ == 0)
{
lean_object* v_unused_4338_; lean_object* v_unused_4339_; lean_object* v_unused_4340_; 
v_unused_4338_ = lean_ctor_get(v_snd_4290_, 2);
lean_dec(v_unused_4338_);
v_unused_4339_ = lean_ctor_get(v_snd_4290_, 1);
lean_dec(v_unused_4339_);
v_unused_4340_ = lean_ctor_get(v_snd_4290_, 0);
lean_dec(v_unused_4340_);
v___x_4304_ = v_snd_4290_;
v_isShared_4305_ = v_isSharedCheck_4337_;
goto v_resetjp_4303_;
}
else
{
lean_dec(v_snd_4290_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4337_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; 
v___x_4306_ = lean_array_fget_borrowed(v_array_4282_, v_start_4283_);
v___x_4307_ = lean_array_fget_borrowed(v_array_4295_, v_start_4296_);
lean_inc(v___y_4280_);
lean_inc_ref(v___y_4279_);
lean_inc(v___y_4278_);
lean_inc_ref(v___y_4277_);
lean_inc(v___x_4307_);
lean_inc(v___x_4306_);
v___x_4308_ = l_Lean_Meta_mkEqHEq(v___x_4306_, v___x_4307_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_);
if (lean_obj_tag(v___x_4308_) == 0)
{
lean_object* v_a_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4313_; 
v_a_4309_ = lean_ctor_get(v___x_4308_, 0);
lean_inc(v_a_4309_);
lean_dec_ref(v___x_4308_);
v___x_4310_ = lean_unsigned_to_nat(1u);
v___x_4311_ = lean_nat_add(v_start_4283_, v___x_4310_);
lean_dec(v_start_4283_);
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 2, v_stop_4284_);
lean_ctor_set(v___x_4304_, 1, v___x_4311_);
lean_ctor_set(v___x_4304_, 0, v_array_4282_);
v___x_4313_ = v___x_4304_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_array_4282_);
lean_ctor_set(v_reuseFailAlloc_4328_, 1, v___x_4311_);
lean_ctor_set(v_reuseFailAlloc_4328_, 2, v_stop_4284_);
v___x_4313_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
lean_object* v___x_4314_; lean_object* v___x_4316_; 
v___x_4314_ = lean_nat_add(v_start_4296_, v___x_4310_);
lean_dec(v_start_4296_);
if (v_isShared_4287_ == 0)
{
lean_ctor_set(v___x_4286_, 2, v_stop_4297_);
lean_ctor_set(v___x_4286_, 1, v___x_4314_);
lean_ctor_set(v___x_4286_, 0, v_array_4295_);
v___x_4316_ = v___x_4286_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v_array_4295_);
lean_ctor_set(v_reuseFailAlloc_4327_, 1, v___x_4314_);
lean_ctor_set(v_reuseFailAlloc_4327_, 2, v_stop_4297_);
v___x_4316_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4322_; 
v___x_4317_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg___closed__1));
v___x_4318_ = lean_array_get_size(v_fst_4291_);
v___x_4319_ = lean_nat_add(v___x_4318_, v___x_4310_);
v___x_4320_ = lean_name_append_index_after(v___x_4317_, v___x_4319_);
if (v_isShared_4294_ == 0)
{
lean_ctor_set(v___x_4293_, 1, v_a_4309_);
lean_ctor_set(v___x_4293_, 0, v___x_4320_);
v___x_4322_ = v___x_4293_;
goto v_reusejp_4321_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v___x_4320_);
lean_ctor_set(v_reuseFailAlloc_4326_, 1, v_a_4309_);
v___x_4322_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4321_;
}
v_reusejp_4321_:
{
lean_object* v___x_4323_; lean_object* v___x_4324_; 
v___x_4323_ = lean_array_push(v_fst_4291_, v___x_4322_);
v___x_4324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4324_, 0, v___x_4323_);
lean_ctor_set(v___x_4324_, 1, v___x_4316_);
v_a_4275_ = v___x_4313_;
v_b_4276_ = v___x_4324_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4336_; 
lean_del_object(v___x_4304_);
lean_dec(v_stop_4297_);
lean_dec(v_start_4296_);
lean_dec_ref(v_array_4295_);
lean_del_object(v___x_4293_);
lean_dec(v_fst_4291_);
lean_del_object(v___x_4286_);
lean_dec(v_stop_4284_);
lean_dec(v_start_4283_);
lean_dec_ref(v_array_4282_);
lean_dec(v___y_4280_);
lean_dec_ref(v___y_4279_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4277_);
v_a_4329_ = lean_ctor_get(v___x_4308_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4331_ = v___x_4308_;
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_a_4329_);
lean_dec(v___x_4308_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v___x_4334_; 
if (v_isShared_4332_ == 0)
{
v___x_4334_ = v___x_4331_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_a_4329_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg___boxed(lean_object* v_a_4343_, lean_object* v_b_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(v_a_4343_, v_b_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
return v_res_4350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(lean_object* v___x_4351_, lean_object* v_a_4352_, lean_object* v___x_4353_, lean_object* v_as_4354_, size_t v_sz_4355_, size_t v_i_4356_, lean_object* v_b_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_){
_start:
{
uint8_t v___x_4363_; 
v___x_4363_ = lean_usize_dec_lt(v_i_4356_, v_sz_4355_);
if (v___x_4363_ == 0)
{
lean_object* v___x_4364_; 
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4358_);
lean_dec(v___x_4353_);
v___x_4364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4364_, 0, v_b_4357_);
return v___x_4364_;
}
else
{
lean_object* v___x_4365_; lean_object* v_a_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; 
v___x_4365_ = l_Lean_instInhabitedExpr;
v_a_4366_ = lean_array_uget_borrowed(v_as_4354_, v_i_4356_);
v___x_4367_ = lean_array_get_borrowed(v___x_4365_, v___x_4351_, v_a_4366_);
lean_inc(v___y_4361_);
lean_inc_ref(v___y_4360_);
lean_inc(v___y_4359_);
lean_inc_ref(v___y_4358_);
lean_inc(v___x_4367_);
v___x_4368_ = l_Lean_Meta_instantiateForall(v___x_4367_, v_a_4352_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
if (lean_obj_tag(v___x_4368_) == 0)
{
lean_object* v_a_4369_; lean_object* v___x_4370_; 
v_a_4369_ = lean_ctor_get(v___x_4368_, 0);
lean_inc(v_a_4369_);
lean_dec_ref(v___x_4368_);
lean_inc(v___y_4361_);
lean_inc_ref(v___y_4360_);
lean_inc(v___y_4359_);
lean_inc_ref(v___y_4358_);
lean_inc(v___x_4353_);
v___x_4370_ = l_Lean_Meta_Match_simpH_x3f(v_a_4369_, v___x_4353_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
if (lean_obj_tag(v___x_4370_) == 0)
{
lean_object* v_a_4371_; lean_object* v_a_4373_; 
v_a_4371_ = lean_ctor_get(v___x_4370_, 0);
lean_inc(v_a_4371_);
lean_dec_ref(v___x_4370_);
if (lean_obj_tag(v_a_4371_) == 1)
{
lean_object* v_val_4377_; lean_object* v___x_4378_; 
v_val_4377_ = lean_ctor_get(v_a_4371_, 0);
lean_inc(v_val_4377_);
lean_dec_ref(v_a_4371_);
v___x_4378_ = lean_array_push(v_b_4357_, v_val_4377_);
v_a_4373_ = v___x_4378_;
goto v___jp_4372_;
}
else
{
lean_dec(v_a_4371_);
v_a_4373_ = v_b_4357_;
goto v___jp_4372_;
}
v___jp_4372_:
{
size_t v___x_4374_; size_t v___x_4375_; 
v___x_4374_ = ((size_t)1ULL);
v___x_4375_ = lean_usize_add(v_i_4356_, v___x_4374_);
v_i_4356_ = v___x_4375_;
v_b_4357_ = v_a_4373_;
goto _start;
}
}
else
{
lean_object* v_a_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4386_; 
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4358_);
lean_dec_ref(v_b_4357_);
lean_dec(v___x_4353_);
v_a_4379_ = lean_ctor_get(v___x_4370_, 0);
v_isSharedCheck_4386_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4386_ == 0)
{
v___x_4381_ = v___x_4370_;
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_a_4379_);
lean_dec(v___x_4370_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v___x_4384_; 
if (v_isShared_4382_ == 0)
{
v___x_4384_ = v___x_4381_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v_a_4379_);
v___x_4384_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
return v___x_4384_;
}
}
}
}
else
{
lean_object* v_a_4387_; lean_object* v___x_4389_; uint8_t v_isShared_4390_; uint8_t v_isSharedCheck_4394_; 
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4358_);
lean_dec_ref(v_b_4357_);
lean_dec(v___x_4353_);
v_a_4387_ = lean_ctor_get(v___x_4368_, 0);
v_isSharedCheck_4394_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4394_ == 0)
{
v___x_4389_ = v___x_4368_;
v_isShared_4390_ = v_isSharedCheck_4394_;
goto v_resetjp_4388_;
}
else
{
lean_inc(v_a_4387_);
lean_dec(v___x_4368_);
v___x_4389_ = lean_box(0);
v_isShared_4390_ = v_isSharedCheck_4394_;
goto v_resetjp_4388_;
}
v_resetjp_4388_:
{
lean_object* v___x_4392_; 
if (v_isShared_4390_ == 0)
{
v___x_4392_ = v___x_4389_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v_a_4387_);
v___x_4392_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
return v___x_4392_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___boxed(lean_object* v___x_4395_, lean_object* v_a_4396_, lean_object* v___x_4397_, lean_object* v_as_4398_, lean_object* v_sz_4399_, lean_object* v_i_4400_, lean_object* v_b_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
size_t v_sz_boxed_4407_; size_t v_i_boxed_4408_; lean_object* v_res_4409_; 
v_sz_boxed_4407_ = lean_unbox_usize(v_sz_4399_);
lean_dec(v_sz_4399_);
v_i_boxed_4408_ = lean_unbox_usize(v_i_4400_);
lean_dec(v_i_4400_);
v_res_4409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(v___x_4395_, v_a_4396_, v___x_4397_, v_as_4398_, v_sz_boxed_4407_, v_i_boxed_4408_, v_b_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_);
lean_dec_ref(v_as_4398_);
lean_dec_ref(v_a_4396_);
lean_dec_ref(v___x_4395_);
return v_res_4409_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(lean_object* v___y_4410_, lean_object* v_args_4411_, lean_object* v___x_4412_, lean_object* v_overlaps_4413_, lean_object* v_a_4414_, lean_object* v_fst_4415_, lean_object* v_a_4416_, lean_object* v___x_4417_, lean_object* v___x_4418_, lean_object* v___x_4419_, lean_object* v___x_4420_, lean_object* v_altVars_4421_, uint8_t v___x_4422_, uint8_t v___x_4423_, lean_object* v_a_4424_, lean_object* v___x_4425_, lean_object* v___x_4426_, lean_object* v___x_4427_, lean_object* v___x_4428_, lean_object* v___x_4429_, lean_object* v___x_4430_, lean_object* v___x_4431_, lean_object* v_matchDeclName_4432_, lean_object* v___x_4433_, lean_object* v___x_4434_, lean_object* v___x_4435_, lean_object* v_heqs_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
lean_object* v___x_4442_; lean_object* v___x_4443_; 
v___x_4442_ = l_Lean_mkAppN(v___y_4410_, v_args_4411_);
lean_inc(v___y_4440_);
lean_inc_ref(v___y_4439_);
lean_inc(v___y_4438_);
lean_inc_ref(v___y_4437_);
lean_inc_ref(v_heqs_4436_);
v___x_4443_ = l_Lean_Meta_Match_mkAppDiscrEqs(v___x_4442_, v_heqs_4436_, v___x_4412_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_);
if (lean_obj_tag(v___x_4443_) == 0)
{
lean_object* v_a_4444_; lean_object* v___x_4445_; size_t v_sz_4446_; size_t v___x_4447_; lean_object* v___x_4448_; 
v_a_4444_ = lean_ctor_get(v___x_4443_, 0);
lean_inc(v_a_4444_);
lean_dec_ref(v___x_4443_);
v___x_4445_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_4413_, v_a_4414_);
v_sz_4446_ = lean_array_size(v___x_4445_);
v___x_4447_ = ((size_t)0ULL);
lean_inc(v___y_4440_);
lean_inc_ref(v___y_4439_);
lean_inc(v___y_4438_);
lean_inc_ref(v___y_4437_);
lean_inc_ref(v___x_4418_);
v___x_4448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(v_fst_4415_, v_a_4416_, v___x_4417_, v___x_4445_, v_sz_4446_, v___x_4447_, v___x_4418_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_);
lean_dec_ref(v___x_4445_);
if (lean_obj_tag(v___x_4448_) == 0)
{
lean_object* v_a_4449_; lean_object* v___y_4451_; lean_object* v___y_4452_; lean_object* v___y_4453_; lean_object* v___y_4454_; lean_object* v___x_4561_; lean_object* v___x_4562_; 
v_a_4449_ = lean_ctor_get(v___x_4448_, 0);
lean_inc(v_a_4449_);
lean_dec_ref(v___x_4448_);
v___x_4561_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_4562_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___redArg(v___x_4561_, v___y_4439_);
if (lean_obj_tag(v___x_4562_) == 0)
{
lean_object* v_a_4563_; uint8_t v___x_4564_; 
v_a_4563_ = lean_ctor_get(v___x_4562_, 0);
lean_inc(v_a_4563_);
lean_dec_ref(v___x_4562_);
v___x_4564_ = lean_unbox(v_a_4563_);
lean_dec(v_a_4563_);
if (v___x_4564_ == 0)
{
v___y_4451_ = v___y_4437_;
v___y_4452_ = v___y_4438_;
v___y_4453_ = v___y_4439_;
v___y_4454_ = v___y_4440_;
goto v___jp_4450_;
}
else
{
lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; 
v___x_4565_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_4449_);
v___x_4566_ = lean_array_to_list(v_a_4449_);
v___x_4567_ = lean_box(0);
v___x_4568_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_4566_, v___x_4567_);
v___x_4569_ = l_Lean_MessageData_ofList(v___x_4568_);
v___x_4570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4570_, 0, v___x_4565_);
lean_ctor_set(v___x_4570_, 1, v___x_4569_);
v___x_4571_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(v___x_4561_, v___x_4570_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_);
if (lean_obj_tag(v___x_4571_) == 0)
{
lean_dec_ref(v___x_4571_);
v___y_4451_ = v___y_4437_;
v___y_4452_ = v___y_4438_;
v___y_4453_ = v___y_4439_;
v___y_4454_ = v___y_4440_;
goto v___jp_4450_;
}
else
{
lean_object* v_a_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4579_; 
lean_dec(v_a_4449_);
lean_dec(v_a_4444_);
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec_ref(v_heqs_4436_);
lean_dec(v___x_4435_);
lean_dec(v___x_4434_);
lean_dec(v___x_4433_);
lean_dec(v_matchDeclName_4432_);
lean_dec_ref(v___x_4429_);
lean_dec_ref(v___x_4428_);
lean_dec_ref(v___x_4426_);
lean_dec(v___x_4425_);
lean_dec_ref(v___x_4420_);
lean_dec(v___x_4419_);
lean_dec_ref(v___x_4418_);
lean_dec_ref(v_a_4416_);
v_a_4572_ = lean_ctor_get(v___x_4571_, 0);
v_isSharedCheck_4579_ = !lean_is_exclusive(v___x_4571_);
if (v_isSharedCheck_4579_ == 0)
{
v___x_4574_ = v___x_4571_;
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v___x_4571_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___x_4577_; 
if (v_isShared_4575_ == 0)
{
v___x_4577_ = v___x_4574_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4578_; 
v_reuseFailAlloc_4578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4578_, 0, v_a_4572_);
v___x_4577_ = v_reuseFailAlloc_4578_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
return v___x_4577_;
}
}
}
}
}
else
{
lean_object* v_a_4580_; lean_object* v___x_4582_; uint8_t v_isShared_4583_; uint8_t v_isSharedCheck_4587_; 
lean_dec(v_a_4449_);
lean_dec(v_a_4444_);
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec_ref(v_heqs_4436_);
lean_dec(v___x_4435_);
lean_dec(v___x_4434_);
lean_dec(v___x_4433_);
lean_dec(v_matchDeclName_4432_);
lean_dec_ref(v___x_4429_);
lean_dec_ref(v___x_4428_);
lean_dec_ref(v___x_4426_);
lean_dec(v___x_4425_);
lean_dec_ref(v___x_4420_);
lean_dec(v___x_4419_);
lean_dec_ref(v___x_4418_);
lean_dec_ref(v_a_4416_);
v_a_4580_ = lean_ctor_get(v___x_4562_, 0);
v_isSharedCheck_4587_ = !lean_is_exclusive(v___x_4562_);
if (v_isSharedCheck_4587_ == 0)
{
v___x_4582_ = v___x_4562_;
v_isShared_4583_ = v_isSharedCheck_4587_;
goto v_resetjp_4581_;
}
else
{
lean_inc(v_a_4580_);
lean_dec(v___x_4562_);
v___x_4582_ = lean_box(0);
v_isShared_4583_ = v_isSharedCheck_4587_;
goto v_resetjp_4581_;
}
v_resetjp_4581_:
{
lean_object* v___x_4585_; 
if (v_isShared_4583_ == 0)
{
v___x_4585_ = v___x_4582_;
goto v_reusejp_4584_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v_a_4580_);
v___x_4585_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4584_;
}
v_reusejp_4584_:
{
return v___x_4585_;
}
}
}
v___jp_4450_:
{
lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; size_t v_sz_4462_; lean_object* v___x_4463_; 
v___x_4455_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
v___x_4456_ = l_Array_reverse___redArg(v_a_4416_);
v___x_4457_ = lean_array_get_size(v___x_4456_);
v___x_4458_ = l_Array_toSubarray___redArg(v___x_4456_, v___x_4419_, v___x_4457_);
lean_inc_ref(v___x_4420_);
v___x_4459_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_4420_, v___x_4418_);
v___x_4460_ = l_Array_reverse___redArg(v___x_4459_);
v___x_4461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4461_, 0, v___x_4455_);
lean_ctor_set(v___x_4461_, 1, v___x_4458_);
v_sz_4462_ = lean_array_size(v___x_4460_);
lean_inc(v___y_4454_);
lean_inc_ref(v___y_4453_);
lean_inc(v___y_4452_);
lean_inc_ref(v___y_4451_);
v___x_4463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_4460_, v_sz_4462_, v___x_4447_, v___x_4461_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
lean_dec_ref(v___x_4460_);
if (lean_obj_tag(v___x_4463_) == 0)
{
lean_object* v_a_4464_; lean_object* v_fst_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4551_; 
v_a_4464_ = lean_ctor_get(v___x_4463_, 0);
lean_inc(v_a_4464_);
lean_dec_ref(v___x_4463_);
v_fst_4465_ = lean_ctor_get(v_a_4464_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v_a_4464_);
if (v_isSharedCheck_4551_ == 0)
{
lean_object* v_unused_4552_; 
v_unused_4552_ = lean_ctor_get(v_a_4464_, 1);
lean_dec(v_unused_4552_);
v___x_4467_ = v_a_4464_;
v_isShared_4468_ = v_isSharedCheck_4551_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_fst_4465_);
lean_dec(v_a_4464_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4551_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4469_; lean_object* v___x_4470_; uint8_t v___x_4471_; lean_object* v___x_4472_; 
v___x_4469_ = l_Subarray_copy___redArg(v___x_4420_);
lean_inc_ref(v___x_4469_);
v___x_4470_ = l_Array_append___redArg(v___x_4469_, v_altVars_4421_);
v___x_4471_ = 1;
v___x_4472_ = l_Lean_Meta_mkForallFVars(v___x_4470_, v_fst_4465_, v___x_4422_, v___x_4423_, v___x_4423_, v___x_4471_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
lean_dec_ref(v___x_4470_);
if (lean_obj_tag(v___x_4472_) == 0)
{
lean_object* v_a_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; 
v_a_4473_ = lean_ctor_get(v___x_4472_, 0);
lean_inc(v_a_4473_);
lean_dec_ref(v___x_4472_);
v___x_4474_ = l_Lean_ConstantInfo_name(v_a_4424_);
v___x_4475_ = l_Lean_mkConst(v___x_4474_, v___x_4425_);
lean_inc_ref(v___x_4426_);
v___x_4476_ = l_Subarray_copy___redArg(v___x_4426_);
v___x_4477_ = lean_mk_empty_array_with_capacity(v___x_4427_);
v___x_4478_ = lean_array_push(v___x_4477_, v___x_4428_);
v___x_4479_ = l_Array_append___redArg(v___x_4476_, v___x_4478_);
lean_dec_ref(v___x_4478_);
v___x_4480_ = l_Array_append___redArg(v___x_4479_, v___x_4469_);
lean_dec_ref(v___x_4469_);
v___x_4481_ = l_Subarray_copy___redArg(v___x_4429_);
v___x_4482_ = l_Array_append___redArg(v___x_4480_, v___x_4481_);
lean_dec_ref(v___x_4481_);
v___x_4483_ = l_Lean_mkAppN(v___x_4475_, v___x_4482_);
lean_inc(v___y_4454_);
lean_inc_ref(v___y_4453_);
lean_inc(v___y_4452_);
lean_inc_ref(v___y_4451_);
v___x_4484_ = l_Lean_Meta_mkHEq(v___x_4483_, v_a_4444_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
if (lean_obj_tag(v___x_4484_) == 0)
{
lean_object* v_a_4485_; lean_object* v___x_4486_; 
v_a_4485_ = lean_ctor_get(v___x_4484_, 0);
lean_inc(v_a_4485_);
lean_dec_ref(v___x_4484_);
lean_inc(v___y_4454_);
lean_inc_ref(v___y_4453_);
v___x_4486_ = l_Lean_mkArrowN(v_a_4449_, v_a_4485_, v___y_4453_, v___y_4454_);
lean_dec(v_a_4449_);
if (lean_obj_tag(v___x_4486_) == 0)
{
lean_object* v_a_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; 
v_a_4487_ = lean_ctor_get(v___x_4486_, 0);
lean_inc(v_a_4487_);
lean_dec_ref(v___x_4486_);
v___x_4488_ = l_Array_append___redArg(v___x_4482_, v_altVars_4421_);
v___x_4489_ = l_Array_append___redArg(v___x_4488_, v_heqs_4436_);
v___x_4490_ = l_Lean_Meta_mkForallFVars(v___x_4489_, v_a_4487_, v___x_4422_, v___x_4423_, v___x_4423_, v___x_4471_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
lean_dec_ref(v___x_4489_);
if (lean_obj_tag(v___x_4490_) == 0)
{
lean_object* v_a_4491_; lean_object* v___x_4492_; 
v_a_4491_ = lean_ctor_get(v___x_4490_, 0);
lean_inc(v_a_4491_);
lean_dec_ref(v___x_4490_);
lean_inc(v___y_4454_);
lean_inc_ref(v___y_4453_);
lean_inc(v___y_4452_);
lean_inc_ref(v___y_4451_);
v___x_4492_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_4491_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
if (lean_obj_tag(v___x_4492_) == 0)
{
lean_object* v_a_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4550_; 
v_a_4493_ = lean_ctor_get(v___x_4492_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4492_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4495_ = v___x_4492_;
v_isShared_4496_ = v_isSharedCheck_4550_;
goto v_resetjp_4494_;
}
else
{
lean_inc(v_a_4493_);
lean_dec(v___x_4492_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4550_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v_start_4497_; lean_object* v_stop_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4548_; 
v_start_4497_ = lean_ctor_get(v___x_4426_, 1);
v_stop_4498_ = lean_ctor_get(v___x_4426_, 2);
v_isSharedCheck_4548_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4548_ == 0)
{
lean_object* v_unused_4549_; 
v_unused_4549_ = lean_ctor_get(v___x_4426_, 0);
lean_dec(v_unused_4549_);
v___x_4500_ = v___x_4426_;
v_isShared_4501_ = v_isSharedCheck_4548_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_stop_4498_);
lean_inc(v_start_4497_);
lean_dec(v___x_4426_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4548_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; 
v___x_4502_ = lean_nat_sub(v_stop_4498_, v_start_4497_);
lean_dec(v_start_4497_);
lean_dec(v_stop_4498_);
v___x_4503_ = lean_nat_add(v___x_4502_, v___x_4427_);
lean_dec(v___x_4502_);
v___x_4504_ = lean_nat_add(v___x_4503_, v___x_4430_);
lean_dec(v___x_4503_);
v___x_4505_ = lean_nat_add(v___x_4504_, v___x_4431_);
lean_dec(v___x_4504_);
v___x_4506_ = lean_array_get_size(v_altVars_4421_);
v___x_4507_ = lean_nat_add(v___x_4505_, v___x_4506_);
lean_dec(v___x_4505_);
v___x_4508_ = lean_array_get_size(v_heqs_4436_);
lean_dec_ref(v_heqs_4436_);
lean_inc(v___y_4454_);
lean_inc_ref(v___y_4453_);
lean_inc(v_a_4493_);
v___x_4509_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_4432_, v_a_4493_, v___x_4507_, v___x_4508_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
if (lean_obj_tag(v___x_4509_) == 0)
{
lean_object* v_a_4510_; lean_object* v___x_4512_; uint8_t v_isShared_4513_; uint8_t v_isSharedCheck_4547_; 
v_a_4510_ = lean_ctor_get(v___x_4509_, 0);
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4509_);
if (v_isSharedCheck_4547_ == 0)
{
v___x_4512_ = v___x_4509_;
v_isShared_4513_ = v_isSharedCheck_4547_;
goto v_resetjp_4511_;
}
else
{
lean_inc(v_a_4510_);
lean_dec(v___x_4509_);
v___x_4512_ = lean_box(0);
v_isShared_4513_ = v_isSharedCheck_4547_;
goto v_resetjp_4511_;
}
v_resetjp_4511_:
{
lean_object* v___x_4514_; lean_object* v_env_4515_; uint8_t v___x_4516_; 
v___x_4514_ = lean_st_ref_get(v___y_4454_);
v_env_4515_ = lean_ctor_get(v___x_4514_, 0);
lean_inc_ref(v_env_4515_);
lean_dec(v___x_4514_);
lean_inc(v___x_4433_);
v___x_4516_ = l_Lean_Environment_contains(v_env_4515_, v___x_4433_, v___x_4423_);
if (v___x_4516_ == 0)
{
lean_object* v___x_4518_; 
lean_del_object(v___x_4512_);
lean_inc(v___x_4433_);
if (v_isShared_4501_ == 0)
{
lean_ctor_set(v___x_4500_, 2, v_a_4493_);
lean_ctor_set(v___x_4500_, 1, v___x_4434_);
lean_ctor_set(v___x_4500_, 0, v___x_4433_);
v___x_4518_ = v___x_4500_;
goto v_reusejp_4517_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v___x_4433_);
lean_ctor_set(v_reuseFailAlloc_4543_, 1, v___x_4434_);
lean_ctor_set(v_reuseFailAlloc_4543_, 2, v_a_4493_);
v___x_4518_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4517_;
}
v_reusejp_4517_:
{
lean_object* v___x_4520_; 
if (v_isShared_4468_ == 0)
{
lean_ctor_set_tag(v___x_4467_, 1);
lean_ctor_set(v___x_4467_, 1, v___x_4435_);
lean_ctor_set(v___x_4467_, 0, v___x_4433_);
v___x_4520_ = v___x_4467_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v___x_4433_);
lean_ctor_set(v_reuseFailAlloc_4542_, 1, v___x_4435_);
v___x_4520_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
lean_object* v___x_4521_; lean_object* v___x_4523_; 
v___x_4521_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4521_, 0, v___x_4518_);
lean_ctor_set(v___x_4521_, 1, v_a_4510_);
lean_ctor_set(v___x_4521_, 2, v___x_4520_);
if (v_isShared_4496_ == 0)
{
lean_ctor_set_tag(v___x_4495_, 2);
lean_ctor_set(v___x_4495_, 0, v___x_4521_);
v___x_4523_ = v___x_4495_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4541_; 
v_reuseFailAlloc_4541_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4541_, 0, v___x_4521_);
v___x_4523_ = v_reuseFailAlloc_4541_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
lean_object* v___x_4524_; 
v___x_4524_ = l_Lean_addDecl(v___x_4523_, v___x_4422_, v___y_4453_, v___y_4454_);
if (lean_obj_tag(v___x_4524_) == 0)
{
lean_object* v___x_4526_; uint8_t v_isShared_4527_; uint8_t v_isSharedCheck_4531_; 
v_isSharedCheck_4531_ = !lean_is_exclusive(v___x_4524_);
if (v_isSharedCheck_4531_ == 0)
{
lean_object* v_unused_4532_; 
v_unused_4532_ = lean_ctor_get(v___x_4524_, 0);
lean_dec(v_unused_4532_);
v___x_4526_ = v___x_4524_;
v_isShared_4527_ = v_isSharedCheck_4531_;
goto v_resetjp_4525_;
}
else
{
lean_dec(v___x_4524_);
v___x_4526_ = lean_box(0);
v_isShared_4527_ = v_isSharedCheck_4531_;
goto v_resetjp_4525_;
}
v_resetjp_4525_:
{
lean_object* v___x_4529_; 
if (v_isShared_4527_ == 0)
{
lean_ctor_set(v___x_4526_, 0, v_a_4473_);
v___x_4529_ = v___x_4526_;
goto v_reusejp_4528_;
}
else
{
lean_object* v_reuseFailAlloc_4530_; 
v_reuseFailAlloc_4530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4530_, 0, v_a_4473_);
v___x_4529_ = v_reuseFailAlloc_4530_;
goto v_reusejp_4528_;
}
v_reusejp_4528_:
{
return v___x_4529_;
}
}
}
else
{
lean_object* v_a_4533_; lean_object* v___x_4535_; uint8_t v_isShared_4536_; uint8_t v_isSharedCheck_4540_; 
lean_dec(v_a_4473_);
v_a_4533_ = lean_ctor_get(v___x_4524_, 0);
v_isSharedCheck_4540_ = !lean_is_exclusive(v___x_4524_);
if (v_isSharedCheck_4540_ == 0)
{
v___x_4535_ = v___x_4524_;
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
else
{
lean_inc(v_a_4533_);
lean_dec(v___x_4524_);
v___x_4535_ = lean_box(0);
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
v_resetjp_4534_:
{
lean_object* v___x_4538_; 
if (v_isShared_4536_ == 0)
{
v___x_4538_ = v___x_4535_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v_a_4533_);
v___x_4538_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
return v___x_4538_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4545_; 
lean_dec(v_a_4510_);
lean_del_object(v___x_4500_);
lean_del_object(v___x_4495_);
lean_dec(v_a_4493_);
lean_del_object(v___x_4467_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___x_4435_);
lean_dec(v___x_4434_);
lean_dec(v___x_4433_);
if (v_isShared_4513_ == 0)
{
lean_ctor_set(v___x_4512_, 0, v_a_4473_);
v___x_4545_ = v___x_4512_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v_a_4473_);
v___x_4545_ = v_reuseFailAlloc_4546_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
return v___x_4545_;
}
}
}
}
else
{
lean_del_object(v___x_4500_);
lean_del_object(v___x_4495_);
lean_dec(v_a_4493_);
lean_dec(v_a_4473_);
lean_del_object(v___x_4467_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___x_4435_);
lean_dec(v___x_4434_);
lean_dec(v___x_4433_);
return v___x_4509_;
}
}
}
}
else
{
lean_dec(v_a_4473_);
lean_del_object(v___x_4467_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec_ref(v_heqs_4436_);
lean_dec(v___x_4435_);
lean_dec(v___x_4434_);
lean_dec(v___x_4433_);
lean_dec(v_matchDeclName_4432_);
lean_dec_ref(v___x_4426_);
return v___x_4492_;
}
}
else
{
lean_dec(v_a_4473_);
lean_del_object(v___x_4467_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec_ref(v_heqs_4436_);
lean_dec(v___x_4435_);
lean_dec(v___x_4434_);
lean_dec(v___x_4433_);
lean_dec(v_matchDeclName_4432_);
lean_dec_ref(v___x_4426_);
return v___x_4490_;
}
}
else
{
lean_dec_ref(v___x_4482_);
lean_dec(v_a_4473_);
lean_del_object(v___x_4467_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec_ref(v_heqs_4436_);
lean_dec(v___x_4435_);
lean_dec(v___x_4434_);
lean_dec(v___x_4433_);
lean_dec(v_matchDeclName_4432_);
lean_dec_ref(v___x_4426_);
return v___x_4486_;
}
}
else
{
lean_dec_ref(v___x_4482_);
lean_dec(v_a_4473_);
lean_del_object(v___x_4467_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v_a_4449_);
lean_dec_ref(v_heqs_4436_);
lean_dec(v___x_4435_);
lean_dec(v___x_4434_);
lean_dec(v___x_4433_);
lean_dec(v_matchDeclName_4432_);
lean_dec_ref(v___x_4426_);
return v___x_4484_;
}
}
else
{
lean_dec_ref(v___x_4469_);
lean_del_object(v___x_4467_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v_a_4449_);
lean_dec(v_a_4444_);
lean_dec_ref(v_heqs_4436_);
lean_dec(v___x_4435_);
lean_dec(v___x_4434_);
lean_dec(v___x_4433_);
lean_dec(v_matchDeclName_4432_);
lean_dec_ref(v___x_4429_);
lean_dec_ref(v___x_4428_);
lean_dec_ref(v___x_4426_);
lean_dec(v___x_4425_);
return v___x_4472_;
}
}
}
else
{
lean_object* v_a_4553_; lean_object* v___x_4555_; uint8_t v_isShared_4556_; uint8_t v_isSharedCheck_4560_; 
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v_a_4449_);
lean_dec(v_a_4444_);
lean_dec_ref(v_heqs_4436_);
lean_dec(v___x_4435_);
lean_dec(v___x_4434_);
lean_dec(v___x_4433_);
lean_dec(v_matchDeclName_4432_);
lean_dec_ref(v___x_4429_);
lean_dec_ref(v___x_4428_);
lean_dec_ref(v___x_4426_);
lean_dec(v___x_4425_);
lean_dec_ref(v___x_4420_);
v_a_4553_ = lean_ctor_get(v___x_4463_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v___x_4463_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4555_ = v___x_4463_;
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
else
{
lean_inc(v_a_4553_);
lean_dec(v___x_4463_);
v___x_4555_ = lean_box(0);
v_isShared_4556_ = v_isSharedCheck_4560_;
goto v_resetjp_4554_;
}
v_resetjp_4554_:
{
lean_object* v___x_4558_; 
if (v_isShared_4556_ == 0)
{
v___x_4558_ = v___x_4555_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v_a_4553_);
v___x_4558_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
return v___x_4558_;
}
}
}
}
}
else
{
lean_object* v_a_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4595_; 
lean_dec(v_a_4444_);
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec_ref(v_heqs_4436_);
lean_dec(v___x_4435_);
lean_dec(v___x_4434_);
lean_dec(v___x_4433_);
lean_dec(v_matchDeclName_4432_);
lean_dec_ref(v___x_4429_);
lean_dec_ref(v___x_4428_);
lean_dec_ref(v___x_4426_);
lean_dec(v___x_4425_);
lean_dec_ref(v___x_4420_);
lean_dec(v___x_4419_);
lean_dec_ref(v___x_4418_);
lean_dec_ref(v_a_4416_);
v_a_4588_ = lean_ctor_get(v___x_4448_, 0);
v_isSharedCheck_4595_ = !lean_is_exclusive(v___x_4448_);
if (v_isSharedCheck_4595_ == 0)
{
v___x_4590_ = v___x_4448_;
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_a_4588_);
lean_dec(v___x_4448_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v___x_4593_; 
if (v_isShared_4591_ == 0)
{
v___x_4593_ = v___x_4590_;
goto v_reusejp_4592_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v_a_4588_);
v___x_4593_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4592_;
}
v_reusejp_4592_:
{
return v___x_4593_;
}
}
}
}
else
{
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec_ref(v_heqs_4436_);
lean_dec(v___x_4435_);
lean_dec(v___x_4434_);
lean_dec(v___x_4433_);
lean_dec(v_matchDeclName_4432_);
lean_dec_ref(v___x_4429_);
lean_dec_ref(v___x_4428_);
lean_dec_ref(v___x_4426_);
lean_dec(v___x_4425_);
lean_dec_ref(v___x_4420_);
lean_dec(v___x_4419_);
lean_dec_ref(v___x_4418_);
lean_dec(v___x_4417_);
lean_dec_ref(v_a_4416_);
return v___x_4443_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___y_4596_ = _args[0];
lean_object* v_args_4597_ = _args[1];
lean_object* v___x_4598_ = _args[2];
lean_object* v_overlaps_4599_ = _args[3];
lean_object* v_a_4600_ = _args[4];
lean_object* v_fst_4601_ = _args[5];
lean_object* v_a_4602_ = _args[6];
lean_object* v___x_4603_ = _args[7];
lean_object* v___x_4604_ = _args[8];
lean_object* v___x_4605_ = _args[9];
lean_object* v___x_4606_ = _args[10];
lean_object* v_altVars_4607_ = _args[11];
lean_object* v___x_4608_ = _args[12];
lean_object* v___x_4609_ = _args[13];
lean_object* v_a_4610_ = _args[14];
lean_object* v___x_4611_ = _args[15];
lean_object* v___x_4612_ = _args[16];
lean_object* v___x_4613_ = _args[17];
lean_object* v___x_4614_ = _args[18];
lean_object* v___x_4615_ = _args[19];
lean_object* v___x_4616_ = _args[20];
lean_object* v___x_4617_ = _args[21];
lean_object* v_matchDeclName_4618_ = _args[22];
lean_object* v___x_4619_ = _args[23];
lean_object* v___x_4620_ = _args[24];
lean_object* v___x_4621_ = _args[25];
lean_object* v_heqs_4622_ = _args[26];
lean_object* v___y_4623_ = _args[27];
lean_object* v___y_4624_ = _args[28];
lean_object* v___y_4625_ = _args[29];
lean_object* v___y_4626_ = _args[30];
lean_object* v___y_4627_ = _args[31];
_start:
{
uint8_t v___x_21845__boxed_4628_; uint8_t v___x_21846__boxed_4629_; lean_object* v_res_4630_; 
v___x_21845__boxed_4628_ = lean_unbox(v___x_4608_);
v___x_21846__boxed_4629_ = lean_unbox(v___x_4609_);
v_res_4630_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(v___y_4596_, v_args_4597_, v___x_4598_, v_overlaps_4599_, v_a_4600_, v_fst_4601_, v_a_4602_, v___x_4603_, v___x_4604_, v___x_4605_, v___x_4606_, v_altVars_4607_, v___x_21845__boxed_4628_, v___x_21846__boxed_4629_, v_a_4610_, v___x_4611_, v___x_4612_, v___x_4613_, v___x_4614_, v___x_4615_, v___x_4616_, v___x_4617_, v_matchDeclName_4618_, v___x_4619_, v___x_4620_, v___x_4621_, v_heqs_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_);
lean_dec(v___x_4617_);
lean_dec(v___x_4616_);
lean_dec(v___x_4613_);
lean_dec_ref(v_a_4610_);
lean_dec_ref(v_altVars_4607_);
lean_dec(v_fst_4601_);
lean_dec(v_a_4600_);
lean_dec_ref(v_overlaps_4599_);
lean_dec_ref(v_args_4597_);
return v_res_4630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(lean_object* v_snd_4631_, lean_object* v_x_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_){
_start:
{
lean_object* v___x_4638_; 
v___x_4638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4638_, 0, v_snd_4631_);
return v___x_4638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed(lean_object* v_snd_4639_, lean_object* v_x_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_){
_start:
{
lean_object* v_res_4646_; 
v_res_4646_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(v_snd_4639_, v_x_4640_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_);
lean_dec(v___y_4644_);
lean_dec_ref(v___y_4643_);
lean_dec(v___y_4642_);
lean_dec_ref(v___y_4641_);
lean_dec_ref(v_x_4640_);
return v_res_4646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(size_t v_sz_4647_, size_t v_i_4648_, lean_object* v_bs_4649_){
_start:
{
uint8_t v___x_4650_; 
v___x_4650_ = lean_usize_dec_lt(v_i_4648_, v_sz_4647_);
if (v___x_4650_ == 0)
{
return v_bs_4649_;
}
else
{
lean_object* v_v_4651_; lean_object* v_fst_4652_; lean_object* v_snd_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4667_; 
v_v_4651_ = lean_array_uget(v_bs_4649_, v_i_4648_);
v_fst_4652_ = lean_ctor_get(v_v_4651_, 0);
v_snd_4653_ = lean_ctor_get(v_v_4651_, 1);
v_isSharedCheck_4667_ = !lean_is_exclusive(v_v_4651_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4655_ = v_v_4651_;
v_isShared_4656_ = v_isSharedCheck_4667_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_snd_4653_);
lean_inc(v_fst_4652_);
lean_dec(v_v_4651_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4667_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
lean_object* v___x_4657_; lean_object* v_bs_x27_4658_; lean_object* v___f_4659_; lean_object* v___x_4661_; 
v___x_4657_ = lean_unsigned_to_nat(0u);
v_bs_x27_4658_ = lean_array_uset(v_bs_4649_, v_i_4648_, v___x_4657_);
v___f_4659_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4659_, 0, v_snd_4653_);
if (v_isShared_4656_ == 0)
{
lean_ctor_set(v___x_4655_, 1, v___f_4659_);
v___x_4661_ = v___x_4655_;
goto v_reusejp_4660_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v_fst_4652_);
lean_ctor_set(v_reuseFailAlloc_4666_, 1, v___f_4659_);
v___x_4661_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4660_;
}
v_reusejp_4660_:
{
size_t v___x_4662_; size_t v___x_4663_; lean_object* v___x_4664_; 
v___x_4662_ = ((size_t)1ULL);
v___x_4663_ = lean_usize_add(v_i_4648_, v___x_4662_);
v___x_4664_ = lean_array_uset(v_bs_x27_4658_, v_i_4648_, v___x_4661_);
v_i_4648_ = v___x_4663_;
v_bs_4649_ = v___x_4664_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___boxed(lean_object* v_sz_4668_, lean_object* v_i_4669_, lean_object* v_bs_4670_){
_start:
{
size_t v_sz_boxed_4671_; size_t v_i_boxed_4672_; lean_object* v_res_4673_; 
v_sz_boxed_4671_ = lean_unbox_usize(v_sz_4668_);
lean_dec(v_sz_4668_);
v_i_boxed_4672_ = lean_unbox_usize(v_i_4669_);
lean_dec(v_i_4669_);
v_res_4673_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_boxed_4671_, v_i_boxed_4672_, v_bs_4670_);
return v_res_4673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(size_t v_sz_4674_, size_t v_i_4675_, lean_object* v_bs_4676_){
_start:
{
uint8_t v___x_4677_; 
v___x_4677_ = lean_usize_dec_lt(v_i_4675_, v_sz_4674_);
if (v___x_4677_ == 0)
{
return v_bs_4676_;
}
else
{
lean_object* v_v_4678_; lean_object* v_fst_4679_; lean_object* v_snd_4680_; lean_object* v___x_4682_; uint8_t v_isShared_4683_; uint8_t v_isSharedCheck_4696_; 
v_v_4678_ = lean_array_uget(v_bs_4676_, v_i_4675_);
v_fst_4679_ = lean_ctor_get(v_v_4678_, 0);
v_snd_4680_ = lean_ctor_get(v_v_4678_, 1);
v_isSharedCheck_4696_ = !lean_is_exclusive(v_v_4678_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4682_ = v_v_4678_;
v_isShared_4683_ = v_isSharedCheck_4696_;
goto v_resetjp_4681_;
}
else
{
lean_inc(v_snd_4680_);
lean_inc(v_fst_4679_);
lean_dec(v_v_4678_);
v___x_4682_ = lean_box(0);
v_isShared_4683_ = v_isSharedCheck_4696_;
goto v_resetjp_4681_;
}
v_resetjp_4681_:
{
lean_object* v___x_4684_; lean_object* v_bs_x27_4685_; uint8_t v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4689_; 
v___x_4684_ = lean_unsigned_to_nat(0u);
v_bs_x27_4685_ = lean_array_uset(v_bs_4676_, v_i_4675_, v___x_4684_);
v___x_4686_ = 0;
v___x_4687_ = lean_box(v___x_4686_);
if (v_isShared_4683_ == 0)
{
lean_ctor_set(v___x_4682_, 0, v___x_4687_);
v___x_4689_ = v___x_4682_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4695_; 
v_reuseFailAlloc_4695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4695_, 0, v___x_4687_);
lean_ctor_set(v_reuseFailAlloc_4695_, 1, v_snd_4680_);
v___x_4689_ = v_reuseFailAlloc_4695_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
lean_object* v___x_4690_; size_t v___x_4691_; size_t v___x_4692_; lean_object* v___x_4693_; 
v___x_4690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4690_, 0, v_fst_4679_);
lean_ctor_set(v___x_4690_, 1, v___x_4689_);
v___x_4691_ = ((size_t)1ULL);
v___x_4692_ = lean_usize_add(v_i_4675_, v___x_4691_);
v___x_4693_ = lean_array_uset(v_bs_x27_4685_, v_i_4675_, v___x_4690_);
v_i_4675_ = v___x_4692_;
v_bs_4676_ = v___x_4693_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6___boxed(lean_object* v_sz_4697_, lean_object* v_i_4698_, lean_object* v_bs_4699_){
_start:
{
size_t v_sz_boxed_4700_; size_t v_i_boxed_4701_; lean_object* v_res_4702_; 
v_sz_boxed_4700_ = lean_unbox_usize(v_sz_4697_);
lean_dec(v_sz_4697_);
v_i_boxed_4701_ = lean_unbox_usize(v_i_4698_);
lean_dec(v_i_4698_);
v_res_4702_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_boxed_4700_, v_i_boxed_4701_, v_bs_4699_);
return v_res_4702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___lam__0(lean_object* v___x_4703_, lean_object* v_a_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_){
_start:
{
lean_object* v___x_4710_; lean_object* v___x_21460__overap_4711_; lean_object* v___x_4712_; 
v___x_4710_ = l_Lean_instInhabitedExpr;
v___x_21460__overap_4711_ = l_instInhabitedOfMonad___redArg(v___x_4703_, v___x_4710_);
v___x_4712_ = lean_apply_5(v___x_21460__overap_4711_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_, lean_box(0));
return v___x_4712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___lam__0___boxed(lean_object* v___x_4713_, lean_object* v_a_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_){
_start:
{
lean_object* v_res_4720_; 
v_res_4720_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___lam__0(v___x_4713_, v_a_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
lean_dec_ref(v_a_4714_);
return v_res_4720_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_4721_; 
v___x_4721_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_4721_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_4722_; lean_object* v___x_4723_; 
v___x_4722_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__0);
v___x_4723_ = l_ReaderT_instMonad___redArg(v___x_4722_);
return v___x_4723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___lam__1___boxed(lean_object* v_acc_4728_, lean_object* v_declInfos_4729_, lean_object* v_k_4730_, lean_object* v_kind_4731_, lean_object* v_x_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_){
_start:
{
uint8_t v_kind_boxed_4738_; lean_object* v_res_4739_; 
v_kind_boxed_4738_ = lean_unbox(v_kind_4731_);
v_res_4739_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___lam__1(v_acc_4728_, v_declInfos_4729_, v_k_4730_, v_kind_boxed_4738_, v_x_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_);
return v_res_4739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg(lean_object* v_declInfos_4740_, lean_object* v_k_4741_, uint8_t v_kind_4742_, lean_object* v_acc_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_){
_start:
{
lean_object* v___x_4749_; lean_object* v_toApplicative_4750_; lean_object* v___x_4752_; uint8_t v_isShared_4753_; uint8_t v_isSharedCheck_4837_; 
v___x_4749_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__1);
v_toApplicative_4750_ = lean_ctor_get(v___x_4749_, 0);
v_isSharedCheck_4837_ = !lean_is_exclusive(v___x_4749_);
if (v_isSharedCheck_4837_ == 0)
{
lean_object* v_unused_4838_; 
v_unused_4838_ = lean_ctor_get(v___x_4749_, 1);
lean_dec(v_unused_4838_);
v___x_4752_ = v___x_4749_;
v_isShared_4753_ = v_isSharedCheck_4837_;
goto v_resetjp_4751_;
}
else
{
lean_inc(v_toApplicative_4750_);
lean_dec(v___x_4749_);
v___x_4752_ = lean_box(0);
v_isShared_4753_ = v_isSharedCheck_4837_;
goto v_resetjp_4751_;
}
v_resetjp_4751_:
{
lean_object* v_toFunctor_4754_; lean_object* v_toSeq_4755_; lean_object* v_toSeqLeft_4756_; lean_object* v_toSeqRight_4757_; lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4835_; 
v_toFunctor_4754_ = lean_ctor_get(v_toApplicative_4750_, 0);
v_toSeq_4755_ = lean_ctor_get(v_toApplicative_4750_, 2);
v_toSeqLeft_4756_ = lean_ctor_get(v_toApplicative_4750_, 3);
v_toSeqRight_4757_ = lean_ctor_get(v_toApplicative_4750_, 4);
v_isSharedCheck_4835_ = !lean_is_exclusive(v_toApplicative_4750_);
if (v_isSharedCheck_4835_ == 0)
{
lean_object* v_unused_4836_; 
v_unused_4836_ = lean_ctor_get(v_toApplicative_4750_, 1);
lean_dec(v_unused_4836_);
v___x_4759_ = v_toApplicative_4750_;
v_isShared_4760_ = v_isSharedCheck_4835_;
goto v_resetjp_4758_;
}
else
{
lean_inc(v_toSeqRight_4757_);
lean_inc(v_toSeqLeft_4756_);
lean_inc(v_toSeq_4755_);
lean_inc(v_toFunctor_4754_);
lean_dec(v_toApplicative_4750_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4835_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
lean_object* v___f_4761_; lean_object* v___f_4762_; lean_object* v___f_4763_; lean_object* v___f_4764_; lean_object* v___x_4765_; lean_object* v___f_4766_; lean_object* v___f_4767_; lean_object* v___f_4768_; lean_object* v___x_4770_; 
v___f_4761_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__2));
v___f_4762_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__3));
lean_inc_ref(v_toFunctor_4754_);
v___f_4763_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4763_, 0, v_toFunctor_4754_);
v___f_4764_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4764_, 0, v_toFunctor_4754_);
v___x_4765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4765_, 0, v___f_4763_);
lean_ctor_set(v___x_4765_, 1, v___f_4764_);
v___f_4766_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4766_, 0, v_toSeqRight_4757_);
v___f_4767_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4767_, 0, v_toSeqLeft_4756_);
v___f_4768_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4768_, 0, v_toSeq_4755_);
if (v_isShared_4760_ == 0)
{
lean_ctor_set(v___x_4759_, 4, v___f_4766_);
lean_ctor_set(v___x_4759_, 3, v___f_4767_);
lean_ctor_set(v___x_4759_, 2, v___f_4768_);
lean_ctor_set(v___x_4759_, 1, v___f_4761_);
lean_ctor_set(v___x_4759_, 0, v___x_4765_);
v___x_4770_ = v___x_4759_;
goto v_reusejp_4769_;
}
else
{
lean_object* v_reuseFailAlloc_4834_; 
v_reuseFailAlloc_4834_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4834_, 0, v___x_4765_);
lean_ctor_set(v_reuseFailAlloc_4834_, 1, v___f_4761_);
lean_ctor_set(v_reuseFailAlloc_4834_, 2, v___f_4768_);
lean_ctor_set(v_reuseFailAlloc_4834_, 3, v___f_4767_);
lean_ctor_set(v_reuseFailAlloc_4834_, 4, v___f_4766_);
v___x_4770_ = v_reuseFailAlloc_4834_;
goto v_reusejp_4769_;
}
v_reusejp_4769_:
{
lean_object* v___x_4772_; 
if (v_isShared_4753_ == 0)
{
lean_ctor_set(v___x_4752_, 1, v___f_4762_);
lean_ctor_set(v___x_4752_, 0, v___x_4770_);
v___x_4772_ = v___x_4752_;
goto v_reusejp_4771_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v___x_4770_);
lean_ctor_set(v_reuseFailAlloc_4833_, 1, v___f_4762_);
v___x_4772_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4771_;
}
v_reusejp_4771_:
{
lean_object* v___x_4773_; lean_object* v_toApplicative_4774_; lean_object* v___x_4776_; uint8_t v_isShared_4777_; uint8_t v_isSharedCheck_4831_; 
v___x_4773_ = l_ReaderT_instMonad___redArg(v___x_4772_);
v_toApplicative_4774_ = lean_ctor_get(v___x_4773_, 0);
v_isSharedCheck_4831_ = !lean_is_exclusive(v___x_4773_);
if (v_isSharedCheck_4831_ == 0)
{
lean_object* v_unused_4832_; 
v_unused_4832_ = lean_ctor_get(v___x_4773_, 1);
lean_dec(v_unused_4832_);
v___x_4776_ = v___x_4773_;
v_isShared_4777_ = v_isSharedCheck_4831_;
goto v_resetjp_4775_;
}
else
{
lean_inc(v_toApplicative_4774_);
lean_dec(v___x_4773_);
v___x_4776_ = lean_box(0);
v_isShared_4777_ = v_isSharedCheck_4831_;
goto v_resetjp_4775_;
}
v_resetjp_4775_:
{
lean_object* v_toFunctor_4778_; lean_object* v_toSeq_4779_; lean_object* v_toSeqLeft_4780_; lean_object* v_toSeqRight_4781_; lean_object* v___x_4783_; uint8_t v_isShared_4784_; uint8_t v_isSharedCheck_4829_; 
v_toFunctor_4778_ = lean_ctor_get(v_toApplicative_4774_, 0);
v_toSeq_4779_ = lean_ctor_get(v_toApplicative_4774_, 2);
v_toSeqLeft_4780_ = lean_ctor_get(v_toApplicative_4774_, 3);
v_toSeqRight_4781_ = lean_ctor_get(v_toApplicative_4774_, 4);
v_isSharedCheck_4829_ = !lean_is_exclusive(v_toApplicative_4774_);
if (v_isSharedCheck_4829_ == 0)
{
lean_object* v_unused_4830_; 
v_unused_4830_ = lean_ctor_get(v_toApplicative_4774_, 1);
lean_dec(v_unused_4830_);
v___x_4783_ = v_toApplicative_4774_;
v_isShared_4784_ = v_isSharedCheck_4829_;
goto v_resetjp_4782_;
}
else
{
lean_inc(v_toSeqRight_4781_);
lean_inc(v_toSeqLeft_4780_);
lean_inc(v_toSeq_4779_);
lean_inc(v_toFunctor_4778_);
lean_dec(v_toApplicative_4774_);
v___x_4783_ = lean_box(0);
v_isShared_4784_ = v_isSharedCheck_4829_;
goto v_resetjp_4782_;
}
v_resetjp_4782_:
{
lean_object* v___f_4785_; lean_object* v___f_4786_; lean_object* v___f_4787_; lean_object* v___f_4788_; lean_object* v___x_4789_; lean_object* v___f_4790_; lean_object* v___f_4791_; lean_object* v___f_4792_; lean_object* v___x_4794_; 
v___f_4785_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__4));
v___f_4786_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___closed__5));
lean_inc_ref(v_toFunctor_4778_);
v___f_4787_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4787_, 0, v_toFunctor_4778_);
v___f_4788_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4788_, 0, v_toFunctor_4778_);
v___x_4789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4789_, 0, v___f_4787_);
lean_ctor_set(v___x_4789_, 1, v___f_4788_);
v___f_4790_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4790_, 0, v_toSeqRight_4781_);
v___f_4791_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4791_, 0, v_toSeqLeft_4780_);
v___f_4792_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4792_, 0, v_toSeq_4779_);
if (v_isShared_4784_ == 0)
{
lean_ctor_set(v___x_4783_, 4, v___f_4790_);
lean_ctor_set(v___x_4783_, 3, v___f_4791_);
lean_ctor_set(v___x_4783_, 2, v___f_4792_);
lean_ctor_set(v___x_4783_, 1, v___f_4785_);
lean_ctor_set(v___x_4783_, 0, v___x_4789_);
v___x_4794_ = v___x_4783_;
goto v_reusejp_4793_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v___x_4789_);
lean_ctor_set(v_reuseFailAlloc_4828_, 1, v___f_4785_);
lean_ctor_set(v_reuseFailAlloc_4828_, 2, v___f_4792_);
lean_ctor_set(v_reuseFailAlloc_4828_, 3, v___f_4791_);
lean_ctor_set(v_reuseFailAlloc_4828_, 4, v___f_4790_);
v___x_4794_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4793_;
}
v_reusejp_4793_:
{
lean_object* v___x_4796_; 
if (v_isShared_4777_ == 0)
{
lean_ctor_set(v___x_4776_, 1, v___f_4786_);
lean_ctor_set(v___x_4776_, 0, v___x_4794_);
v___x_4796_ = v___x_4776_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4827_; 
v_reuseFailAlloc_4827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4827_, 0, v___x_4794_);
lean_ctor_set(v_reuseFailAlloc_4827_, 1, v___f_4786_);
v___x_4796_ = v_reuseFailAlloc_4827_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
lean_object* v___x_4797_; lean_object* v___x_4798_; uint8_t v___x_4799_; 
v___x_4797_ = lean_array_get_size(v_acc_4743_);
v___x_4798_ = lean_array_get_size(v_declInfos_4740_);
v___x_4799_ = lean_nat_dec_lt(v___x_4797_, v___x_4798_);
if (v___x_4799_ == 0)
{
lean_object* v___x_4800_; 
lean_dec_ref(v___x_4796_);
lean_dec_ref(v_declInfos_4740_);
v___x_4800_ = lean_apply_6(v_k_4741_, v_acc_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, lean_box(0));
return v___x_4800_;
}
else
{
lean_object* v___f_4801_; lean_object* v___x_4802_; uint8_t v___x_4803_; lean_object* v___f_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v_snd_4809_; lean_object* v_fst_4810_; lean_object* v_fst_4811_; lean_object* v_snd_4812_; lean_object* v___x_4813_; 
v___f_4801_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4801_, 0, v___x_4796_);
v___x_4802_ = lean_box(0);
v___x_4803_ = 0;
v___f_4804_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4804_, 0, v___f_4801_);
v___x_4805_ = lean_box(v___x_4803_);
v___x_4806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4806_, 0, v___x_4805_);
lean_ctor_set(v___x_4806_, 1, v___f_4804_);
v___x_4807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4807_, 0, v___x_4802_);
lean_ctor_set(v___x_4807_, 1, v___x_4806_);
v___x_4808_ = lean_array_get_borrowed(v___x_4807_, v_declInfos_4740_, v___x_4797_);
v_snd_4809_ = lean_ctor_get(v___x_4808_, 1);
v_fst_4810_ = lean_ctor_get(v___x_4808_, 0);
lean_inc(v_fst_4810_);
v_fst_4811_ = lean_ctor_get(v_snd_4809_, 0);
lean_inc(v_fst_4811_);
v_snd_4812_ = lean_ctor_get(v_snd_4809_, 1);
lean_inc(v_snd_4812_);
lean_inc(v___y_4747_);
lean_inc_ref(v___y_4746_);
lean_inc(v___y_4745_);
lean_inc_ref(v___y_4744_);
lean_inc_ref(v_acc_4743_);
v___x_4813_ = lean_apply_6(v_snd_4812_, v_acc_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, lean_box(0));
if (lean_obj_tag(v___x_4813_) == 0)
{
lean_object* v_a_4814_; lean_object* v___x_4815_; lean_object* v___f_4816_; uint8_t v___x_4817_; lean_object* v___x_4818_; 
v_a_4814_ = lean_ctor_get(v___x_4813_, 0);
lean_inc(v_a_4814_);
lean_dec_ref(v___x_4813_);
v___x_4815_ = lean_box(v_kind_4742_);
v___f_4816_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_4816_, 0, v_acc_4743_);
lean_closure_set(v___f_4816_, 1, v_declInfos_4740_);
lean_closure_set(v___f_4816_, 2, v_k_4741_);
lean_closure_set(v___f_4816_, 3, v___x_4815_);
v___x_4817_ = lean_unbox(v_fst_4811_);
lean_dec(v_fst_4811_);
v___x_4818_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_fst_4810_, v___x_4817_, v_a_4814_, v___f_4816_, v_kind_4742_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_);
return v___x_4818_;
}
else
{
lean_object* v_a_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4826_; 
lean_dec(v_fst_4811_);
lean_dec(v_fst_4810_);
lean_dec(v___y_4747_);
lean_dec_ref(v___y_4746_);
lean_dec(v___y_4745_);
lean_dec_ref(v___y_4744_);
lean_dec_ref(v_acc_4743_);
lean_dec_ref(v_k_4741_);
lean_dec_ref(v_declInfos_4740_);
v_a_4819_ = lean_ctor_get(v___x_4813_, 0);
v_isSharedCheck_4826_ = !lean_is_exclusive(v___x_4813_);
if (v_isSharedCheck_4826_ == 0)
{
v___x_4821_ = v___x_4813_;
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_a_4819_);
lean_dec(v___x_4813_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v___x_4824_; 
if (v_isShared_4822_ == 0)
{
v___x_4824_ = v___x_4821_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v_a_4819_);
v___x_4824_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
return v___x_4824_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___lam__1(lean_object* v_acc_4839_, lean_object* v_declInfos_4840_, lean_object* v_k_4841_, uint8_t v_kind_4842_, lean_object* v_x_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_){
_start:
{
lean_object* v___x_4849_; lean_object* v___x_4850_; 
v___x_4849_ = lean_array_push(v_acc_4839_, v_x_4843_);
v___x_4850_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg(v_declInfos_4840_, v_k_4841_, v_kind_4842_, v___x_4849_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_);
return v___x_4850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_declInfos_4851_, lean_object* v_k_4852_, lean_object* v_kind_4853_, lean_object* v_acc_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_){
_start:
{
uint8_t v_kind_boxed_4860_; lean_object* v_res_4861_; 
v_kind_boxed_4860_ = lean_unbox(v_kind_4853_);
v_res_4861_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg(v_declInfos_4851_, v_k_4852_, v_kind_boxed_4860_, v_acc_4854_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_);
return v_res_4861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7___redArg(lean_object* v_inst_4862_, lean_object* v_declInfos_4863_, lean_object* v_k_4864_, uint8_t v_kind_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_){
_start:
{
lean_object* v___x_4871_; lean_object* v___x_4872_; 
v___x_4871_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4872_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg(v_declInfos_4863_, v_k_4864_, v_kind_4865_, v___x_4871_, v___y_4866_, v___y_4867_, v___y_4868_, v___y_4869_);
return v___x_4872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_inst_4873_, lean_object* v_declInfos_4874_, lean_object* v_k_4875_, lean_object* v_kind_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_){
_start:
{
uint8_t v_kind_boxed_4882_; lean_object* v_res_4883_; 
v_kind_boxed_4882_ = lean_unbox(v_kind_4876_);
v_res_4883_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7___redArg(v_inst_4873_, v_declInfos_4874_, v_k_4875_, v_kind_boxed_4882_, v___y_4877_, v___y_4878_, v___y_4879_, v___y_4880_);
lean_dec(v_inst_4873_);
return v_res_4883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5___redArg(lean_object* v_inst_4884_, lean_object* v_declInfos_4885_, lean_object* v_k_4886_, uint8_t v_kind_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_){
_start:
{
size_t v_sz_4893_; size_t v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; 
v_sz_4893_ = lean_array_size(v_declInfos_4885_);
v___x_4894_ = ((size_t)0ULL);
v___x_4895_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_4893_, v___x_4894_, v_declInfos_4885_);
v___x_4896_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7___redArg(v_inst_4884_, v___x_4895_, v_k_4886_, v_kind_4887_, v___y_4888_, v___y_4889_, v___y_4890_, v___y_4891_);
return v___x_4896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5___redArg___boxed(lean_object* v_inst_4897_, lean_object* v_declInfos_4898_, lean_object* v_k_4899_, lean_object* v_kind_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_){
_start:
{
uint8_t v_kind_boxed_4906_; lean_object* v_res_4907_; 
v_kind_boxed_4906_ = lean_unbox(v_kind_4900_);
v_res_4907_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5___redArg(v_inst_4897_, v_declInfos_4898_, v_k_4899_, v_kind_boxed_4906_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_);
lean_dec(v_inst_4897_);
return v_res_4907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4___redArg(lean_object* v_inst_4908_, lean_object* v_declInfos_4909_, lean_object* v_k_4910_, uint8_t v_kind_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_){
_start:
{
size_t v_sz_4917_; size_t v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; 
v_sz_4917_ = lean_array_size(v_declInfos_4909_);
v___x_4918_ = ((size_t)0ULL);
v___x_4919_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_4917_, v___x_4918_, v_declInfos_4909_);
v___x_4920_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5___redArg(v_inst_4908_, v___x_4919_, v_k_4910_, v_kind_4911_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_);
return v___x_4920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4___redArg___boxed(lean_object* v_inst_4921_, lean_object* v_declInfos_4922_, lean_object* v_k_4923_, lean_object* v_kind_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_){
_start:
{
uint8_t v_kind_boxed_4930_; lean_object* v_res_4931_; 
v_kind_boxed_4930_ = lean_unbox(v_kind_4924_);
v_res_4931_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4___redArg(v_inst_4921_, v_declInfos_4922_, v_k_4923_, v_kind_boxed_4930_, v___y_4925_, v___y_4926_, v___y_4927_, v___y_4928_);
lean_dec(v_inst_4921_);
return v_res_4931_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; 
v___x_4934_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__1));
v___x_4935_ = lean_unsigned_to_nat(8u);
v___x_4936_ = lean_unsigned_to_nat(291u);
v___x_4937_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__0));
v___x_4938_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_4939_ = l_mkPanicMessageWithDecl(v___x_4938_, v___x_4937_, v___x_4936_, v___x_4935_, v___x_4934_);
return v___x_4939_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(lean_object* v___f_4940_, lean_object* v___x_4941_, lean_object* v___x_4942_, lean_object* v___y_4943_, lean_object* v___x_4944_, lean_object* v_overlaps_4945_, lean_object* v_a_4946_, lean_object* v_fst_4947_, lean_object* v___x_4948_, lean_object* v_a_4949_, lean_object* v___x_4950_, lean_object* v___x_4951_, lean_object* v___x_4952_, lean_object* v___x_4953_, lean_object* v___x_4954_, lean_object* v___x_4955_, lean_object* v_matchDeclName_4956_, lean_object* v___x_4957_, lean_object* v___x_4958_, lean_object* v___x_4959_, lean_object* v___x_4960_, lean_object* v_altVars_4961_, lean_object* v_args_4962_, lean_object* v___mask_4963_, lean_object* v_altResultType_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_){
_start:
{
uint8_t v___x_4970_; lean_object* v___x_4971_; 
v___x_4970_ = 0;
lean_inc(v___y_4968_);
lean_inc_ref(v___y_4967_);
lean_inc(v___y_4966_);
lean_inc_ref(v___y_4965_);
v___x_4971_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_altResultType_4964_, v___f_4940_, v___x_4970_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_);
if (lean_obj_tag(v___x_4971_) == 0)
{
lean_object* v_a_4972_; lean_object* v_start_4973_; lean_object* v_stop_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; uint8_t v___x_4977_; 
v_a_4972_ = lean_ctor_get(v___x_4971_, 0);
lean_inc(v_a_4972_);
lean_dec_ref(v___x_4971_);
v_start_4973_ = lean_ctor_get(v___x_4941_, 1);
v_stop_4974_ = lean_ctor_get(v___x_4941_, 2);
v___x_4975_ = lean_array_get_size(v_a_4972_);
v___x_4976_ = lean_nat_sub(v_stop_4974_, v_start_4973_);
v___x_4977_ = lean_nat_dec_eq(v___x_4975_, v___x_4976_);
if (v___x_4977_ == 0)
{
lean_object* v___x_4978_; lean_object* v___x_4979_; 
lean_dec(v___x_4976_);
lean_dec(v_a_4972_);
lean_dec_ref(v_args_4962_);
lean_dec_ref(v_altVars_4961_);
lean_dec(v___x_4959_);
lean_dec(v___x_4958_);
lean_dec(v___x_4957_);
lean_dec(v_matchDeclName_4956_);
lean_dec(v___x_4955_);
lean_dec_ref(v___x_4954_);
lean_dec_ref(v___x_4953_);
lean_dec(v___x_4952_);
lean_dec_ref(v___x_4951_);
lean_dec(v___x_4950_);
lean_dec_ref(v_a_4949_);
lean_dec_ref(v___x_4948_);
lean_dec(v_fst_4947_);
lean_dec(v_a_4946_);
lean_dec_ref(v_overlaps_4945_);
lean_dec(v___x_4944_);
lean_dec_ref(v___y_4943_);
lean_dec(v___x_4942_);
lean_dec_ref(v___x_4941_);
v___x_4978_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2);
v___x_4979_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v___x_4978_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_);
return v___x_4979_;
}
else
{
lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; 
v___x_4980_ = lean_mk_empty_array_with_capacity(v___x_4942_);
lean_inc(v___x_4942_);
lean_inc(v_a_4972_);
v___x_4981_ = l_Array_toSubarray___redArg(v_a_4972_, v___x_4942_, v___x_4975_);
v___x_4982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4982_, 0, v___x_4980_);
lean_ctor_set(v___x_4982_, 1, v___x_4981_);
lean_inc(v___y_4968_);
lean_inc_ref(v___y_4967_);
lean_inc(v___y_4966_);
lean_inc_ref(v___y_4965_);
lean_inc_ref(v___x_4941_);
v___x_4983_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(v___x_4941_, v___x_4982_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_);
if (lean_obj_tag(v___x_4983_) == 0)
{
lean_object* v_a_4984_; lean_object* v_fst_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___f_4988_; uint8_t v___x_4989_; lean_object* v___x_4990_; 
v_a_4984_ = lean_ctor_get(v___x_4983_, 0);
lean_inc(v_a_4984_);
lean_dec_ref(v___x_4983_);
v_fst_4985_ = lean_ctor_get(v_a_4984_, 0);
lean_inc(v_fst_4985_);
lean_dec(v_a_4984_);
v___x_4986_ = lean_box(v___x_4970_);
v___x_4987_ = lean_box(v___x_4977_);
v___f_4988_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed), 32, 26);
lean_closure_set(v___f_4988_, 0, v___y_4943_);
lean_closure_set(v___f_4988_, 1, v_args_4962_);
lean_closure_set(v___f_4988_, 2, v___x_4944_);
lean_closure_set(v___f_4988_, 3, v_overlaps_4945_);
lean_closure_set(v___f_4988_, 4, v_a_4946_);
lean_closure_set(v___f_4988_, 5, v_fst_4947_);
lean_closure_set(v___f_4988_, 6, v_a_4972_);
lean_closure_set(v___f_4988_, 7, v___x_4975_);
lean_closure_set(v___f_4988_, 8, v___x_4948_);
lean_closure_set(v___f_4988_, 9, v___x_4942_);
lean_closure_set(v___f_4988_, 10, v___x_4941_);
lean_closure_set(v___f_4988_, 11, v_altVars_4961_);
lean_closure_set(v___f_4988_, 12, v___x_4986_);
lean_closure_set(v___f_4988_, 13, v___x_4987_);
lean_closure_set(v___f_4988_, 14, v_a_4949_);
lean_closure_set(v___f_4988_, 15, v___x_4950_);
lean_closure_set(v___f_4988_, 16, v___x_4951_);
lean_closure_set(v___f_4988_, 17, v___x_4952_);
lean_closure_set(v___f_4988_, 18, v___x_4953_);
lean_closure_set(v___f_4988_, 19, v___x_4954_);
lean_closure_set(v___f_4988_, 20, v___x_4976_);
lean_closure_set(v___f_4988_, 21, v___x_4955_);
lean_closure_set(v___f_4988_, 22, v_matchDeclName_4956_);
lean_closure_set(v___f_4988_, 23, v___x_4957_);
lean_closure_set(v___f_4988_, 24, v___x_4958_);
lean_closure_set(v___f_4988_, 25, v___x_4959_);
v___x_4989_ = 0;
v___x_4990_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4___redArg(v___x_4960_, v_fst_4985_, v___f_4988_, v___x_4989_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_);
return v___x_4990_;
}
else
{
lean_object* v_a_4991_; lean_object* v___x_4993_; uint8_t v_isShared_4994_; uint8_t v_isSharedCheck_4998_; 
lean_dec(v___x_4976_);
lean_dec(v_a_4972_);
lean_dec(v___y_4968_);
lean_dec_ref(v___y_4967_);
lean_dec(v___y_4966_);
lean_dec_ref(v___y_4965_);
lean_dec_ref(v_args_4962_);
lean_dec_ref(v_altVars_4961_);
lean_dec(v___x_4959_);
lean_dec(v___x_4958_);
lean_dec(v___x_4957_);
lean_dec(v_matchDeclName_4956_);
lean_dec(v___x_4955_);
lean_dec_ref(v___x_4954_);
lean_dec_ref(v___x_4953_);
lean_dec(v___x_4952_);
lean_dec_ref(v___x_4951_);
lean_dec(v___x_4950_);
lean_dec_ref(v_a_4949_);
lean_dec_ref(v___x_4948_);
lean_dec(v_fst_4947_);
lean_dec(v_a_4946_);
lean_dec_ref(v_overlaps_4945_);
lean_dec(v___x_4944_);
lean_dec_ref(v___y_4943_);
lean_dec(v___x_4942_);
lean_dec_ref(v___x_4941_);
v_a_4991_ = lean_ctor_get(v___x_4983_, 0);
v_isSharedCheck_4998_ = !lean_is_exclusive(v___x_4983_);
if (v_isSharedCheck_4998_ == 0)
{
v___x_4993_ = v___x_4983_;
v_isShared_4994_ = v_isSharedCheck_4998_;
goto v_resetjp_4992_;
}
else
{
lean_inc(v_a_4991_);
lean_dec(v___x_4983_);
v___x_4993_ = lean_box(0);
v_isShared_4994_ = v_isSharedCheck_4998_;
goto v_resetjp_4992_;
}
v_resetjp_4992_:
{
lean_object* v___x_4996_; 
if (v_isShared_4994_ == 0)
{
v___x_4996_ = v___x_4993_;
goto v_reusejp_4995_;
}
else
{
lean_object* v_reuseFailAlloc_4997_; 
v_reuseFailAlloc_4997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4997_, 0, v_a_4991_);
v___x_4996_ = v_reuseFailAlloc_4997_;
goto v_reusejp_4995_;
}
v_reusejp_4995_:
{
return v___x_4996_;
}
}
}
}
}
else
{
lean_object* v_a_4999_; lean_object* v___x_5001_; uint8_t v_isShared_5002_; uint8_t v_isSharedCheck_5006_; 
lean_dec(v___y_4968_);
lean_dec_ref(v___y_4967_);
lean_dec(v___y_4966_);
lean_dec_ref(v___y_4965_);
lean_dec_ref(v_args_4962_);
lean_dec_ref(v_altVars_4961_);
lean_dec(v___x_4959_);
lean_dec(v___x_4958_);
lean_dec(v___x_4957_);
lean_dec(v_matchDeclName_4956_);
lean_dec(v___x_4955_);
lean_dec_ref(v___x_4954_);
lean_dec_ref(v___x_4953_);
lean_dec(v___x_4952_);
lean_dec_ref(v___x_4951_);
lean_dec(v___x_4950_);
lean_dec_ref(v_a_4949_);
lean_dec_ref(v___x_4948_);
lean_dec(v_fst_4947_);
lean_dec(v_a_4946_);
lean_dec_ref(v_overlaps_4945_);
lean_dec(v___x_4944_);
lean_dec_ref(v___y_4943_);
lean_dec(v___x_4942_);
lean_dec_ref(v___x_4941_);
v_a_4999_ = lean_ctor_get(v___x_4971_, 0);
v_isSharedCheck_5006_ = !lean_is_exclusive(v___x_4971_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_5001_ = v___x_4971_;
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
else
{
lean_inc(v_a_4999_);
lean_dec(v___x_4971_);
v___x_5001_ = lean_box(0);
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
v_resetjp_5000_:
{
lean_object* v___x_5004_; 
if (v_isShared_5002_ == 0)
{
v___x_5004_ = v___x_5001_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_a_4999_);
v___x_5004_ = v_reuseFailAlloc_5005_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
return v___x_5004_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___f_5007_ = _args[0];
lean_object* v___x_5008_ = _args[1];
lean_object* v___x_5009_ = _args[2];
lean_object* v___y_5010_ = _args[3];
lean_object* v___x_5011_ = _args[4];
lean_object* v_overlaps_5012_ = _args[5];
lean_object* v_a_5013_ = _args[6];
lean_object* v_fst_5014_ = _args[7];
lean_object* v___x_5015_ = _args[8];
lean_object* v_a_5016_ = _args[9];
lean_object* v___x_5017_ = _args[10];
lean_object* v___x_5018_ = _args[11];
lean_object* v___x_5019_ = _args[12];
lean_object* v___x_5020_ = _args[13];
lean_object* v___x_5021_ = _args[14];
lean_object* v___x_5022_ = _args[15];
lean_object* v_matchDeclName_5023_ = _args[16];
lean_object* v___x_5024_ = _args[17];
lean_object* v___x_5025_ = _args[18];
lean_object* v___x_5026_ = _args[19];
lean_object* v___x_5027_ = _args[20];
lean_object* v_altVars_5028_ = _args[21];
lean_object* v_args_5029_ = _args[22];
lean_object* v___mask_5030_ = _args[23];
lean_object* v_altResultType_5031_ = _args[24];
lean_object* v___y_5032_ = _args[25];
lean_object* v___y_5033_ = _args[26];
lean_object* v___y_5034_ = _args[27];
lean_object* v___y_5035_ = _args[28];
lean_object* v___y_5036_ = _args[29];
_start:
{
lean_object* v_res_5037_; 
v_res_5037_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(v___f_5007_, v___x_5008_, v___x_5009_, v___y_5010_, v___x_5011_, v_overlaps_5012_, v_a_5013_, v_fst_5014_, v___x_5015_, v_a_5016_, v___x_5017_, v___x_5018_, v___x_5019_, v___x_5020_, v___x_5021_, v___x_5022_, v_matchDeclName_5023_, v___x_5024_, v___x_5025_, v___x_5026_, v___x_5027_, v_altVars_5028_, v_args_5029_, v___mask_5030_, v_altResultType_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_);
lean_dec_ref(v___mask_5030_);
lean_dec_ref(v___x_5027_);
return v_res_5037_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(lean_object* v_upperBound_5039_, lean_object* v_val_5040_, lean_object* v_matchDeclName_5041_, lean_object* v___x_5042_, lean_object* v___x_5043_, lean_object* v_a_5044_, lean_object* v___x_5045_, lean_object* v___x_5046_, lean_object* v___x_5047_, lean_object* v___x_5048_, lean_object* v___x_5049_, lean_object* v___x_5050_, lean_object* v_a_5051_, lean_object* v_b_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_){
_start:
{
uint8_t v___x_5058_; 
v___x_5058_ = lean_nat_dec_lt(v_a_5051_, v_upperBound_5039_);
if (v___x_5058_ == 0)
{
lean_object* v___x_5059_; 
lean_dec(v___y_5056_);
lean_dec_ref(v___y_5055_);
lean_dec(v___y_5054_);
lean_dec_ref(v___y_5053_);
lean_dec(v_a_5051_);
lean_dec(v___x_5050_);
lean_dec(v___x_5049_);
lean_dec_ref(v___x_5048_);
lean_dec_ref(v___x_5047_);
lean_dec_ref(v___x_5046_);
lean_dec(v___x_5045_);
lean_dec_ref(v_a_5044_);
lean_dec(v___x_5043_);
lean_dec_ref(v___x_5042_);
lean_dec(v_matchDeclName_5041_);
lean_dec_ref(v_val_5040_);
v___x_5059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5059_, 0, v_b_5052_);
return v___x_5059_;
}
else
{
lean_object* v_snd_5060_; lean_object* v_fst_5061_; lean_object* v___x_5063_; uint8_t v_isShared_5064_; uint8_t v_isSharedCheck_5124_; 
v_snd_5060_ = lean_ctor_get(v_b_5052_, 1);
v_fst_5061_ = lean_ctor_get(v_b_5052_, 0);
v_isSharedCheck_5124_ = !lean_is_exclusive(v_b_5052_);
if (v_isSharedCheck_5124_ == 0)
{
v___x_5063_ = v_b_5052_;
v_isShared_5064_ = v_isSharedCheck_5124_;
goto v_resetjp_5062_;
}
else
{
lean_inc(v_snd_5060_);
lean_inc(v_fst_5061_);
lean_dec(v_b_5052_);
v___x_5063_ = lean_box(0);
v_isShared_5064_ = v_isSharedCheck_5124_;
goto v_resetjp_5062_;
}
v_resetjp_5062_:
{
lean_object* v_fst_5065_; lean_object* v_snd_5066_; lean_object* v___x_5068_; uint8_t v_isShared_5069_; uint8_t v_isSharedCheck_5123_; 
v_fst_5065_ = lean_ctor_get(v_snd_5060_, 0);
v_snd_5066_ = lean_ctor_get(v_snd_5060_, 1);
v_isSharedCheck_5123_ = !lean_is_exclusive(v_snd_5060_);
if (v_isSharedCheck_5123_ == 0)
{
v___x_5068_ = v_snd_5060_;
v_isShared_5069_ = v_isSharedCheck_5123_;
goto v_resetjp_5067_;
}
else
{
lean_inc(v_snd_5066_);
lean_inc(v_fst_5065_);
lean_dec(v_snd_5060_);
v___x_5068_ = lean_box(0);
v_isShared_5069_ = v_isSharedCheck_5123_;
goto v_resetjp_5067_;
}
v_resetjp_5067_:
{
lean_object* v_altInfos_5070_; lean_object* v_overlaps_5071_; lean_object* v_start_5072_; lean_object* v_stop_5073_; lean_object* v___f_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___y_5087_; lean_object* v___x_5119_; uint8_t v___x_5120_; 
v_altInfos_5070_ = lean_ctor_get(v_val_5040_, 2);
v_overlaps_5071_ = lean_ctor_get(v_val_5040_, 5);
v_start_5072_ = lean_ctor_get(v___x_5048_, 1);
v_stop_5073_ = lean_ctor_get(v___x_5048_, 2);
v___f_5074_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___closed__0));
v___x_5075_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_5076_ = l_Lean_instInhabitedExpr;
v___x_5077_ = lean_unsigned_to_nat(0u);
v___x_5078_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_5079_ = lean_unsigned_to_nat(1u);
v___x_5080_ = lean_box(0);
v___x_5081_ = lean_array_get_borrowed(v___x_5075_, v_altInfos_5070_, v_a_5051_);
v___x_5082_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_5041_);
v___x_5083_ = l_Lean_Name_str___override(v_matchDeclName_5041_, v___x_5082_);
lean_inc(v_snd_5066_);
v___x_5084_ = lean_name_append_index_after(v___x_5083_, v_snd_5066_);
lean_inc(v___x_5084_);
v___x_5085_ = lean_array_push(v_fst_5061_, v___x_5084_);
v___x_5119_ = lean_nat_sub(v_stop_5073_, v_start_5072_);
v___x_5120_ = lean_nat_dec_lt(v_a_5051_, v___x_5119_);
lean_dec(v___x_5119_);
if (v___x_5120_ == 0)
{
lean_object* v___x_5121_; 
v___x_5121_ = l_outOfBounds___redArg(v___x_5076_);
v___y_5087_ = v___x_5121_;
goto v___jp_5086_;
}
else
{
lean_object* v___x_5122_; 
v___x_5122_ = l_Subarray_get___redArg(v___x_5048_, v_a_5051_);
v___y_5087_ = v___x_5122_;
goto v___jp_5086_;
}
v___jp_5086_:
{
lean_object* v___x_5088_; 
lean_inc(v___y_5056_);
lean_inc_ref(v___y_5055_);
lean_inc(v___y_5054_);
lean_inc_ref(v___y_5053_);
lean_inc_ref(v___y_5087_);
v___x_5088_ = lean_infer_type(v___y_5087_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_);
if (lean_obj_tag(v___x_5088_) == 0)
{
lean_object* v_a_5089_; lean_object* v___f_5090_; lean_object* v___x_5091_; 
v_a_5089_ = lean_ctor_get(v___x_5088_, 0);
lean_inc(v_a_5089_);
lean_dec_ref(v___x_5088_);
lean_inc(v___x_5050_);
lean_inc(v_matchDeclName_5041_);
lean_inc(v___x_5049_);
lean_inc_ref(v___x_5048_);
lean_inc_ref(v___x_5047_);
lean_inc_ref(v___x_5046_);
lean_inc(v___x_5045_);
lean_inc_ref(v_a_5044_);
lean_inc(v_fst_5065_);
lean_inc(v_a_5051_);
lean_inc_ref(v_overlaps_5071_);
lean_inc(v___x_5043_);
lean_inc_ref(v___x_5042_);
v___f_5090_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed), 30, 21);
lean_closure_set(v___f_5090_, 0, v___f_5074_);
lean_closure_set(v___f_5090_, 1, v___x_5042_);
lean_closure_set(v___f_5090_, 2, v___x_5077_);
lean_closure_set(v___f_5090_, 3, v___y_5087_);
lean_closure_set(v___f_5090_, 4, v___x_5043_);
lean_closure_set(v___f_5090_, 5, v_overlaps_5071_);
lean_closure_set(v___f_5090_, 6, v_a_5051_);
lean_closure_set(v___f_5090_, 7, v_fst_5065_);
lean_closure_set(v___f_5090_, 8, v___x_5078_);
lean_closure_set(v___f_5090_, 9, v_a_5044_);
lean_closure_set(v___f_5090_, 10, v___x_5045_);
lean_closure_set(v___f_5090_, 11, v___x_5046_);
lean_closure_set(v___f_5090_, 12, v___x_5079_);
lean_closure_set(v___f_5090_, 13, v___x_5047_);
lean_closure_set(v___f_5090_, 14, v___x_5048_);
lean_closure_set(v___f_5090_, 15, v___x_5049_);
lean_closure_set(v___f_5090_, 16, v_matchDeclName_5041_);
lean_closure_set(v___f_5090_, 17, v___x_5084_);
lean_closure_set(v___f_5090_, 18, v___x_5050_);
lean_closure_set(v___f_5090_, 19, v___x_5080_);
lean_closure_set(v___f_5090_, 20, v___x_5076_);
lean_inc(v___y_5056_);
lean_inc_ref(v___y_5055_);
lean_inc(v___y_5054_);
lean_inc_ref(v___y_5053_);
lean_inc(v___x_5081_);
v___x_5091_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_a_5089_, v___x_5081_, v___f_5090_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_);
if (lean_obj_tag(v___x_5091_) == 0)
{
lean_object* v_a_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5096_; 
v_a_5092_ = lean_ctor_get(v___x_5091_, 0);
lean_inc(v_a_5092_);
lean_dec_ref(v___x_5091_);
v___x_5093_ = lean_array_push(v_fst_5065_, v_a_5092_);
v___x_5094_ = lean_nat_add(v_snd_5066_, v___x_5079_);
lean_dec(v_snd_5066_);
if (v_isShared_5069_ == 0)
{
lean_ctor_set(v___x_5068_, 1, v___x_5094_);
lean_ctor_set(v___x_5068_, 0, v___x_5093_);
v___x_5096_ = v___x_5068_;
goto v_reusejp_5095_;
}
else
{
lean_object* v_reuseFailAlloc_5102_; 
v_reuseFailAlloc_5102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5102_, 0, v___x_5093_);
lean_ctor_set(v_reuseFailAlloc_5102_, 1, v___x_5094_);
v___x_5096_ = v_reuseFailAlloc_5102_;
goto v_reusejp_5095_;
}
v_reusejp_5095_:
{
lean_object* v___x_5098_; 
if (v_isShared_5064_ == 0)
{
lean_ctor_set(v___x_5063_, 1, v___x_5096_);
lean_ctor_set(v___x_5063_, 0, v___x_5085_);
v___x_5098_ = v___x_5063_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5101_; 
v_reuseFailAlloc_5101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5101_, 0, v___x_5085_);
lean_ctor_set(v_reuseFailAlloc_5101_, 1, v___x_5096_);
v___x_5098_ = v_reuseFailAlloc_5101_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
lean_object* v___x_5099_; 
v___x_5099_ = lean_nat_add(v_a_5051_, v___x_5079_);
lean_dec(v_a_5051_);
v_a_5051_ = v___x_5099_;
v_b_5052_ = v___x_5098_;
goto _start;
}
}
}
else
{
lean_object* v_a_5103_; lean_object* v___x_5105_; uint8_t v_isShared_5106_; uint8_t v_isSharedCheck_5110_; 
lean_dec_ref(v___x_5085_);
lean_del_object(v___x_5068_);
lean_dec(v_snd_5066_);
lean_dec(v_fst_5065_);
lean_del_object(v___x_5063_);
lean_dec(v___y_5056_);
lean_dec_ref(v___y_5055_);
lean_dec(v___y_5054_);
lean_dec_ref(v___y_5053_);
lean_dec(v_a_5051_);
lean_dec(v___x_5050_);
lean_dec(v___x_5049_);
lean_dec_ref(v___x_5048_);
lean_dec_ref(v___x_5047_);
lean_dec_ref(v___x_5046_);
lean_dec(v___x_5045_);
lean_dec_ref(v_a_5044_);
lean_dec(v___x_5043_);
lean_dec_ref(v___x_5042_);
lean_dec(v_matchDeclName_5041_);
lean_dec_ref(v_val_5040_);
v_a_5103_ = lean_ctor_get(v___x_5091_, 0);
v_isSharedCheck_5110_ = !lean_is_exclusive(v___x_5091_);
if (v_isSharedCheck_5110_ == 0)
{
v___x_5105_ = v___x_5091_;
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
else
{
lean_inc(v_a_5103_);
lean_dec(v___x_5091_);
v___x_5105_ = lean_box(0);
v_isShared_5106_ = v_isSharedCheck_5110_;
goto v_resetjp_5104_;
}
v_resetjp_5104_:
{
lean_object* v___x_5108_; 
if (v_isShared_5106_ == 0)
{
v___x_5108_ = v___x_5105_;
goto v_reusejp_5107_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v_a_5103_);
v___x_5108_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5107_;
}
v_reusejp_5107_:
{
return v___x_5108_;
}
}
}
}
else
{
lean_object* v_a_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5118_; 
lean_dec_ref(v___y_5087_);
lean_dec_ref(v___x_5085_);
lean_dec(v___x_5084_);
lean_del_object(v___x_5068_);
lean_dec(v_snd_5066_);
lean_dec(v_fst_5065_);
lean_del_object(v___x_5063_);
lean_dec(v___y_5056_);
lean_dec_ref(v___y_5055_);
lean_dec(v___y_5054_);
lean_dec_ref(v___y_5053_);
lean_dec(v_a_5051_);
lean_dec(v___x_5050_);
lean_dec(v___x_5049_);
lean_dec_ref(v___x_5048_);
lean_dec_ref(v___x_5047_);
lean_dec_ref(v___x_5046_);
lean_dec(v___x_5045_);
lean_dec_ref(v_a_5044_);
lean_dec(v___x_5043_);
lean_dec_ref(v___x_5042_);
lean_dec(v_matchDeclName_5041_);
lean_dec_ref(v_val_5040_);
v_a_5111_ = lean_ctor_get(v___x_5088_, 0);
v_isSharedCheck_5118_ = !lean_is_exclusive(v___x_5088_);
if (v_isSharedCheck_5118_ == 0)
{
v___x_5113_ = v___x_5088_;
v_isShared_5114_ = v_isSharedCheck_5118_;
goto v_resetjp_5112_;
}
else
{
lean_inc(v_a_5111_);
lean_dec(v___x_5088_);
v___x_5113_ = lean_box(0);
v_isShared_5114_ = v_isSharedCheck_5118_;
goto v_resetjp_5112_;
}
v_resetjp_5112_:
{
lean_object* v___x_5116_; 
if (v_isShared_5114_ == 0)
{
v___x_5116_ = v___x_5113_;
goto v_reusejp_5115_;
}
else
{
lean_object* v_reuseFailAlloc_5117_; 
v_reuseFailAlloc_5117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5117_, 0, v_a_5111_);
v___x_5116_ = v_reuseFailAlloc_5117_;
goto v_reusejp_5115_;
}
v_reusejp_5115_:
{
return v___x_5116_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_5125_ = _args[0];
lean_object* v_val_5126_ = _args[1];
lean_object* v_matchDeclName_5127_ = _args[2];
lean_object* v___x_5128_ = _args[3];
lean_object* v___x_5129_ = _args[4];
lean_object* v_a_5130_ = _args[5];
lean_object* v___x_5131_ = _args[6];
lean_object* v___x_5132_ = _args[7];
lean_object* v___x_5133_ = _args[8];
lean_object* v___x_5134_ = _args[9];
lean_object* v___x_5135_ = _args[10];
lean_object* v___x_5136_ = _args[11];
lean_object* v_a_5137_ = _args[12];
lean_object* v_b_5138_ = _args[13];
lean_object* v___y_5139_ = _args[14];
lean_object* v___y_5140_ = _args[15];
lean_object* v___y_5141_ = _args[16];
lean_object* v___y_5142_ = _args[17];
lean_object* v___y_5143_ = _args[18];
_start:
{
lean_object* v_res_5144_; 
v_res_5144_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5125_, v_val_5126_, v_matchDeclName_5127_, v___x_5128_, v___x_5129_, v_a_5130_, v___x_5131_, v___x_5132_, v___x_5133_, v___x_5134_, v___x_5135_, v___x_5136_, v_a_5137_, v_b_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_);
lean_dec(v_upperBound_5125_);
return v_res_5144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(lean_object* v_val_5151_, lean_object* v___x_5152_, lean_object* v_matchDeclName_5153_, lean_object* v___x_5154_, lean_object* v_a_5155_, lean_object* v___x_5156_, lean_object* v___x_5157_, lean_object* v_xs_5158_, lean_object* v___matchResultType_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_){
_start:
{
lean_object* v_numParams_5165_; lean_object* v_numDiscrs_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v_lower_5172_; lean_object* v_upper_5173_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; uint8_t v___x_5204_; 
v_numParams_5165_ = lean_ctor_get(v_val_5151_, 0);
v_numDiscrs_5166_ = lean_ctor_get(v_val_5151_, 1);
v___x_5167_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5165_);
lean_inc_ref(v_xs_5158_);
v___x_5168_ = l_Array_toSubarray___redArg(v_xs_5158_, v___x_5167_, v_numParams_5165_);
v___x_5169_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_5151_);
v___x_5170_ = lean_array_get(v___x_5152_, v_xs_5158_, v___x_5169_);
lean_dec(v___x_5169_);
v___x_5201_ = lean_array_get_size(v_xs_5158_);
v___x_5202_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5151_);
v___x_5203_ = lean_nat_sub(v___x_5201_, v___x_5202_);
lean_dec(v___x_5202_);
v___x_5204_ = lean_nat_dec_le(v___x_5203_, v___x_5167_);
if (v___x_5204_ == 0)
{
v_lower_5172_ = v___x_5203_;
v_upper_5173_ = v___x_5201_;
goto v___jp_5171_;
}
else
{
lean_dec(v___x_5203_);
v_lower_5172_ = v___x_5167_;
v_upper_5173_ = v___x_5201_;
goto v___jp_5171_;
}
v___jp_5171_:
{
lean_object* v___x_5174_; lean_object* v_start_5175_; lean_object* v_stop_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; 
lean_inc_ref(v_xs_5158_);
v___x_5174_ = l_Array_toSubarray___redArg(v_xs_5158_, v_lower_5172_, v_upper_5173_);
v_start_5175_ = lean_ctor_get(v___x_5174_, 1);
lean_inc(v_start_5175_);
v_stop_5176_ = lean_ctor_get(v___x_5174_, 2);
lean_inc(v_stop_5176_);
v___x_5177_ = lean_unsigned_to_nat(1u);
v___x_5178_ = lean_nat_add(v_numParams_5165_, v___x_5177_);
v___x_5179_ = lean_nat_add(v___x_5178_, v_numDiscrs_5166_);
v___x_5180_ = lean_nat_sub(v_stop_5176_, v_start_5175_);
lean_dec(v_start_5175_);
lean_dec(v_stop_5176_);
v___x_5181_ = l_Array_toSubarray___redArg(v_xs_5158_, v___x_5178_, v___x_5179_);
v___x_5182_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__1));
lean_inc(v___x_5180_);
v___x_5183_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v___x_5180_, v_val_5151_, v_matchDeclName_5153_, v___x_5181_, v___x_5154_, v_a_5155_, v___x_5156_, v___x_5168_, v___x_5170_, v___x_5174_, v___x_5180_, v___x_5157_, v___x_5167_, v___x_5182_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_);
lean_dec(v___x_5180_);
if (lean_obj_tag(v___x_5183_) == 0)
{
lean_object* v___x_5185_; uint8_t v_isShared_5186_; uint8_t v_isSharedCheck_5191_; 
v_isSharedCheck_5191_ = !lean_is_exclusive(v___x_5183_);
if (v_isSharedCheck_5191_ == 0)
{
lean_object* v_unused_5192_; 
v_unused_5192_ = lean_ctor_get(v___x_5183_, 0);
lean_dec(v_unused_5192_);
v___x_5185_ = v___x_5183_;
v_isShared_5186_ = v_isSharedCheck_5191_;
goto v_resetjp_5184_;
}
else
{
lean_dec(v___x_5183_);
v___x_5185_ = lean_box(0);
v_isShared_5186_ = v_isSharedCheck_5191_;
goto v_resetjp_5184_;
}
v_resetjp_5184_:
{
lean_object* v___x_5187_; lean_object* v___x_5189_; 
v___x_5187_ = lean_box(0);
if (v_isShared_5186_ == 0)
{
lean_ctor_set(v___x_5185_, 0, v___x_5187_);
v___x_5189_ = v___x_5185_;
goto v_reusejp_5188_;
}
else
{
lean_object* v_reuseFailAlloc_5190_; 
v_reuseFailAlloc_5190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5190_, 0, v___x_5187_);
v___x_5189_ = v_reuseFailAlloc_5190_;
goto v_reusejp_5188_;
}
v_reusejp_5188_:
{
return v___x_5189_;
}
}
}
else
{
lean_object* v_a_5193_; lean_object* v___x_5195_; uint8_t v_isShared_5196_; uint8_t v_isSharedCheck_5200_; 
v_a_5193_ = lean_ctor_get(v___x_5183_, 0);
v_isSharedCheck_5200_ = !lean_is_exclusive(v___x_5183_);
if (v_isSharedCheck_5200_ == 0)
{
v___x_5195_ = v___x_5183_;
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
else
{
lean_inc(v_a_5193_);
lean_dec(v___x_5183_);
v___x_5195_ = lean_box(0);
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
v_resetjp_5194_:
{
lean_object* v___x_5198_; 
if (v_isShared_5196_ == 0)
{
v___x_5198_ = v___x_5195_;
goto v_reusejp_5197_;
}
else
{
lean_object* v_reuseFailAlloc_5199_; 
v_reuseFailAlloc_5199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5199_, 0, v_a_5193_);
v___x_5198_ = v_reuseFailAlloc_5199_;
goto v_reusejp_5197_;
}
v_reusejp_5197_:
{
return v___x_5198_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed(lean_object* v_val_5205_, lean_object* v___x_5206_, lean_object* v_matchDeclName_5207_, lean_object* v___x_5208_, lean_object* v_a_5209_, lean_object* v___x_5210_, lean_object* v___x_5211_, lean_object* v_xs_5212_, lean_object* v___matchResultType_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_){
_start:
{
lean_object* v_res_5219_; 
v_res_5219_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(v_val_5205_, v___x_5206_, v_matchDeclName_5207_, v___x_5208_, v_a_5209_, v___x_5210_, v___x_5211_, v_xs_5212_, v___matchResultType_5213_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_);
lean_dec_ref(v___matchResultType_5213_);
return v_res_5219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(lean_object* v_matchDeclName_5220_, lean_object* v_a_5221_, lean_object* v_a_5222_, lean_object* v_a_5223_, lean_object* v_a_5224_){
_start:
{
uint8_t v_trackZetaDelta_5226_; lean_object* v_zetaDeltaSet_5227_; lean_object* v_lctx_5228_; lean_object* v_localInstances_5229_; lean_object* v_defEqCtx_x3f_5230_; lean_object* v_synthPendingDepth_5231_; lean_object* v_canUnfold_x3f_5232_; uint8_t v_univApprox_5233_; uint8_t v_inTypeClassResolution_5234_; uint8_t v_cacheInferType_5235_; lean_object* v___x_5236_; lean_object* v___x_5238_; uint8_t v_isShared_5239_; uint8_t v_isSharedCheck_5279_; 
v_trackZetaDelta_5226_ = lean_ctor_get_uint8(v_a_5221_, sizeof(void*)*7);
v_zetaDeltaSet_5227_ = lean_ctor_get(v_a_5221_, 1);
lean_inc(v_zetaDeltaSet_5227_);
v_lctx_5228_ = lean_ctor_get(v_a_5221_, 2);
lean_inc_ref(v_lctx_5228_);
v_localInstances_5229_ = lean_ctor_get(v_a_5221_, 3);
lean_inc_ref(v_localInstances_5229_);
v_defEqCtx_x3f_5230_ = lean_ctor_get(v_a_5221_, 4);
lean_inc(v_defEqCtx_x3f_5230_);
v_synthPendingDepth_5231_ = lean_ctor_get(v_a_5221_, 5);
lean_inc(v_synthPendingDepth_5231_);
v_canUnfold_x3f_5232_ = lean_ctor_get(v_a_5221_, 6);
lean_inc(v_canUnfold_x3f_5232_);
v_univApprox_5233_ = lean_ctor_get_uint8(v_a_5221_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_5234_ = lean_ctor_get_uint8(v_a_5221_, sizeof(void*)*7 + 2);
v_cacheInferType_5235_ = lean_ctor_get_uint8(v_a_5221_, sizeof(void*)*7 + 3);
v___x_5236_ = l_Lean_Meta_Context_config(v_a_5221_);
v_isSharedCheck_5279_ = !lean_is_exclusive(v_a_5221_);
if (v_isSharedCheck_5279_ == 0)
{
lean_object* v_unused_5280_; lean_object* v_unused_5281_; lean_object* v_unused_5282_; lean_object* v_unused_5283_; lean_object* v_unused_5284_; lean_object* v_unused_5285_; lean_object* v_unused_5286_; 
v_unused_5280_ = lean_ctor_get(v_a_5221_, 6);
lean_dec(v_unused_5280_);
v_unused_5281_ = lean_ctor_get(v_a_5221_, 5);
lean_dec(v_unused_5281_);
v_unused_5282_ = lean_ctor_get(v_a_5221_, 4);
lean_dec(v_unused_5282_);
v_unused_5283_ = lean_ctor_get(v_a_5221_, 3);
lean_dec(v_unused_5283_);
v_unused_5284_ = lean_ctor_get(v_a_5221_, 2);
lean_dec(v_unused_5284_);
v_unused_5285_ = lean_ctor_get(v_a_5221_, 1);
lean_dec(v_unused_5285_);
v_unused_5286_ = lean_ctor_get(v_a_5221_, 0);
lean_dec(v_unused_5286_);
v___x_5238_ = v_a_5221_;
v_isShared_5239_ = v_isSharedCheck_5279_;
goto v_resetjp_5237_;
}
else
{
lean_dec(v_a_5221_);
v___x_5238_ = lean_box(0);
v_isShared_5239_ = v_isSharedCheck_5279_;
goto v_resetjp_5237_;
}
v_resetjp_5237_:
{
lean_object* v___x_5240_; uint64_t v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5244_; 
v___x_5240_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5236_);
v___x_5241_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5240_);
v___x_5242_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5242_, 0, v___x_5240_);
lean_ctor_set_uint64(v___x_5242_, sizeof(void*)*1, v___x_5241_);
lean_inc(v_canUnfold_x3f_5232_);
lean_inc(v_synthPendingDepth_5231_);
lean_inc(v_defEqCtx_x3f_5230_);
lean_inc_ref(v_localInstances_5229_);
lean_inc_ref(v_lctx_5228_);
lean_inc(v_zetaDeltaSet_5227_);
if (v_isShared_5239_ == 0)
{
lean_ctor_set(v___x_5238_, 0, v___x_5242_);
v___x_5244_ = v___x_5238_;
goto v_reusejp_5243_;
}
else
{
lean_object* v_reuseFailAlloc_5278_; 
v_reuseFailAlloc_5278_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_5278_, 0, v___x_5242_);
lean_ctor_set(v_reuseFailAlloc_5278_, 1, v_zetaDeltaSet_5227_);
lean_ctor_set(v_reuseFailAlloc_5278_, 2, v_lctx_5228_);
lean_ctor_set(v_reuseFailAlloc_5278_, 3, v_localInstances_5229_);
lean_ctor_set(v_reuseFailAlloc_5278_, 4, v_defEqCtx_x3f_5230_);
lean_ctor_set(v_reuseFailAlloc_5278_, 5, v_synthPendingDepth_5231_);
lean_ctor_set(v_reuseFailAlloc_5278_, 6, v_canUnfold_x3f_5232_);
lean_ctor_set_uint8(v_reuseFailAlloc_5278_, sizeof(void*)*7, v_trackZetaDelta_5226_);
lean_ctor_set_uint8(v_reuseFailAlloc_5278_, sizeof(void*)*7 + 1, v_univApprox_5233_);
lean_ctor_set_uint8(v_reuseFailAlloc_5278_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5234_);
lean_ctor_set_uint8(v_reuseFailAlloc_5278_, sizeof(void*)*7 + 3, v_cacheInferType_5235_);
v___x_5244_ = v_reuseFailAlloc_5278_;
goto v_reusejp_5243_;
}
v_reusejp_5243_:
{
lean_object* v___x_5245_; lean_object* v___x_5246_; uint64_t v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; 
v___x_5245_ = l_Lean_Meta_Context_config(v___x_5244_);
lean_dec_ref(v___x_5244_);
v___x_5246_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5245_);
v___x_5247_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5246_);
v___x_5248_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5248_, 0, v___x_5246_);
lean_ctor_set_uint64(v___x_5248_, sizeof(void*)*1, v___x_5247_);
v___x_5249_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5249_, 0, v___x_5248_);
lean_ctor_set(v___x_5249_, 1, v_zetaDeltaSet_5227_);
lean_ctor_set(v___x_5249_, 2, v_lctx_5228_);
lean_ctor_set(v___x_5249_, 3, v_localInstances_5229_);
lean_ctor_set(v___x_5249_, 4, v_defEqCtx_x3f_5230_);
lean_ctor_set(v___x_5249_, 5, v_synthPendingDepth_5231_);
lean_ctor_set(v___x_5249_, 6, v_canUnfold_x3f_5232_);
lean_ctor_set_uint8(v___x_5249_, sizeof(void*)*7, v_trackZetaDelta_5226_);
lean_ctor_set_uint8(v___x_5249_, sizeof(void*)*7 + 1, v_univApprox_5233_);
lean_ctor_set_uint8(v___x_5249_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5234_);
lean_ctor_set_uint8(v___x_5249_, sizeof(void*)*7 + 3, v_cacheInferType_5235_);
lean_inc_ref(v_a_5223_);
lean_inc(v_matchDeclName_5220_);
v___x_5250_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_5220_, v___x_5249_, v_a_5222_, v_a_5223_, v_a_5224_);
if (lean_obj_tag(v___x_5250_) == 0)
{
lean_object* v_a_5251_; lean_object* v___x_5252_; lean_object* v_a_5253_; 
v_a_5251_ = lean_ctor_get(v___x_5250_, 0);
lean_inc(v_a_5251_);
lean_dec_ref(v___x_5250_);
lean_inc(v_matchDeclName_5220_);
v___x_5252_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_5220_, v_a_5224_);
v_a_5253_ = lean_ctor_get(v___x_5252_, 0);
lean_inc(v_a_5253_);
lean_dec_ref(v___x_5252_);
if (lean_obj_tag(v_a_5253_) == 1)
{
lean_object* v_val_5254_; lean_object* v___x_5255_; lean_object* v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___f_5260_; lean_object* v___x_5261_; uint8_t v___x_5262_; lean_object* v___x_5263_; 
v_val_5254_ = lean_ctor_get(v_a_5253_, 0);
lean_inc(v_val_5254_);
lean_dec_ref(v_a_5253_);
v___x_5255_ = l_Lean_instInhabitedExpr;
v___x_5256_ = l_Lean_ConstantInfo_levelParams(v_a_5251_);
v___x_5257_ = lean_box(0);
lean_inc(v___x_5256_);
v___x_5258_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(v___x_5256_, v___x_5257_);
v___x_5259_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_5254_);
lean_inc(v_a_5251_);
v___f_5260_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed), 14, 7);
lean_closure_set(v___f_5260_, 0, v_val_5254_);
lean_closure_set(v___f_5260_, 1, v___x_5255_);
lean_closure_set(v___f_5260_, 2, v_matchDeclName_5220_);
lean_closure_set(v___f_5260_, 3, v___x_5259_);
lean_closure_set(v___f_5260_, 4, v_a_5251_);
lean_closure_set(v___f_5260_, 5, v___x_5258_);
lean_closure_set(v___f_5260_, 6, v___x_5256_);
v___x_5261_ = l_Lean_ConstantInfo_type(v_a_5251_);
lean_dec(v_a_5251_);
v___x_5262_ = 0;
v___x_5263_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_5261_, v___f_5260_, v___x_5262_, v___x_5262_, v___x_5249_, v_a_5222_, v_a_5223_, v_a_5224_);
return v___x_5263_;
}
else
{
lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; 
lean_dec(v_a_5253_);
lean_dec(v_a_5251_);
v___x_5264_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5265_ = l_Lean_MessageData_ofName(v_matchDeclName_5220_);
v___x_5266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5266_, 0, v___x_5264_);
lean_ctor_set(v___x_5266_, 1, v___x_5265_);
v___x_5267_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5268_, 0, v___x_5266_);
lean_ctor_set(v___x_5268_, 1, v___x_5267_);
v___x_5269_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5268_, v___x_5249_, v_a_5222_, v_a_5223_, v_a_5224_);
lean_dec(v_a_5224_);
lean_dec_ref(v_a_5223_);
lean_dec(v_a_5222_);
lean_dec_ref(v___x_5249_);
return v___x_5269_;
}
}
else
{
lean_object* v_a_5270_; lean_object* v___x_5272_; uint8_t v_isShared_5273_; uint8_t v_isSharedCheck_5277_; 
lean_dec_ref(v___x_5249_);
lean_dec(v_a_5224_);
lean_dec_ref(v_a_5223_);
lean_dec(v_a_5222_);
lean_dec(v_matchDeclName_5220_);
v_a_5270_ = lean_ctor_get(v___x_5250_, 0);
v_isSharedCheck_5277_ = !lean_is_exclusive(v___x_5250_);
if (v_isSharedCheck_5277_ == 0)
{
v___x_5272_ = v___x_5250_;
v_isShared_5273_ = v_isSharedCheck_5277_;
goto v_resetjp_5271_;
}
else
{
lean_inc(v_a_5270_);
lean_dec(v___x_5250_);
v___x_5272_ = lean_box(0);
v_isShared_5273_ = v_isSharedCheck_5277_;
goto v_resetjp_5271_;
}
v_resetjp_5271_:
{
lean_object* v___x_5275_; 
if (v_isShared_5273_ == 0)
{
v___x_5275_ = v___x_5272_;
goto v_reusejp_5274_;
}
else
{
lean_object* v_reuseFailAlloc_5276_; 
v_reuseFailAlloc_5276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5276_, 0, v_a_5270_);
v___x_5275_ = v_reuseFailAlloc_5276_;
goto v_reusejp_5274_;
}
v_reusejp_5274_:
{
return v___x_5275_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed(lean_object* v_matchDeclName_5287_, lean_object* v_a_5288_, lean_object* v_a_5289_, lean_object* v_a_5290_, lean_object* v_a_5291_, lean_object* v_a_5292_){
_start:
{
lean_object* v_res_5293_; 
v_res_5293_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(v_matchDeclName_5287_, v_a_5288_, v_a_5289_, v_a_5290_, v_a_5291_);
return v_res_5293_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(lean_object* v_inst_5294_, lean_object* v_R_5295_, lean_object* v_a_5296_, lean_object* v_b_5297_, lean_object* v_c_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_){
_start:
{
lean_object* v___x_5304_; 
v___x_5304_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(v_a_5296_, v_b_5297_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_);
return v___x_5304_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___boxed(lean_object* v_inst_5305_, lean_object* v_R_5306_, lean_object* v_a_5307_, lean_object* v_b_5308_, lean_object* v_c_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_){
_start:
{
lean_object* v_res_5315_; 
v_res_5315_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(v_inst_5305_, v_R_5306_, v_a_5307_, v_b_5308_, v_c_5309_, v___y_5310_, v___y_5311_, v___y_5312_, v___y_5313_);
return v_res_5315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(lean_object* v_00_u03b1_5316_, lean_object* v_inst_5317_, lean_object* v_declInfos_5318_, lean_object* v_k_5319_, uint8_t v_kind_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_){
_start:
{
lean_object* v___x_5326_; 
v___x_5326_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4___redArg(v_inst_5317_, v_declInfos_5318_, v_k_5319_, v_kind_5320_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_);
return v___x_5326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4___boxed(lean_object* v_00_u03b1_5327_, lean_object* v_inst_5328_, lean_object* v_declInfos_5329_, lean_object* v_k_5330_, lean_object* v_kind_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_){
_start:
{
uint8_t v_kind_boxed_5337_; lean_object* v_res_5338_; 
v_kind_boxed_5337_ = lean_unbox(v_kind_5331_);
v_res_5338_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_00_u03b1_5327_, v_inst_5328_, v_declInfos_5329_, v_k_5330_, v_kind_boxed_5337_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_);
lean_dec(v_inst_5328_);
return v_res_5338_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(lean_object* v_upperBound_5339_, lean_object* v_val_5340_, lean_object* v_matchDeclName_5341_, lean_object* v___x_5342_, lean_object* v___x_5343_, lean_object* v_a_5344_, lean_object* v___x_5345_, lean_object* v___x_5346_, lean_object* v___x_5347_, lean_object* v___x_5348_, lean_object* v___x_5349_, lean_object* v___x_5350_, lean_object* v_inst_5351_, lean_object* v_R_5352_, lean_object* v_a_5353_, lean_object* v_b_5354_, lean_object* v_c_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_){
_start:
{
lean_object* v___x_5361_; 
v___x_5361_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5339_, v_val_5340_, v_matchDeclName_5341_, v___x_5342_, v___x_5343_, v_a_5344_, v___x_5345_, v___x_5346_, v___x_5347_, v___x_5348_, v___x_5349_, v___x_5350_, v_a_5353_, v_b_5354_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_);
return v___x_5361_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___boxed(lean_object** _args){
lean_object* v_upperBound_5362_ = _args[0];
lean_object* v_val_5363_ = _args[1];
lean_object* v_matchDeclName_5364_ = _args[2];
lean_object* v___x_5365_ = _args[3];
lean_object* v___x_5366_ = _args[4];
lean_object* v_a_5367_ = _args[5];
lean_object* v___x_5368_ = _args[6];
lean_object* v___x_5369_ = _args[7];
lean_object* v___x_5370_ = _args[8];
lean_object* v___x_5371_ = _args[9];
lean_object* v___x_5372_ = _args[10];
lean_object* v___x_5373_ = _args[11];
lean_object* v_inst_5374_ = _args[12];
lean_object* v_R_5375_ = _args[13];
lean_object* v_a_5376_ = _args[14];
lean_object* v_b_5377_ = _args[15];
lean_object* v_c_5378_ = _args[16];
lean_object* v___y_5379_ = _args[17];
lean_object* v___y_5380_ = _args[18];
lean_object* v___y_5381_ = _args[19];
lean_object* v___y_5382_ = _args[20];
lean_object* v___y_5383_ = _args[21];
_start:
{
lean_object* v_res_5384_; 
v_res_5384_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(v_upperBound_5362_, v_val_5363_, v_matchDeclName_5364_, v___x_5365_, v___x_5366_, v_a_5367_, v___x_5368_, v___x_5369_, v___x_5370_, v___x_5371_, v___x_5372_, v___x_5373_, v_inst_5374_, v_R_5375_, v_a_5376_, v_b_5377_, v_c_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_);
lean_dec(v_upperBound_5362_);
return v_res_5384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(lean_object* v_00_u03b1_5385_, lean_object* v_inst_5386_, lean_object* v_declInfos_5387_, lean_object* v_k_5388_, uint8_t v_kind_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_){
_start:
{
lean_object* v___x_5395_; 
v___x_5395_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5___redArg(v_inst_5386_, v_declInfos_5387_, v_k_5388_, v_kind_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_);
return v___x_5395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5___boxed(lean_object* v_00_u03b1_5396_, lean_object* v_inst_5397_, lean_object* v_declInfos_5398_, lean_object* v_k_5399_, lean_object* v_kind_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_){
_start:
{
uint8_t v_kind_boxed_5406_; lean_object* v_res_5407_; 
v_kind_boxed_5406_ = lean_unbox(v_kind_5400_);
v_res_5407_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v_00_u03b1_5396_, v_inst_5397_, v_declInfos_5398_, v_k_5399_, v_kind_boxed_5406_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_);
lean_dec(v_inst_5397_);
return v_res_5407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(lean_object* v_00_u03b1_5408_, lean_object* v_inst_5409_, lean_object* v_declInfos_5410_, lean_object* v_k_5411_, uint8_t v_kind_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_){
_start:
{
lean_object* v___x_5418_; 
v___x_5418_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7___redArg(v_inst_5409_, v_declInfos_5410_, v_k_5411_, v_kind_5412_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_);
return v___x_5418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b1_5419_, lean_object* v_inst_5420_, lean_object* v_declInfos_5421_, lean_object* v_k_5422_, lean_object* v_kind_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_){
_start:
{
uint8_t v_kind_boxed_5429_; lean_object* v_res_5430_; 
v_kind_boxed_5429_ = lean_unbox(v_kind_5423_);
v_res_5430_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v_00_u03b1_5419_, v_inst_5420_, v_declInfos_5421_, v_k_5422_, v_kind_boxed_5429_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_);
lean_dec(v_inst_5420_);
return v_res_5430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_5431_, lean_object* v_declInfos_5432_, lean_object* v_k_5433_, uint8_t v_kind_5434_, lean_object* v_inst_5435_, lean_object* v_acc_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_){
_start:
{
lean_object* v___x_5442_; 
v___x_5442_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___redArg(v_declInfos_5432_, v_k_5433_, v_kind_5434_, v_acc_5436_, v___y_5437_, v___y_5438_, v___y_5439_, v___y_5440_);
return v___x_5442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_5443_, lean_object* v_declInfos_5444_, lean_object* v_k_5445_, lean_object* v_kind_5446_, lean_object* v_inst_5447_, lean_object* v_acc_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_){
_start:
{
uint8_t v_kind_boxed_5454_; lean_object* v_res_5455_; 
v_kind_boxed_5454_ = lean_unbox(v_kind_5446_);
v_res_5455_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_00_u03b1_5443_, v_declInfos_5444_, v_k_5445_, v_kind_boxed_5454_, v_inst_5447_, v_acc_5448_, v___y_5449_, v___y_5450_, v___y_5451_, v___y_5452_);
lean_dec(v_inst_5447_);
return v_res_5455_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(lean_object* v_upperBound_5456_, lean_object* v_matchDeclName_5457_, lean_object* v_a_5458_, lean_object* v_b_5459_){
_start:
{
uint8_t v___x_5461_; 
v___x_5461_ = lean_nat_dec_lt(v_a_5458_, v_upperBound_5456_);
if (v___x_5461_ == 0)
{
lean_object* v___x_5462_; 
lean_dec(v_a_5458_);
lean_dec(v_matchDeclName_5457_);
v___x_5462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5462_, 0, v_b_5459_);
return v___x_5462_;
}
else
{
lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; 
v___x_5463_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_5457_);
v___x_5464_ = l_Lean_Name_str___override(v_matchDeclName_5457_, v___x_5463_);
v___x_5465_ = lean_unsigned_to_nat(1u);
v___x_5466_ = lean_nat_add(v_a_5458_, v___x_5465_);
lean_dec(v_a_5458_);
lean_inc(v___x_5466_);
v___x_5467_ = lean_name_append_index_after(v___x_5464_, v___x_5466_);
v___x_5468_ = lean_array_push(v_b_5459_, v___x_5467_);
v_a_5458_ = v___x_5466_;
v_b_5459_ = v___x_5468_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg___boxed(lean_object* v_upperBound_5470_, lean_object* v_matchDeclName_5471_, lean_object* v_a_5472_, lean_object* v_b_5473_, lean_object* v___y_5474_){
_start:
{
lean_object* v_res_5475_; 
v_res_5475_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5470_, v_matchDeclName_5471_, v_a_5472_, v_b_5473_);
lean_dec(v_upperBound_5470_);
return v_res_5475_;
}
}
LEAN_EXPORT lean_object* lean_get_congr_match_equations_for(lean_object* v_matchDeclName_5476_, lean_object* v_a_5477_, lean_object* v_a_5478_, lean_object* v_a_5479_, lean_object* v_a_5480_){
_start:
{
lean_object* v___x_5482_; lean_object* v_firstEqnName_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; 
v___x_5482_ = l_Lean_Meta_Match_congrEqn1ThmSuffix;
lean_inc(v_matchDeclName_5476_);
v_firstEqnName_5483_ = l_Lean_Name_str___override(v_matchDeclName_5476_, v___x_5482_);
lean_inc(v_matchDeclName_5476_);
v___x_5484_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed), 6, 1);
lean_closure_set(v___x_5484_, 0, v_matchDeclName_5476_);
lean_inc(v_a_5480_);
lean_inc_ref(v_a_5479_);
lean_inc(v_a_5478_);
lean_inc_ref(v_a_5477_);
lean_inc(v_matchDeclName_5476_);
v___x_5485_ = l_Lean_Meta_realizeConst(v_matchDeclName_5476_, v_firstEqnName_5483_, v___x_5484_, v_a_5477_, v_a_5478_, v_a_5479_, v_a_5480_);
if (lean_obj_tag(v___x_5485_) == 0)
{
lean_object* v___x_5486_; lean_object* v_a_5487_; 
lean_dec_ref(v___x_5485_);
lean_inc(v_matchDeclName_5476_);
v___x_5486_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_5476_, v_a_5480_);
v_a_5487_ = lean_ctor_get(v___x_5486_, 0);
lean_inc(v_a_5487_);
lean_dec_ref(v___x_5486_);
if (lean_obj_tag(v_a_5487_) == 1)
{
lean_object* v_val_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; 
lean_dec(v_a_5480_);
lean_dec_ref(v_a_5479_);
lean_dec(v_a_5478_);
lean_dec_ref(v_a_5477_);
v_val_5488_ = lean_ctor_get(v_a_5487_, 0);
lean_inc(v_val_5488_);
lean_dec_ref(v_a_5487_);
v___x_5489_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5488_);
lean_dec(v_val_5488_);
v___x_5490_ = lean_unsigned_to_nat(0u);
v___x_5491_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___x_5492_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v___x_5489_, v_matchDeclName_5476_, v___x_5490_, v___x_5491_);
lean_dec(v___x_5489_);
return v___x_5492_;
}
else
{
lean_object* v___x_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5498_; 
lean_dec(v_a_5487_);
v___x_5493_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5494_ = l_Lean_MessageData_ofName(v_matchDeclName_5476_);
v___x_5495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5495_, 0, v___x_5493_);
lean_ctor_set(v___x_5495_, 1, v___x_5494_);
v___x_5496_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5497_, 0, v___x_5495_);
lean_ctor_set(v___x_5497_, 1, v___x_5496_);
v___x_5498_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5497_, v_a_5477_, v_a_5478_, v_a_5479_, v_a_5480_);
lean_dec(v_a_5480_);
lean_dec_ref(v_a_5479_);
lean_dec(v_a_5478_);
lean_dec_ref(v_a_5477_);
return v___x_5498_;
}
}
else
{
lean_object* v_a_5499_; lean_object* v___x_5501_; uint8_t v_isShared_5502_; uint8_t v_isSharedCheck_5506_; 
lean_dec(v_a_5480_);
lean_dec_ref(v_a_5479_);
lean_dec(v_a_5478_);
lean_dec_ref(v_a_5477_);
lean_dec(v_matchDeclName_5476_);
v_a_5499_ = lean_ctor_get(v___x_5485_, 0);
v_isSharedCheck_5506_ = !lean_is_exclusive(v___x_5485_);
if (v_isSharedCheck_5506_ == 0)
{
v___x_5501_ = v___x_5485_;
v_isShared_5502_ = v_isSharedCheck_5506_;
goto v_resetjp_5500_;
}
else
{
lean_inc(v_a_5499_);
lean_dec(v___x_5485_);
v___x_5501_ = lean_box(0);
v_isShared_5502_ = v_isSharedCheck_5506_;
goto v_resetjp_5500_;
}
v_resetjp_5500_:
{
lean_object* v___x_5504_; 
if (v_isShared_5502_ == 0)
{
v___x_5504_ = v___x_5501_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5505_; 
v_reuseFailAlloc_5505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5505_, 0, v_a_5499_);
v___x_5504_ = v_reuseFailAlloc_5505_;
goto v_reusejp_5503_;
}
v_reusejp_5503_:
{
return v___x_5504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_genMatchCongrEqnsImpl___boxed(lean_object* v_matchDeclName_5507_, lean_object* v_a_5508_, lean_object* v_a_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_, lean_object* v_a_5512_){
_start:
{
lean_object* v_res_5513_; 
v_res_5513_ = lean_get_congr_match_equations_for(v_matchDeclName_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_);
return v_res_5513_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(lean_object* v_upperBound_5514_, lean_object* v_matchDeclName_5515_, lean_object* v_inst_5516_, lean_object* v_R_5517_, lean_object* v_a_5518_, lean_object* v_b_5519_, lean_object* v_c_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_, lean_object* v___y_5524_){
_start:
{
lean_object* v___x_5526_; 
v___x_5526_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5514_, v_matchDeclName_5515_, v_a_5518_, v_b_5519_);
return v___x_5526_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___boxed(lean_object* v_upperBound_5527_, lean_object* v_matchDeclName_5528_, lean_object* v_inst_5529_, lean_object* v_R_5530_, lean_object* v_a_5531_, lean_object* v_b_5532_, lean_object* v_c_5533_, lean_object* v___y_5534_, lean_object* v___y_5535_, lean_object* v___y_5536_, lean_object* v___y_5537_, lean_object* v___y_5538_){
_start:
{
lean_object* v_res_5539_; 
v_res_5539_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(v_upperBound_5527_, v_matchDeclName_5528_, v_inst_5529_, v_R_5530_, v_a_5531_, v_b_5532_, v_c_5533_, v___y_5534_, v___y_5535_, v___y_5536_, v___y_5537_);
lean_dec(v___y_5537_);
lean_dec_ref(v___y_5536_);
lean_dec(v___y_5535_);
lean_dec_ref(v___y_5534_);
lean_dec(v_upperBound_5527_);
return v_res_5539_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5590_; lean_object* v___x_5591_; lean_object* v___x_5592_; 
v___x_5590_ = lean_unsigned_to_nat(3248161880u);
v___x_5591_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__19_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5592_ = l_Lean_Name_num___override(v___x_5591_, v___x_5590_);
return v___x_5592_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5594_; lean_object* v___x_5595_; lean_object* v___x_5596_; 
v___x_5594_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__21_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5595_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5596_ = l_Lean_Name_str___override(v___x_5595_, v___x_5594_);
return v___x_5596_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; 
v___x_5598_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__23_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5599_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5600_ = l_Lean_Name_str___override(v___x_5599_, v___x_5598_);
return v___x_5600_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5601_; lean_object* v___x_5602_; lean_object* v___x_5603_; 
v___x_5601_ = lean_unsigned_to_nat(2u);
v___x_5602_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5603_ = l_Lean_Name_num___override(v___x_5602_, v___x_5601_);
return v___x_5603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5605_; uint8_t v___x_5606_; lean_object* v___x_5607_; lean_object* v___x_5608_; 
v___x_5605_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_5606_ = 0;
v___x_5607_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5608_ = l_Lean_registerTraceClass(v___x_5605_, v___x_5606_, v___x_5607_);
return v___x_5608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2____boxed(lean_object* v_a_5609_){
_start:
{
lean_object* v_res_5610_; 
v_res_5610_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_();
return v_res_5610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(lean_object* v_env_5611_, lean_object* v_n_5612_){
_start:
{
if (lean_obj_tag(v_n_5612_) == 1)
{
lean_object* v_pre_5613_; lean_object* v_str_5614_; uint8_t v___y_5616_; uint8_t v___x_5622_; 
v_pre_5613_ = lean_ctor_get(v_n_5612_, 0);
lean_inc(v_pre_5613_);
v_str_5614_ = lean_ctor_get(v_n_5612_, 1);
lean_inc_ref(v_str_5614_);
lean_dec_ref(v_n_5612_);
lean_inc_ref(v_str_5614_);
v___x_5622_ = l_Lean_Meta_isEqnReservedNameSuffix(v_str_5614_);
if (v___x_5622_ == 0)
{
lean_object* v___x_5623_; uint8_t v___x_5624_; 
v___x_5623_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__0));
v___x_5624_ = lean_string_dec_eq(v_str_5614_, v___x_5623_);
lean_dec_ref(v_str_5614_);
v___y_5616_ = v___x_5624_;
goto v___jp_5615_;
}
else
{
lean_dec_ref(v_str_5614_);
v___y_5616_ = v___x_5622_;
goto v___jp_5615_;
}
v___jp_5615_:
{
if (v___y_5616_ == 0)
{
lean_object* v___x_5617_; 
lean_dec(v_pre_5613_);
lean_dec_ref(v_env_5611_);
v___x_5617_ = lean_box(0);
return v___x_5617_;
}
else
{
lean_object* v___x_5618_; 
v___x_5618_ = lean_private_to_user_name(v_pre_5613_);
if (lean_obj_tag(v___x_5618_) == 0)
{
lean_dec_ref(v_env_5611_);
return v___x_5618_;
}
else
{
lean_object* v_val_5619_; uint8_t v___x_5620_; 
v_val_5619_ = lean_ctor_get(v___x_5618_, 0);
lean_inc(v_val_5619_);
v___x_5620_ = lean_is_matcher(v_env_5611_, v_val_5619_);
if (v___x_5620_ == 0)
{
lean_object* v___x_5621_; 
lean_dec_ref(v___x_5618_);
v___x_5621_ = lean_box(0);
return v___x_5621_;
}
else
{
return v___x_5618_;
}
}
}
}
}
else
{
lean_object* v___x_5625_; 
lean_dec(v_n_5612_);
lean_dec_ref(v_env_5611_);
v___x_5625_ = lean_box(0);
return v___x_5625_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(lean_object* v_x1_5626_, lean_object* v_x2_5627_){
_start:
{
lean_object* v___x_5628_; 
v___x_5628_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_x1_5626_, v_x2_5627_);
if (lean_obj_tag(v___x_5628_) == 0)
{
uint8_t v___x_5629_; 
v___x_5629_ = 0;
return v___x_5629_;
}
else
{
uint8_t v___x_5630_; 
lean_dec_ref(v___x_5628_);
v___x_5630_ = 1;
return v___x_5630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_x1_5631_, lean_object* v_x2_5632_){
_start:
{
uint8_t v_res_5633_; lean_object* v_r_5634_; 
v_res_5633_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(v_x1_5631_, v_x2_5632_);
v_r_5634_ = lean_box(v_res_5633_);
return v_r_5634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5637_; lean_object* v___x_5638_; 
v___f_5637_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_));
v___x_5638_ = l_Lean_registerReservedNamePredicate(v___f_5637_);
return v___x_5638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_a_5639_){
_start:
{
lean_object* v_res_5640_; 
v_res_5640_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_();
return v_res_5640_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; 
v___x_5643_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5644_ = lean_unsigned_to_nat(0u);
v___x_5645_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_5645_, 0, v___x_5644_);
lean_ctor_set(v___x_5645_, 1, v___x_5644_);
lean_ctor_set(v___x_5645_, 2, v___x_5644_);
lean_ctor_set(v___x_5645_, 3, v___x_5643_);
lean_ctor_set(v___x_5645_, 4, v___x_5643_);
lean_ctor_set(v___x_5645_, 5, v___x_5643_);
lean_ctor_set(v___x_5645_, 6, v___x_5643_);
lean_ctor_set(v___x_5645_, 7, v___x_5643_);
lean_ctor_set(v___x_5645_, 8, v___x_5643_);
return v___x_5645_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5646_; lean_object* v___x_5647_; 
v___x_5646_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5647_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5647_, 0, v___x_5646_);
lean_ctor_set(v___x_5647_, 1, v___x_5646_);
lean_ctor_set(v___x_5647_, 2, v___x_5646_);
lean_ctor_set(v___x_5647_, 3, v___x_5646_);
lean_ctor_set(v___x_5647_, 4, v___x_5646_);
lean_ctor_set(v___x_5647_, 5, v___x_5646_);
return v___x_5647_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5648_; lean_object* v___x_5649_; 
v___x_5648_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5649_, 0, v___x_5648_);
lean_ctor_set(v___x_5649_, 1, v___x_5648_);
lean_ctor_set(v___x_5649_, 2, v___x_5648_);
lean_ctor_set(v___x_5649_, 3, v___x_5648_);
lean_ctor_set(v___x_5649_, 4, v___x_5648_);
return v___x_5649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(lean_object* v___x_5650_, lean_object* v_name_5651_, lean_object* v___y_5652_, lean_object* v___y_5653_){
_start:
{
lean_object* v___x_5655_; lean_object* v_env_5656_; lean_object* v___x_5657_; 
v___x_5655_ = lean_st_ref_get(v___y_5653_);
v_env_5656_ = lean_ctor_get(v___x_5655_, 0);
lean_inc_ref(v_env_5656_);
lean_dec(v___x_5655_);
v___x_5657_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_env_5656_, v_name_5651_);
if (lean_obj_tag(v___x_5657_) == 1)
{
lean_object* v_val_5658_; lean_object* v___x_5659_; uint8_t v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; uint8_t v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; 
v_val_5658_ = lean_ctor_get(v___x_5657_, 0);
lean_inc(v_val_5658_);
lean_dec_ref(v___x_5657_);
v___x_5659_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_5660_ = 0;
v___x_5661_ = lean_unsigned_to_nat(0u);
v___x_5662_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5663_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5664_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5665_ = lean_box(0);
v___x_5666_ = 1;
lean_inc(v___x_5650_);
v___x_5667_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5667_, 0, v___x_5659_);
lean_ctor_set(v___x_5667_, 1, v___x_5650_);
lean_ctor_set(v___x_5667_, 2, v___x_5663_);
lean_ctor_set(v___x_5667_, 3, v___x_5664_);
lean_ctor_set(v___x_5667_, 4, v___x_5665_);
lean_ctor_set(v___x_5667_, 5, v___x_5661_);
lean_ctor_set(v___x_5667_, 6, v___x_5665_);
lean_ctor_set_uint8(v___x_5667_, sizeof(void*)*7, v___x_5660_);
lean_ctor_set_uint8(v___x_5667_, sizeof(void*)*7 + 1, v___x_5660_);
lean_ctor_set_uint8(v___x_5667_, sizeof(void*)*7 + 2, v___x_5660_);
lean_ctor_set_uint8(v___x_5667_, sizeof(void*)*7 + 3, v___x_5666_);
v___x_5668_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5669_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5670_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5671_, 0, v___x_5668_);
lean_ctor_set(v___x_5671_, 1, v___x_5669_);
lean_ctor_set(v___x_5671_, 2, v___x_5650_);
lean_ctor_set(v___x_5671_, 3, v___x_5662_);
lean_ctor_set(v___x_5671_, 4, v___x_5670_);
v___x_5672_ = lean_st_mk_ref(v___x_5671_);
lean_inc(v___x_5672_);
v___x_5673_ = lean_get_match_equations_for(v_val_5658_, v___x_5667_, v___x_5672_, v___y_5652_, v___y_5653_);
if (lean_obj_tag(v___x_5673_) == 0)
{
lean_object* v___x_5675_; uint8_t v_isShared_5676_; uint8_t v_isSharedCheck_5682_; 
v_isSharedCheck_5682_ = !lean_is_exclusive(v___x_5673_);
if (v_isSharedCheck_5682_ == 0)
{
lean_object* v_unused_5683_; 
v_unused_5683_ = lean_ctor_get(v___x_5673_, 0);
lean_dec(v_unused_5683_);
v___x_5675_ = v___x_5673_;
v_isShared_5676_ = v_isSharedCheck_5682_;
goto v_resetjp_5674_;
}
else
{
lean_dec(v___x_5673_);
v___x_5675_ = lean_box(0);
v_isShared_5676_ = v_isSharedCheck_5682_;
goto v_resetjp_5674_;
}
v_resetjp_5674_:
{
lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5680_; 
v___x_5677_ = lean_st_ref_get(v___x_5672_);
lean_dec(v___x_5672_);
lean_dec(v___x_5677_);
v___x_5678_ = lean_box(v___x_5666_);
if (v_isShared_5676_ == 0)
{
lean_ctor_set(v___x_5675_, 0, v___x_5678_);
v___x_5680_ = v___x_5675_;
goto v_reusejp_5679_;
}
else
{
lean_object* v_reuseFailAlloc_5681_; 
v_reuseFailAlloc_5681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5681_, 0, v___x_5678_);
v___x_5680_ = v_reuseFailAlloc_5681_;
goto v_reusejp_5679_;
}
v_reusejp_5679_:
{
return v___x_5680_;
}
}
}
else
{
lean_dec(v___x_5672_);
if (lean_obj_tag(v___x_5673_) == 0)
{
lean_object* v___x_5685_; uint8_t v_isShared_5686_; uint8_t v_isSharedCheck_5691_; 
v_isSharedCheck_5691_ = !lean_is_exclusive(v___x_5673_);
if (v_isSharedCheck_5691_ == 0)
{
lean_object* v_unused_5692_; 
v_unused_5692_ = lean_ctor_get(v___x_5673_, 0);
lean_dec(v_unused_5692_);
v___x_5685_ = v___x_5673_;
v_isShared_5686_ = v_isSharedCheck_5691_;
goto v_resetjp_5684_;
}
else
{
lean_dec(v___x_5673_);
v___x_5685_ = lean_box(0);
v_isShared_5686_ = v_isSharedCheck_5691_;
goto v_resetjp_5684_;
}
v_resetjp_5684_:
{
lean_object* v___x_5687_; lean_object* v___x_5689_; 
v___x_5687_ = lean_box(v___x_5666_);
if (v_isShared_5686_ == 0)
{
lean_ctor_set_tag(v___x_5685_, 0);
lean_ctor_set(v___x_5685_, 0, v___x_5687_);
v___x_5689_ = v___x_5685_;
goto v_reusejp_5688_;
}
else
{
lean_object* v_reuseFailAlloc_5690_; 
v_reuseFailAlloc_5690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5690_, 0, v___x_5687_);
v___x_5689_ = v_reuseFailAlloc_5690_;
goto v_reusejp_5688_;
}
v_reusejp_5688_:
{
return v___x_5689_;
}
}
}
else
{
lean_object* v_a_5693_; lean_object* v___x_5695_; uint8_t v_isShared_5696_; uint8_t v_isSharedCheck_5700_; 
v_a_5693_ = lean_ctor_get(v___x_5673_, 0);
v_isSharedCheck_5700_ = !lean_is_exclusive(v___x_5673_);
if (v_isSharedCheck_5700_ == 0)
{
v___x_5695_ = v___x_5673_;
v_isShared_5696_ = v_isSharedCheck_5700_;
goto v_resetjp_5694_;
}
else
{
lean_inc(v_a_5693_);
lean_dec(v___x_5673_);
v___x_5695_ = lean_box(0);
v_isShared_5696_ = v_isSharedCheck_5700_;
goto v_resetjp_5694_;
}
v_resetjp_5694_:
{
lean_object* v___x_5698_; 
if (v_isShared_5696_ == 0)
{
v___x_5698_ = v___x_5695_;
goto v_reusejp_5697_;
}
else
{
lean_object* v_reuseFailAlloc_5699_; 
v_reuseFailAlloc_5699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5699_, 0, v_a_5693_);
v___x_5698_ = v_reuseFailAlloc_5699_;
goto v_reusejp_5697_;
}
v_reusejp_5697_:
{
return v___x_5698_;
}
}
}
}
}
else
{
uint8_t v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; 
lean_dec(v___x_5657_);
lean_dec(v___y_5653_);
lean_dec_ref(v___y_5652_);
lean_dec(v___x_5650_);
v___x_5701_ = 0;
v___x_5702_ = lean_box(v___x_5701_);
v___x_5703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5703_, 0, v___x_5702_);
return v___x_5703_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v___x_5704_, lean_object* v_name_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_){
_start:
{
lean_object* v_res_5709_; 
v_res_5709_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(v___x_5704_, v_name_5705_, v___y_5706_, v___y_5707_);
return v_res_5709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5713_; lean_object* v___x_5714_; 
v___f_5713_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5714_ = l_Lean_registerReservedNameAction(v___f_5713_);
return v___x_5714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v_a_5715_){
_start:
{
lean_object* v_res_5716_; 
v_res_5716_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_();
return v_res_5716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(lean_object* v_env_5717_, lean_object* v_n_5718_){
_start:
{
if (lean_obj_tag(v_n_5718_) == 1)
{
lean_object* v_pre_5719_; lean_object* v_str_5720_; uint8_t v___x_5721_; 
v_pre_5719_ = lean_ctor_get(v_n_5718_, 0);
lean_inc(v_pre_5719_);
v_str_5720_ = lean_ctor_get(v_n_5718_, 1);
lean_inc_ref(v_str_5720_);
lean_dec_ref(v_n_5718_);
v___x_5721_ = l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(v_str_5720_);
if (v___x_5721_ == 0)
{
lean_object* v___x_5722_; 
lean_dec(v_pre_5719_);
lean_dec_ref(v_env_5717_);
v___x_5722_ = lean_box(0);
return v___x_5722_;
}
else
{
uint8_t v___x_5723_; 
lean_inc(v_pre_5719_);
v___x_5723_ = lean_is_matcher(v_env_5717_, v_pre_5719_);
if (v___x_5723_ == 0)
{
lean_object* v___x_5724_; 
lean_dec(v_pre_5719_);
v___x_5724_ = lean_box(0);
return v___x_5724_;
}
else
{
lean_object* v___x_5725_; 
v___x_5725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5725_, 0, v_pre_5719_);
return v___x_5725_;
}
}
}
else
{
lean_object* v___x_5726_; 
lean_dec(v_n_5718_);
lean_dec_ref(v_env_5717_);
v___x_5726_ = lean_box(0);
return v___x_5726_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(lean_object* v_x1_5727_, lean_object* v_x2_5728_){
_start:
{
lean_object* v___x_5729_; 
v___x_5729_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_x1_5727_, v_x2_5728_);
if (lean_obj_tag(v___x_5729_) == 0)
{
uint8_t v___x_5730_; 
v___x_5730_ = 0;
return v___x_5730_;
}
else
{
uint8_t v___x_5731_; 
lean_dec_ref(v___x_5729_);
v___x_5731_ = 1;
return v___x_5731_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_x1_5732_, lean_object* v_x2_5733_){
_start:
{
uint8_t v_res_5734_; lean_object* v_r_5735_; 
v_res_5734_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(v_x1_5732_, v_x2_5733_);
v_r_5735_ = lean_box(v_res_5734_);
return v_r_5735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5738_; lean_object* v___x_5739_; 
v___f_5738_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_));
v___x_5739_ = l_Lean_registerReservedNamePredicate(v___f_5738_);
return v___x_5739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_a_5740_){
_start:
{
lean_object* v_res_5741_; 
v_res_5741_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_();
return v_res_5741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(lean_object* v___x_5742_, lean_object* v_name_5743_, lean_object* v___y_5744_, lean_object* v___y_5745_){
_start:
{
lean_object* v___x_5747_; lean_object* v_env_5748_; lean_object* v___x_5749_; 
v___x_5747_ = lean_st_ref_get(v___y_5745_);
v_env_5748_ = lean_ctor_get(v___x_5747_, 0);
lean_inc_ref(v_env_5748_);
lean_dec(v___x_5747_);
v___x_5749_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_env_5748_, v_name_5743_);
if (lean_obj_tag(v___x_5749_) == 1)
{
lean_object* v_val_5750_; lean_object* v___x_5751_; uint8_t v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; uint8_t v___x_5760_; lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; lean_object* v___x_5767_; 
v_val_5750_ = lean_ctor_get(v___x_5749_, 0);
lean_inc(v_val_5750_);
lean_dec_ref(v___x_5749_);
v___x_5751_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_5752_ = 0;
v___x_5753_ = lean_unsigned_to_nat(32u);
v___x_5754_ = lean_mk_empty_array_with_capacity(v___x_5753_);
lean_dec_ref(v___x_5754_);
v___x_5755_ = lean_unsigned_to_nat(0u);
v___x_5756_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5757_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5758_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5759_ = lean_box(0);
v___x_5760_ = 1;
lean_inc(v___x_5742_);
v___x_5761_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5761_, 0, v___x_5751_);
lean_ctor_set(v___x_5761_, 1, v___x_5742_);
lean_ctor_set(v___x_5761_, 2, v___x_5757_);
lean_ctor_set(v___x_5761_, 3, v___x_5758_);
lean_ctor_set(v___x_5761_, 4, v___x_5759_);
lean_ctor_set(v___x_5761_, 5, v___x_5755_);
lean_ctor_set(v___x_5761_, 6, v___x_5759_);
lean_ctor_set_uint8(v___x_5761_, sizeof(void*)*7, v___x_5752_);
lean_ctor_set_uint8(v___x_5761_, sizeof(void*)*7 + 1, v___x_5752_);
lean_ctor_set_uint8(v___x_5761_, sizeof(void*)*7 + 2, v___x_5752_);
lean_ctor_set_uint8(v___x_5761_, sizeof(void*)*7 + 3, v___x_5760_);
v___x_5762_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5763_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5764_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5765_, 0, v___x_5762_);
lean_ctor_set(v___x_5765_, 1, v___x_5763_);
lean_ctor_set(v___x_5765_, 2, v___x_5742_);
lean_ctor_set(v___x_5765_, 3, v___x_5756_);
lean_ctor_set(v___x_5765_, 4, v___x_5764_);
v___x_5766_ = lean_st_mk_ref(v___x_5765_);
lean_inc(v___x_5766_);
v___x_5767_ = lean_get_congr_match_equations_for(v_val_5750_, v___x_5761_, v___x_5766_, v___y_5744_, v___y_5745_);
if (lean_obj_tag(v___x_5767_) == 0)
{
lean_object* v___x_5769_; uint8_t v_isShared_5770_; uint8_t v_isSharedCheck_5776_; 
v_isSharedCheck_5776_ = !lean_is_exclusive(v___x_5767_);
if (v_isSharedCheck_5776_ == 0)
{
lean_object* v_unused_5777_; 
v_unused_5777_ = lean_ctor_get(v___x_5767_, 0);
lean_dec(v_unused_5777_);
v___x_5769_ = v___x_5767_;
v_isShared_5770_ = v_isSharedCheck_5776_;
goto v_resetjp_5768_;
}
else
{
lean_dec(v___x_5767_);
v___x_5769_ = lean_box(0);
v_isShared_5770_ = v_isSharedCheck_5776_;
goto v_resetjp_5768_;
}
v_resetjp_5768_:
{
lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5774_; 
v___x_5771_ = lean_st_ref_get(v___x_5766_);
lean_dec(v___x_5766_);
lean_dec(v___x_5771_);
v___x_5772_ = lean_box(v___x_5760_);
if (v_isShared_5770_ == 0)
{
lean_ctor_set(v___x_5769_, 0, v___x_5772_);
v___x_5774_ = v___x_5769_;
goto v_reusejp_5773_;
}
else
{
lean_object* v_reuseFailAlloc_5775_; 
v_reuseFailAlloc_5775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5775_, 0, v___x_5772_);
v___x_5774_ = v_reuseFailAlloc_5775_;
goto v_reusejp_5773_;
}
v_reusejp_5773_:
{
return v___x_5774_;
}
}
}
else
{
lean_dec(v___x_5766_);
if (lean_obj_tag(v___x_5767_) == 0)
{
lean_object* v___x_5779_; uint8_t v_isShared_5780_; uint8_t v_isSharedCheck_5785_; 
v_isSharedCheck_5785_ = !lean_is_exclusive(v___x_5767_);
if (v_isSharedCheck_5785_ == 0)
{
lean_object* v_unused_5786_; 
v_unused_5786_ = lean_ctor_get(v___x_5767_, 0);
lean_dec(v_unused_5786_);
v___x_5779_ = v___x_5767_;
v_isShared_5780_ = v_isSharedCheck_5785_;
goto v_resetjp_5778_;
}
else
{
lean_dec(v___x_5767_);
v___x_5779_ = lean_box(0);
v_isShared_5780_ = v_isSharedCheck_5785_;
goto v_resetjp_5778_;
}
v_resetjp_5778_:
{
lean_object* v___x_5781_; lean_object* v___x_5783_; 
v___x_5781_ = lean_box(v___x_5760_);
if (v_isShared_5780_ == 0)
{
lean_ctor_set_tag(v___x_5779_, 0);
lean_ctor_set(v___x_5779_, 0, v___x_5781_);
v___x_5783_ = v___x_5779_;
goto v_reusejp_5782_;
}
else
{
lean_object* v_reuseFailAlloc_5784_; 
v_reuseFailAlloc_5784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5784_, 0, v___x_5781_);
v___x_5783_ = v_reuseFailAlloc_5784_;
goto v_reusejp_5782_;
}
v_reusejp_5782_:
{
return v___x_5783_;
}
}
}
else
{
lean_object* v_a_5787_; lean_object* v___x_5789_; uint8_t v_isShared_5790_; uint8_t v_isSharedCheck_5794_; 
v_a_5787_ = lean_ctor_get(v___x_5767_, 0);
v_isSharedCheck_5794_ = !lean_is_exclusive(v___x_5767_);
if (v_isSharedCheck_5794_ == 0)
{
v___x_5789_ = v___x_5767_;
v_isShared_5790_ = v_isSharedCheck_5794_;
goto v_resetjp_5788_;
}
else
{
lean_inc(v_a_5787_);
lean_dec(v___x_5767_);
v___x_5789_ = lean_box(0);
v_isShared_5790_ = v_isSharedCheck_5794_;
goto v_resetjp_5788_;
}
v_resetjp_5788_:
{
lean_object* v___x_5792_; 
if (v_isShared_5790_ == 0)
{
v___x_5792_ = v___x_5789_;
goto v_reusejp_5791_;
}
else
{
lean_object* v_reuseFailAlloc_5793_; 
v_reuseFailAlloc_5793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5793_, 0, v_a_5787_);
v___x_5792_ = v_reuseFailAlloc_5793_;
goto v_reusejp_5791_;
}
v_reusejp_5791_:
{
return v___x_5792_;
}
}
}
}
}
else
{
uint8_t v___x_5795_; lean_object* v___x_5796_; lean_object* v___x_5797_; 
lean_dec(v___x_5749_);
lean_dec(v___y_5745_);
lean_dec_ref(v___y_5744_);
lean_dec(v___x_5742_);
v___x_5795_ = 0;
v___x_5796_ = lean_box(v___x_5795_);
v___x_5797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5797_, 0, v___x_5796_);
return v___x_5797_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v___x_5798_, lean_object* v_name_5799_, lean_object* v___y_5800_, lean_object* v___y_5801_, lean_object* v___y_5802_){
_start:
{
lean_object* v_res_5803_; 
v_res_5803_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(v___x_5798_, v_name_5799_, v___y_5800_, v___y_5801_);
return v_res_5803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5807_; lean_object* v___x_5808_; 
v___f_5807_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_));
v___x_5808_ = l_Lean_registerReservedNameAction(v___f_5807_);
return v___x_5808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v_a_5809_){
_start:
{
lean_object* v_res_5810_; 
v_res_5810_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_();
return v_res_5810_;
}
}
lean_object* runtime_initialize_Lean_Meta_Match_Match(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_MatchEqsExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_SplitIf(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_CasesOnStuckLHS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_SimpH(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_AltTelescopes(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_NamedPatterns(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SplitSparseCasesOn(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_MatchEqs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Match_Match(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_MatchEqsExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_SplitIf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_CasesOnStuckLHS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_SimpH(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_AltTelescopes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_NamedPatterns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_SplitSparseCasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Match_MatchEqs(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Match_Match(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_MatchEqsExt(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_SplitIf(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_CasesOnStuckLHS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_SimpH(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_AltTelescopes(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_NamedPatterns(uint8_t builtin);
lean_object* initialize_Lean_Meta_SplitSparseCasesOn(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_MatchEqs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Match_Match(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatchEqsExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_SplitIf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_CasesOnStuckLHS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_SimpH(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_AltTelescopes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_NamedPatterns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SplitSparseCasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_MatchEqs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Match_MatchEqs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Match_MatchEqs(builtin);
}
#ifdef __cplusplus
}
#endif
