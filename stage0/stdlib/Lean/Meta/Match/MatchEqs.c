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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introSubstEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_deltaTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(lean_object*);
uint8_t l_Lean_Meta_isMatcherCore(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
size_t lean_usize_shift_right(size_t, size_t);
extern lean_object* l_Lean_Meta_eqnThmSuffixBase;
lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
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
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
extern lean_object* l_Lean_Meta_Match_matchEqnsExt;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_Meta_Match_congrEqn1ThmSuffix;
lean_object* l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_privateToUserName_x3f(lean_object*);
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
static lean_once_cell_t l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__3;
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
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elimOffset"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(238, 85, 239, 193, 128, 115, 38, 143)}};
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(94, 91, 22, 141, 221, 120, 153, 253)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__3_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__1 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "goal's target does not contain `Nat.Internal.elimOffset`"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__2 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__14_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__15 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__15_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16;
static const lean_string_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "proveCondEqThm.go "};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8_value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8_value)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__4_value)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8_value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__5_value)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8_value),((lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__6_value)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__7 = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__7_value;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__2 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__3 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__4 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__5 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 77, .m_capacity = 77, .m_length = 76, .m_data = "_private.Lean.Meta.Match.MatchEqs.0.Lean.Meta.Match.genMatchCongrEqnsImpl.go"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "assertion violation: patterns.size == discrs.size\n        "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__1_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___boxed(lean_object**);
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
static const lean_ctor_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_;
static const lean_array_object l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_;
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
lean_inc_ref_n(v_binderType_93_, 2);
v_body_94_ = lean_ctor_get(v_ty_83_, 2);
lean_inc_ref(v_body_94_);
lean_dec_ref_known(v_ty_83_, 3);
v___x_95_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0___closed__0));
v_sz_96_ = lean_array_size(v_heqs_80_);
v___x_97_ = ((size_t)0ULL);
lean_inc_ref(v_heqs_80_);
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
return v___x_122_;
}
}
else
{
lean_object* v_val_124_; lean_object* v___x_126_; 
lean_del_object(v___x_105_);
lean_dec_ref(v_binderType_93_);
lean_dec(v_binderName_92_);
lean_dec_ref(v_heqs_80_);
v_val_124_ = lean_ctor_get(v_fst_103_, 0);
lean_inc(v_val_124_);
lean_dec_ref_known(v_fst_103_, 1);
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
lean_dec_ref_known(v___x_168_, 1);
lean_inc_ref(v_binderType_149_);
v___x_170_ = l_Lean_Meta_isExprDefEq(v_a_169_, v_binderType_149_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v_a_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v_a_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_a_171_);
lean_dec_ref_known(v___x_170_, 1);
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
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
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
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
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
lean_dec_ref_known(v___x_272_, 1);
v___x_274_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alt_264_);
v___x_275_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go(v_alt_264_, v_heqs_265_, v_numDiscrEqs_266_, v_alt_264_, v_a_273_, v___x_274_, v_a_267_, v_a_268_, v_a_269_, v_a_270_);
return v___x_275_;
}
else
{
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
lean_dec(v_a_282_);
lean_dec_ref(v_a_281_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
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
lean_object* v_cellCount_298_; lean_object* v___x_299_; 
v_cellCount_298_ = lean_unsigned_to_nat(16u);
v___x_299_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_298_);
return v___x_299_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v_cellCount_300_; lean_object* v___x_301_; 
v_cellCount_300_ = lean_unsigned_to_nat(16u);
v___x_301_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_300_);
return v___x_301_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_302_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2);
v___x_303_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__1, &l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__1);
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v___x_303_);
lean_ctor_set(v___x_305_, 2, v___x_302_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(lean_object* v_e_306_, lean_object* v_fvarId_307_, lean_object* v___y_308_){
_start:
{
lean_object* v___x_310_; uint8_t v_fst_312_; lean_object* v_mctx_313_; lean_object* v___y_331_; lean_object* v_mctx_336_; lean_object* v___f_337_; lean_object* v___f_338_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_310_ = lean_st_ref_get(v___y_308_);
v_mctx_336_ = lean_ctor_get(v___x_310_, 0);
lean_inc_ref_n(v_mctx_336_, 2);
lean_dec(v___x_310_);
v___f_337_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__0));
v___f_338_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_338_, 0, v_fvarId_307_);
v___x_339_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__3, &l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__3_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__3);
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v_mctx_336_);
v___x_341_ = l_Lean_Expr_hasFVar(v_e_306_);
if (v___x_341_ == 0)
{
uint8_t v___x_342_; 
v___x_342_ = l_Lean_Expr_hasMVar(v_e_306_);
if (v___x_342_ == 0)
{
lean_dec_ref_known(v___x_340_, 2);
lean_dec_ref(v___f_338_);
lean_dec_ref(v_e_306_);
v_fst_312_ = v___x_342_;
v_mctx_313_ = v_mctx_336_;
goto v___jp_311_;
}
else
{
lean_object* v___x_343_; 
lean_dec_ref(v_mctx_336_);
v___x_343_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_338_, v___f_337_, v_e_306_, v___x_340_);
v___y_331_ = v___x_343_;
goto v___jp_330_;
}
}
else
{
lean_object* v___x_344_; 
lean_dec_ref(v_mctx_336_);
v___x_344_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_338_, v___f_337_, v_e_306_, v___x_340_);
v___y_331_ = v___x_344_;
goto v___jp_330_;
}
v___jp_311_:
{
lean_object* v___x_314_; lean_object* v_cache_315_; lean_object* v_zetaDeltaFVarIds_316_; lean_object* v_postponed_317_; lean_object* v_diag_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_328_; 
v___x_314_ = lean_st_ref_take(v___y_308_);
v_cache_315_ = lean_ctor_get(v___x_314_, 1);
v_zetaDeltaFVarIds_316_ = lean_ctor_get(v___x_314_, 2);
v_postponed_317_ = lean_ctor_get(v___x_314_, 3);
v_diag_318_ = lean_ctor_get(v___x_314_, 4);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_328_ == 0)
{
lean_object* v_unused_329_; 
v_unused_329_ = lean_ctor_get(v___x_314_, 0);
lean_dec(v_unused_329_);
v___x_320_ = v___x_314_;
v_isShared_321_ = v_isSharedCheck_328_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_diag_318_);
lean_inc(v_postponed_317_);
lean_inc(v_zetaDeltaFVarIds_316_);
lean_inc(v_cache_315_);
lean_dec(v___x_314_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_328_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 0, v_mctx_313_);
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_mctx_313_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_cache_315_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_zetaDeltaFVarIds_316_);
lean_ctor_set(v_reuseFailAlloc_327_, 3, v_postponed_317_);
lean_ctor_set(v_reuseFailAlloc_327_, 4, v_diag_318_);
v___x_323_ = v_reuseFailAlloc_327_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_324_ = lean_st_ref_put(v___y_308_, v___x_323_);
v___x_325_ = lean_box(v_fst_312_);
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
return v___x_326_;
}
}
}
v___jp_330_:
{
lean_object* v_snd_332_; lean_object* v_fst_333_; lean_object* v_mctx_334_; uint8_t v___x_335_; 
v_snd_332_ = lean_ctor_get(v___y_331_, 1);
lean_inc(v_snd_332_);
v_fst_333_ = lean_ctor_get(v___y_331_, 0);
lean_inc(v_fst_333_);
lean_dec_ref(v___y_331_);
v_mctx_334_ = lean_ctor_get(v_snd_332_, 1);
lean_inc_ref(v_mctx_334_);
lean_dec(v_snd_332_);
v___x_335_ = lean_unbox(v_fst_333_);
lean_dec(v_fst_333_);
v_fst_312_ = v___x_335_;
v_mctx_313_ = v_mctx_334_;
goto v___jp_311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___boxed(lean_object* v_e_345_, lean_object* v_fvarId_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_e_345_, v_fvarId_346_, v___y_347_);
lean_dec(v___y_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0(lean_object* v_e_350_, lean_object* v_fvarId_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_e_350_, v_fvarId_351_, v___y_353_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___boxed(lean_object* v_e_358_, lean_object* v_fvarId_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0(v_e_358_, v_fvarId_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg(lean_object* v_mvarId_366_, lean_object* v_x_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_366_, v_x_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
v_a_382_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_373_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_373_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg___boxed(lean_object* v_mvarId_390_, lean_object* v_x_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg(v_mvarId_390_, v_x_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2(lean_object* v_00_u03b1_398_, lean_object* v_mvarId_399_, lean_object* v_x_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg(v_mvarId_399_, v_x_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___boxed(lean_object* v_00_u03b1_407_, lean_object* v_mvarId_408_, lean_object* v_x_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2(v_00_u03b1_407_, v_mvarId_408_, v_x_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5(lean_object* v_mvarId_419_, lean_object* v_as_420_, size_t v_sz_421_, size_t v_i_422_, lean_object* v_b_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
uint8_t v___x_429_; 
v___x_429_ = lean_usize_dec_lt(v_i_422_, v_sz_421_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; 
lean_dec(v_mvarId_419_);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v_b_423_);
return v___x_430_;
}
else
{
lean_object* v_snd_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_533_; 
v_snd_431_ = lean_ctor_get(v_b_423_, 1);
v_isSharedCheck_533_ = !lean_is_exclusive(v_b_423_);
if (v_isSharedCheck_533_ == 0)
{
lean_object* v_unused_534_; 
v_unused_534_ = lean_ctor_get(v_b_423_, 0);
lean_dec(v_unused_534_);
v___x_433_ = v_b_423_;
v_isShared_434_ = v_isSharedCheck_533_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_snd_431_);
lean_dec(v_b_423_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_533_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v_a_437_; lean_object* v_a_444_; 
v___x_435_ = lean_box(0);
v_a_444_ = lean_array_uget(v_as_420_, v_i_422_);
if (lean_obj_tag(v_a_444_) == 0)
{
v_a_437_ = v_snd_431_;
goto v___jp_436_;
}
else
{
lean_object* v_val_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_532_; 
v_val_445_ = lean_ctor_get(v_a_444_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v_a_444_);
if (v_isSharedCheck_532_ == 0)
{
v___x_447_ = v_a_444_;
v_isShared_448_ = v_isSharedCheck_532_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_val_445_);
lean_dec(v_a_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_532_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = l_Lean_LocalDecl_type(v_val_445_);
lean_dec(v_val_445_);
v___x_450_ = l_Lean_Meta_matchEq_x3f(v___x_449_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_a_451_);
lean_dec_ref_known(v___x_450_, 1);
v___x_452_ = lean_box(0);
v___x_453_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5___closed__0));
if (lean_obj_tag(v_a_451_) == 1)
{
lean_object* v_val_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_523_; 
v_val_454_ = lean_ctor_get(v_a_451_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v_a_451_);
if (v_isSharedCheck_523_ == 0)
{
v___x_456_ = v_a_451_;
v_isShared_457_ = v_isSharedCheck_523_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_val_454_);
lean_dec(v_a_451_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_523_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v_snd_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_521_; 
v_snd_458_ = lean_ctor_get(v_val_454_, 1);
v_isSharedCheck_521_ = !lean_is_exclusive(v_val_454_);
if (v_isSharedCheck_521_ == 0)
{
lean_object* v_unused_522_; 
v_unused_522_ = lean_ctor_get(v_val_454_, 0);
lean_dec(v_unused_522_);
v___x_460_ = v_val_454_;
v_isShared_461_ = v_isSharedCheck_521_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_snd_458_);
lean_dec(v_val_454_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_521_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v_fst_462_; lean_object* v_snd_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_520_; 
v_fst_462_ = lean_ctor_get(v_snd_458_, 0);
v_snd_463_ = lean_ctor_get(v_snd_458_, 1);
v_isSharedCheck_520_ = !lean_is_exclusive(v_snd_458_);
if (v_isSharedCheck_520_ == 0)
{
v___x_465_ = v_snd_458_;
v_isShared_466_ = v_isSharedCheck_520_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_snd_463_);
lean_inc(v_fst_462_);
lean_dec(v_snd_458_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_520_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
uint8_t v___x_467_; 
v___x_467_ = l_Lean_Expr_isFVar(v_fst_462_);
if (v___x_467_ == 0)
{
lean_del_object(v___x_465_);
lean_dec(v_snd_463_);
lean_dec(v_fst_462_);
lean_del_object(v___x_460_);
lean_del_object(v___x_456_);
lean_del_object(v___x_447_);
lean_dec(v_snd_431_);
v_a_437_ = v___x_453_;
goto v___jp_436_;
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = l_Lean_Expr_fvarId_x21(v_fst_462_);
lean_dec(v_fst_462_);
lean_inc(v___x_468_);
v___x_469_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_463_, v___x_468_, v___y_425_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; uint8_t v___x_471_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref_known(v___x_469_, 1);
v___x_471_ = lean_unbox(v_a_470_);
lean_dec(v_a_470_);
if (v___x_471_ == 0)
{
if (v___x_467_ == 0)
{
lean_dec(v___x_468_);
lean_del_object(v___x_465_);
lean_del_object(v___x_460_);
lean_del_object(v___x_456_);
lean_del_object(v___x_447_);
lean_dec(v_snd_431_);
v_a_437_ = v___x_453_;
goto v___jp_436_;
}
else
{
lean_object* v___x_472_; 
lean_inc(v_mvarId_419_);
v___x_472_ = l_Lean_Meta_subst_x3f(v_mvarId_419_, v___x_468_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_503_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_503_ == 0)
{
v___x_475_ = v___x_472_;
v_isShared_476_ = v_isSharedCheck_503_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_503_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
if (lean_obj_tag(v_a_473_) == 0)
{
lean_del_object(v___x_475_);
lean_del_object(v___x_465_);
lean_del_object(v___x_460_);
lean_del_object(v___x_456_);
lean_del_object(v___x_447_);
lean_dec(v_snd_431_);
v_a_437_ = v___x_453_;
goto v___jp_436_;
}
else
{
lean_object* v_val_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_502_; 
lean_del_object(v___x_433_);
lean_dec(v_mvarId_419_);
v_val_477_ = lean_ctor_get(v_a_473_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v_a_473_);
if (v_isSharedCheck_502_ == 0)
{
v___x_479_ = v_a_473_;
v_isShared_480_ = v_isSharedCheck_502_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_val_477_);
lean_dec(v_a_473_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_502_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_481_ = lean_unsigned_to_nat(1u);
v___x_482_ = lean_mk_empty_array_with_capacity(v___x_481_);
v___x_483_ = lean_array_push(v___x_482_, v_val_477_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_483_);
v___x_485_ = v___x_479_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_501_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_487_; 
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 1, v___x_452_);
lean_ctor_set(v___x_465_, 0, v___x_485_);
v___x_487_ = v___x_465_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v___x_452_);
v___x_487_ = v_reuseFailAlloc_500_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_489_; 
if (v_isShared_448_ == 0)
{
lean_ctor_set_tag(v___x_447_, 0);
lean_ctor_set(v___x_447_, 0, v___x_487_);
v___x_489_ = v___x_447_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_487_);
v___x_489_ = v_reuseFailAlloc_499_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_491_; 
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_489_);
v___x_491_ = v___x_456_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_489_);
v___x_491_ = v_reuseFailAlloc_498_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_493_; 
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 1, v_snd_431_);
lean_ctor_set(v___x_460_, 0, v___x_491_);
v___x_493_ = v___x_460_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v_snd_431_);
v___x_493_ = v_reuseFailAlloc_497_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_495_; 
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_493_);
v___x_495_ = v___x_475_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_493_);
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
}
}
}
}
}
else
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
lean_del_object(v___x_465_);
lean_del_object(v___x_460_);
lean_del_object(v___x_456_);
lean_del_object(v___x_447_);
lean_del_object(v___x_433_);
lean_dec(v_snd_431_);
lean_dec(v_mvarId_419_);
v_a_504_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_472_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_472_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
}
else
{
lean_dec(v___x_468_);
lean_del_object(v___x_465_);
lean_del_object(v___x_460_);
lean_del_object(v___x_456_);
lean_del_object(v___x_447_);
lean_dec(v_snd_431_);
v_a_437_ = v___x_453_;
goto v___jp_436_;
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec(v___x_468_);
lean_del_object(v___x_465_);
lean_del_object(v___x_460_);
lean_del_object(v___x_456_);
lean_del_object(v___x_447_);
lean_del_object(v___x_433_);
lean_dec(v_snd_431_);
lean_dec(v_mvarId_419_);
v_a_512_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_469_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_469_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
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
lean_dec(v_a_451_);
lean_del_object(v___x_447_);
lean_dec(v_snd_431_);
v_a_437_ = v___x_453_;
goto v___jp_436_;
}
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
lean_del_object(v___x_447_);
lean_del_object(v___x_433_);
lean_dec(v_snd_431_);
lean_dec(v_mvarId_419_);
v_a_524_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_450_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_450_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
v___jp_436_:
{
lean_object* v___x_439_; 
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 1, v_a_437_);
lean_ctor_set(v___x_433_, 0, v___x_435_);
v___x_439_ = v___x_433_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_a_437_);
v___x_439_ = v_reuseFailAlloc_443_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
size_t v___x_440_; size_t v___x_441_; 
v___x_440_ = ((size_t)1ULL);
v___x_441_ = lean_usize_add(v_i_422_, v___x_440_);
v_i_422_ = v___x_441_;
v_b_423_ = v___x_439_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5___boxed(lean_object* v_mvarId_535_, lean_object* v_as_536_, lean_object* v_sz_537_, lean_object* v_i_538_, lean_object* v_b_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
size_t v_sz_boxed_545_; size_t v_i_boxed_546_; lean_object* v_res_547_; 
v_sz_boxed_545_ = lean_unbox_usize(v_sz_537_);
lean_dec(v_sz_537_);
v_i_boxed_546_ = lean_unbox_usize(v_i_538_);
lean_dec(v_i_538_);
v_res_547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5(v_mvarId_535_, v_as_536_, v_sz_boxed_545_, v_i_boxed_546_, v_b_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec_ref(v_as_536_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4(lean_object* v_mvarId_548_, lean_object* v_as_549_, size_t v_sz_550_, size_t v_i_551_, lean_object* v_b_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
uint8_t v___x_558_; 
v___x_558_ = lean_usize_dec_lt(v_i_551_, v_sz_550_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; 
lean_dec(v_mvarId_548_);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v_b_552_);
return v___x_559_;
}
else
{
lean_object* v_snd_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_662_; 
v_snd_560_ = lean_ctor_get(v_b_552_, 1);
v_isSharedCheck_662_ = !lean_is_exclusive(v_b_552_);
if (v_isSharedCheck_662_ == 0)
{
lean_object* v_unused_663_; 
v_unused_663_ = lean_ctor_get(v_b_552_, 0);
lean_dec(v_unused_663_);
v___x_562_ = v_b_552_;
v_isShared_563_ = v_isSharedCheck_662_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_snd_560_);
lean_dec(v_b_552_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_662_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v_a_566_; lean_object* v_a_573_; 
v___x_564_ = lean_box(0);
v_a_573_ = lean_array_uget(v_as_549_, v_i_551_);
if (lean_obj_tag(v_a_573_) == 0)
{
v_a_566_ = v_snd_560_;
goto v___jp_565_;
}
else
{
lean_object* v_val_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_661_; 
v_val_574_ = lean_ctor_get(v_a_573_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v_a_573_);
if (v_isSharedCheck_661_ == 0)
{
v___x_576_ = v_a_573_;
v_isShared_577_ = v_isSharedCheck_661_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_val_574_);
lean_dec(v_a_573_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_661_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = l_Lean_LocalDecl_type(v_val_574_);
lean_dec(v_val_574_);
v___x_579_ = l_Lean_Meta_matchEq_x3f(v___x_578_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_a_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_a_580_);
lean_dec_ref_known(v___x_579_, 1);
v___x_581_ = lean_box(0);
v___x_582_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5___closed__0));
if (lean_obj_tag(v_a_580_) == 1)
{
lean_object* v_val_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_652_; 
v_val_583_ = lean_ctor_get(v_a_580_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v_a_580_);
if (v_isSharedCheck_652_ == 0)
{
v___x_585_ = v_a_580_;
v_isShared_586_ = v_isSharedCheck_652_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_val_583_);
lean_dec(v_a_580_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_652_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v_snd_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_650_; 
v_snd_587_ = lean_ctor_get(v_val_583_, 1);
v_isSharedCheck_650_ = !lean_is_exclusive(v_val_583_);
if (v_isSharedCheck_650_ == 0)
{
lean_object* v_unused_651_; 
v_unused_651_ = lean_ctor_get(v_val_583_, 0);
lean_dec(v_unused_651_);
v___x_589_ = v_val_583_;
v_isShared_590_ = v_isSharedCheck_650_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_snd_587_);
lean_dec(v_val_583_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_650_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v_fst_591_; lean_object* v_snd_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_649_; 
v_fst_591_ = lean_ctor_get(v_snd_587_, 0);
v_snd_592_ = lean_ctor_get(v_snd_587_, 1);
v_isSharedCheck_649_ = !lean_is_exclusive(v_snd_587_);
if (v_isSharedCheck_649_ == 0)
{
v___x_594_ = v_snd_587_;
v_isShared_595_ = v_isSharedCheck_649_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_snd_592_);
lean_inc(v_fst_591_);
lean_dec(v_snd_587_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_649_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
uint8_t v___x_596_; 
v___x_596_ = l_Lean_Expr_isFVar(v_fst_591_);
if (v___x_596_ == 0)
{
lean_del_object(v___x_594_);
lean_dec(v_snd_592_);
lean_dec(v_fst_591_);
lean_del_object(v___x_589_);
lean_del_object(v___x_585_);
lean_del_object(v___x_576_);
lean_dec(v_snd_560_);
v_a_566_ = v___x_582_;
goto v___jp_565_;
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = l_Lean_Expr_fvarId_x21(v_fst_591_);
lean_dec(v_fst_591_);
lean_inc(v___x_597_);
v___x_598_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_592_, v___x_597_, v___y_554_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; uint8_t v___x_600_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_a_599_);
lean_dec_ref_known(v___x_598_, 1);
v___x_600_ = lean_unbox(v_a_599_);
lean_dec(v_a_599_);
if (v___x_600_ == 0)
{
if (v___x_596_ == 0)
{
lean_dec(v___x_597_);
lean_del_object(v___x_594_);
lean_del_object(v___x_589_);
lean_del_object(v___x_585_);
lean_del_object(v___x_576_);
lean_dec(v_snd_560_);
v_a_566_ = v___x_582_;
goto v___jp_565_;
}
else
{
lean_object* v___x_601_; 
lean_inc(v_mvarId_548_);
v___x_601_ = l_Lean_Meta_subst_x3f(v_mvarId_548_, v___x_597_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_632_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_632_ == 0)
{
v___x_604_ = v___x_601_;
v_isShared_605_ = v_isSharedCheck_632_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_632_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
if (lean_obj_tag(v_a_602_) == 0)
{
lean_del_object(v___x_604_);
lean_del_object(v___x_594_);
lean_del_object(v___x_589_);
lean_del_object(v___x_585_);
lean_del_object(v___x_576_);
lean_dec(v_snd_560_);
v_a_566_ = v___x_582_;
goto v___jp_565_;
}
else
{
lean_object* v_val_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_631_; 
lean_del_object(v___x_562_);
lean_dec(v_mvarId_548_);
v_val_606_ = lean_ctor_get(v_a_602_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v_a_602_);
if (v_isSharedCheck_631_ == 0)
{
v___x_608_ = v_a_602_;
v_isShared_609_ = v_isSharedCheck_631_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_val_606_);
lean_dec(v_a_602_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_631_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_610_ = lean_unsigned_to_nat(1u);
v___x_611_ = lean_mk_empty_array_with_capacity(v___x_610_);
v___x_612_ = lean_array_push(v___x_611_, v_val_606_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_612_);
v___x_614_ = v___x_608_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_612_);
v___x_614_ = v_reuseFailAlloc_630_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_616_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 1, v___x_581_);
lean_ctor_set(v___x_594_, 0, v___x_614_);
v___x_616_ = v___x_594_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_614_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v___x_581_);
v___x_616_ = v_reuseFailAlloc_629_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_618_; 
if (v_isShared_577_ == 0)
{
lean_ctor_set_tag(v___x_576_, 0);
lean_ctor_set(v___x_576_, 0, v___x_616_);
v___x_618_ = v___x_576_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_616_);
v___x_618_ = v_reuseFailAlloc_628_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
lean_object* v___x_620_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 0, v___x_618_);
v___x_620_ = v___x_585_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_618_);
v___x_620_ = v_reuseFailAlloc_627_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_622_; 
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 1, v_snd_560_);
lean_ctor_set(v___x_589_, 0, v___x_620_);
v___x_622_ = v___x_589_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_snd_560_);
v___x_622_ = v_reuseFailAlloc_626_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_624_; 
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_622_);
v___x_624_ = v___x_604_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_622_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
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
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
lean_del_object(v___x_594_);
lean_del_object(v___x_589_);
lean_del_object(v___x_585_);
lean_del_object(v___x_576_);
lean_del_object(v___x_562_);
lean_dec(v_snd_560_);
lean_dec(v_mvarId_548_);
v_a_633_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_601_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_601_);
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
}
else
{
lean_dec(v___x_597_);
lean_del_object(v___x_594_);
lean_del_object(v___x_589_);
lean_del_object(v___x_585_);
lean_del_object(v___x_576_);
lean_dec(v_snd_560_);
v_a_566_ = v___x_582_;
goto v___jp_565_;
}
}
else
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec(v___x_597_);
lean_del_object(v___x_594_);
lean_del_object(v___x_589_);
lean_del_object(v___x_585_);
lean_del_object(v___x_576_);
lean_del_object(v___x_562_);
lean_dec(v_snd_560_);
lean_dec(v_mvarId_548_);
v_a_641_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_598_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_598_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_a_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
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
lean_dec(v_a_580_);
lean_del_object(v___x_576_);
lean_dec(v_snd_560_);
v_a_566_ = v___x_582_;
goto v___jp_565_;
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_del_object(v___x_576_);
lean_del_object(v___x_562_);
lean_dec(v_snd_560_);
lean_dec(v_mvarId_548_);
v_a_653_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_579_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_579_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
v___jp_565_:
{
lean_object* v___x_568_; 
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 1, v_a_566_);
lean_ctor_set(v___x_562_, 0, v___x_564_);
v___x_568_ = v___x_562_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_a_566_);
v___x_568_ = v_reuseFailAlloc_572_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
size_t v___x_569_; size_t v___x_570_; lean_object* v___x_571_; 
v___x_569_ = ((size_t)1ULL);
v___x_570_ = lean_usize_add(v_i_551_, v___x_569_);
v___x_571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5(v_mvarId_548_, v_as_549_, v_sz_550_, v___x_570_, v___x_568_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
return v___x_571_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4___boxed(lean_object* v_mvarId_664_, lean_object* v_as_665_, lean_object* v_sz_666_, lean_object* v_i_667_, lean_object* v_b_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
size_t v_sz_boxed_674_; size_t v_i_boxed_675_; lean_object* v_res_676_; 
v_sz_boxed_674_ = lean_unbox_usize(v_sz_666_);
lean_dec(v_sz_666_);
v_i_boxed_675_ = lean_unbox_usize(v_i_667_);
lean_dec(v_i_667_);
v_res_676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4(v_mvarId_664_, v_as_665_, v_sz_boxed_674_, v_i_boxed_675_, v_b_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec_ref(v_as_665_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(lean_object* v_init_677_, lean_object* v_mvarId_678_, lean_object* v_n_679_, lean_object* v_b_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
if (lean_obj_tag(v_n_679_) == 0)
{
lean_object* v_cs_686_; lean_object* v___x_687_; lean_object* v___x_688_; size_t v_sz_689_; size_t v___x_690_; lean_object* v___x_691_; 
v_cs_686_ = lean_ctor_get(v_n_679_, 0);
v___x_687_ = lean_box(0);
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
lean_ctor_set(v___x_688_, 1, v_b_680_);
v_sz_689_ = lean_array_size(v_cs_686_);
v___x_690_ = ((size_t)0ULL);
v___x_691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(v_init_677_, v_mvarId_678_, v_cs_686_, v_sz_689_, v___x_690_, v___x_688_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_706_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_706_ == 0)
{
v___x_694_ = v___x_691_;
v_isShared_695_ = v_isSharedCheck_706_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_706_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_fst_696_; 
v_fst_696_ = lean_ctor_get(v_a_692_, 0);
if (lean_obj_tag(v_fst_696_) == 0)
{
lean_object* v_snd_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
v_snd_697_ = lean_ctor_get(v_a_692_, 1);
lean_inc(v_snd_697_);
lean_dec(v_a_692_);
v___x_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_698_, 0, v_snd_697_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_698_);
v___x_700_ = v___x_694_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
else
{
lean_object* v_val_702_; lean_object* v___x_704_; 
lean_inc_ref(v_fst_696_);
lean_dec(v_a_692_);
v_val_702_ = lean_ctor_get(v_fst_696_, 0);
lean_inc(v_val_702_);
lean_dec_ref_known(v_fst_696_, 1);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v_val_702_);
v___x_704_ = v___x_694_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_val_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
v_a_707_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_691_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_691_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
else
{
lean_object* v_vs_715_; lean_object* v___x_716_; lean_object* v___x_717_; size_t v_sz_718_; size_t v___x_719_; lean_object* v___x_720_; 
v_vs_715_ = lean_ctor_get(v_n_679_, 0);
v___x_716_ = lean_box(0);
v___x_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
lean_ctor_set(v___x_717_, 1, v_b_680_);
v_sz_718_ = lean_array_size(v_vs_715_);
v___x_719_ = ((size_t)0ULL);
v___x_720_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4(v_mvarId_678_, v_vs_715_, v_sz_718_, v___x_719_, v___x_717_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_735_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_735_ == 0)
{
v___x_723_ = v___x_720_;
v_isShared_724_ = v_isSharedCheck_735_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_720_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_735_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v_fst_725_; 
v_fst_725_ = lean_ctor_get(v_a_721_, 0);
if (lean_obj_tag(v_fst_725_) == 0)
{
lean_object* v_snd_726_; lean_object* v___x_727_; lean_object* v___x_729_; 
v_snd_726_ = lean_ctor_get(v_a_721_, 1);
lean_inc(v_snd_726_);
lean_dec(v_a_721_);
v___x_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_727_, 0, v_snd_726_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_727_);
v___x_729_ = v___x_723_;
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
else
{
lean_object* v_val_731_; lean_object* v___x_733_; 
lean_inc_ref(v_fst_725_);
lean_dec(v_a_721_);
v_val_731_ = lean_ctor_get(v_fst_725_, 0);
lean_inc(v_val_731_);
lean_dec_ref_known(v_fst_725_, 1);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v_val_731_);
v___x_733_ = v___x_723_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_val_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
v_a_736_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_720_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_720_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(lean_object* v_init_744_, lean_object* v_mvarId_745_, lean_object* v_as_746_, size_t v_sz_747_, size_t v_i_748_, lean_object* v_b_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
uint8_t v___x_755_; 
v___x_755_ = lean_usize_dec_lt(v_i_748_, v_sz_747_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; 
lean_dec(v_mvarId_745_);
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v_b_749_);
return v___x_756_;
}
else
{
lean_object* v_snd_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_791_; 
v_snd_757_ = lean_ctor_get(v_b_749_, 1);
v_isSharedCheck_791_ = !lean_is_exclusive(v_b_749_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; 
v_unused_792_ = lean_ctor_get(v_b_749_, 0);
lean_dec(v_unused_792_);
v___x_759_ = v_b_749_;
v_isShared_760_ = v_isSharedCheck_791_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_snd_757_);
lean_dec(v_b_749_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_791_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v_a_761_; lean_object* v___x_762_; 
v_a_761_ = lean_array_uget_borrowed(v_as_746_, v_i_748_);
lean_inc(v_snd_757_);
lean_inc(v_mvarId_745_);
v___x_762_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_init_744_, v_mvarId_745_, v_a_761_, v_snd_757_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_782_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_782_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_782_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_782_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
if (lean_obj_tag(v_a_763_) == 0)
{
lean_object* v___x_767_; lean_object* v___x_769_; 
lean_dec(v_mvarId_745_);
v___x_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_767_, 0, v_a_763_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v___x_767_);
v___x_769_ = v___x_759_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_snd_757_);
v___x_769_ = v_reuseFailAlloc_773_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_771_; 
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_769_);
v___x_771_ = v___x_765_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
lean_del_object(v___x_765_);
lean_dec(v_snd_757_);
v_a_774_ = lean_ctor_get(v_a_763_, 0);
lean_inc(v_a_774_);
lean_dec_ref_known(v_a_763_, 1);
v___x_775_ = lean_box(0);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 1, v_a_774_);
lean_ctor_set(v___x_759_, 0, v___x_775_);
v___x_777_ = v___x_759_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_a_774_);
v___x_777_ = v_reuseFailAlloc_781_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
size_t v___x_778_; size_t v___x_779_; 
v___x_778_ = ((size_t)1ULL);
v___x_779_ = lean_usize_add(v_i_748_, v___x_778_);
v_i_748_ = v___x_779_;
v_b_749_ = v___x_777_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_del_object(v___x_759_);
lean_dec(v_snd_757_);
lean_dec(v_mvarId_745_);
v_a_783_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_762_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_762_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3___boxed(lean_object* v_init_793_, lean_object* v_mvarId_794_, lean_object* v_as_795_, lean_object* v_sz_796_, lean_object* v_i_797_, lean_object* v_b_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
size_t v_sz_boxed_804_; size_t v_i_boxed_805_; lean_object* v_res_806_; 
v_sz_boxed_804_ = lean_unbox_usize(v_sz_796_);
lean_dec(v_sz_796_);
v_i_boxed_805_ = lean_unbox_usize(v_i_797_);
lean_dec(v_i_797_);
v_res_806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(v_init_793_, v_mvarId_794_, v_as_795_, v_sz_boxed_804_, v_i_boxed_805_, v_b_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec_ref(v_as_795_);
lean_dec_ref(v_init_793_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1___boxed(lean_object* v_init_807_, lean_object* v_mvarId_808_, lean_object* v_n_809_, lean_object* v_b_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_init_807_, v_mvarId_808_, v_n_809_, v_b_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec_ref(v_n_809_);
lean_dec_ref(v_init_807_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(lean_object* v_mvarId_820_, lean_object* v_as_821_, size_t v_sz_822_, size_t v_i_823_, lean_object* v_b_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
uint8_t v___x_830_; 
v___x_830_ = lean_usize_dec_lt(v_i_823_, v_sz_822_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; 
lean_dec(v_mvarId_820_);
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v_b_824_);
return v___x_831_;
}
else
{
lean_object* v_snd_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_927_; 
v_snd_832_ = lean_ctor_get(v_b_824_, 1);
v_isSharedCheck_927_ = !lean_is_exclusive(v_b_824_);
if (v_isSharedCheck_927_ == 0)
{
lean_object* v_unused_928_; 
v_unused_928_ = lean_ctor_get(v_b_824_, 0);
lean_dec(v_unused_928_);
v___x_834_ = v_b_824_;
v_isShared_835_ = v_isSharedCheck_927_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_snd_832_);
lean_dec(v_b_824_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_927_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v_a_838_; lean_object* v_a_845_; 
v___x_836_ = lean_box(0);
v_a_845_ = lean_array_uget_borrowed(v_as_821_, v_i_823_);
if (lean_obj_tag(v_a_845_) == 0)
{
v_a_838_ = v_snd_832_;
goto v___jp_837_;
}
else
{
lean_object* v_val_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v_val_846_ = lean_ctor_get(v_a_845_, 0);
v___x_847_ = l_Lean_LocalDecl_type(v_val_846_);
v___x_848_ = l_Lean_Meta_matchEq_x3f(v___x_847_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
v___x_850_ = lean_box(0);
v___x_851_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___closed__0));
if (lean_obj_tag(v_a_849_) == 1)
{
lean_object* v_val_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_918_; 
v_val_852_ = lean_ctor_get(v_a_849_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v_a_849_);
if (v_isSharedCheck_918_ == 0)
{
v___x_854_ = v_a_849_;
v_isShared_855_ = v_isSharedCheck_918_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_val_852_);
lean_dec(v_a_849_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_918_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v_snd_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_916_; 
v_snd_856_ = lean_ctor_get(v_val_852_, 1);
v_isSharedCheck_916_ = !lean_is_exclusive(v_val_852_);
if (v_isSharedCheck_916_ == 0)
{
lean_object* v_unused_917_; 
v_unused_917_ = lean_ctor_get(v_val_852_, 0);
lean_dec(v_unused_917_);
v___x_858_ = v_val_852_;
v_isShared_859_ = v_isSharedCheck_916_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_snd_856_);
lean_dec(v_val_852_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_916_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v_fst_860_; lean_object* v_snd_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_915_; 
v_fst_860_ = lean_ctor_get(v_snd_856_, 0);
v_snd_861_ = lean_ctor_get(v_snd_856_, 1);
v_isSharedCheck_915_ = !lean_is_exclusive(v_snd_856_);
if (v_isSharedCheck_915_ == 0)
{
v___x_863_ = v_snd_856_;
v_isShared_864_ = v_isSharedCheck_915_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_snd_861_);
lean_inc(v_fst_860_);
lean_dec(v_snd_856_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_915_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
uint8_t v___x_865_; 
v___x_865_ = l_Lean_Expr_isFVar(v_fst_860_);
if (v___x_865_ == 0)
{
lean_del_object(v___x_863_);
lean_dec(v_snd_861_);
lean_dec(v_fst_860_);
lean_del_object(v___x_858_);
lean_del_object(v___x_854_);
lean_dec(v_snd_832_);
v_a_838_ = v___x_851_;
goto v___jp_837_;
}
else
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = l_Lean_Expr_fvarId_x21(v_fst_860_);
lean_dec(v_fst_860_);
lean_inc(v___x_866_);
v___x_867_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_861_, v___x_866_, v___y_826_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; uint8_t v___x_869_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_867_, 1);
v___x_869_ = lean_unbox(v_a_868_);
lean_dec(v_a_868_);
if (v___x_869_ == 0)
{
if (v___x_865_ == 0)
{
lean_dec(v___x_866_);
lean_del_object(v___x_863_);
lean_del_object(v___x_858_);
lean_del_object(v___x_854_);
lean_dec(v_snd_832_);
v_a_838_ = v___x_851_;
goto v___jp_837_;
}
else
{
lean_object* v___x_870_; 
lean_inc(v_mvarId_820_);
v___x_870_ = l_Lean_Meta_subst_x3f(v_mvarId_820_, v___x_866_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_898_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_898_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_898_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_898_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
if (lean_obj_tag(v_a_871_) == 0)
{
lean_del_object(v___x_873_);
lean_del_object(v___x_863_);
lean_del_object(v___x_858_);
lean_del_object(v___x_854_);
lean_dec(v_snd_832_);
v_a_838_ = v___x_851_;
goto v___jp_837_;
}
else
{
lean_object* v_val_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_897_; 
lean_del_object(v___x_834_);
lean_dec(v_mvarId_820_);
v_val_875_ = lean_ctor_get(v_a_871_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v_a_871_);
if (v_isSharedCheck_897_ == 0)
{
v___x_877_ = v_a_871_;
v_isShared_878_ = v_isSharedCheck_897_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_val_875_);
lean_dec(v_a_871_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_897_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_879_ = lean_unsigned_to_nat(1u);
v___x_880_ = lean_mk_empty_array_with_capacity(v___x_879_);
v___x_881_ = lean_array_push(v___x_880_, v_val_875_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_881_);
v___x_883_ = v___x_877_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_881_);
v___x_883_ = v_reuseFailAlloc_896_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_885_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 1, v___x_850_);
lean_ctor_set(v___x_863_, 0, v___x_883_);
v___x_885_ = v___x_863_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v___x_850_);
v___x_885_ = v_reuseFailAlloc_895_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_887_; 
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_885_);
v___x_887_ = v___x_854_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_885_);
v___x_887_ = v_reuseFailAlloc_894_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_889_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 1, v_snd_832_);
lean_ctor_set(v___x_858_, 0, v___x_887_);
v___x_889_ = v___x_858_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_snd_832_);
v___x_889_ = v_reuseFailAlloc_893_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_891_; 
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_889_);
v___x_891_ = v___x_873_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
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
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_del_object(v___x_863_);
lean_del_object(v___x_858_);
lean_del_object(v___x_854_);
lean_del_object(v___x_834_);
lean_dec(v_snd_832_);
lean_dec(v_mvarId_820_);
v_a_899_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_870_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_870_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
else
{
lean_dec(v___x_866_);
lean_del_object(v___x_863_);
lean_del_object(v___x_858_);
lean_del_object(v___x_854_);
lean_dec(v_snd_832_);
v_a_838_ = v___x_851_;
goto v___jp_837_;
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_dec(v___x_866_);
lean_del_object(v___x_863_);
lean_del_object(v___x_858_);
lean_del_object(v___x_854_);
lean_del_object(v___x_834_);
lean_dec(v_snd_832_);
lean_dec(v_mvarId_820_);
v_a_907_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_867_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_867_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
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
lean_dec(v_a_849_);
lean_dec(v_snd_832_);
v_a_838_ = v___x_851_;
goto v___jp_837_;
}
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
lean_del_object(v___x_834_);
lean_dec(v_snd_832_);
lean_dec(v_mvarId_820_);
v_a_919_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_848_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_848_);
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
v___jp_837_:
{
lean_object* v___x_840_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 1, v_a_838_);
lean_ctor_set(v___x_834_, 0, v___x_836_);
v___x_840_ = v___x_834_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_836_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v_a_838_);
v___x_840_ = v_reuseFailAlloc_844_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
size_t v___x_841_; size_t v___x_842_; 
v___x_841_ = ((size_t)1ULL);
v___x_842_ = lean_usize_add(v_i_823_, v___x_841_);
v_i_823_ = v___x_842_;
v_b_824_ = v___x_840_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___boxed(lean_object* v_mvarId_929_, lean_object* v_as_930_, lean_object* v_sz_931_, lean_object* v_i_932_, lean_object* v_b_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
size_t v_sz_boxed_939_; size_t v_i_boxed_940_; lean_object* v_res_941_; 
v_sz_boxed_939_ = lean_unbox_usize(v_sz_931_);
lean_dec(v_sz_931_);
v_i_boxed_940_ = lean_unbox_usize(v_i_932_);
lean_dec(v_i_932_);
v_res_941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(v_mvarId_929_, v_as_930_, v_sz_boxed_939_, v_i_boxed_940_, v_b_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec_ref(v_as_930_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(lean_object* v_mvarId_942_, lean_object* v_as_943_, size_t v_sz_944_, size_t v_i_945_, lean_object* v_b_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
uint8_t v___x_952_; 
v___x_952_ = lean_usize_dec_lt(v_i_945_, v_sz_944_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; 
lean_dec(v_mvarId_942_);
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v_b_946_);
return v___x_953_;
}
else
{
lean_object* v_snd_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_1049_; 
v_snd_954_ = lean_ctor_get(v_b_946_, 1);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_b_946_);
if (v_isSharedCheck_1049_ == 0)
{
lean_object* v_unused_1050_; 
v_unused_1050_ = lean_ctor_get(v_b_946_, 0);
lean_dec(v_unused_1050_);
v___x_956_ = v_b_946_;
v_isShared_957_ = v_isSharedCheck_1049_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_snd_954_);
lean_dec(v_b_946_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_1049_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; lean_object* v_a_960_; lean_object* v_a_967_; 
v___x_958_ = lean_box(0);
v_a_967_ = lean_array_uget_borrowed(v_as_943_, v_i_945_);
if (lean_obj_tag(v_a_967_) == 0)
{
v_a_960_ = v_snd_954_;
goto v___jp_959_;
}
else
{
lean_object* v_val_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v_val_968_ = lean_ctor_get(v_a_967_, 0);
v___x_969_ = l_Lean_LocalDecl_type(v_val_968_);
v___x_970_ = l_Lean_Meta_matchEq_x3f(v___x_969_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_a_971_);
lean_dec_ref_known(v___x_970_, 1);
v___x_972_ = lean_box(0);
v___x_973_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___closed__0));
if (lean_obj_tag(v_a_971_) == 1)
{
lean_object* v_val_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_1040_; 
v_val_974_ = lean_ctor_get(v_a_971_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_a_971_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_976_ = v_a_971_;
v_isShared_977_ = v_isSharedCheck_1040_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_val_974_);
lean_dec(v_a_971_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_1040_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v_snd_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_1038_; 
v_snd_978_ = lean_ctor_get(v_val_974_, 1);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_val_974_);
if (v_isSharedCheck_1038_ == 0)
{
lean_object* v_unused_1039_; 
v_unused_1039_ = lean_ctor_get(v_val_974_, 0);
lean_dec(v_unused_1039_);
v___x_980_ = v_val_974_;
v_isShared_981_ = v_isSharedCheck_1038_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_snd_978_);
lean_dec(v_val_974_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_1038_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v_fst_982_; lean_object* v_snd_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1037_; 
v_fst_982_ = lean_ctor_get(v_snd_978_, 0);
v_snd_983_ = lean_ctor_get(v_snd_978_, 1);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_snd_978_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_985_ = v_snd_978_;
v_isShared_986_ = v_isSharedCheck_1037_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_snd_983_);
lean_inc(v_fst_982_);
lean_dec(v_snd_978_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1037_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
uint8_t v___x_987_; 
v___x_987_ = l_Lean_Expr_isFVar(v_fst_982_);
if (v___x_987_ == 0)
{
lean_del_object(v___x_985_);
lean_dec(v_snd_983_);
lean_dec(v_fst_982_);
lean_del_object(v___x_980_);
lean_del_object(v___x_976_);
lean_dec(v_snd_954_);
v_a_960_ = v___x_973_;
goto v___jp_959_;
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = l_Lean_Expr_fvarId_x21(v_fst_982_);
lean_dec(v_fst_982_);
lean_inc(v___x_988_);
v___x_989_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_983_, v___x_988_, v___y_948_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; uint8_t v___x_991_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_a_990_);
lean_dec_ref_known(v___x_989_, 1);
v___x_991_ = lean_unbox(v_a_990_);
lean_dec(v_a_990_);
if (v___x_991_ == 0)
{
if (v___x_987_ == 0)
{
lean_dec(v___x_988_);
lean_del_object(v___x_985_);
lean_del_object(v___x_980_);
lean_del_object(v___x_976_);
lean_dec(v_snd_954_);
v_a_960_ = v___x_973_;
goto v___jp_959_;
}
else
{
lean_object* v___x_992_; 
lean_inc(v_mvarId_942_);
v___x_992_ = l_Lean_Meta_subst_x3f(v_mvarId_942_, v___x_988_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1020_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1020_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1020_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
if (lean_obj_tag(v_a_993_) == 0)
{
lean_del_object(v___x_995_);
lean_del_object(v___x_985_);
lean_del_object(v___x_980_);
lean_del_object(v___x_976_);
lean_dec(v_snd_954_);
v_a_960_ = v___x_973_;
goto v___jp_959_;
}
else
{
lean_object* v_val_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1019_; 
lean_del_object(v___x_956_);
lean_dec(v_mvarId_942_);
v_val_997_ = lean_ctor_get(v_a_993_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_a_993_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_999_ = v_a_993_;
v_isShared_1000_ = v_isSharedCheck_1019_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_val_997_);
lean_dec(v_a_993_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1019_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1001_ = lean_unsigned_to_nat(1u);
v___x_1002_ = lean_mk_empty_array_with_capacity(v___x_1001_);
v___x_1003_ = lean_array_push(v___x_1002_, v_val_997_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_1003_);
v___x_1005_ = v___x_999_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
lean_object* v___x_1007_; 
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 1, v___x_972_);
lean_ctor_set(v___x_985_, 0, v___x_1005_);
v___x_1007_ = v___x_985_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v___x_972_);
v___x_1007_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1009_; 
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_1007_);
v___x_1009_ = v___x_976_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
lean_object* v___x_1011_; 
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 1, v_snd_954_);
lean_ctor_set(v___x_980_, 0, v___x_1009_);
v___x_1011_ = v___x_980_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1009_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_snd_954_);
v___x_1011_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
lean_object* v___x_1013_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_1011_);
v___x_1013_ = v___x_995_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
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
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_del_object(v___x_985_);
lean_del_object(v___x_980_);
lean_del_object(v___x_976_);
lean_del_object(v___x_956_);
lean_dec(v_snd_954_);
lean_dec(v_mvarId_942_);
v_a_1021_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_992_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_992_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
else
{
lean_dec(v___x_988_);
lean_del_object(v___x_985_);
lean_del_object(v___x_980_);
lean_del_object(v___x_976_);
lean_dec(v_snd_954_);
v_a_960_ = v___x_973_;
goto v___jp_959_;
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
lean_dec(v___x_988_);
lean_del_object(v___x_985_);
lean_del_object(v___x_980_);
lean_del_object(v___x_976_);
lean_del_object(v___x_956_);
lean_dec(v_snd_954_);
lean_dec(v_mvarId_942_);
v_a_1029_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_989_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_989_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
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
lean_dec(v_a_971_);
lean_dec(v_snd_954_);
v_a_960_ = v___x_973_;
goto v___jp_959_;
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
lean_del_object(v___x_956_);
lean_dec(v_snd_954_);
lean_dec(v_mvarId_942_);
v_a_1041_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_970_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_970_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
v___jp_959_:
{
lean_object* v___x_962_; 
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 1, v_a_960_);
lean_ctor_set(v___x_956_, 0, v___x_958_);
v___x_962_ = v___x_956_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_a_960_);
v___x_962_ = v_reuseFailAlloc_966_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
size_t v___x_963_; size_t v___x_964_; lean_object* v___x_965_; 
v___x_963_ = ((size_t)1ULL);
v___x_964_ = lean_usize_add(v_i_945_, v___x_963_);
v___x_965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(v_mvarId_942_, v_as_943_, v_sz_944_, v___x_964_, v___x_962_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
return v___x_965_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2___boxed(lean_object* v_mvarId_1051_, lean_object* v_as_1052_, lean_object* v_sz_1053_, lean_object* v_i_1054_, lean_object* v_b_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
size_t v_sz_boxed_1061_; size_t v_i_boxed_1062_; lean_object* v_res_1063_; 
v_sz_boxed_1061_ = lean_unbox_usize(v_sz_1053_);
lean_dec(v_sz_1053_);
v_i_boxed_1062_ = lean_unbox_usize(v_i_1054_);
lean_dec(v_i_1054_);
v_res_1063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(v_mvarId_1051_, v_as_1052_, v_sz_boxed_1061_, v_i_boxed_1062_, v_b_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec_ref(v_as_1052_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(lean_object* v_mvarId_1064_, lean_object* v_t_1065_, lean_object* v_init_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v_root_1072_; lean_object* v_tail_1073_; lean_object* v___x_1074_; 
v_root_1072_ = lean_ctor_get(v_t_1065_, 0);
v_tail_1073_ = lean_ctor_get(v_t_1065_, 1);
lean_inc(v_mvarId_1064_);
lean_inc_ref(v_init_1066_);
v___x_1074_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_init_1066_, v_mvarId_1064_, v_root_1072_, v_init_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
lean_dec_ref(v_init_1066_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1111_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1077_ = v___x_1074_;
v_isShared_1078_ = v_isSharedCheck_1111_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1074_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1111_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
if (lean_obj_tag(v_a_1075_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1081_; 
lean_dec(v_mvarId_1064_);
v_a_1079_ = lean_ctor_get(v_a_1075_, 0);
lean_inc(v_a_1079_);
lean_dec_ref_known(v_a_1075_, 1);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v_a_1079_);
v___x_1081_ = v___x_1077_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; size_t v_sz_1086_; size_t v___x_1087_; lean_object* v___x_1088_; 
lean_del_object(v___x_1077_);
v_a_1083_ = lean_ctor_get(v_a_1075_, 0);
lean_inc(v_a_1083_);
lean_dec_ref_known(v_a_1075_, 1);
v___x_1084_ = lean_box(0);
v___x_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
lean_ctor_set(v___x_1085_, 1, v_a_1083_);
v_sz_1086_ = lean_array_size(v_tail_1073_);
v___x_1087_ = ((size_t)0ULL);
v___x_1088_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(v_mvarId_1064_, v_tail_1073_, v_sz_1086_, v___x_1087_, v___x_1085_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1102_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1091_ = v___x_1088_;
v_isShared_1092_ = v_isSharedCheck_1102_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1088_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1102_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v_fst_1093_; 
v_fst_1093_ = lean_ctor_get(v_a_1089_, 0);
if (lean_obj_tag(v_fst_1093_) == 0)
{
lean_object* v_snd_1094_; lean_object* v___x_1096_; 
v_snd_1094_ = lean_ctor_get(v_a_1089_, 1);
lean_inc(v_snd_1094_);
lean_dec(v_a_1089_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v_snd_1094_);
v___x_1096_ = v___x_1091_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_snd_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
else
{
lean_object* v_val_1098_; lean_object* v___x_1100_; 
lean_inc_ref(v_fst_1093_);
lean_dec(v_a_1089_);
v_val_1098_ = lean_ctor_get(v_fst_1093_, 0);
lean_inc(v_val_1098_);
lean_dec_ref_known(v_fst_1093_, 1);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v_val_1098_);
v___x_1100_ = v___x_1091_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_val_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
v_a_1103_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1088_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1088_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_dec(v_mvarId_1064_);
v_a_1112_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1074_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1074_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1___boxed(lean_object* v_mvarId_1120_, lean_object* v_t_1121_, lean_object* v_init_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(v_mvarId_1120_, v_t_1121_, v_init_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec_ref(v_t_1121_);
return v_res_1128_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__1));
v___x_1134_ = l_Lean_stringToMessageData(v___x_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0(lean_object* v_mvarId_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v_lctx_1141_; lean_object* v_decls_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v_lctx_1141_ = lean_ctor_get(v___y_1136_, 2);
v_decls_1142_ = lean_ctor_get(v_lctx_1141_, 1);
v___x_1143_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__0));
v___x_1144_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(v_mvarId_1135_, v_decls_1142_, v___x_1143_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1156_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1147_ = v___x_1144_;
v_isShared_1148_ = v_isSharedCheck_1156_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1144_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1156_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v_fst_1149_; 
v_fst_1149_ = lean_ctor_get(v_a_1145_, 0);
lean_inc(v_fst_1149_);
lean_dec(v_a_1145_);
if (lean_obj_tag(v_fst_1149_) == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
lean_del_object(v___x_1147_);
v___x_1150_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2);
v___x_1151_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1150_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
return v___x_1151_;
}
else
{
lean_object* v_val_1152_; lean_object* v___x_1154_; 
v_val_1152_ = lean_ctor_get(v_fst_1149_, 0);
lean_inc(v_val_1152_);
lean_dec_ref_known(v_fst_1149_, 1);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v_val_1152_);
v___x_1154_ = v___x_1147_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_val_1152_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
v_a_1157_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1144_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1144_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___boxed(lean_object* v_mvarId_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0(v_mvarId_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(lean_object* v_mvarId_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v___f_1178_; lean_object* v___x_1179_; 
lean_inc(v_mvarId_1172_);
v___f_1178_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1178_, 0, v_mvarId_1172_);
v___x_1179_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg(v_mvarId_1172_, v___f_1178_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___boxed(lean_object* v_mvarId_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(v_mvarId_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
return v_res_1186_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0(lean_object* v_x_1194_){
_start:
{
lean_object* v___x_1195_; uint8_t v___x_1196_; 
v___x_1195_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__3));
v___x_1196_ = lean_name_eq(v_x_1194_, v___x_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___boxed(lean_object* v_x_1197_){
_start:
{
uint8_t v_res_1198_; lean_object* v_r_1199_; 
v_res_1198_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0(v_x_1197_);
lean_dec(v_x_1197_);
v_r_1199_ = lean_box(v_res_1198_);
return v_r_1199_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1(lean_object* v_e_1200_){
_start:
{
lean_object* v___x_1201_; uint8_t v___x_1202_; 
v___x_1201_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__3));
v___x_1202_ = l_Lean_Expr_isConstOf(v_e_1200_, v___x_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1___boxed(lean_object* v_e_1203_){
_start:
{
uint8_t v_res_1204_; lean_object* v_r_1205_; 
v_res_1204_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1(v_e_1203_);
lean_dec_ref(v_e_1203_);
v_r_1205_ = lean_box(v_res_1204_);
return v_r_1205_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__2));
v___x_1210_ = l_Lean_stringToMessageData(v___x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(lean_object* v_mvarId_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v___x_1217_; 
lean_inc(v_mvarId_1211_);
v___x_1217_ = l_Lean_MVarId_getType(v_mvarId_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v___f_1219_; lean_object* v___f_1220_; lean_object* v___x_1221_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
lean_dec_ref_known(v___x_1217_, 1);
v___f_1219_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__0));
v___f_1220_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__1));
v___x_1221_ = lean_find_expr(v___f_1220_, v_a_1218_);
lean_dec(v_a_1218_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_dec(v_mvarId_1211_);
v___x_1222_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3);
v___x_1223_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1222_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_);
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1223_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1223_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
else
{
lean_object* v___x_1232_; 
lean_dec_ref_known(v___x_1221_, 1);
v___x_1232_ = l_Lean_MVarId_deltaTarget(v_mvarId_1211_, v___f_1219_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_);
return v___x_1232_;
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec(v_mvarId_1211_);
v_a_1233_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1217_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1217_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___boxed(lean_object* v_mvarId_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(v_mvarId_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
lean_dec(v_a_1245_);
lean_dec_ref(v_a_1244_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
return v_res_1247_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = l_Lean_maxRecDepthErrorMessage;
v___x_1254_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
return v___x_1254_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3);
v___x_1256_ = l_Lean_MessageData_ofFormat(v___x_1255_);
return v___x_1256_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1257_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4);
v___x_1258_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__2));
v___x_1259_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
lean_ctor_set(v___x_1259_, 1, v___x_1257_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(lean_object* v_ref_1260_){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5);
v___x_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1263_, 0, v_ref_1260_);
lean_ctor_set(v___x_1263_, 1, v___x_1262_);
v___x_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___boxed(lean_object* v_ref_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1265_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(lean_object* v_00_u03b1_1268_, lean_object* v_ref_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1269_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___boxed(lean_object* v_00_u03b1_1276_, lean_object* v_ref_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(v_00_u03b1_1276_, v_ref_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(lean_object* v_a_1284_, lean_object* v_____r_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1291_ = lean_unsigned_to_nat(1u);
v___x_1292_ = lean_mk_empty_array_with_capacity(v___x_1291_);
v___x_1293_ = lean_array_push(v___x_1292_, v_a_1284_);
v___x_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0___boxed(lean_object* v_a_1295_, lean_object* v_____r_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1295_, v_____r_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
return v_res_1302_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1303_; double v___x_1304_; 
v___x_1303_ = lean_unsigned_to_nat(0u);
v___x_1304_ = lean_float_of_nat(v___x_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(lean_object* v_cls_1308_, lean_object* v_msg_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v_ref_1315_; lean_object* v___x_1316_; lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1361_; 
v_ref_1315_ = lean_ctor_get(v___y_1312_, 5);
v___x_1316_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2(v_msg_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1319_ = v___x_1316_;
v_isShared_1320_ = v_isSharedCheck_1361_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1316_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1361_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; lean_object* v_traceState_1322_; lean_object* v_env_1323_; lean_object* v_nextMacroScope_1324_; lean_object* v_ngen_1325_; lean_object* v_auxDeclNGen_1326_; lean_object* v_cache_1327_; lean_object* v_messages_1328_; lean_object* v_infoState_1329_; lean_object* v_snapshotTasks_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1360_; 
v___x_1321_ = lean_st_ref_take(v___y_1313_);
v_traceState_1322_ = lean_ctor_get(v___x_1321_, 4);
v_env_1323_ = lean_ctor_get(v___x_1321_, 0);
v_nextMacroScope_1324_ = lean_ctor_get(v___x_1321_, 1);
v_ngen_1325_ = lean_ctor_get(v___x_1321_, 2);
v_auxDeclNGen_1326_ = lean_ctor_get(v___x_1321_, 3);
v_cache_1327_ = lean_ctor_get(v___x_1321_, 5);
v_messages_1328_ = lean_ctor_get(v___x_1321_, 6);
v_infoState_1329_ = lean_ctor_get(v___x_1321_, 7);
v_snapshotTasks_1330_ = lean_ctor_get(v___x_1321_, 8);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1332_ = v___x_1321_;
v_isShared_1333_ = v_isSharedCheck_1360_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_snapshotTasks_1330_);
lean_inc(v_infoState_1329_);
lean_inc(v_messages_1328_);
lean_inc(v_cache_1327_);
lean_inc(v_traceState_1322_);
lean_inc(v_auxDeclNGen_1326_);
lean_inc(v_ngen_1325_);
lean_inc(v_nextMacroScope_1324_);
lean_inc(v_env_1323_);
lean_dec(v___x_1321_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1360_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
uint64_t v_tid_1334_; lean_object* v_traces_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1359_; 
v_tid_1334_ = lean_ctor_get_uint64(v_traceState_1322_, sizeof(void*)*1);
v_traces_1335_ = lean_ctor_get(v_traceState_1322_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v_traceState_1322_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1337_ = v_traceState_1322_;
v_isShared_1338_ = v_isSharedCheck_1359_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_traces_1335_);
lean_dec(v_traceState_1322_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1359_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1339_; double v___x_1340_; uint8_t v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1339_ = lean_box(0);
v___x_1340_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0);
v___x_1341_ = 0;
v___x_1342_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__1));
v___x_1343_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1343_, 0, v_cls_1308_);
lean_ctor_set(v___x_1343_, 1, v___x_1339_);
lean_ctor_set(v___x_1343_, 2, v___x_1342_);
lean_ctor_set_float(v___x_1343_, sizeof(void*)*3, v___x_1340_);
lean_ctor_set_float(v___x_1343_, sizeof(void*)*3 + 8, v___x_1340_);
lean_ctor_set_uint8(v___x_1343_, sizeof(void*)*3 + 16, v___x_1341_);
v___x_1344_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__2));
v___x_1345_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1343_);
lean_ctor_set(v___x_1345_, 1, v_a_1317_);
lean_ctor_set(v___x_1345_, 2, v___x_1344_);
lean_inc(v_ref_1315_);
v___x_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1346_, 0, v_ref_1315_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
v___x_1347_ = l_Lean_PersistentArray_push___redArg(v_traces_1335_, v___x_1346_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v___x_1347_);
v___x_1349_ = v___x_1337_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1347_);
lean_ctor_set_uint64(v_reuseFailAlloc_1358_, sizeof(void*)*1, v_tid_1334_);
v___x_1349_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_object* v___x_1351_; 
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 4, v___x_1349_);
v___x_1351_ = v___x_1332_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_env_1323_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_nextMacroScope_1324_);
lean_ctor_set(v_reuseFailAlloc_1357_, 2, v_ngen_1325_);
lean_ctor_set(v_reuseFailAlloc_1357_, 3, v_auxDeclNGen_1326_);
lean_ctor_set(v_reuseFailAlloc_1357_, 4, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1357_, 5, v_cache_1327_);
lean_ctor_set(v_reuseFailAlloc_1357_, 6, v_messages_1328_);
lean_ctor_set(v_reuseFailAlloc_1357_, 7, v_infoState_1329_);
lean_ctor_set(v_reuseFailAlloc_1357_, 8, v_snapshotTasks_1330_);
v___x_1351_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1355_; 
v___x_1352_ = lean_st_ref_put(v___y_1313_, v___x_1351_);
v___x_1353_ = lean_box(0);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v___x_1353_);
v___x_1355_ = v___x_1319_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___boxed(lean_object* v_cls_1362_, lean_object* v_msg_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v_cls_1362_, v_msg_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
return v_res_1369_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1(void){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__0));
v___x_1372_ = l_Lean_stringToMessageData(v___x_1371_);
return v___x_1372_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3(void){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__2));
v___x_1375_ = l_Lean_stringToMessageData(v___x_1374_);
return v___x_1375_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5(void){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__4));
v___x_1378_ = l_Lean_stringToMessageData(v___x_1377_);
return v___x_1378_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7(void){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__6));
v___x_1381_ = l_Lean_stringToMessageData(v___x_1380_);
return v___x_1381_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16(void){
_start:
{
lean_object* v_cls_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v_cls_1395_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_1396_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__15));
v___x_1397_ = l_Lean_Name_append(v___x_1396_, v_cls_1395_);
return v___x_1397_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18(void){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__17));
v___x_1400_ = l_Lean_stringToMessageData(v___x_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(lean_object* v_matchDeclName_1401_, lean_object* v_mvarId_1402_, lean_object* v_depth_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v_a_1414_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; uint8_t v___y_1451_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; uint8_t v___y_1476_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v_a_1500_; lean_object* v___y_1504_; uint8_t v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; uint8_t v___y_1512_; lean_object* v___y_1547_; uint8_t v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v_a_1554_; lean_object* v___y_1558_; uint8_t v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; uint8_t v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; uint8_t v___y_1577_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; uint8_t v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; uint8_t v___y_1609_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; uint8_t v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; uint8_t v___y_1634_; lean_object* v___y_1651_; lean_object* v___y_1652_; uint8_t v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; uint8_t v___y_1659_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; uint8_t v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; uint8_t v___y_1685_; lean_object* v___y_1706_; lean_object* v___y_1707_; uint8_t v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; uint8_t v___y_1714_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v_fileName_1765_; lean_object* v_fileMap_1766_; lean_object* v_options_1767_; lean_object* v_currRecDepth_1768_; lean_object* v_maxRecDepth_1769_; lean_object* v_ref_1770_; lean_object* v_currNamespace_1771_; lean_object* v_openDecls_1772_; lean_object* v_initHeartbeats_1773_; lean_object* v_maxHeartbeats_1774_; lean_object* v_quotContext_1775_; lean_object* v_currMacroScope_1776_; uint8_t v_diag_1777_; lean_object* v_cancelTk_x3f_1778_; uint8_t v_suppressElabErrors_1779_; lean_object* v_inheritedTraceOptions_1780_; lean_object* v_cls_1781_; lean_object* v___x_1793_; uint8_t v___x_1794_; 
v_fileName_1765_ = lean_ctor_get(v_a_1406_, 0);
v_fileMap_1766_ = lean_ctor_get(v_a_1406_, 1);
v_options_1767_ = lean_ctor_get(v_a_1406_, 2);
v_currRecDepth_1768_ = lean_ctor_get(v_a_1406_, 3);
v_maxRecDepth_1769_ = lean_ctor_get(v_a_1406_, 4);
v_ref_1770_ = lean_ctor_get(v_a_1406_, 5);
v_currNamespace_1771_ = lean_ctor_get(v_a_1406_, 6);
v_openDecls_1772_ = lean_ctor_get(v_a_1406_, 7);
v_initHeartbeats_1773_ = lean_ctor_get(v_a_1406_, 8);
v_maxHeartbeats_1774_ = lean_ctor_get(v_a_1406_, 9);
v_quotContext_1775_ = lean_ctor_get(v_a_1406_, 10);
v_currMacroScope_1776_ = lean_ctor_get(v_a_1406_, 11);
v_diag_1777_ = lean_ctor_get_uint8(v_a_1406_, sizeof(void*)*14);
v_cancelTk_x3f_1778_ = lean_ctor_get(v_a_1406_, 12);
v_suppressElabErrors_1779_ = lean_ctor_get_uint8(v_a_1406_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1780_ = lean_ctor_get(v_a_1406_, 13);
v_cls_1781_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_1793_ = lean_unsigned_to_nat(0u);
v___x_1794_ = lean_nat_dec_eq(v_maxRecDepth_1769_, v___x_1793_);
if (v___x_1794_ == 0)
{
uint8_t v___x_1795_; 
v___x_1795_ = lean_nat_dec_eq(v_currRecDepth_1768_, v_maxRecDepth_1769_);
if (v___x_1795_ == 0)
{
goto v___jp_1782_;
}
else
{
lean_object* v___x_1796_; 
lean_dec(v_mvarId_1402_);
lean_dec(v_matchDeclName_1401_);
lean_inc(v_ref_1770_);
v___x_1796_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1770_);
return v___x_1796_;
}
}
else
{
goto v___jp_1782_;
}
v___jp_1409_:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v___x_1415_ = lean_unsigned_to_nat(0u);
v___x_1416_ = lean_array_get_size(v_a_1414_);
v___x_1417_ = lean_box(0);
v___x_1418_ = lean_nat_dec_lt(v___x_1415_, v___x_1416_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; 
lean_dec_ref(v_a_1414_);
lean_dec_ref(v___y_1411_);
lean_dec(v_matchDeclName_1401_);
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1417_);
return v___x_1419_;
}
else
{
uint8_t v___x_1420_; 
v___x_1420_ = lean_nat_dec_le(v___x_1416_, v___x_1416_);
if (v___x_1420_ == 0)
{
if (v___x_1418_ == 0)
{
lean_object* v___x_1421_; 
lean_dec_ref(v_a_1414_);
lean_dec_ref(v___y_1411_);
lean_dec(v_matchDeclName_1401_);
v___x_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1421_, 0, v___x_1417_);
return v___x_1421_;
}
else
{
size_t v___x_1422_; size_t v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = ((size_t)0ULL);
v___x_1423_ = lean_usize_of_nat(v___x_1416_);
v___x_1424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1403_, v_matchDeclName_1401_, v_a_1414_, v___x_1422_, v___x_1423_, v___x_1417_, v___y_1412_, v___y_1413_, v___y_1411_, v___y_1410_);
lean_dec_ref(v___y_1411_);
lean_dec_ref(v_a_1414_);
return v___x_1424_;
}
}
else
{
size_t v___x_1425_; size_t v___x_1426_; lean_object* v___x_1427_; 
v___x_1425_ = ((size_t)0ULL);
v___x_1426_ = lean_usize_of_nat(v___x_1416_);
v___x_1427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1403_, v_matchDeclName_1401_, v_a_1414_, v___x_1425_, v___x_1426_, v___x_1417_, v___y_1412_, v___y_1413_, v___y_1411_, v___y_1410_);
lean_dec_ref(v___y_1411_);
lean_dec_ref(v_a_1414_);
return v___x_1427_;
}
}
}
v___jp_1428_:
{
if (lean_obj_tag(v___y_1433_) == 0)
{
lean_object* v_a_1434_; 
v_a_1434_ = lean_ctor_get(v___y_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___y_1433_, 1);
v___y_1410_ = v___y_1429_;
v___y_1411_ = v___y_1430_;
v___y_1412_ = v___y_1431_;
v___y_1413_ = v___y_1432_;
v_a_1414_ = v_a_1434_;
goto v___jp_1409_;
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
lean_dec_ref(v___y_1430_);
lean_dec(v_matchDeclName_1401_);
v_a_1435_ = lean_ctor_get(v___y_1433_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___y_1433_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___y_1433_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___y_1433_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
v___jp_1443_:
{
if (v___y_1451_ == 0)
{
lean_object* v___x_1452_; 
lean_dec_ref(v___y_1446_);
v___x_1452_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1449_, v___y_1448_, v___y_1444_);
lean_dec_ref(v___y_1449_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1466_; 
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; 
v_unused_1467_ = lean_ctor_get(v___x_1452_, 0);
lean_dec(v_unused_1467_);
v___x_1454_ = v___x_1452_;
v_isShared_1455_ = v_isSharedCheck_1466_;
goto v_resetjp_1453_;
}
else
{
lean_dec(v___x_1452_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1466_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1456_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__1);
lean_inc(v_matchDeclName_1401_);
v___x_1457_ = l_Lean_MessageData_ofName(v_matchDeclName_1401_);
v___x_1458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1456_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
v___x_1459_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__3);
v___x_1460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1458_);
lean_ctor_set(v___x_1460_, 1, v___x_1459_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set_tag(v___x_1454_, 1);
lean_ctor_set(v___x_1454_, 0, v___y_1450_);
v___x_1462_ = v___x_1454_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___y_1450_);
v___x_1462_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1460_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v___x_1464_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1463_, v___y_1445_, v___y_1448_, v___y_1447_, v___y_1444_);
v___y_1429_ = v___y_1444_;
v___y_1430_ = v___y_1447_;
v___y_1431_ = v___y_1445_;
v___y_1432_ = v___y_1448_;
v___y_1433_ = v___x_1464_;
goto v___jp_1428_;
}
}
}
else
{
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1447_);
lean_dec(v_matchDeclName_1401_);
return v___x_1452_;
}
}
else
{
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
v___y_1429_ = v___y_1444_;
v___y_1430_ = v___y_1447_;
v___y_1431_ = v___y_1445_;
v___y_1432_ = v___y_1448_;
v___y_1433_ = v___y_1446_;
goto v___jp_1428_;
}
}
v___jp_1468_:
{
if (v___y_1476_ == 0)
{
lean_object* v___x_1477_; 
lean_dec_ref(v___y_1470_);
v___x_1477_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1472_, v___y_1473_, v___y_1469_);
lean_dec_ref(v___y_1472_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v___x_1478_; 
lean_dec_ref_known(v___x_1477_, 1);
v___x_1478_ = l_Lean_Meta_saveState___redArg(v___y_1473_, v___y_1469_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1480_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref_known(v___x_1478_, 1);
lean_inc(v___y_1474_);
v___x_1480_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(v___y_1474_, v___y_1475_, v___y_1473_, v___y_1471_, v___y_1469_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_dec(v_a_1479_);
lean_dec(v___y_1474_);
v___y_1429_ = v___y_1469_;
v___y_1430_ = v___y_1471_;
v___y_1431_ = v___y_1475_;
v___y_1432_ = v___y_1473_;
v___y_1433_ = v___x_1480_;
goto v___jp_1428_;
}
else
{
lean_object* v_a_1481_; uint8_t v___x_1482_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_a_1481_);
v___x_1482_ = l_Lean_Exception_isInterrupt(v_a_1481_);
if (v___x_1482_ == 0)
{
uint8_t v___x_1483_; 
v___x_1483_ = l_Lean_Exception_isRuntime(v_a_1481_);
v___y_1444_ = v___y_1469_;
v___y_1445_ = v___y_1475_;
v___y_1446_ = v___x_1480_;
v___y_1447_ = v___y_1471_;
v___y_1448_ = v___y_1473_;
v___y_1449_ = v_a_1479_;
v___y_1450_ = v___y_1474_;
v___y_1451_ = v___x_1483_;
goto v___jp_1443_;
}
else
{
lean_dec(v_a_1481_);
v___y_1444_ = v___y_1469_;
v___y_1445_ = v___y_1475_;
v___y_1446_ = v___x_1480_;
v___y_1447_ = v___y_1471_;
v___y_1448_ = v___y_1473_;
v___y_1449_ = v_a_1479_;
v___y_1450_ = v___y_1474_;
v___y_1451_ = v___x_1482_;
goto v___jp_1443_;
}
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1471_);
lean_dec(v_matchDeclName_1401_);
v_a_1484_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1478_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1478_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
else
{
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1471_);
lean_dec(v_matchDeclName_1401_);
return v___x_1477_;
}
}
else
{
lean_object* v___x_1492_; 
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v_matchDeclName_1401_);
v___x_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1492_, 0, v___y_1470_);
return v___x_1492_;
}
}
v___jp_1493_:
{
uint8_t v___x_1501_; 
v___x_1501_ = l_Lean_Exception_isInterrupt(v_a_1500_);
if (v___x_1501_ == 0)
{
uint8_t v___x_1502_; 
lean_inc_ref(v_a_1500_);
v___x_1502_ = l_Lean_Exception_isRuntime(v_a_1500_);
v___y_1469_ = v___y_1494_;
v___y_1470_ = v_a_1500_;
v___y_1471_ = v___y_1495_;
v___y_1472_ = v___y_1496_;
v___y_1473_ = v___y_1497_;
v___y_1474_ = v___y_1498_;
v___y_1475_ = v___y_1499_;
v___y_1476_ = v___x_1502_;
goto v___jp_1468_;
}
else
{
v___y_1469_ = v___y_1494_;
v___y_1470_ = v_a_1500_;
v___y_1471_ = v___y_1495_;
v___y_1472_ = v___y_1496_;
v___y_1473_ = v___y_1497_;
v___y_1474_ = v___y_1498_;
v___y_1475_ = v___y_1499_;
v___y_1476_ = v___x_1501_;
goto v___jp_1468_;
}
}
v___jp_1503_:
{
if (v___y_1512_ == 0)
{
lean_object* v___x_1513_; 
lean_dec_ref(v___y_1508_);
v___x_1513_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1506_, v___y_1509_, v___y_1504_);
lean_dec_ref(v___y_1506_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v___x_1514_; 
lean_dec_ref_known(v___x_1513_, 1);
v___x_1514_ = l_Lean_Meta_saveState___redArg(v___y_1509_, v___y_1504_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref_known(v___x_1514_, 1);
v___x_1516_ = lean_box(0);
lean_inc(v___y_1510_);
v___x_1517_ = l_Lean_Meta_splitIfTarget_x3f(v___y_1510_, v___x_1516_, v___y_1505_, v___y_1511_, v___y_1509_, v___y_1507_, v___y_1504_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___x_1517_, 1);
if (lean_obj_tag(v_a_1518_) == 1)
{
lean_object* v_val_1519_; lean_object* v_fst_1520_; lean_object* v_snd_1521_; lean_object* v_mvarId_1522_; lean_object* v_fvarId_1523_; lean_object* v___x_1524_; 
v_val_1519_ = lean_ctor_get(v_a_1518_, 0);
lean_inc(v_val_1519_);
lean_dec_ref_known(v_a_1518_, 1);
v_fst_1520_ = lean_ctor_get(v_val_1519_, 0);
lean_inc(v_fst_1520_);
v_snd_1521_ = lean_ctor_get(v_val_1519_, 1);
lean_inc(v_snd_1521_);
lean_dec(v_val_1519_);
v_mvarId_1522_ = lean_ctor_get(v_fst_1520_, 0);
lean_inc(v_mvarId_1522_);
v_fvarId_1523_ = lean_ctor_get(v_fst_1520_, 1);
lean_inc(v_fvarId_1523_);
lean_dec(v_fst_1520_);
v___x_1524_ = l_Lean_Meta_trySubst(v_mvarId_1522_, v_fvarId_1523_, v___y_1511_, v___y_1509_, v___y_1507_, v___y_1504_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v_mvarId_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_dec(v_a_1515_);
lean_dec(v___y_1510_);
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1524_, 1);
v_mvarId_1526_ = lean_ctor_get(v_snd_1521_, 0);
lean_inc(v_mvarId_1526_);
lean_dec(v_snd_1521_);
v___x_1527_ = lean_unsigned_to_nat(2u);
v___x_1528_ = lean_mk_empty_array_with_capacity(v___x_1527_);
v___x_1529_ = lean_array_push(v___x_1528_, v_a_1525_);
v___x_1530_ = lean_array_push(v___x_1529_, v_mvarId_1526_);
v___y_1410_ = v___y_1504_;
v___y_1411_ = v___y_1507_;
v___y_1412_ = v___y_1511_;
v___y_1413_ = v___y_1509_;
v_a_1414_ = v___x_1530_;
goto v___jp_1409_;
}
else
{
lean_object* v_a_1531_; 
lean_dec(v_snd_1521_);
v_a_1531_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v___x_1524_, 1);
v___y_1494_ = v___y_1504_;
v___y_1495_ = v___y_1507_;
v___y_1496_ = v_a_1515_;
v___y_1497_ = v___y_1509_;
v___y_1498_ = v___y_1510_;
v___y_1499_ = v___y_1511_;
v_a_1500_ = v_a_1531_;
goto v___jp_1493_;
}
}
else
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_dec(v_a_1518_);
v___x_1532_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5);
v___x_1533_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1532_, v___y_1511_, v___y_1509_, v___y_1507_, v___y_1504_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; 
lean_dec(v_a_1515_);
lean_dec(v___y_1510_);
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1533_, 1);
v___y_1410_ = v___y_1504_;
v___y_1411_ = v___y_1507_;
v___y_1412_ = v___y_1511_;
v___y_1413_ = v___y_1509_;
v_a_1414_ = v_a_1534_;
goto v___jp_1409_;
}
else
{
lean_object* v_a_1535_; 
v_a_1535_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1535_);
lean_dec_ref_known(v___x_1533_, 1);
v___y_1494_ = v___y_1504_;
v___y_1495_ = v___y_1507_;
v___y_1496_ = v_a_1515_;
v___y_1497_ = v___y_1509_;
v___y_1498_ = v___y_1510_;
v___y_1499_ = v___y_1511_;
v_a_1500_ = v_a_1535_;
goto v___jp_1493_;
}
}
}
else
{
lean_object* v_a_1536_; 
v_a_1536_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1517_, 1);
v___y_1494_ = v___y_1504_;
v___y_1495_ = v___y_1507_;
v___y_1496_ = v_a_1515_;
v___y_1497_ = v___y_1509_;
v___y_1498_ = v___y_1510_;
v___y_1499_ = v___y_1511_;
v_a_1500_ = v_a_1536_;
goto v___jp_1493_;
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1507_);
lean_dec(v_matchDeclName_1401_);
v_a_1537_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1514_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1514_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
else
{
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1507_);
lean_dec(v_matchDeclName_1401_);
return v___x_1513_;
}
}
else
{
lean_object* v___x_1545_; 
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v_matchDeclName_1401_);
v___x_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1545_, 0, v___y_1508_);
return v___x_1545_;
}
}
v___jp_1546_:
{
uint8_t v___x_1555_; 
v___x_1555_ = l_Lean_Exception_isInterrupt(v_a_1554_);
if (v___x_1555_ == 0)
{
uint8_t v___x_1556_; 
lean_inc_ref(v_a_1554_);
v___x_1556_ = l_Lean_Exception_isRuntime(v_a_1554_);
v___y_1504_ = v___y_1547_;
v___y_1505_ = v___y_1548_;
v___y_1506_ = v___y_1549_;
v___y_1507_ = v___y_1550_;
v___y_1508_ = v_a_1554_;
v___y_1509_ = v___y_1551_;
v___y_1510_ = v___y_1552_;
v___y_1511_ = v___y_1553_;
v___y_1512_ = v___x_1556_;
goto v___jp_1503_;
}
else
{
v___y_1504_ = v___y_1547_;
v___y_1505_ = v___y_1548_;
v___y_1506_ = v___y_1549_;
v___y_1507_ = v___y_1550_;
v___y_1508_ = v_a_1554_;
v___y_1509_ = v___y_1551_;
v___y_1510_ = v___y_1552_;
v___y_1511_ = v___y_1553_;
v___y_1512_ = v___x_1555_;
goto v___jp_1503_;
}
}
v___jp_1557_:
{
if (lean_obj_tag(v___y_1565_) == 0)
{
lean_object* v_a_1566_; 
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1560_);
v_a_1566_ = lean_ctor_get(v___y_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___y_1565_, 1);
v___y_1410_ = v___y_1558_;
v___y_1411_ = v___y_1561_;
v___y_1412_ = v___y_1562_;
v___y_1413_ = v___y_1563_;
v_a_1414_ = v_a_1566_;
goto v___jp_1409_;
}
else
{
lean_object* v_a_1567_; 
v_a_1567_ = lean_ctor_get(v___y_1565_, 0);
lean_inc(v_a_1567_);
lean_dec_ref_known(v___y_1565_, 1);
v___y_1547_ = v___y_1558_;
v___y_1548_ = v___y_1559_;
v___y_1549_ = v___y_1560_;
v___y_1550_ = v___y_1561_;
v___y_1551_ = v___y_1563_;
v___y_1552_ = v___y_1564_;
v___y_1553_ = v___y_1562_;
v_a_1554_ = v_a_1567_;
goto v___jp_1546_;
}
}
v___jp_1568_:
{
if (v___y_1577_ == 0)
{
lean_object* v___x_1578_; 
lean_dec_ref(v___y_1571_);
v___x_1578_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1574_, v___y_1575_, v___y_1570_);
lean_dec_ref(v___y_1574_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v___x_1579_; 
lean_dec_ref_known(v___x_1578_, 1);
v___x_1579_ = l_Lean_Meta_saveState___redArg(v___y_1575_, v___y_1570_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1581_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
lean_inc(v___y_1576_);
v___x_1581_ = l_Lean_Meta_simpIfTarget(v___y_1576_, v___y_1572_, v___y_1572_, v___y_1569_, v___y_1575_, v___y_1573_, v___y_1570_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; uint8_t v___x_1583_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1581_, 1);
v___x_1583_ = l_Lean_instBEqMVarId_beq(v_a_1582_, v___y_1576_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = lean_box(0);
v___x_1585_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1582_, v___x_1584_, v___y_1569_, v___y_1575_, v___y_1573_, v___y_1570_);
v___y_1558_ = v___y_1570_;
v___y_1559_ = v___y_1572_;
v___y_1560_ = v_a_1580_;
v___y_1561_ = v___y_1573_;
v___y_1562_ = v___y_1569_;
v___y_1563_ = v___y_1575_;
v___y_1564_ = v___y_1576_;
v___y_1565_ = v___x_1585_;
goto v___jp_1557_;
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7);
v___x_1587_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1586_, v___y_1569_, v___y_1575_, v___y_1573_, v___y_1570_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1589_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v___x_1589_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1582_, v_a_1588_, v___y_1569_, v___y_1575_, v___y_1573_, v___y_1570_);
v___y_1558_ = v___y_1570_;
v___y_1559_ = v___y_1572_;
v___y_1560_ = v_a_1580_;
v___y_1561_ = v___y_1573_;
v___y_1562_ = v___y_1569_;
v___y_1563_ = v___y_1575_;
v___y_1564_ = v___y_1576_;
v___y_1565_ = v___x_1589_;
goto v___jp_1557_;
}
else
{
lean_object* v_a_1590_; 
lean_dec(v_a_1582_);
v_a_1590_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1587_, 1);
v___y_1547_ = v___y_1570_;
v___y_1548_ = v___y_1572_;
v___y_1549_ = v_a_1580_;
v___y_1550_ = v___y_1573_;
v___y_1551_ = v___y_1575_;
v___y_1552_ = v___y_1576_;
v___y_1553_ = v___y_1569_;
v_a_1554_ = v_a_1590_;
goto v___jp_1546_;
}
}
}
else
{
lean_object* v_a_1591_; 
v_a_1591_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1591_);
lean_dec_ref_known(v___x_1581_, 1);
v___y_1547_ = v___y_1570_;
v___y_1548_ = v___y_1572_;
v___y_1549_ = v_a_1580_;
v___y_1550_ = v___y_1573_;
v___y_1551_ = v___y_1575_;
v___y_1552_ = v___y_1576_;
v___y_1553_ = v___y_1569_;
v_a_1554_ = v_a_1591_;
goto v___jp_1546_;
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1573_);
lean_dec(v_matchDeclName_1401_);
v_a_1592_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1579_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1579_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
else
{
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1573_);
lean_dec(v_matchDeclName_1401_);
return v___x_1578_;
}
}
else
{
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1574_);
v___y_1429_ = v___y_1570_;
v___y_1430_ = v___y_1573_;
v___y_1431_ = v___y_1569_;
v___y_1432_ = v___y_1575_;
v___y_1433_ = v___y_1571_;
goto v___jp_1428_;
}
}
v___jp_1600_:
{
if (v___y_1609_ == 0)
{
lean_object* v___x_1610_; 
lean_dec_ref(v___y_1603_);
v___x_1610_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1601_, v___y_1606_, v___y_1602_);
lean_dec_ref(v___y_1601_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v___x_1611_; 
lean_dec_ref_known(v___x_1610_, 1);
v___x_1611_ = l_Lean_Meta_saveState___redArg(v___y_1606_, v___y_1602_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v___x_1613_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_a_1612_);
lean_dec_ref_known(v___x_1611_, 1);
lean_inc(v___y_1607_);
v___x_1613_ = l_Lean_Meta_splitSparseCasesOn(v___y_1607_, v___y_1608_, v___y_1606_, v___y_1605_, v___y_1602_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_dec(v_a_1612_);
lean_dec(v___y_1607_);
v___y_1429_ = v___y_1602_;
v___y_1430_ = v___y_1605_;
v___y_1431_ = v___y_1608_;
v___y_1432_ = v___y_1606_;
v___y_1433_ = v___x_1613_;
goto v___jp_1428_;
}
else
{
lean_object* v_a_1614_; uint8_t v___x_1615_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
v___x_1615_ = l_Lean_Exception_isInterrupt(v_a_1614_);
if (v___x_1615_ == 0)
{
uint8_t v___x_1616_; 
v___x_1616_ = l_Lean_Exception_isRuntime(v_a_1614_);
v___y_1569_ = v___y_1608_;
v___y_1570_ = v___y_1602_;
v___y_1571_ = v___x_1613_;
v___y_1572_ = v___y_1604_;
v___y_1573_ = v___y_1605_;
v___y_1574_ = v_a_1612_;
v___y_1575_ = v___y_1606_;
v___y_1576_ = v___y_1607_;
v___y_1577_ = v___x_1616_;
goto v___jp_1568_;
}
else
{
lean_dec(v_a_1614_);
v___y_1569_ = v___y_1608_;
v___y_1570_ = v___y_1602_;
v___y_1571_ = v___x_1613_;
v___y_1572_ = v___y_1604_;
v___y_1573_ = v___y_1605_;
v___y_1574_ = v_a_1612_;
v___y_1575_ = v___y_1606_;
v___y_1576_ = v___y_1607_;
v___y_1577_ = v___x_1615_;
goto v___jp_1568_;
}
}
}
else
{
lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1624_; 
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1605_);
lean_dec(v_matchDeclName_1401_);
v_a_1617_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1619_ = v___x_1611_;
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v___x_1611_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1624_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1622_; 
if (v_isShared_1620_ == 0)
{
v___x_1622_ = v___x_1619_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
else
{
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1605_);
lean_dec(v_matchDeclName_1401_);
return v___x_1610_;
}
}
else
{
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1601_);
v___y_1429_ = v___y_1602_;
v___y_1430_ = v___y_1605_;
v___y_1431_ = v___y_1608_;
v___y_1432_ = v___y_1606_;
v___y_1433_ = v___y_1603_;
goto v___jp_1428_;
}
}
v___jp_1625_:
{
if (v___y_1634_ == 0)
{
lean_object* v___x_1635_; 
lean_dec_ref(v___y_1628_);
v___x_1635_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1627_, v___y_1631_, v___y_1626_);
lean_dec_ref(v___y_1627_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v___x_1636_; 
lean_dec_ref_known(v___x_1635_, 1);
v___x_1636_ = l_Lean_Meta_saveState___redArg(v___y_1631_, v___y_1626_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1638_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1636_, 1);
lean_inc(v___y_1632_);
v___x_1638_ = l_Lean_Meta_reduceSparseCasesOn(v___y_1632_, v___y_1633_, v___y_1631_, v___y_1630_, v___y_1626_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_dec(v_a_1637_);
lean_dec(v___y_1632_);
v___y_1429_ = v___y_1626_;
v___y_1430_ = v___y_1630_;
v___y_1431_ = v___y_1633_;
v___y_1432_ = v___y_1631_;
v___y_1433_ = v___x_1638_;
goto v___jp_1428_;
}
else
{
lean_object* v_a_1639_; uint8_t v___x_1640_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
v___x_1640_ = l_Lean_Exception_isInterrupt(v_a_1639_);
if (v___x_1640_ == 0)
{
uint8_t v___x_1641_; 
v___x_1641_ = l_Lean_Exception_isRuntime(v_a_1639_);
v___y_1601_ = v_a_1637_;
v___y_1602_ = v___y_1626_;
v___y_1603_ = v___x_1638_;
v___y_1604_ = v___y_1629_;
v___y_1605_ = v___y_1630_;
v___y_1606_ = v___y_1631_;
v___y_1607_ = v___y_1632_;
v___y_1608_ = v___y_1633_;
v___y_1609_ = v___x_1641_;
goto v___jp_1600_;
}
else
{
lean_dec(v_a_1639_);
v___y_1601_ = v_a_1637_;
v___y_1602_ = v___y_1626_;
v___y_1603_ = v___x_1638_;
v___y_1604_ = v___y_1629_;
v___y_1605_ = v___y_1630_;
v___y_1606_ = v___y_1631_;
v___y_1607_ = v___y_1632_;
v___y_1608_ = v___y_1633_;
v___y_1609_ = v___x_1640_;
goto v___jp_1600_;
}
}
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1630_);
lean_dec(v_matchDeclName_1401_);
v_a_1642_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1636_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1636_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
else
{
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1630_);
lean_dec(v_matchDeclName_1401_);
return v___x_1635_;
}
}
else
{
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1627_);
v___y_1429_ = v___y_1626_;
v___y_1430_ = v___y_1630_;
v___y_1431_ = v___y_1633_;
v___y_1432_ = v___y_1631_;
v___y_1433_ = v___y_1628_;
goto v___jp_1428_;
}
}
v___jp_1650_:
{
if (v___y_1659_ == 0)
{
lean_object* v___x_1660_; 
lean_dec_ref(v___y_1651_);
v___x_1660_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1654_, v___y_1656_, v___y_1652_);
lean_dec_ref(v___y_1654_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v___x_1661_; 
lean_dec_ref_known(v___x_1660_, 1);
v___x_1661_ = l_Lean_Meta_saveState___redArg(v___y_1656_, v___y_1652_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1663_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref_known(v___x_1661_, 1);
lean_inc(v___y_1657_);
v___x_1663_ = l_Lean_Meta_casesOnStuckLHS(v___y_1657_, v___y_1658_, v___y_1656_, v___y_1655_, v___y_1652_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_dec(v_a_1662_);
lean_dec(v___y_1657_);
v___y_1429_ = v___y_1652_;
v___y_1430_ = v___y_1655_;
v___y_1431_ = v___y_1658_;
v___y_1432_ = v___y_1656_;
v___y_1433_ = v___x_1663_;
goto v___jp_1428_;
}
else
{
lean_object* v_a_1664_; uint8_t v___x_1665_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
v___x_1665_ = l_Lean_Exception_isInterrupt(v_a_1664_);
if (v___x_1665_ == 0)
{
uint8_t v___x_1666_; 
v___x_1666_ = l_Lean_Exception_isRuntime(v_a_1664_);
v___y_1626_ = v___y_1652_;
v___y_1627_ = v_a_1662_;
v___y_1628_ = v___x_1663_;
v___y_1629_ = v___y_1653_;
v___y_1630_ = v___y_1655_;
v___y_1631_ = v___y_1656_;
v___y_1632_ = v___y_1657_;
v___y_1633_ = v___y_1658_;
v___y_1634_ = v___x_1666_;
goto v___jp_1625_;
}
else
{
lean_dec(v_a_1664_);
v___y_1626_ = v___y_1652_;
v___y_1627_ = v_a_1662_;
v___y_1628_ = v___x_1663_;
v___y_1629_ = v___y_1653_;
v___y_1630_ = v___y_1655_;
v___y_1631_ = v___y_1656_;
v___y_1632_ = v___y_1657_;
v___y_1633_ = v___y_1658_;
v___y_1634_ = v___x_1665_;
goto v___jp_1625_;
}
}
}
else
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1655_);
lean_dec(v_matchDeclName_1401_);
v_a_1667_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1661_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1661_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
else
{
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1655_);
lean_dec(v_matchDeclName_1401_);
return v___x_1660_;
}
}
else
{
lean_object* v___x_1675_; 
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v_matchDeclName_1401_);
v___x_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___y_1651_);
return v___x_1675_;
}
}
v___jp_1676_:
{
if (v___y_1685_ == 0)
{
lean_object* v___x_1686_; 
lean_dec_ref(v___y_1679_);
v___x_1686_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1677_, v___y_1682_, v___y_1678_);
lean_dec_ref(v___y_1677_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v___x_1687_; 
lean_dec_ref_known(v___x_1686_, 1);
v___x_1687_ = l_Lean_Meta_saveState___redArg(v___y_1682_, v___y_1678_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1689_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1688_);
lean_dec_ref_known(v___x_1687_, 1);
lean_inc(v___y_1683_);
v___x_1689_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(v___y_1683_, v___y_1684_, v___y_1682_, v___y_1681_, v___y_1678_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
lean_dec(v_a_1688_);
lean_dec(v___y_1683_);
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1690_);
lean_dec_ref_known(v___x_1689_, 1);
v___x_1691_ = lean_unsigned_to_nat(1u);
v___x_1692_ = lean_mk_empty_array_with_capacity(v___x_1691_);
v___x_1693_ = lean_array_push(v___x_1692_, v_a_1690_);
v___y_1410_ = v___y_1678_;
v___y_1411_ = v___y_1681_;
v___y_1412_ = v___y_1684_;
v___y_1413_ = v___y_1682_;
v_a_1414_ = v___x_1693_;
goto v___jp_1409_;
}
else
{
lean_object* v_a_1694_; uint8_t v___x_1695_; 
v_a_1694_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1694_);
lean_dec_ref_known(v___x_1689_, 1);
v___x_1695_ = l_Lean_Exception_isInterrupt(v_a_1694_);
if (v___x_1695_ == 0)
{
uint8_t v___x_1696_; 
lean_inc(v_a_1694_);
v___x_1696_ = l_Lean_Exception_isRuntime(v_a_1694_);
v___y_1651_ = v_a_1694_;
v___y_1652_ = v___y_1678_;
v___y_1653_ = v___y_1680_;
v___y_1654_ = v_a_1688_;
v___y_1655_ = v___y_1681_;
v___y_1656_ = v___y_1682_;
v___y_1657_ = v___y_1683_;
v___y_1658_ = v___y_1684_;
v___y_1659_ = v___x_1696_;
goto v___jp_1650_;
}
else
{
v___y_1651_ = v_a_1694_;
v___y_1652_ = v___y_1678_;
v___y_1653_ = v___y_1680_;
v___y_1654_ = v_a_1688_;
v___y_1655_ = v___y_1681_;
v___y_1656_ = v___y_1682_;
v___y_1657_ = v___y_1683_;
v___y_1658_ = v___y_1684_;
v___y_1659_ = v___x_1695_;
goto v___jp_1650_;
}
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1681_);
lean_dec(v_matchDeclName_1401_);
v_a_1697_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1687_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1687_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
else
{
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1681_);
lean_dec(v_matchDeclName_1401_);
return v___x_1686_;
}
}
else
{
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1681_);
lean_dec_ref(v___y_1677_);
lean_dec(v_matchDeclName_1401_);
return v___y_1679_;
}
}
v___jp_1705_:
{
if (v___y_1714_ == 0)
{
lean_object* v___x_1715_; 
lean_dec_ref(v___y_1710_);
v___x_1715_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1711_, v___y_1712_, v___y_1707_);
lean_dec_ref(v___y_1711_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
lean_dec_ref_known(v___x_1715_, 1);
v___x_1716_ = lean_unsigned_to_nat(16u);
v___x_1717_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
lean_ctor_set_uint8(v___x_1717_, sizeof(void*)*1, v___y_1708_);
lean_ctor_set_uint8(v___x_1717_, sizeof(void*)*1 + 1, v___y_1708_);
lean_ctor_set_uint8(v___x_1717_, sizeof(void*)*1 + 2, v___y_1708_);
v___x_1718_ = l_Lean_Meta_saveState___redArg(v___y_1712_, v___y_1707_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1720_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref_known(v___x_1718_, 1);
lean_inc(v___y_1713_);
v___x_1720_ = l_Lean_MVarId_contradiction(v___y_1713_, v___x_1717_, v___y_1706_, v___y_1712_, v___y_1709_, v___y_1707_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v___x_1721_; 
lean_dec_ref_known(v___x_1720_, 1);
lean_dec(v_a_1719_);
lean_dec(v___y_1713_);
v___x_1721_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___y_1410_ = v___y_1707_;
v___y_1411_ = v___y_1709_;
v___y_1412_ = v___y_1706_;
v___y_1413_ = v___y_1712_;
v_a_1414_ = v___x_1721_;
goto v___jp_1409_;
}
else
{
lean_object* v_a_1722_; uint8_t v___x_1723_; 
v_a_1722_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1722_);
v___x_1723_ = l_Lean_Exception_isInterrupt(v_a_1722_);
if (v___x_1723_ == 0)
{
uint8_t v___x_1724_; 
v___x_1724_ = l_Lean_Exception_isRuntime(v_a_1722_);
v___y_1677_ = v_a_1719_;
v___y_1678_ = v___y_1707_;
v___y_1679_ = v___x_1720_;
v___y_1680_ = v___y_1708_;
v___y_1681_ = v___y_1709_;
v___y_1682_ = v___y_1712_;
v___y_1683_ = v___y_1713_;
v___y_1684_ = v___y_1706_;
v___y_1685_ = v___x_1724_;
goto v___jp_1676_;
}
else
{
lean_dec(v_a_1722_);
v___y_1677_ = v_a_1719_;
v___y_1678_ = v___y_1707_;
v___y_1679_ = v___x_1720_;
v___y_1680_ = v___y_1708_;
v___y_1681_ = v___y_1709_;
v___y_1682_ = v___y_1712_;
v___y_1683_ = v___y_1713_;
v___y_1684_ = v___y_1706_;
v___y_1685_ = v___x_1723_;
goto v___jp_1676_;
}
}
}
else
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
lean_dec_ref_known(v___x_1717_, 1);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1709_);
lean_dec(v_matchDeclName_1401_);
v_a_1725_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1718_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1718_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
else
{
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1709_);
lean_dec(v_matchDeclName_1401_);
return v___x_1715_;
}
}
else
{
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1711_);
lean_dec_ref(v___y_1709_);
lean_dec(v_matchDeclName_1401_);
return v___y_1710_;
}
}
v___jp_1733_:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__9));
v___x_1739_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_1402_, v___x_1738_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v___x_1741_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1739_, 1);
v___x_1741_ = l_Lean_Meta_saveState___redArg(v___y_1735_, v___y_1737_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; uint8_t v___x_1743_; lean_object* v___x_1744_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1742_);
lean_dec_ref_known(v___x_1741_, 1);
v___x_1743_ = 1;
lean_inc(v_a_1740_);
v___x_1744_ = l_Lean_MVarId_refl(v_a_1740_, v___x_1743_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v___x_1745_; 
lean_dec_ref_known(v___x_1744_, 1);
lean_dec(v_a_1742_);
lean_dec(v_a_1740_);
v___x_1745_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___y_1410_ = v___y_1737_;
v___y_1411_ = v___y_1736_;
v___y_1412_ = v___y_1734_;
v___y_1413_ = v___y_1735_;
v_a_1414_ = v___x_1745_;
goto v___jp_1409_;
}
else
{
lean_object* v_a_1746_; uint8_t v___x_1747_; 
v_a_1746_ = lean_ctor_get(v___x_1744_, 0);
lean_inc(v_a_1746_);
v___x_1747_ = l_Lean_Exception_isInterrupt(v_a_1746_);
if (v___x_1747_ == 0)
{
uint8_t v___x_1748_; 
v___x_1748_ = l_Lean_Exception_isRuntime(v_a_1746_);
v___y_1706_ = v___y_1734_;
v___y_1707_ = v___y_1737_;
v___y_1708_ = v___x_1743_;
v___y_1709_ = v___y_1736_;
v___y_1710_ = v___x_1744_;
v___y_1711_ = v_a_1742_;
v___y_1712_ = v___y_1735_;
v___y_1713_ = v_a_1740_;
v___y_1714_ = v___x_1748_;
goto v___jp_1705_;
}
else
{
lean_dec(v_a_1746_);
v___y_1706_ = v___y_1734_;
v___y_1707_ = v___y_1737_;
v___y_1708_ = v___x_1743_;
v___y_1709_ = v___y_1736_;
v___y_1710_ = v___x_1744_;
v___y_1711_ = v_a_1742_;
v___y_1712_ = v___y_1735_;
v___y_1713_ = v_a_1740_;
v___y_1714_ = v___x_1747_;
goto v___jp_1705_;
}
}
}
else
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1756_; 
lean_dec(v_a_1740_);
lean_dec_ref(v___y_1736_);
lean_dec(v_matchDeclName_1401_);
v_a_1749_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1751_ = v___x_1741_;
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1741_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1749_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_dec_ref(v___y_1736_);
lean_dec(v_matchDeclName_1401_);
v_a_1757_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1739_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1739_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
v___jp_1782_:
{
uint8_t v_hasTrace_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v_hasTrace_1783_ = lean_ctor_get_uint8(v_options_1767_, sizeof(void*)*1);
v___x_1784_ = lean_unsigned_to_nat(1u);
v___x_1785_ = lean_nat_add(v_currRecDepth_1768_, v___x_1784_);
lean_inc_ref(v_inheritedTraceOptions_1780_);
lean_inc(v_cancelTk_x3f_1778_);
lean_inc(v_currMacroScope_1776_);
lean_inc(v_quotContext_1775_);
lean_inc(v_maxHeartbeats_1774_);
lean_inc(v_initHeartbeats_1773_);
lean_inc(v_openDecls_1772_);
lean_inc(v_currNamespace_1771_);
lean_inc(v_ref_1770_);
lean_inc(v_maxRecDepth_1769_);
lean_inc_ref(v_options_1767_);
lean_inc_ref(v_fileMap_1766_);
lean_inc_ref(v_fileName_1765_);
v___x_1786_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1786_, 0, v_fileName_1765_);
lean_ctor_set(v___x_1786_, 1, v_fileMap_1766_);
lean_ctor_set(v___x_1786_, 2, v_options_1767_);
lean_ctor_set(v___x_1786_, 3, v___x_1785_);
lean_ctor_set(v___x_1786_, 4, v_maxRecDepth_1769_);
lean_ctor_set(v___x_1786_, 5, v_ref_1770_);
lean_ctor_set(v___x_1786_, 6, v_currNamespace_1771_);
lean_ctor_set(v___x_1786_, 7, v_openDecls_1772_);
lean_ctor_set(v___x_1786_, 8, v_initHeartbeats_1773_);
lean_ctor_set(v___x_1786_, 9, v_maxHeartbeats_1774_);
lean_ctor_set(v___x_1786_, 10, v_quotContext_1775_);
lean_ctor_set(v___x_1786_, 11, v_currMacroScope_1776_);
lean_ctor_set(v___x_1786_, 12, v_cancelTk_x3f_1778_);
lean_ctor_set(v___x_1786_, 13, v_inheritedTraceOptions_1780_);
lean_ctor_set_uint8(v___x_1786_, sizeof(void*)*14, v_diag_1777_);
lean_ctor_set_uint8(v___x_1786_, sizeof(void*)*14 + 1, v_suppressElabErrors_1779_);
if (v_hasTrace_1783_ == 0)
{
v___y_1734_ = v_a_1404_;
v___y_1735_ = v_a_1405_;
v___y_1736_ = v___x_1786_;
v___y_1737_ = v_a_1407_;
goto v___jp_1733_;
}
else
{
lean_object* v___x_1787_; uint8_t v___x_1788_; 
v___x_1787_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_1788_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1780_, v_options_1767_, v___x_1787_);
if (v___x_1788_ == 0)
{
v___y_1734_ = v_a_1404_;
v___y_1735_ = v_a_1405_;
v___y_1736_ = v___x_1786_;
v___y_1737_ = v_a_1407_;
goto v___jp_1733_;
}
else
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1789_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18);
lean_inc(v_mvarId_1402_);
v___x_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1790_, 0, v_mvarId_1402_);
v___x_1791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1789_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
v___x_1792_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v_cls_1781_, v___x_1791_, v_a_1404_, v_a_1405_, v___x_1786_, v_a_1407_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_dec_ref_known(v___x_1792_, 1);
v___y_1734_ = v_a_1404_;
v___y_1735_ = v_a_1405_;
v___y_1736_ = v___x_1786_;
v___y_1737_ = v_a_1407_;
goto v___jp_1733_;
}
else
{
lean_dec_ref_known(v___x_1786_, 14);
lean_dec(v_mvarId_1402_);
lean_dec(v_matchDeclName_1401_);
return v___x_1792_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(lean_object* v_depth_1797_, lean_object* v_matchDeclName_1798_, lean_object* v_as_1799_, size_t v_i_1800_, size_t v_stop_1801_, lean_object* v_b_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
uint8_t v___x_1808_; 
v___x_1808_ = lean_usize_dec_eq(v_i_1800_, v_stop_1801_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1809_ = lean_array_uget_borrowed(v_as_1799_, v_i_1800_);
v___x_1810_ = lean_unsigned_to_nat(1u);
v___x_1811_ = lean_nat_add(v_depth_1797_, v___x_1810_);
lean_inc(v___x_1809_);
lean_inc(v_matchDeclName_1798_);
v___x_1812_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1798_, v___x_1809_, v___x_1811_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___x_1811_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; size_t v___x_1814_; size_t v___x_1815_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_a_1813_);
lean_dec_ref_known(v___x_1812_, 1);
v___x_1814_ = ((size_t)1ULL);
v___x_1815_ = lean_usize_add(v_i_1800_, v___x_1814_);
v_i_1800_ = v___x_1815_;
v_b_1802_ = v_a_1813_;
goto _start;
}
else
{
lean_dec(v_matchDeclName_1798_);
return v___x_1812_;
}
}
else
{
lean_object* v___x_1817_; 
lean_dec(v_matchDeclName_1798_);
v___x_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1817_, 0, v_b_1802_);
return v___x_1817_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0___boxed(lean_object* v_depth_1818_, lean_object* v_matchDeclName_1819_, lean_object* v_as_1820_, lean_object* v_i_1821_, lean_object* v_stop_1822_, lean_object* v_b_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
size_t v_i_boxed_1829_; size_t v_stop_boxed_1830_; lean_object* v_res_1831_; 
v_i_boxed_1829_ = lean_unbox_usize(v_i_1821_);
lean_dec(v_i_1821_);
v_stop_boxed_1830_ = lean_unbox_usize(v_stop_1822_);
lean_dec(v_stop_1822_);
v_res_1831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1818_, v_matchDeclName_1819_, v_as_1820_, v_i_boxed_1829_, v_stop_boxed_1830_, v_b_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec_ref(v_as_1820_);
lean_dec(v_depth_1818_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___boxed(lean_object* v_matchDeclName_1832_, lean_object* v_mvarId_1833_, lean_object* v_depth_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1832_, v_mvarId_1833_, v_depth_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_depth_1834_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(lean_object* v_e_1841_, lean_object* v___y_1842_){
_start:
{
uint8_t v___x_1844_; 
v___x_1844_ = l_Lean_Expr_hasMVar(v_e_1841_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; 
v___x_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1845_, 0, v_e_1841_);
return v___x_1845_;
}
else
{
lean_object* v___x_1846_; lean_object* v_mctx_1847_; lean_object* v___x_1848_; lean_object* v_fst_1849_; lean_object* v_snd_1850_; lean_object* v___x_1851_; lean_object* v_cache_1852_; lean_object* v_zetaDeltaFVarIds_1853_; lean_object* v_postponed_1854_; lean_object* v_diag_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1864_; 
v___x_1846_ = lean_st_ref_get(v___y_1842_);
v_mctx_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc_ref(v_mctx_1847_);
lean_dec(v___x_1846_);
v___x_1848_ = l_Lean_instantiateMVarsCore(v_mctx_1847_, v_e_1841_);
v_fst_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_fst_1849_);
v_snd_1850_ = lean_ctor_get(v___x_1848_, 1);
lean_inc(v_snd_1850_);
lean_dec_ref(v___x_1848_);
v___x_1851_ = lean_st_ref_take(v___y_1842_);
v_cache_1852_ = lean_ctor_get(v___x_1851_, 1);
v_zetaDeltaFVarIds_1853_ = lean_ctor_get(v___x_1851_, 2);
v_postponed_1854_ = lean_ctor_get(v___x_1851_, 3);
v_diag_1855_ = lean_ctor_get(v___x_1851_, 4);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1864_ == 0)
{
lean_object* v_unused_1865_; 
v_unused_1865_ = lean_ctor_get(v___x_1851_, 0);
lean_dec(v_unused_1865_);
v___x_1857_ = v___x_1851_;
v_isShared_1858_ = v_isSharedCheck_1864_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_diag_1855_);
lean_inc(v_postponed_1854_);
lean_inc(v_zetaDeltaFVarIds_1853_);
lean_inc(v_cache_1852_);
lean_dec(v___x_1851_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1864_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 0, v_snd_1850_);
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_snd_1850_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_cache_1852_);
lean_ctor_set(v_reuseFailAlloc_1863_, 2, v_zetaDeltaFVarIds_1853_);
lean_ctor_set(v_reuseFailAlloc_1863_, 3, v_postponed_1854_);
lean_ctor_set(v_reuseFailAlloc_1863_, 4, v_diag_1855_);
v___x_1860_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1861_ = lean_st_ref_put(v___y_1842_, v___x_1860_);
v___x_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1862_, 0, v_fst_1849_);
return v___x_1862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg___boxed(lean_object* v_e_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1866_, v___y_1867_);
lean_dec(v___y_1867_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(lean_object* v_e_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1870_, v___y_1872_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___boxed(lean_object* v_e_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(v_e_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(lean_object* v_lctx_1884_, lean_object* v_localInsts_1885_, lean_object* v_x_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1884_, v_localInsts_1885_, v_x_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
v_a_1901_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1892_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1892_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg___boxed(lean_object* v_lctx_1909_, lean_object* v_localInsts_1910_, lean_object* v_x_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1909_, v_localInsts_1910_, v_x_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(lean_object* v_00_u03b1_1918_, lean_object* v_lctx_1919_, lean_object* v_localInsts_1920_, lean_object* v_x_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1919_, v_localInsts_1920_, v_x_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___boxed(lean_object* v_00_u03b1_1928_, lean_object* v_lctx_1929_, lean_object* v_localInsts_1930_, lean_object* v_x_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(v_00_u03b1_1928_, v_lctx_1929_, v_localInsts_1930_, v_x_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
return v_res_1937_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_proveCondEqThm___lam__0(lean_object* v_matchDeclName_1938_, lean_object* v_x_1939_){
_start:
{
uint8_t v___x_1940_; 
v___x_1940_ = lean_name_eq(v_x_1939_, v_matchDeclName_1938_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed(lean_object* v_matchDeclName_1941_, lean_object* v_x_1942_){
_start:
{
uint8_t v_res_1943_; lean_object* v_r_1944_; 
v_res_1943_ = l_Lean_Meta_Match_proveCondEqThm___lam__0(v_matchDeclName_1941_, v_x_1942_);
lean_dec(v_x_1942_);
lean_dec(v_matchDeclName_1941_);
v_r_1944_ = lean_box(v_res_1943_);
return v_r_1944_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(lean_object* v_upperBound_1945_, lean_object* v_a_1946_, lean_object* v_b_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
uint8_t v___x_1953_; 
v___x_1953_ = lean_nat_dec_lt(v_a_1946_, v_upperBound_1945_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; 
lean_dec(v_a_1946_);
v___x_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1954_, 0, v_b_1947_);
return v___x_1954_;
}
else
{
uint8_t v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = 0;
v___x_1956_ = l_Lean_Meta_introSubstEq(v_b_1947_, v___x_1955_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; lean_object* v_snd_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref_known(v___x_1956_, 1);
v_snd_1958_ = lean_ctor_get(v_a_1957_, 1);
lean_inc(v_snd_1958_);
lean_dec(v_a_1957_);
v___x_1959_ = lean_unsigned_to_nat(1u);
v___x_1960_ = lean_nat_add(v_a_1946_, v___x_1959_);
lean_dec(v_a_1946_);
v_a_1946_ = v___x_1960_;
v_b_1947_ = v_snd_1958_;
goto _start;
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec(v_a_1946_);
v_a_1962_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1956_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1956_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg___boxed(lean_object* v_upperBound_1970_, lean_object* v_a_1971_, lean_object* v_b_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_1970_, v_a_1971_, v_b_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v_upperBound_1970_);
return v_res_1978_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__0));
v___x_1981_ = l_Lean_stringToMessageData(v___x_1980_);
return v___x_1981_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1983_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__2));
v___x_1984_ = l_Lean_stringToMessageData(v___x_1983_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1(lean_object* v_type_1985_, lean_object* v___f_1986_, lean_object* v_matchDeclName_1987_, lean_object* v___x_1988_, uint8_t v___x_1989_, lean_object* v_heqPos_1990_, lean_object* v_heqNum_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v___x_1997_; lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2148_; 
v___x_1997_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_type_1985_, v___y_1993_);
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2000_ = v___x_1997_;
v_isShared_2001_ = v_isSharedCheck_2148_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1997_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2148_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = lean_box(0);
v___x_2003_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1998_, v___x_2002_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2147_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2006_ = v___x_2003_;
v_isShared_2007_ = v_isSharedCheck_2147_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_2003_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2147_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; uint8_t v___y_2015_; lean_object* v_mvarId_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2053_; lean_object* v___y_2054_; lean_object* v_options_2072_; lean_object* v_inheritedTraceOptions_2073_; uint8_t v_hasTrace_2074_; lean_object* v___x_2075_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; 
v_options_2072_ = lean_ctor_get(v___y_1994_, 2);
v_inheritedTraceOptions_2073_ = lean_ctor_get(v___y_1994_, 13);
v_hasTrace_2074_ = lean_ctor_get_uint8(v_options_2072_, sizeof(void*)*1);
v___x_2075_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
if (v_hasTrace_2074_ == 0)
{
v___y_2077_ = v___y_1992_;
v___y_2078_ = v___y_1993_;
v___y_2079_ = v___y_1994_;
v___y_2080_ = v___y_1995_;
goto v___jp_2076_;
}
else
{
lean_object* v___x_2132_; uint8_t v___x_2133_; 
v___x_2132_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_2133_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2073_, v_options_2072_, v___x_2132_);
if (v___x_2133_ == 0)
{
v___y_2077_ = v___y_1992_;
v___y_2078_ = v___y_1993_;
v___y_2079_ = v___y_1994_;
v___y_2080_ = v___y_1995_;
goto v___jp_2076_;
}
else
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2134_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3);
v___x_2135_ = l_Lean_Expr_mvarId_x21(v_a_2004_);
v___x_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
v___x_2137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2134_);
lean_ctor_set(v___x_2137_, 1, v___x_2136_);
v___x_2138_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2075_, v___x_2137_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_dec_ref_known(v___x_2138_, 1);
v___y_2077_ = v___y_1992_;
v___y_2078_ = v___y_1993_;
v___y_2079_ = v___y_1994_;
v___y_2080_ = v___y_1995_;
goto v___jp_2076_;
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
lean_del_object(v___x_2006_);
lean_dec(v_a_2004_);
lean_del_object(v___x_2000_);
lean_dec(v_heqPos_1990_);
lean_dec(v___x_1988_);
lean_dec(v_matchDeclName_1987_);
lean_dec_ref(v___f_1986_);
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___x_2138_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2138_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
}
v___jp_2008_:
{
if (v___y_2015_ == 0)
{
lean_object* v___x_2016_; 
lean_dec_ref(v___y_2014_);
lean_del_object(v___x_2006_);
v___x_2016_ = l_Lean_MVarId_deltaTarget(v___y_2013_, v___f_1986_, v___y_2009_, v___y_2012_, v___y_2011_, v___y_2010_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2018_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2017_);
lean_dec_ref_known(v___x_2016_, 1);
v___x_2018_ = l_Lean_MVarId_heqOfEq(v_a_2017_, v___y_2009_, v___y_2012_, v___y_2011_, v___y_2010_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2020_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2019_);
lean_dec_ref_known(v___x_2018_, 1);
v___x_2020_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1987_, v_a_2019_, v___x_1988_, v___y_2009_, v___y_2012_, v___y_2011_, v___y_2010_);
lean_dec(v___x_1988_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v___x_2021_; 
lean_dec_ref_known(v___x_2020_, 1);
v___x_2021_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_2004_, v___y_2012_);
return v___x_2021_;
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_dec(v_a_2004_);
v_a_2022_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_2020_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2020_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_dec(v_a_2004_);
lean_dec(v___x_1988_);
lean_dec(v_matchDeclName_1987_);
v_a_2030_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_2018_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2018_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec(v_a_2004_);
lean_dec(v___x_1988_);
lean_dec(v_matchDeclName_1987_);
v_a_2038_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2016_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2016_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
else
{
lean_object* v___x_2047_; 
lean_dec(v___y_2013_);
lean_dec(v_a_2004_);
lean_dec(v___x_1988_);
lean_dec(v_matchDeclName_1987_);
lean_dec_ref(v___f_1986_);
if (v_isShared_2007_ == 0)
{
lean_ctor_set_tag(v___x_2006_, 1);
lean_ctor_set(v___x_2006_, 0, v___y_2014_);
v___x_2047_ = v___x_2006_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___y_2014_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
v___jp_2049_:
{
lean_object* v___x_2055_; 
v___x_2055_ = l_Lean_MVarId_intros(v_mvarId_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v_snd_2057_; uint8_t v___x_2058_; lean_object* v___x_2059_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref_known(v___x_2055_, 1);
v_snd_2057_ = lean_ctor_get(v_a_2056_, 1);
lean_inc_n(v_snd_2057_, 2);
lean_dec(v_a_2056_);
v___x_2058_ = 1;
v___x_2059_ = l_Lean_MVarId_refl(v_snd_2057_, v___x_2058_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v___x_2060_; 
lean_dec_ref_known(v___x_2059_, 1);
lean_dec(v_snd_2057_);
lean_del_object(v___x_2006_);
lean_dec(v___x_1988_);
lean_dec(v_matchDeclName_1987_);
lean_dec_ref(v___f_1986_);
v___x_2060_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_2004_, v___y_2052_);
return v___x_2060_;
}
else
{
lean_object* v_a_2061_; uint8_t v___x_2062_; 
v_a_2061_ = lean_ctor_get(v___x_2059_, 0);
lean_inc(v_a_2061_);
lean_dec_ref_known(v___x_2059_, 1);
v___x_2062_ = l_Lean_Exception_isInterrupt(v_a_2061_);
if (v___x_2062_ == 0)
{
uint8_t v___x_2063_; 
lean_inc(v_a_2061_);
v___x_2063_ = l_Lean_Exception_isRuntime(v_a_2061_);
v___y_2009_ = v___y_2051_;
v___y_2010_ = v___y_2054_;
v___y_2011_ = v___y_2053_;
v___y_2012_ = v___y_2052_;
v___y_2013_ = v_snd_2057_;
v___y_2014_ = v_a_2061_;
v___y_2015_ = v___x_2063_;
goto v___jp_2008_;
}
else
{
v___y_2009_ = v___y_2051_;
v___y_2010_ = v___y_2054_;
v___y_2011_ = v___y_2053_;
v___y_2012_ = v___y_2052_;
v___y_2013_ = v_snd_2057_;
v___y_2014_ = v_a_2061_;
v___y_2015_ = v___x_2062_;
goto v___jp_2008_;
}
}
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_del_object(v___x_2006_);
lean_dec(v_a_2004_);
lean_dec(v___x_1988_);
lean_dec(v_matchDeclName_1987_);
lean_dec_ref(v___f_1986_);
v_a_2064_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2055_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2055_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
v___jp_2076_:
{
lean_object* v___x_2081_; 
v___x_2081_ = l_Lean_Expr_mvarId_x21(v_a_2004_);
if (v___x_1989_ == 0)
{
lean_del_object(v___x_2000_);
lean_dec(v_heqPos_1990_);
v_mvarId_2050_ = v___x_2081_;
v___y_2051_ = v___y_2077_;
v___y_2052_ = v___y_2078_;
v___y_2053_ = v___y_2079_;
v___y_2054_ = v___y_2080_;
goto v___jp_2049_;
}
else
{
lean_object* v___x_2082_; uint8_t v___x_2083_; lean_object* v___x_2084_; 
v___x_2082_ = lean_box(0);
v___x_2083_ = 0;
v___x_2084_ = l_Lean_Meta_introNCore(v___x_2081_, v_heqPos_1990_, v___x_2082_, v___x_2083_, v___x_2083_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; lean_object* v_snd_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2122_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
lean_dec_ref_known(v___x_2084_, 1);
v_snd_2086_ = lean_ctor_get(v_a_2085_, 1);
v_isSharedCheck_2122_ = !lean_is_exclusive(v_a_2085_);
if (v_isSharedCheck_2122_ == 0)
{
lean_object* v_unused_2123_; 
v_unused_2123_ = lean_ctor_get(v_a_2085_, 0);
lean_dec(v_unused_2123_);
v___x_2088_ = v_a_2085_;
v_isShared_2089_ = v_isSharedCheck_2122_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_snd_2086_);
lean_dec(v_a_2085_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2122_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2090_; 
lean_inc(v___x_1988_);
v___x_2090_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_heqNum_1991_, v___x_1988_, v_snd_2086_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_options_2091_; uint8_t v_hasTrace_2092_; 
v_options_2091_ = lean_ctor_get(v___y_2079_, 2);
v_hasTrace_2092_ = lean_ctor_get_uint8(v_options_2091_, sizeof(void*)*1);
if (v_hasTrace_2092_ == 0)
{
lean_object* v_a_2093_; 
lean_del_object(v___x_2088_);
lean_del_object(v___x_2000_);
v_a_2093_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2090_, 1);
v_mvarId_2050_ = v_a_2093_;
v___y_2051_ = v___y_2077_;
v___y_2052_ = v___y_2078_;
v___y_2053_ = v___y_2079_;
v___y_2054_ = v___y_2080_;
goto v___jp_2049_;
}
else
{
lean_object* v_a_2094_; lean_object* v_inheritedTraceOptions_2095_; lean_object* v___x_2096_; uint8_t v___x_2097_; 
v_a_2094_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2094_);
lean_dec_ref_known(v___x_2090_, 1);
v_inheritedTraceOptions_2095_ = lean_ctor_get(v___y_2079_, 13);
v___x_2096_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_2097_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2095_, v_options_2091_, v___x_2096_);
if (v___x_2097_ == 0)
{
lean_del_object(v___x_2088_);
lean_del_object(v___x_2000_);
v_mvarId_2050_ = v_a_2094_;
v___y_2051_ = v___y_2077_;
v___y_2052_ = v___y_2078_;
v___y_2053_ = v___y_2079_;
v___y_2054_ = v___y_2080_;
goto v___jp_2049_;
}
else
{
lean_object* v___x_2098_; lean_object* v___x_2100_; 
v___x_2098_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1);
lean_inc(v_a_2094_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set_tag(v___x_2000_, 1);
lean_ctor_set(v___x_2000_, 0, v_a_2094_);
v___x_2100_ = v___x_2000_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2094_);
v___x_2100_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2102_; 
if (v_isShared_2089_ == 0)
{
lean_ctor_set_tag(v___x_2088_, 7);
lean_ctor_set(v___x_2088_, 1, v___x_2100_);
lean_ctor_set(v___x_2088_, 0, v___x_2098_);
v___x_2102_ = v___x_2088_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v___x_2100_);
v___x_2102_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
lean_object* v___x_2103_; 
v___x_2103_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2075_, v___x_2102_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_dec_ref_known(v___x_2103_, 1);
v_mvarId_2050_ = v_a_2094_;
v___y_2051_ = v___y_2077_;
v___y_2052_ = v___y_2078_;
v___y_2053_ = v___y_2079_;
v___y_2054_ = v___y_2080_;
goto v___jp_2049_;
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec(v_a_2094_);
lean_del_object(v___x_2006_);
lean_dec(v_a_2004_);
lean_dec(v___x_1988_);
lean_dec(v_matchDeclName_1987_);
lean_dec_ref(v___f_1986_);
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2103_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2103_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
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
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_del_object(v___x_2088_);
lean_del_object(v___x_2006_);
lean_dec(v_a_2004_);
lean_del_object(v___x_2000_);
lean_dec(v___x_1988_);
lean_dec(v_matchDeclName_1987_);
lean_dec_ref(v___f_1986_);
v_a_2114_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2090_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2090_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_del_object(v___x_2006_);
lean_dec(v_a_2004_);
lean_del_object(v___x_2000_);
lean_dec(v___x_1988_);
lean_dec(v_matchDeclName_1987_);
lean_dec_ref(v___f_1986_);
v_a_2124_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2084_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2084_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2000_);
lean_dec(v_heqPos_1990_);
lean_dec(v___x_1988_);
lean_dec(v_matchDeclName_1987_);
lean_dec_ref(v___f_1986_);
return v___x_2003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed(lean_object* v_type_2149_, lean_object* v___f_2150_, lean_object* v_matchDeclName_2151_, lean_object* v___x_2152_, lean_object* v___x_2153_, lean_object* v_heqPos_2154_, lean_object* v_heqNum_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
uint8_t v___x_6049__boxed_2161_; lean_object* v_res_2162_; 
v___x_6049__boxed_2161_ = lean_unbox(v___x_2153_);
v_res_2162_ = l_Lean_Meta_Match_proveCondEqThm___lam__1(v_type_2149_, v___f_2150_, v_matchDeclName_2151_, v___x_2152_, v___x_6049__boxed_2161_, v_heqPos_2154_, v_heqNum_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v_heqNum_2155_);
return v_res_2162_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__0(void){
_start:
{
lean_object* v___x_2163_; 
v___x_2163_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2163_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__1(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__0, &l_Lean_Meta_Match_proveCondEqThm___closed__0_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__0);
v___x_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
return v___x_2165_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__2(void){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2166_ = lean_unsigned_to_nat(32u);
v___x_2167_ = lean_mk_empty_array_with_capacity(v___x_2166_);
v___x_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
return v___x_2168_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__3(void){
_start:
{
size_t v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2169_ = ((size_t)5ULL);
v___x_2170_ = lean_unsigned_to_nat(0u);
v___x_2171_ = lean_unsigned_to_nat(32u);
v___x_2172_ = lean_mk_empty_array_with_capacity(v___x_2171_);
v___x_2173_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__2, &l_Lean_Meta_Match_proveCondEqThm___closed__2_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__2);
v___x_2174_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
lean_ctor_set(v___x_2174_, 1, v___x_2172_);
lean_ctor_set(v___x_2174_, 2, v___x_2170_);
lean_ctor_set(v___x_2174_, 3, v___x_2170_);
lean_ctor_set_usize(v___x_2174_, 4, v___x_2169_);
return v___x_2174_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__4(void){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2175_ = lean_box(1);
v___x_2176_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_2177_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_2178_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2177_);
lean_ctor_set(v___x_2178_, 1, v___x_2176_);
lean_ctor_set(v___x_2178_, 2, v___x_2175_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm(lean_object* v_matchDeclName_2181_, lean_object* v_type_2182_, lean_object* v_heqPos_2183_, lean_object* v_heqNum_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v___f_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; uint8_t v___x_2194_; lean_object* v___x_2195_; lean_object* v___f_2196_; lean_object* v___x_2197_; 
lean_inc(v_matchDeclName_2181_);
v___f_2190_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2190_, 0, v_matchDeclName_2181_);
v___x_2191_ = lean_unsigned_to_nat(0u);
v___x_2192_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_2193_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___closed__5));
v___x_2194_ = lean_nat_dec_lt(v___x_2191_, v_heqNum_2184_);
v___x_2195_ = lean_box(v___x_2194_);
v___f_2196_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed), 12, 7);
lean_closure_set(v___f_2196_, 0, v_type_2182_);
lean_closure_set(v___f_2196_, 1, v___f_2190_);
lean_closure_set(v___f_2196_, 2, v_matchDeclName_2181_);
lean_closure_set(v___f_2196_, 3, v___x_2191_);
lean_closure_set(v___f_2196_, 4, v___x_2195_);
lean_closure_set(v___f_2196_, 5, v_heqPos_2183_);
lean_closure_set(v___f_2196_, 6, v_heqNum_2184_);
v___x_2197_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v___x_2192_, v___x_2193_, v___f_2196_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___boxed(lean_object* v_matchDeclName_2198_, lean_object* v_type_2199_, lean_object* v_heqPos_2200_, lean_object* v_heqNum_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2198_, v_type_2199_, v_heqPos_2200_, v_heqNum_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
lean_dec(v_a_2203_);
lean_dec_ref(v_a_2202_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(lean_object* v_upperBound_2208_, lean_object* v_inst_2209_, lean_object* v_R_2210_, lean_object* v_a_2211_, lean_object* v_b_2212_, lean_object* v_c_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v___x_2219_; 
v___x_2219_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_2208_, v_a_2211_, v_b_2212_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___boxed(lean_object* v_upperBound_2220_, lean_object* v_inst_2221_, lean_object* v_R_2222_, lean_object* v_a_2223_, lean_object* v_b_2224_, lean_object* v_c_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(v_upperBound_2220_, v_inst_2221_, v_R_2222_, v_a_2223_, v_b_2224_, v_c_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v_upperBound_2220_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(lean_object* v_k_2232_, lean_object* v_b_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v___x_2239_; 
lean_inc(v___y_2237_);
lean_inc_ref(v___y_2236_);
lean_inc(v___y_2235_);
lean_inc_ref(v___y_2234_);
v___x_2239_ = lean_apply_6(v_k_2232_, v_b_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, lean_box(0));
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_2240_, lean_object* v_b_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(v_k_2240_, v_b_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(lean_object* v_name_2248_, uint8_t v_bi_2249_, lean_object* v_type_2250_, lean_object* v_k_2251_, uint8_t v_kind_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v___f_2258_; lean_object* v___x_2259_; 
v___f_2258_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2258_, 0, v_k_2251_);
v___x_2259_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2248_, v_bi_2249_, v_type_2250_, v___f_2258_, v_kind_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2262_ = v___x_2259_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2259_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2265_; 
if (v_isShared_2263_ == 0)
{
v___x_2265_ = v___x_2262_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_a_2260_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
v_a_2268_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2259_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2259_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___boxed(lean_object* v_name_2276_, lean_object* v_bi_2277_, lean_object* v_type_2278_, lean_object* v_k_2279_, lean_object* v_kind_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
uint8_t v_bi_boxed_2286_; uint8_t v_kind_boxed_2287_; lean_object* v_res_2288_; 
v_bi_boxed_2286_ = lean_unbox(v_bi_2277_);
v_kind_boxed_2287_ = lean_unbox(v_kind_2280_);
v_res_2288_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_name_2276_, v_bi_boxed_2286_, v_type_2278_, v_k_2279_, v_kind_boxed_2287_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(lean_object* v_00_u03b1_2289_, lean_object* v_name_2290_, uint8_t v_bi_2291_, lean_object* v_type_2292_, lean_object* v_k_2293_, uint8_t v_kind_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_name_2290_, v_bi_2291_, v_type_2292_, v_k_2293_, v_kind_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___boxed(lean_object* v_00_u03b1_2301_, lean_object* v_name_2302_, lean_object* v_bi_2303_, lean_object* v_type_2304_, lean_object* v_k_2305_, lean_object* v_kind_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
uint8_t v_bi_boxed_2312_; uint8_t v_kind_boxed_2313_; lean_object* v_res_2314_; 
v_bi_boxed_2312_ = lean_unbox(v_bi_2303_);
v_kind_boxed_2313_ = lean_unbox(v_kind_2306_);
v_res_2314_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(v_00_u03b1_2301_, v_name_2302_, v_bi_boxed_2312_, v_type_2304_, v_k_2305_, v_kind_boxed_2313_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed(lean_object* v_i_2315_, lean_object* v_altsNew_2316_, lean_object* v_discrs_2317_, lean_object* v_patterns_2318_, lean_object* v_alts_2319_, lean_object* v_k_2320_, lean_object* v_altNew_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(v_i_2315_, v_altsNew_2316_, v_discrs_2317_, v_patterns_2318_, v_alts_2319_, v_k_2320_, v_altNew_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v_i_2315_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(lean_object* v_discrs_2328_, lean_object* v_patterns_2329_, lean_object* v_alts_2330_, lean_object* v_k_2331_, lean_object* v_i_2332_, lean_object* v_altsNew_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_){
_start:
{
lean_object* v___x_2339_; uint8_t v___x_2340_; 
v___x_2339_ = lean_array_get_size(v_alts_2330_);
v___x_2340_ = lean_nat_dec_lt(v_i_2332_, v___x_2339_);
if (v___x_2340_ == 0)
{
lean_object* v___x_2341_; 
lean_dec(v_i_2332_);
lean_dec_ref(v_alts_2330_);
lean_dec_ref(v_patterns_2329_);
lean_dec_ref(v_discrs_2328_);
lean_inc(v_a_2337_);
lean_inc_ref(v_a_2336_);
lean_inc(v_a_2335_);
lean_inc_ref(v_a_2334_);
v___x_2341_ = lean_apply_6(v_k_2331_, v_altsNew_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, lean_box(0));
return v___x_2341_;
}
else
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2342_ = lean_array_fget_borrowed(v_alts_2330_, v_i_2332_);
v___x_2343_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_2342_, v_a_2334_, v_a_2336_, v_a_2337_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v___f_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; uint8_t v___x_2350_; lean_object* v___x_2351_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_a_2344_);
lean_dec_ref_known(v___x_2343_, 1);
lean_inc_ref(v_patterns_2329_);
lean_inc_ref(v_discrs_2328_);
v___f_2345_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_2345_, 0, v_i_2332_);
lean_closure_set(v___f_2345_, 1, v_altsNew_2333_);
lean_closure_set(v___f_2345_, 2, v_discrs_2328_);
lean_closure_set(v___f_2345_, 3, v_patterns_2329_);
lean_closure_set(v___f_2345_, 4, v_alts_2330_);
lean_closure_set(v___f_2345_, 5, v_k_2331_);
v___x_2346_ = l_Lean_LocalDecl_type(v_a_2344_);
v___x_2347_ = l_Lean_Expr_replaceFVars(v___x_2346_, v_discrs_2328_, v_patterns_2329_);
lean_dec_ref(v_patterns_2329_);
lean_dec_ref(v_discrs_2328_);
lean_dec_ref(v___x_2346_);
v___x_2348_ = l_Lean_LocalDecl_userName(v_a_2344_);
v___x_2349_ = l_Lean_LocalDecl_binderInfo(v_a_2344_);
lean_dec(v_a_2344_);
v___x_2350_ = 0;
v___x_2351_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v___x_2348_, v___x_2349_, v___x_2347_, v___f_2345_, v___x_2350_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_2351_;
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
lean_dec_ref(v_altsNew_2333_);
lean_dec(v_i_2332_);
lean_dec_ref(v_k_2331_);
lean_dec_ref(v_alts_2330_);
lean_dec_ref(v_patterns_2329_);
lean_dec_ref(v_discrs_2328_);
v_a_2352_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2343_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2343_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(lean_object* v_i_2360_, lean_object* v_altsNew_2361_, lean_object* v_discrs_2362_, lean_object* v_patterns_2363_, lean_object* v_alts_2364_, lean_object* v_k_2365_, lean_object* v_altNew_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2372_ = lean_unsigned_to_nat(1u);
v___x_2373_ = lean_nat_add(v_i_2360_, v___x_2372_);
v___x_2374_ = lean_array_push(v_altsNew_2361_, v_altNew_2366_);
v___x_2375_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2362_, v_patterns_2363_, v_alts_2364_, v_k_2365_, v___x_2373_, v___x_2374_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___boxed(lean_object* v_discrs_2376_, lean_object* v_patterns_2377_, lean_object* v_alts_2378_, lean_object* v_k_2379_, lean_object* v_i_2380_, lean_object* v_altsNew_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2376_, v_patterns_2377_, v_alts_2378_, v_k_2379_, v_i_2380_, v_altsNew_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
lean_dec(v_a_2383_);
lean_dec_ref(v_a_2382_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(lean_object* v_00_u03b1_2388_, lean_object* v_discrs_2389_, lean_object* v_patterns_2390_, lean_object* v_alts_2391_, lean_object* v_k_2392_, lean_object* v_i_2393_, lean_object* v_altsNew_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2389_, v_patterns_2390_, v_alts_2391_, v_k_2392_, v_i_2393_, v_altsNew_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___boxed(lean_object* v_00_u03b1_2401_, lean_object* v_discrs_2402_, lean_object* v_patterns_2403_, lean_object* v_alts_2404_, lean_object* v_k_2405_, lean_object* v_i_2406_, lean_object* v_altsNew_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(v_00_u03b1_2401_, v_discrs_2402_, v_patterns_2403_, v_alts_2404_, v_k_2405_, v_i_2406_, v_altsNew_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_);
lean_dec(v_a_2411_);
lean_dec_ref(v_a_2410_);
lean_dec(v_a_2409_);
lean_dec_ref(v_a_2408_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(lean_object* v_numDiscrEqs_2416_, lean_object* v_discrs_2417_, lean_object* v_patterns_2418_, lean_object* v_alts_2419_, lean_object* v_k_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v___x_2426_; uint8_t v___x_2427_; 
v___x_2426_ = lean_unsigned_to_nat(0u);
v___x_2427_ = lean_nat_dec_eq(v_numDiscrEqs_2416_, v___x_2426_);
if (v___x_2427_ == 0)
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2428_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_2429_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2417_, v_patterns_2418_, v_alts_2419_, v_k_2420_, v___x_2426_, v___x_2428_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
return v___x_2429_;
}
else
{
lean_object* v___x_2430_; 
lean_dec_ref(v_patterns_2418_);
lean_dec_ref(v_discrs_2417_);
lean_inc(v_a_2424_);
lean_inc_ref(v_a_2423_);
lean_inc(v_a_2422_);
lean_inc_ref(v_a_2421_);
v___x_2430_ = lean_apply_6(v_k_2420_, v_alts_2419_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, lean_box(0));
return v___x_2430_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___boxed(lean_object* v_numDiscrEqs_2431_, lean_object* v_discrs_2432_, lean_object* v_patterns_2433_, lean_object* v_alts_2434_, lean_object* v_k_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v_numDiscrEqs_2431_, v_discrs_2432_, v_patterns_2433_, v_alts_2434_, v_k_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_);
lean_dec(v_a_2439_);
lean_dec_ref(v_a_2438_);
lean_dec(v_a_2437_);
lean_dec_ref(v_a_2436_);
lean_dec(v_numDiscrEqs_2431_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(lean_object* v_00_u03b1_2442_, lean_object* v_numDiscrEqs_2443_, lean_object* v_discrs_2444_, lean_object* v_patterns_2445_, lean_object* v_alts_2446_, lean_object* v_k_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v_numDiscrEqs_2443_, v_discrs_2444_, v_patterns_2445_, v_alts_2446_, v_k_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___boxed(lean_object* v_00_u03b1_2454_, lean_object* v_numDiscrEqs_2455_, lean_object* v_discrs_2456_, lean_object* v_patterns_2457_, lean_object* v_alts_2458_, lean_object* v_k_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(v_00_u03b1_2454_, v_numDiscrEqs_2455_, v_discrs_2456_, v_patterns_2457_, v_alts_2458_, v_k_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_);
lean_dec(v_a_2463_);
lean_dec_ref(v_a_2462_);
lean_dec(v_a_2461_);
lean_dec_ref(v_a_2460_);
lean_dec(v_numDiscrEqs_2455_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(lean_object* v_declName_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v___x_2469_; lean_object* v_env_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2469_ = lean_st_ref_get(v___y_2467_);
v_env_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc_ref(v_env_2470_);
lean_dec(v___x_2469_);
v___x_2471_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2470_, v_declName_2466_);
v___x_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2471_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg___boxed(lean_object* v_declName_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_declName_2473_, v___y_2474_);
lean_dec(v___y_2474_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(lean_object* v_declName_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v___x_2483_; 
v___x_2483_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_declName_2477_, v___y_2481_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___boxed(lean_object* v_declName_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(v_declName_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(lean_object* v_msg_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v___f_2498_; lean_object* v___x_14710__overap_2499_; lean_object* v___x_2500_; 
v___f_2498_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_14710__overap_2499_ = lean_panic_fn_borrowed(v___f_2498_, v_msg_2492_);
lean_inc(v___y_2496_);
lean_inc_ref(v___y_2495_);
lean_inc(v___y_2494_);
lean_inc_ref(v___y_2493_);
v___x_2500_ = lean_apply_5(v___x_14710__overap_2499_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, lean_box(0));
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___boxed(lean_object* v_msg_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v_msg_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(lean_object* v_k_2508_, lean_object* v_b_2509_, lean_object* v_c_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v___x_2516_; 
lean_inc(v___y_2514_);
lean_inc_ref(v___y_2513_);
lean_inc(v___y_2512_);
lean_inc_ref(v___y_2511_);
v___x_2516_ = lean_apply_7(v_k_2508_, v_b_2509_, v_c_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, lean_box(0));
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed(lean_object* v_k_2517_, lean_object* v_b_2518_, lean_object* v_c_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(v_k_2517_, v_b_2518_, v_c_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(lean_object* v_type_2526_, lean_object* v_k_2527_, uint8_t v_cleanupAnnotations_2528_, uint8_t v_whnfType_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v___f_2535_; lean_object* v___x_2536_; 
v___f_2535_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2535_, 0, v_k_2527_);
v___x_2536_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2526_, v___f_2535_, v_cleanupAnnotations_2528_, v_whnfType_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2536_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2536_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
v_a_2545_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2536_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2536_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___boxed(lean_object* v_type_2553_, lean_object* v_k_2554_, lean_object* v_cleanupAnnotations_2555_, lean_object* v_whnfType_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2562_; uint8_t v_whnfType_boxed_2563_; lean_object* v_res_2564_; 
v_cleanupAnnotations_boxed_2562_ = lean_unbox(v_cleanupAnnotations_2555_);
v_whnfType_boxed_2563_ = lean_unbox(v_whnfType_2556_);
v_res_2564_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v_type_2553_, v_k_2554_, v_cleanupAnnotations_boxed_2562_, v_whnfType_boxed_2563_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(lean_object* v_00_u03b1_2565_, lean_object* v_type_2566_, lean_object* v_k_2567_, uint8_t v_cleanupAnnotations_2568_, uint8_t v_whnfType_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v___x_2575_; 
v___x_2575_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v_type_2566_, v_k_2567_, v_cleanupAnnotations_2568_, v_whnfType_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___boxed(lean_object* v_00_u03b1_2576_, lean_object* v_type_2577_, lean_object* v_k_2578_, lean_object* v_cleanupAnnotations_2579_, lean_object* v_whnfType_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2586_; uint8_t v_whnfType_boxed_2587_; lean_object* v_res_2588_; 
v_cleanupAnnotations_boxed_2586_ = lean_unbox(v_cleanupAnnotations_2579_);
v_whnfType_boxed_2587_ = lean_unbox(v_whnfType_2580_);
v_res_2588_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(v_00_u03b1_2576_, v_type_2577_, v_k_2578_, v_cleanupAnnotations_boxed_2586_, v_whnfType_boxed_2587_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(lean_object* v_overlaps_2589_, lean_object* v_splitterName_2590_, lean_object* v_matcherInput_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v_matchType_2597_; lean_object* v_discrInfos_2598_; lean_object* v_lhss_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2619_; 
v_matchType_2597_ = lean_ctor_get(v_matcherInput_2591_, 1);
v_discrInfos_2598_ = lean_ctor_get(v_matcherInput_2591_, 2);
v_lhss_2599_ = lean_ctor_get(v_matcherInput_2591_, 3);
v_isSharedCheck_2619_ = !lean_is_exclusive(v_matcherInput_2591_);
if (v_isSharedCheck_2619_ == 0)
{
lean_object* v_unused_2620_; lean_object* v_unused_2621_; 
v_unused_2620_ = lean_ctor_get(v_matcherInput_2591_, 4);
lean_dec(v_unused_2620_);
v_unused_2621_ = lean_ctor_get(v_matcherInput_2591_, 0);
lean_dec(v_unused_2621_);
v___x_2601_ = v_matcherInput_2591_;
v_isShared_2602_ = v_isSharedCheck_2619_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_lhss_2599_);
lean_inc(v_discrInfos_2598_);
lean_inc(v_matchType_2597_);
lean_dec(v_matcherInput_2591_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2619_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2603_; lean_object* v___x_2605_; 
v___x_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2603_, 0, v_overlaps_2589_);
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 4, v___x_2603_);
lean_ctor_set(v___x_2601_, 0, v_splitterName_2590_);
v___x_2605_ = v___x_2601_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_splitterName_2590_);
lean_ctor_set(v_reuseFailAlloc_2618_, 1, v_matchType_2597_);
lean_ctor_set(v_reuseFailAlloc_2618_, 2, v_discrInfos_2598_);
lean_ctor_set(v_reuseFailAlloc_2618_, 3, v_lhss_2599_);
lean_ctor_set(v_reuseFailAlloc_2618_, 4, v___x_2603_);
v___x_2605_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
lean_object* v___x_2606_; 
v___x_2606_ = l_Lean_Meta_Match_mkMatcher(v___x_2605_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v_addMatcher_2608_; lean_object* v___x_2609_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
lean_dec_ref_known(v___x_2606_, 1);
v_addMatcher_2608_ = lean_ctor_get(v_a_2607_, 3);
lean_inc_ref(v_addMatcher_2608_);
lean_dec(v_a_2607_);
lean_inc(v___y_2595_);
lean_inc_ref(v___y_2594_);
lean_inc(v___y_2593_);
lean_inc_ref(v___y_2592_);
v___x_2609_ = lean_apply_5(v_addMatcher_2608_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, lean_box(0));
return v___x_2609_;
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
v_a_2610_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2606_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2606_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed(lean_object* v_overlaps_2622_, lean_object* v_splitterName_2623_, lean_object* v_matcherInput_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(v_overlaps_2622_, v_splitterName_2623_, v_matcherInput_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
return v_res_2630_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(lean_object* v_xs_2631_, lean_object* v_ys_2632_, lean_object* v_x_2633_){
_start:
{
lean_object* v_zero_2634_; uint8_t v_isZero_2635_; 
v_zero_2634_ = lean_unsigned_to_nat(0u);
v_isZero_2635_ = lean_nat_dec_eq(v_x_2633_, v_zero_2634_);
if (v_isZero_2635_ == 1)
{
lean_dec(v_x_2633_);
return v_isZero_2635_;
}
else
{
lean_object* v_one_2636_; lean_object* v_n_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; uint8_t v___x_2640_; 
v_one_2636_ = lean_unsigned_to_nat(1u);
v_n_2637_ = lean_nat_sub(v_x_2633_, v_one_2636_);
lean_dec(v_x_2633_);
v___x_2638_ = lean_array_fget_borrowed(v_xs_2631_, v_n_2637_);
v___x_2639_ = lean_array_fget_borrowed(v_ys_2632_, v_n_2637_);
v___x_2640_ = l_Lean_Meta_Match_instBEqAltParamInfo_beq(v___x_2638_, v___x_2639_);
if (v___x_2640_ == 0)
{
lean_dec(v_n_2637_);
return v___x_2640_;
}
else
{
v_x_2633_ = v_n_2637_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg___boxed(lean_object* v_xs_2642_, lean_object* v_ys_2643_, lean_object* v_x_2644_){
_start:
{
uint8_t v_res_2645_; lean_object* v_r_2646_; 
v_res_2645_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_2642_, v_ys_2643_, v_x_2644_);
lean_dec_ref(v_ys_2643_);
lean_dec_ref(v_xs_2642_);
v_r_2646_ = lean_box(v_res_2645_);
return v_r_2646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(lean_object* v_a_2647_, lean_object* v_b_2648_){
_start:
{
lean_object* v_array_2649_; lean_object* v_start_2650_; lean_object* v_stop_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2664_; 
v_array_2649_ = lean_ctor_get(v_a_2647_, 0);
v_start_2650_ = lean_ctor_get(v_a_2647_, 1);
v_stop_2651_ = lean_ctor_get(v_a_2647_, 2);
v_isSharedCheck_2664_ = !lean_is_exclusive(v_a_2647_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2653_ = v_a_2647_;
v_isShared_2654_ = v_isSharedCheck_2664_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_stop_2651_);
lean_inc(v_start_2650_);
lean_inc(v_array_2649_);
lean_dec(v_a_2647_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2664_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
uint8_t v___x_2655_; 
v___x_2655_ = lean_nat_dec_lt(v_start_2650_, v_stop_2651_);
if (v___x_2655_ == 0)
{
lean_del_object(v___x_2653_);
lean_dec(v_stop_2651_);
lean_dec(v_start_2650_);
lean_dec_ref(v_array_2649_);
return v_b_2648_;
}
else
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2659_; 
v___x_2656_ = lean_unsigned_to_nat(1u);
v___x_2657_ = lean_nat_add(v_start_2650_, v___x_2656_);
lean_inc_ref(v_array_2649_);
if (v_isShared_2654_ == 0)
{
lean_ctor_set(v___x_2653_, 1, v___x_2657_);
v___x_2659_ = v___x_2653_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_array_2649_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v___x_2657_);
lean_ctor_set(v_reuseFailAlloc_2663_, 2, v_stop_2651_);
v___x_2659_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = lean_array_fget(v_array_2649_, v_start_2650_);
lean_dec(v_start_2650_);
lean_dec_ref(v_array_2649_);
v___x_2661_ = lean_array_push(v_b_2648_, v___x_2660_);
v_a_2647_ = v___x_2659_;
v_b_2648_ = v___x_2661_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(lean_object* v___x_2665_, lean_object* v___x_2666_, lean_object* v_as_2667_, size_t v_sz_2668_, size_t v_i_2669_, lean_object* v_b_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
uint8_t v___x_2676_; 
v___x_2676_ = lean_usize_dec_lt(v_i_2669_, v_sz_2668_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2677_; 
v___x_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2677_, 0, v_b_2670_);
return v___x_2677_;
}
else
{
lean_object* v___x_2678_; lean_object* v_a_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2678_ = l_Lean_instInhabitedExpr;
v_a_2679_ = lean_array_uget_borrowed(v_as_2667_, v_i_2669_);
v___x_2680_ = lean_array_get_borrowed(v___x_2678_, v___x_2665_, v_a_2679_);
lean_inc(v___x_2680_);
v___x_2681_ = l_Lean_Meta_instantiateForall(v___x_2680_, v___x_2666_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v_a_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_a_2682_);
lean_dec_ref_known(v___x_2681_, 1);
v___x_2683_ = lean_array_get_size(v___x_2666_);
v___x_2684_ = l_Lean_Meta_Match_simpH_x3f(v_a_2682_, v___x_2683_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; lean_object* v_a_2687_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2685_);
lean_dec_ref_known(v___x_2684_, 1);
if (lean_obj_tag(v_a_2685_) == 1)
{
lean_object* v_val_2691_; lean_object* v___x_2692_; 
v_val_2691_ = lean_ctor_get(v_a_2685_, 0);
lean_inc(v_val_2691_);
lean_dec_ref_known(v_a_2685_, 1);
v___x_2692_ = lean_array_push(v_b_2670_, v_val_2691_);
v_a_2687_ = v___x_2692_;
goto v___jp_2686_;
}
else
{
lean_dec(v_a_2685_);
v_a_2687_ = v_b_2670_;
goto v___jp_2686_;
}
v___jp_2686_:
{
size_t v___x_2688_; size_t v___x_2689_; 
v___x_2688_ = ((size_t)1ULL);
v___x_2689_ = lean_usize_add(v_i_2669_, v___x_2688_);
v_i_2669_ = v___x_2689_;
v_b_2670_ = v_a_2687_;
goto _start;
}
}
else
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
lean_dec_ref(v_b_2670_);
v_a_2693_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2684_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2684_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
else
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2708_; 
lean_dec_ref(v_b_2670_);
v_a_2701_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2703_ = v___x_2681_;
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2681_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2701_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5___boxed(lean_object* v___x_2709_, lean_object* v___x_2710_, lean_object* v_as_2711_, lean_object* v_sz_2712_, lean_object* v_i_2713_, lean_object* v_b_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
size_t v_sz_boxed_2720_; size_t v_i_boxed_2721_; lean_object* v_res_2722_; 
v_sz_boxed_2720_ = lean_unbox_usize(v_sz_2712_);
lean_dec(v_sz_2712_);
v_i_boxed_2721_ = lean_unbox_usize(v_i_2713_);
lean_dec(v_i_2713_);
v_res_2722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(v___x_2709_, v___x_2710_, v_as_2711_, v_sz_boxed_2720_, v_i_boxed_2721_, v_b_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec_ref(v_as_2711_);
lean_dec_ref(v___x_2710_);
lean_dec_ref(v___x_2709_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(lean_object* v_as_2723_, size_t v_sz_2724_, size_t v_i_2725_, lean_object* v_b_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
uint8_t v___x_2732_; 
v___x_2732_ = lean_usize_dec_lt(v_i_2725_, v_sz_2724_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; 
v___x_2733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2733_, 0, v_b_2726_);
return v___x_2733_;
}
else
{
lean_object* v_snd_2734_; lean_object* v_fst_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2787_; 
v_snd_2734_ = lean_ctor_get(v_b_2726_, 1);
v_fst_2735_ = lean_ctor_get(v_b_2726_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v_b_2726_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2737_ = v_b_2726_;
v_isShared_2738_ = v_isSharedCheck_2787_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_snd_2734_);
lean_inc(v_fst_2735_);
lean_dec(v_b_2726_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2787_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v_array_2739_; lean_object* v_start_2740_; lean_object* v_stop_2741_; uint8_t v___x_2742_; 
v_array_2739_ = lean_ctor_get(v_snd_2734_, 0);
v_start_2740_ = lean_ctor_get(v_snd_2734_, 1);
v_stop_2741_ = lean_ctor_get(v_snd_2734_, 2);
v___x_2742_ = lean_nat_dec_lt(v_start_2740_, v_stop_2741_);
if (v___x_2742_ == 0)
{
lean_object* v___x_2744_; 
if (v_isShared_2738_ == 0)
{
v___x_2744_ = v___x_2737_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_fst_2735_);
lean_ctor_set(v_reuseFailAlloc_2746_, 1, v_snd_2734_);
v___x_2744_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
lean_object* v___x_2745_; 
v___x_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2744_);
return v___x_2745_;
}
}
else
{
lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2783_; 
lean_inc(v_stop_2741_);
lean_inc(v_start_2740_);
lean_inc_ref(v_array_2739_);
v_isSharedCheck_2783_ = !lean_is_exclusive(v_snd_2734_);
if (v_isSharedCheck_2783_ == 0)
{
lean_object* v_unused_2784_; lean_object* v_unused_2785_; lean_object* v_unused_2786_; 
v_unused_2784_ = lean_ctor_get(v_snd_2734_, 2);
lean_dec(v_unused_2784_);
v_unused_2785_ = lean_ctor_get(v_snd_2734_, 1);
lean_dec(v_unused_2785_);
v_unused_2786_ = lean_ctor_get(v_snd_2734_, 0);
lean_dec(v_unused_2786_);
v___x_2748_ = v_snd_2734_;
v_isShared_2749_ = v_isSharedCheck_2783_;
goto v_resetjp_2747_;
}
else
{
lean_dec(v_snd_2734_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2783_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v_a_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v_a_2750_ = lean_array_uget_borrowed(v_as_2723_, v_i_2725_);
v___x_2751_ = lean_array_fget_borrowed(v_array_2739_, v_start_2740_);
lean_inc(v___x_2751_);
lean_inc(v_a_2750_);
v___x_2752_ = l_Lean_Meta_mkEqHEq(v_a_2750_, v___x_2751_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v___x_2754_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc(v_a_2753_);
lean_dec_ref_known(v___x_2752_, 1);
v___x_2754_ = l_Lean_mkArrow(v_a_2753_, v_fst_2735_, v___y_2729_, v___y_2730_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2759_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_a_2755_);
lean_dec_ref_known(v___x_2754_, 1);
v___x_2756_ = lean_unsigned_to_nat(1u);
v___x_2757_ = lean_nat_add(v_start_2740_, v___x_2756_);
lean_dec(v_start_2740_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 1, v___x_2757_);
v___x_2759_ = v___x_2748_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_array_2739_);
lean_ctor_set(v_reuseFailAlloc_2766_, 1, v___x_2757_);
lean_ctor_set(v_reuseFailAlloc_2766_, 2, v_stop_2741_);
v___x_2759_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
lean_object* v___x_2761_; 
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 1, v___x_2759_);
lean_ctor_set(v___x_2737_, 0, v_a_2755_);
v___x_2761_ = v___x_2737_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_a_2755_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v___x_2759_);
v___x_2761_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
size_t v___x_2762_; size_t v___x_2763_; 
v___x_2762_ = ((size_t)1ULL);
v___x_2763_ = lean_usize_add(v_i_2725_, v___x_2762_);
v_i_2725_ = v___x_2763_;
v_b_2726_ = v___x_2761_;
goto _start;
}
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
lean_del_object(v___x_2748_);
lean_dec(v_stop_2741_);
lean_dec(v_start_2740_);
lean_dec_ref(v_array_2739_);
lean_del_object(v___x_2737_);
v_a_2767_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2754_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2754_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
else
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
lean_del_object(v___x_2748_);
lean_dec(v_stop_2741_);
lean_dec(v_start_2740_);
lean_dec_ref(v_array_2739_);
lean_del_object(v___x_2737_);
lean_dec(v_fst_2735_);
v_a_2775_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2752_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2752_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7___boxed(lean_object* v_as_2788_, lean_object* v_sz_2789_, lean_object* v_i_2790_, lean_object* v_b_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
size_t v_sz_boxed_2797_; size_t v_i_boxed_2798_; lean_object* v_res_2799_; 
v_sz_boxed_2797_ = lean_unbox_usize(v_sz_2789_);
lean_dec(v_sz_2789_);
v_i_boxed_2798_ = lean_unbox_usize(v_i_2790_);
lean_dec(v_i_2790_);
v_res_2799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v_as_2788_, v_sz_boxed_2797_, v_i_boxed_2798_, v_b_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec_ref(v_as_2788_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(lean_object* v___x_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v___x_2803_, lean_object* v___x_2804_, lean_object* v___x_2805_, lean_object* v___x_2806_, lean_object* v___x_2807_, lean_object* v_rhsArgs_2808_, lean_object* v_a_2809_, lean_object* v_ys_2810_, uint8_t v___x_2811_, uint8_t v___x_2812_, uint8_t v___x_2813_, lean_object* v_matchDeclName_2814_, lean_object* v___x_2815_, lean_object* v___x_2816_, lean_object* v___x_2817_, lean_object* v___x_2818_, lean_object* v___x_2819_, lean_object* v_argMask_2820_, lean_object* v_a_2821_, lean_object* v_alts_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2828_ = lean_array_get_borrowed(v___x_2800_, v_alts_2822_, v_a_2801_);
v___x_2829_ = l_Lean_ConstantInfo_name(v_a_2802_);
v___x_2830_ = l_Lean_mkConst(v___x_2829_, v___x_2803_);
v___x_2831_ = l_Subarray_copy___redArg(v___x_2804_);
v___x_2832_ = lean_mk_empty_array_with_capacity(v___x_2805_);
v___x_2833_ = lean_array_push(v___x_2832_, v___x_2806_);
v___x_2834_ = l_Array_append___redArg(v___x_2831_, v___x_2833_);
lean_dec_ref(v___x_2833_);
lean_inc_ref(v___x_2834_);
v___x_2835_ = l_Array_append___redArg(v___x_2834_, v___x_2807_);
v___x_2836_ = l_Array_append___redArg(v___x_2835_, v_alts_2822_);
v___x_2837_ = l_Lean_mkAppN(v___x_2830_, v___x_2836_);
lean_dec_ref(v___x_2836_);
lean_inc(v___x_2828_);
v___x_2838_ = l_Lean_mkAppN(v___x_2828_, v_rhsArgs_2808_);
v___x_2839_ = l_Lean_Meta_mkEq(v___x_2837_, v___x_2838_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2841_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
lean_dec_ref_known(v___x_2839_, 1);
v___x_2841_ = l_Lean_mkArrowN(v_a_2809_, v_a_2840_, v___y_2825_, v___y_2826_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2842_);
lean_dec_ref_known(v___x_2841_, 1);
v___x_2843_ = l_Array_append___redArg(v___x_2834_, v_ys_2810_);
v___x_2844_ = l_Array_append___redArg(v___x_2843_, v_alts_2822_);
v___x_2845_ = l_Lean_Meta_mkForallFVars(v___x_2844_, v_a_2842_, v___x_2811_, v___x_2812_, v___x_2812_, v___x_2813_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
lean_dec_ref(v___x_2844_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v_a_2846_; lean_object* v___x_2847_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
lean_inc(v_a_2846_);
lean_dec_ref_known(v___x_2845_, 1);
v___x_2847_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_2846_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_a_2848_; lean_object* v___x_2849_; 
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc_n(v_a_2848_, 2);
lean_dec_ref_known(v___x_2847_, 1);
lean_inc(v___x_2815_);
v___x_2849_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2814_, v_a_2848_, v___x_2815_, v___x_2815_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_a_2850_);
lean_dec_ref_known(v___x_2849_, 1);
lean_inc(v___x_2816_);
v___x_2851_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2816_);
lean_ctor_set(v___x_2851_, 1, v___x_2817_);
lean_ctor_set(v___x_2851_, 2, v_a_2848_);
v___x_2852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2816_);
lean_ctor_set(v___x_2852_, 1, v___x_2818_);
v___x_2853_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2851_);
lean_ctor_set(v___x_2853_, 1, v_a_2850_);
lean_ctor_set(v___x_2853_, 2, v___x_2852_);
v___x_2854_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2853_);
v___x_2855_ = l_Lean_addDecl(v___x_2854_, v___x_2811_, v___y_2825_, v___y_2826_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2864_; 
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2864_ == 0)
{
lean_object* v_unused_2865_; 
v_unused_2865_ = lean_ctor_get(v___x_2855_, 0);
lean_dec(v_unused_2865_);
v___x_2857_ = v___x_2855_;
v_isShared_2858_ = v_isSharedCheck_2864_;
goto v_resetjp_2856_;
}
else
{
lean_dec(v___x_2855_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2864_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2862_; 
v___x_2859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2819_);
lean_ctor_set(v___x_2859_, 1, v_argMask_2820_);
v___x_2860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2860_, 0, v_a_2821_);
lean_ctor_set(v___x_2860_, 1, v___x_2859_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 0, v___x_2860_);
v___x_2862_ = v___x_2857_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v___x_2860_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_dec_ref(v_a_2821_);
lean_dec_ref(v_argMask_2820_);
lean_dec_ref(v___x_2819_);
v_a_2866_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2855_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2855_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2821_);
lean_dec_ref(v_argMask_2820_);
lean_dec_ref(v___x_2819_);
lean_dec(v___x_2818_);
lean_dec(v___x_2817_);
lean_dec(v___x_2816_);
v_a_2874_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2849_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2849_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_dec_ref(v_a_2821_);
lean_dec_ref(v_argMask_2820_);
lean_dec_ref(v___x_2819_);
lean_dec(v___x_2818_);
lean_dec(v___x_2817_);
lean_dec(v___x_2816_);
lean_dec(v___x_2815_);
lean_dec(v_matchDeclName_2814_);
v_a_2882_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2847_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2847_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2882_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_dec_ref(v_a_2821_);
lean_dec_ref(v_argMask_2820_);
lean_dec_ref(v___x_2819_);
lean_dec(v___x_2818_);
lean_dec(v___x_2817_);
lean_dec(v___x_2816_);
lean_dec(v___x_2815_);
lean_dec(v_matchDeclName_2814_);
v_a_2890_ = lean_ctor_get(v___x_2845_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2845_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2845_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_dec_ref(v___x_2834_);
lean_dec_ref(v_a_2821_);
lean_dec_ref(v_argMask_2820_);
lean_dec_ref(v___x_2819_);
lean_dec(v___x_2818_);
lean_dec(v___x_2817_);
lean_dec(v___x_2816_);
lean_dec(v___x_2815_);
lean_dec(v_matchDeclName_2814_);
v_a_2898_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2841_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2841_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec_ref(v___x_2834_);
lean_dec_ref(v_a_2821_);
lean_dec_ref(v_argMask_2820_);
lean_dec_ref(v___x_2819_);
lean_dec(v___x_2818_);
lean_dec(v___x_2817_);
lean_dec(v___x_2816_);
lean_dec(v___x_2815_);
lean_dec(v_matchDeclName_2814_);
v_a_2906_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2839_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2839_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_2914_ = _args[0];
lean_object* v_a_2915_ = _args[1];
lean_object* v_a_2916_ = _args[2];
lean_object* v___x_2917_ = _args[3];
lean_object* v___x_2918_ = _args[4];
lean_object* v___x_2919_ = _args[5];
lean_object* v___x_2920_ = _args[6];
lean_object* v___x_2921_ = _args[7];
lean_object* v_rhsArgs_2922_ = _args[8];
lean_object* v_a_2923_ = _args[9];
lean_object* v_ys_2924_ = _args[10];
lean_object* v___x_2925_ = _args[11];
lean_object* v___x_2926_ = _args[12];
lean_object* v___x_2927_ = _args[13];
lean_object* v_matchDeclName_2928_ = _args[14];
lean_object* v___x_2929_ = _args[15];
lean_object* v___x_2930_ = _args[16];
lean_object* v___x_2931_ = _args[17];
lean_object* v___x_2932_ = _args[18];
lean_object* v___x_2933_ = _args[19];
lean_object* v_argMask_2934_ = _args[20];
lean_object* v_a_2935_ = _args[21];
lean_object* v_alts_2936_ = _args[22];
lean_object* v___y_2937_ = _args[23];
lean_object* v___y_2938_ = _args[24];
lean_object* v___y_2939_ = _args[25];
lean_object* v___y_2940_ = _args[26];
lean_object* v___y_2941_ = _args[27];
_start:
{
uint8_t v___x_18956__boxed_2942_; uint8_t v___x_18957__boxed_2943_; uint8_t v___x_18958__boxed_2944_; lean_object* v_res_2945_; 
v___x_18956__boxed_2942_ = lean_unbox(v___x_2925_);
v___x_18957__boxed_2943_ = lean_unbox(v___x_2926_);
v___x_18958__boxed_2944_ = lean_unbox(v___x_2927_);
v_res_2945_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(v___x_2914_, v_a_2915_, v_a_2916_, v___x_2917_, v___x_2918_, v___x_2919_, v___x_2920_, v___x_2921_, v_rhsArgs_2922_, v_a_2923_, v_ys_2924_, v___x_18956__boxed_2942_, v___x_18957__boxed_2943_, v___x_18958__boxed_2944_, v_matchDeclName_2928_, v___x_2929_, v___x_2930_, v___x_2931_, v___x_2932_, v___x_2933_, v_argMask_2934_, v_a_2935_, v_alts_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec_ref(v_alts_2936_);
lean_dec_ref(v_ys_2924_);
lean_dec_ref(v_a_2923_);
lean_dec_ref(v_rhsArgs_2922_);
lean_dec_ref(v___x_2921_);
lean_dec(v___x_2919_);
lean_dec_ref(v_a_2916_);
lean_dec(v_a_2915_);
lean_dec_ref(v___x_2914_);
return v_res_2945_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2946_; lean_object* v_dummy_2947_; 
v___x_2946_ = lean_box(0);
v_dummy_2947_ = l_Lean_Expr_sort___override(v___x_2946_);
return v_dummy_2947_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2951_ = lean_box(0);
v___x_2952_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__2));
v___x_2953_ = l_Lean_mkConst(v___x_2952_, v___x_2951_);
return v___x_2953_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2955_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__4));
v___x_2956_ = l_Lean_stringToMessageData(v___x_2955_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(lean_object* v___x_2957_, lean_object* v_overlaps_2958_, lean_object* v_a_2959_, lean_object* v_fst_2960_, lean_object* v___x_2961_, lean_object* v___x_2962_, lean_object* v___x_2963_, uint8_t v___x_2964_, lean_object* v___x_2965_, lean_object* v_a_2966_, lean_object* v___x_2967_, lean_object* v___x_2968_, lean_object* v___x_2969_, lean_object* v_matchDeclName_2970_, lean_object* v___x_2971_, lean_object* v___x_2972_, lean_object* v___x_2973_, lean_object* v___x_2974_, lean_object* v___x_2975_, lean_object* v_ys_2976_, lean_object* v___eqs_2977_, lean_object* v_rhsArgs_2978_, lean_object* v_argMask_2979_, lean_object* v_altResultType_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_){
_start:
{
lean_object* v_dummy_2986_; lean_object* v_nargs_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; size_t v_sz_2992_; size_t v___x_2993_; lean_object* v___x_2994_; 
v_dummy_2986_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_2987_ = l_Lean_Expr_getAppNumArgs(v_altResultType_2980_);
lean_inc(v_nargs_2987_);
v___x_2988_ = lean_mk_array(v_nargs_2987_, v_dummy_2986_);
v___x_2989_ = lean_nat_sub(v_nargs_2987_, v___x_2957_);
lean_dec(v_nargs_2987_);
v___x_2990_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_altResultType_2980_, v___x_2988_, v___x_2989_);
v___x_2991_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_2958_, v_a_2959_);
v_sz_2992_ = lean_array_size(v___x_2991_);
v___x_2993_ = ((size_t)0ULL);
lean_inc_ref(v___x_2961_);
v___x_2994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(v_fst_2960_, v___x_2990_, v___x_2991_, v_sz_2992_, v___x_2993_, v___x_2961_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_);
lean_dec_ref(v___x_2991_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_2995_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; uint8_t v___y_3001_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; uint8_t v___y_3049_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v_options_3060_; uint8_t v_hasTrace_3061_; 
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
lean_inc(v_a_2995_);
lean_dec_ref_known(v___x_2994_, 1);
v_options_3060_ = lean_ctor_get(v___y_2983_, 2);
v_hasTrace_3061_ = lean_ctor_get_uint8(v_options_3060_, sizeof(void*)*1);
if (v_hasTrace_3061_ == 0)
{
v___y_3052_ = v___y_2981_;
v___y_3053_ = v___y_2982_;
v___y_3054_ = v___y_2983_;
v___y_3055_ = v___y_2984_;
goto v___jp_3051_;
}
else
{
lean_object* v_inheritedTraceOptions_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; uint8_t v___x_3065_; 
v_inheritedTraceOptions_3062_ = lean_ctor_get(v___y_2983_, 13);
v___x_3063_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_3064_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_3065_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3062_, v_options_3060_, v___x_3064_);
if (v___x_3065_ == 0)
{
v___y_3052_ = v___y_2981_;
v___y_3053_ = v___y_2982_;
v___y_3054_ = v___y_2983_;
v___y_3055_ = v___y_2984_;
goto v___jp_3051_;
}
else
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3066_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_2995_);
v___x_3067_ = lean_array_to_list(v_a_2995_);
v___x_3068_ = lean_box(0);
v___x_3069_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_3067_, v___x_3068_);
v___x_3070_ = l_Lean_MessageData_ofList(v___x_3069_);
v___x_3071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3066_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
v___x_3072_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_3063_, v___x_3071_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_dec_ref_known(v___x_3072_, 1);
v___y_3052_ = v___y_2981_;
v___y_3053_ = v___y_2982_;
v___y_3054_ = v___y_2983_;
v___y_3055_ = v___y_2984_;
goto v___jp_3051_;
}
else
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3080_; 
lean_dec(v_a_2995_);
lean_dec_ref(v___x_2990_);
lean_dec_ref(v_argMask_2979_);
lean_dec_ref(v_rhsArgs_2978_);
lean_dec_ref(v_ys_2976_);
lean_dec_ref(v___x_2974_);
lean_dec(v___x_2973_);
lean_dec(v___x_2972_);
lean_dec(v___x_2971_);
lean_dec(v_matchDeclName_2970_);
lean_dec_ref(v___x_2969_);
lean_dec_ref(v___x_2968_);
lean_dec(v___x_2967_);
lean_dec_ref(v_a_2966_);
lean_dec_ref(v___x_2965_);
lean_dec_ref(v___x_2963_);
lean_dec(v___x_2962_);
lean_dec_ref(v___x_2961_);
lean_dec(v_a_2959_);
lean_dec(v___x_2957_);
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3075_ = v___x_3072_;
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3072_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3078_; 
if (v_isShared_3076_ == 0)
{
v___x_3078_ = v___x_3075_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3073_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
}
}
v___jp_2996_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; size_t v_sz_3009_; lean_object* v___x_3010_; 
v___x_3002_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
lean_inc_ref(v___x_2990_);
v___x_3003_ = l_Array_reverse___redArg(v___x_2990_);
v___x_3004_ = lean_array_get_size(v___x_3003_);
lean_inc(v___x_2962_);
v___x_3005_ = l_Array_toSubarray___redArg(v___x_3003_, v___x_2962_, v___x_3004_);
lean_inc_ref(v___x_2963_);
v___x_3006_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_2963_, v___x_2961_);
v___x_3007_ = l_Array_reverse___redArg(v___x_3006_);
v___x_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3002_);
lean_ctor_set(v___x_3008_, 1, v___x_3005_);
v_sz_3009_ = lean_array_size(v___x_3007_);
v___x_3010_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_3007_, v_sz_3009_, v___x_2993_, v___x_3008_, v___y_2997_, v___y_3000_, v___y_2998_, v___y_2999_);
lean_dec_ref(v___x_3007_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v_fst_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; uint8_t v___x_3016_; lean_object* v___x_3017_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref_known(v___x_3010_, 1);
v_fst_3012_ = lean_ctor_get(v_a_3011_, 0);
lean_inc(v_fst_3012_);
lean_dec(v_a_3011_);
v___x_3013_ = l_Subarray_copy___redArg(v___x_2963_);
lean_inc_ref(v___x_3013_);
v___x_3014_ = l_Array_append___redArg(v___x_3013_, v_ys_2976_);
v___x_3015_ = 0;
v___x_3016_ = 1;
v___x_3017_ = l_Lean_Meta_mkForallFVars(v___x_3014_, v_fst_3012_, v___x_3015_, v___x_2964_, v___x_2964_, v___x_3016_, v___y_2997_, v___y_3000_, v___y_2998_, v___y_2999_);
lean_dec_ref(v___x_3014_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___f_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref_known(v___x_3017_, 1);
v___x_3019_ = lean_array_get_size(v_ys_2976_);
v___x_3020_ = lean_array_get_size(v_a_2995_);
v___x_3021_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3021_, 0, v___x_3019_);
lean_ctor_set(v___x_3021_, 1, v___x_3020_);
lean_ctor_set_uint8(v___x_3021_, sizeof(void*)*2, v___y_3001_);
v___x_3022_ = lean_box(v___x_3015_);
v___x_3023_ = lean_box(v___x_2964_);
v___x_3024_ = lean_box(v___x_3016_);
lean_inc_ref(v___x_2990_);
v___f_3025_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0___boxed), 28, 22);
lean_closure_set(v___f_3025_, 0, v___x_2965_);
lean_closure_set(v___f_3025_, 1, v_a_2959_);
lean_closure_set(v___f_3025_, 2, v_a_2966_);
lean_closure_set(v___f_3025_, 3, v___x_2967_);
lean_closure_set(v___f_3025_, 4, v___x_2968_);
lean_closure_set(v___f_3025_, 5, v___x_2957_);
lean_closure_set(v___f_3025_, 6, v___x_2969_);
lean_closure_set(v___f_3025_, 7, v___x_2990_);
lean_closure_set(v___f_3025_, 8, v_rhsArgs_2978_);
lean_closure_set(v___f_3025_, 9, v_a_2995_);
lean_closure_set(v___f_3025_, 10, v_ys_2976_);
lean_closure_set(v___f_3025_, 11, v___x_3022_);
lean_closure_set(v___f_3025_, 12, v___x_3023_);
lean_closure_set(v___f_3025_, 13, v___x_3024_);
lean_closure_set(v___f_3025_, 14, v_matchDeclName_2970_);
lean_closure_set(v___f_3025_, 15, v___x_2962_);
lean_closure_set(v___f_3025_, 16, v___x_2971_);
lean_closure_set(v___f_3025_, 17, v___x_2972_);
lean_closure_set(v___f_3025_, 18, v___x_2973_);
lean_closure_set(v___f_3025_, 19, v___x_3021_);
lean_closure_set(v___f_3025_, 20, v_argMask_2979_);
lean_closure_set(v___f_3025_, 21, v_a_3018_);
v___x_3026_ = l_Subarray_copy___redArg(v___x_2974_);
v___x_3027_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v___x_2975_, v___x_3013_, v___x_2990_, v___x_3026_, v___f_3025_, v___y_2997_, v___y_3000_, v___y_2998_, v___y_2999_);
return v___x_3027_;
}
else
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
lean_dec_ref(v___x_3013_);
lean_dec(v_a_2995_);
lean_dec_ref(v___x_2990_);
lean_dec_ref(v_argMask_2979_);
lean_dec_ref(v_rhsArgs_2978_);
lean_dec_ref(v_ys_2976_);
lean_dec_ref(v___x_2974_);
lean_dec(v___x_2973_);
lean_dec(v___x_2972_);
lean_dec(v___x_2971_);
lean_dec(v_matchDeclName_2970_);
lean_dec_ref(v___x_2969_);
lean_dec_ref(v___x_2968_);
lean_dec(v___x_2967_);
lean_dec_ref(v_a_2966_);
lean_dec_ref(v___x_2965_);
lean_dec(v___x_2962_);
lean_dec(v_a_2959_);
lean_dec(v___x_2957_);
v_a_3028_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_3017_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_3017_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_dec(v_a_2995_);
lean_dec_ref(v___x_2990_);
lean_dec_ref(v_argMask_2979_);
lean_dec_ref(v_rhsArgs_2978_);
lean_dec_ref(v_ys_2976_);
lean_dec_ref(v___x_2974_);
lean_dec(v___x_2973_);
lean_dec(v___x_2972_);
lean_dec(v___x_2971_);
lean_dec(v_matchDeclName_2970_);
lean_dec_ref(v___x_2969_);
lean_dec_ref(v___x_2968_);
lean_dec(v___x_2967_);
lean_dec_ref(v_a_2966_);
lean_dec_ref(v___x_2965_);
lean_dec_ref(v___x_2963_);
lean_dec(v___x_2962_);
lean_dec(v_a_2959_);
lean_dec(v___x_2957_);
v_a_3036_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_3010_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3010_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
v___jp_3044_:
{
if (v___y_3049_ == 0)
{
v___y_2997_ = v___y_3045_;
v___y_2998_ = v___y_3046_;
v___y_2999_ = v___y_3047_;
v___y_3000_ = v___y_3048_;
v___y_3001_ = v___y_3049_;
goto v___jp_2996_;
}
else
{
uint8_t v___x_3050_; 
v___x_3050_ = lean_nat_dec_eq(v___x_2975_, v___x_2962_);
v___y_2997_ = v___y_3045_;
v___y_2998_ = v___y_3046_;
v___y_2999_ = v___y_3047_;
v___y_3000_ = v___y_3048_;
v___y_3001_ = v___x_3050_;
goto v___jp_2996_;
}
}
v___jp_3051_:
{
lean_object* v___x_3056_; uint8_t v___x_3057_; 
v___x_3056_ = lean_array_get_size(v_ys_2976_);
v___x_3057_ = lean_nat_dec_eq(v___x_3056_, v___x_2962_);
if (v___x_3057_ == 0)
{
v___y_3045_ = v___y_3052_;
v___y_3046_ = v___y_3054_;
v___y_3047_ = v___y_3055_;
v___y_3048_ = v___y_3053_;
v___y_3049_ = v___x_3057_;
goto v___jp_3044_;
}
else
{
lean_object* v___x_3058_; uint8_t v___x_3059_; 
v___x_3058_ = lean_array_get_size(v_a_2995_);
v___x_3059_ = lean_nat_dec_eq(v___x_3058_, v___x_2962_);
v___y_3045_ = v___y_3052_;
v___y_3046_ = v___y_3054_;
v___y_3047_ = v___y_3055_;
v___y_3048_ = v___y_3053_;
v___y_3049_ = v___x_3059_;
goto v___jp_3044_;
}
}
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_dec_ref(v___x_2990_);
lean_dec_ref(v_argMask_2979_);
lean_dec_ref(v_rhsArgs_2978_);
lean_dec_ref(v_ys_2976_);
lean_dec_ref(v___x_2974_);
lean_dec(v___x_2973_);
lean_dec(v___x_2972_);
lean_dec(v___x_2971_);
lean_dec(v_matchDeclName_2970_);
lean_dec_ref(v___x_2969_);
lean_dec_ref(v___x_2968_);
lean_dec(v___x_2967_);
lean_dec_ref(v_a_2966_);
lean_dec_ref(v___x_2965_);
lean_dec_ref(v___x_2963_);
lean_dec(v___x_2962_);
lean_dec_ref(v___x_2961_);
lean_dec(v_a_2959_);
lean_dec(v___x_2957_);
v_a_3081_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_2994_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_2994_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_3089_ = _args[0];
lean_object* v_overlaps_3090_ = _args[1];
lean_object* v_a_3091_ = _args[2];
lean_object* v_fst_3092_ = _args[3];
lean_object* v___x_3093_ = _args[4];
lean_object* v___x_3094_ = _args[5];
lean_object* v___x_3095_ = _args[6];
lean_object* v___x_3096_ = _args[7];
lean_object* v___x_3097_ = _args[8];
lean_object* v_a_3098_ = _args[9];
lean_object* v___x_3099_ = _args[10];
lean_object* v___x_3100_ = _args[11];
lean_object* v___x_3101_ = _args[12];
lean_object* v_matchDeclName_3102_ = _args[13];
lean_object* v___x_3103_ = _args[14];
lean_object* v___x_3104_ = _args[15];
lean_object* v___x_3105_ = _args[16];
lean_object* v___x_3106_ = _args[17];
lean_object* v___x_3107_ = _args[18];
lean_object* v_ys_3108_ = _args[19];
lean_object* v___eqs_3109_ = _args[20];
lean_object* v_rhsArgs_3110_ = _args[21];
lean_object* v_argMask_3111_ = _args[22];
lean_object* v_altResultType_3112_ = _args[23];
lean_object* v___y_3113_ = _args[24];
lean_object* v___y_3114_ = _args[25];
lean_object* v___y_3115_ = _args[26];
lean_object* v___y_3116_ = _args[27];
lean_object* v___y_3117_ = _args[28];
_start:
{
uint8_t v___x_19224__boxed_3118_; lean_object* v_res_3119_; 
v___x_19224__boxed_3118_ = lean_unbox(v___x_3096_);
v_res_3119_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(v___x_3089_, v_overlaps_3090_, v_a_3091_, v_fst_3092_, v___x_3093_, v___x_3094_, v___x_3095_, v___x_19224__boxed_3118_, v___x_3097_, v_a_3098_, v___x_3099_, v___x_3100_, v___x_3101_, v_matchDeclName_3102_, v___x_3103_, v___x_3104_, v___x_3105_, v___x_3106_, v___x_3107_, v_ys_3108_, v___eqs_3109_, v_rhsArgs_3110_, v_argMask_3111_, v_altResultType_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec_ref(v___eqs_3109_);
lean_dec(v___x_3107_);
lean_dec(v_fst_3092_);
lean_dec_ref(v_overlaps_3090_);
return v_res_3119_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(lean_object* v_upperBound_3120_, lean_object* v_val_3121_, lean_object* v_baseName_3122_, lean_object* v___x_3123_, lean_object* v_a_3124_, lean_object* v___x_3125_, lean_object* v___x_3126_, lean_object* v___x_3127_, lean_object* v_matchDeclName_3128_, lean_object* v___x_3129_, lean_object* v___x_3130_, lean_object* v___x_3131_, lean_object* v_a_3132_, lean_object* v_b_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_){
_start:
{
uint8_t v___x_3139_; 
v___x_3139_ = lean_nat_dec_lt(v_a_3132_, v_upperBound_3120_);
if (v___x_3139_ == 0)
{
lean_object* v___x_3140_; 
lean_dec(v_a_3132_);
lean_dec(v___x_3131_);
lean_dec_ref(v___x_3130_);
lean_dec(v___x_3129_);
lean_dec(v_matchDeclName_3128_);
lean_dec_ref(v___x_3127_);
lean_dec_ref(v___x_3126_);
lean_dec(v___x_3125_);
lean_dec_ref(v_a_3124_);
lean_dec_ref(v___x_3123_);
lean_dec(v_baseName_3122_);
lean_dec_ref(v_val_3121_);
v___x_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3140_, 0, v_b_3133_);
return v___x_3140_;
}
else
{
lean_object* v_snd_3141_; lean_object* v_snd_3142_; lean_object* v_snd_3143_; lean_object* v_fst_3144_; lean_object* v_fst_3145_; lean_object* v_fst_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3229_; 
v_snd_3141_ = lean_ctor_get(v_b_3133_, 1);
lean_inc(v_snd_3141_);
v_snd_3142_ = lean_ctor_get(v_snd_3141_, 1);
lean_inc(v_snd_3142_);
v_snd_3143_ = lean_ctor_get(v_snd_3142_, 1);
lean_inc(v_snd_3143_);
v_fst_3144_ = lean_ctor_get(v_b_3133_, 0);
lean_inc(v_fst_3144_);
lean_dec_ref(v_b_3133_);
v_fst_3145_ = lean_ctor_get(v_snd_3141_, 0);
lean_inc(v_fst_3145_);
lean_dec(v_snd_3141_);
v_fst_3146_ = lean_ctor_get(v_snd_3142_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v_snd_3142_);
if (v_isSharedCheck_3229_ == 0)
{
lean_object* v_unused_3230_; 
v_unused_3230_ = lean_ctor_get(v_snd_3142_, 1);
lean_dec(v_unused_3230_);
v___x_3148_ = v_snd_3142_;
v_isShared_3149_ = v_isSharedCheck_3229_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_fst_3146_);
lean_dec(v_snd_3142_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3229_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v_fst_3150_; lean_object* v_snd_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3228_; 
v_fst_3150_ = lean_ctor_get(v_snd_3143_, 0);
v_snd_3151_ = lean_ctor_get(v_snd_3143_, 1);
v_isSharedCheck_3228_ = !lean_is_exclusive(v_snd_3143_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3153_ = v_snd_3143_;
v_isShared_3154_ = v_isSharedCheck_3228_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_snd_3151_);
lean_inc(v_fst_3150_);
lean_dec(v_snd_3143_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3228_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v_altInfos_3155_; lean_object* v_overlaps_3156_; lean_object* v_start_3157_; lean_object* v_stop_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___f_3170_; lean_object* v___x_3171_; lean_object* v___y_3173_; lean_object* v___x_3224_; uint8_t v___x_3225_; 
v_altInfos_3155_ = lean_ctor_get(v_val_3121_, 2);
v_overlaps_3156_ = lean_ctor_get(v_val_3121_, 5);
v_start_3157_ = lean_ctor_get(v___x_3130_, 1);
v_stop_3158_ = lean_ctor_get(v___x_3130_, 2);
v___x_3159_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_3160_ = l_Lean_instInhabitedExpr;
v___x_3161_ = lean_unsigned_to_nat(0u);
v___x_3162_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_3163_ = lean_box(0);
v___x_3164_ = lean_unsigned_to_nat(1u);
v___x_3165_ = lean_array_get_borrowed(v___x_3159_, v_altInfos_3155_, v_a_3132_);
v___x_3166_ = l_Lean_Meta_eqnThmSuffixBase;
lean_inc(v_baseName_3122_);
v___x_3167_ = l_Lean_Name_str___override(v_baseName_3122_, v___x_3166_);
lean_inc(v_fst_3146_);
v___x_3168_ = lean_name_append_index_after(v___x_3167_, v_fst_3146_);
v___x_3169_ = lean_box(v___x_3139_);
lean_inc(v___x_3131_);
lean_inc_ref(v___x_3130_);
lean_inc(v___x_3129_);
lean_inc(v___x_3168_);
lean_inc(v_matchDeclName_3128_);
lean_inc_ref(v___x_3127_);
lean_inc_ref(v___x_3126_);
lean_inc(v___x_3125_);
lean_inc_ref(v_a_3124_);
lean_inc_ref(v___x_3123_);
lean_inc(v_fst_3145_);
lean_inc(v_a_3132_);
lean_inc_ref(v_overlaps_3156_);
v___f_3170_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed), 29, 19);
lean_closure_set(v___f_3170_, 0, v___x_3164_);
lean_closure_set(v___f_3170_, 1, v_overlaps_3156_);
lean_closure_set(v___f_3170_, 2, v_a_3132_);
lean_closure_set(v___f_3170_, 3, v_fst_3145_);
lean_closure_set(v___f_3170_, 4, v___x_3162_);
lean_closure_set(v___f_3170_, 5, v___x_3161_);
lean_closure_set(v___f_3170_, 6, v___x_3123_);
lean_closure_set(v___f_3170_, 7, v___x_3169_);
lean_closure_set(v___f_3170_, 8, v___x_3160_);
lean_closure_set(v___f_3170_, 9, v_a_3124_);
lean_closure_set(v___f_3170_, 10, v___x_3125_);
lean_closure_set(v___f_3170_, 11, v___x_3126_);
lean_closure_set(v___f_3170_, 12, v___x_3127_);
lean_closure_set(v___f_3170_, 13, v_matchDeclName_3128_);
lean_closure_set(v___f_3170_, 14, v___x_3168_);
lean_closure_set(v___f_3170_, 15, v___x_3129_);
lean_closure_set(v___f_3170_, 16, v___x_3163_);
lean_closure_set(v___f_3170_, 17, v___x_3130_);
lean_closure_set(v___f_3170_, 18, v___x_3131_);
v___x_3171_ = lean_array_push(v_fst_3144_, v___x_3168_);
v___x_3224_ = lean_nat_sub(v_stop_3158_, v_start_3157_);
v___x_3225_ = lean_nat_dec_lt(v_a_3132_, v___x_3224_);
lean_dec(v___x_3224_);
if (v___x_3225_ == 0)
{
lean_object* v___x_3226_; 
v___x_3226_ = l_outOfBounds___redArg(v___x_3160_);
v___y_3173_ = v___x_3226_;
goto v___jp_3172_;
}
else
{
lean_object* v___x_3227_; 
v___x_3227_ = l_Subarray_get___redArg(v___x_3130_, v_a_3132_);
v___y_3173_ = v___x_3227_;
goto v___jp_3172_;
}
v___jp_3172_:
{
lean_object* v___x_3174_; 
lean_inc(v___y_3137_);
lean_inc_ref(v___y_3136_);
lean_inc(v___y_3135_);
lean_inc_ref(v___y_3134_);
v___x_3174_ = lean_infer_type(v___y_3173_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_object* v_a_3175_; lean_object* v___x_3176_; 
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
lean_inc(v_a_3175_);
lean_dec_ref_known(v___x_3174_, 1);
lean_inc(v___x_3131_);
lean_inc(v___x_3165_);
v___x_3176_ = l_Lean_Meta_Match_forallAltTelescope___redArg(v_a_3175_, v___x_3165_, v___x_3131_, v___f_3170_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v_a_3177_; lean_object* v_snd_3178_; lean_object* v_fst_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3207_; 
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
lean_inc(v_a_3177_);
lean_dec_ref_known(v___x_3176_, 1);
v_snd_3178_ = lean_ctor_get(v_a_3177_, 1);
v_fst_3179_ = lean_ctor_get(v_a_3177_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v_a_3177_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3181_ = v_a_3177_;
v_isShared_3182_ = v_isSharedCheck_3207_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_snd_3178_);
lean_inc(v_fst_3179_);
lean_dec(v_a_3177_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3207_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v_fst_3183_; lean_object* v_snd_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3206_; 
v_fst_3183_ = lean_ctor_get(v_snd_3178_, 0);
v_snd_3184_ = lean_ctor_get(v_snd_3178_, 1);
v_isSharedCheck_3206_ = !lean_is_exclusive(v_snd_3178_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3186_ = v_snd_3178_;
v_isShared_3187_ = v_isSharedCheck_3206_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_snd_3184_);
lean_inc(v_fst_3183_);
lean_dec(v_snd_3178_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3206_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3193_; 
v___x_3188_ = lean_array_push(v_fst_3145_, v_fst_3179_);
v___x_3189_ = lean_array_push(v_fst_3150_, v_fst_3183_);
v___x_3190_ = lean_array_push(v_snd_3151_, v_snd_3184_);
v___x_3191_ = lean_nat_add(v_fst_3146_, v___x_3164_);
lean_dec(v_fst_3146_);
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 1, v___x_3190_);
lean_ctor_set(v___x_3186_, 0, v___x_3189_);
v___x_3193_ = v___x_3186_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3189_);
lean_ctor_set(v_reuseFailAlloc_3205_, 1, v___x_3190_);
v___x_3193_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
lean_object* v___x_3195_; 
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 1, v___x_3193_);
lean_ctor_set(v___x_3181_, 0, v___x_3191_);
v___x_3195_ = v___x_3181_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v___x_3191_);
lean_ctor_set(v_reuseFailAlloc_3204_, 1, v___x_3193_);
v___x_3195_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
lean_object* v___x_3197_; 
if (v_isShared_3154_ == 0)
{
lean_ctor_set(v___x_3153_, 1, v___x_3195_);
lean_ctor_set(v___x_3153_, 0, v___x_3188_);
v___x_3197_ = v___x_3153_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3188_);
lean_ctor_set(v_reuseFailAlloc_3203_, 1, v___x_3195_);
v___x_3197_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
lean_object* v___x_3199_; 
if (v_isShared_3149_ == 0)
{
lean_ctor_set(v___x_3148_, 1, v___x_3197_);
lean_ctor_set(v___x_3148_, 0, v___x_3171_);
v___x_3199_ = v___x_3148_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3171_);
lean_ctor_set(v_reuseFailAlloc_3202_, 1, v___x_3197_);
v___x_3199_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
lean_object* v___x_3200_; 
v___x_3200_ = lean_nat_add(v_a_3132_, v___x_3164_);
lean_dec(v_a_3132_);
v_a_3132_ = v___x_3200_;
v_b_3133_ = v___x_3199_;
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
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
lean_dec_ref(v___x_3171_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_fst_3150_);
lean_del_object(v___x_3148_);
lean_dec(v_fst_3146_);
lean_dec(v_fst_3145_);
lean_dec(v_a_3132_);
lean_dec(v___x_3131_);
lean_dec_ref(v___x_3130_);
lean_dec(v___x_3129_);
lean_dec(v_matchDeclName_3128_);
lean_dec_ref(v___x_3127_);
lean_dec_ref(v___x_3126_);
lean_dec(v___x_3125_);
lean_dec_ref(v_a_3124_);
lean_dec_ref(v___x_3123_);
lean_dec(v_baseName_3122_);
lean_dec_ref(v_val_3121_);
v_a_3208_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_3176_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3176_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_dec_ref(v___x_3171_);
lean_dec_ref(v___f_3170_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_fst_3150_);
lean_del_object(v___x_3148_);
lean_dec(v_fst_3146_);
lean_dec(v_fst_3145_);
lean_dec(v_a_3132_);
lean_dec(v___x_3131_);
lean_dec_ref(v___x_3130_);
lean_dec(v___x_3129_);
lean_dec(v_matchDeclName_3128_);
lean_dec_ref(v___x_3127_);
lean_dec_ref(v___x_3126_);
lean_dec(v___x_3125_);
lean_dec_ref(v_a_3124_);
lean_dec_ref(v___x_3123_);
lean_dec(v_baseName_3122_);
lean_dec_ref(v_val_3121_);
v_a_3216_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3174_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3174_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
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
lean_object* v_upperBound_3231_ = _args[0];
lean_object* v_val_3232_ = _args[1];
lean_object* v_baseName_3233_ = _args[2];
lean_object* v___x_3234_ = _args[3];
lean_object* v_a_3235_ = _args[4];
lean_object* v___x_3236_ = _args[5];
lean_object* v___x_3237_ = _args[6];
lean_object* v___x_3238_ = _args[7];
lean_object* v_matchDeclName_3239_ = _args[8];
lean_object* v___x_3240_ = _args[9];
lean_object* v___x_3241_ = _args[10];
lean_object* v___x_3242_ = _args[11];
lean_object* v_a_3243_ = _args[12];
lean_object* v_b_3244_ = _args[13];
lean_object* v___y_3245_ = _args[14];
lean_object* v___y_3246_ = _args[15];
lean_object* v___y_3247_ = _args[16];
lean_object* v___y_3248_ = _args[17];
lean_object* v___y_3249_ = _args[18];
_start:
{
lean_object* v_res_3250_; 
v_res_3250_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3231_, v_val_3232_, v_baseName_3233_, v___x_3234_, v_a_3235_, v___x_3236_, v___x_3237_, v___x_3238_, v_matchDeclName_3239_, v___x_3240_, v___x_3241_, v___x_3242_, v_a_3243_, v_b_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v_upperBound_3231_);
return v_res_3250_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3254_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__2));
v___x_3255_ = lean_unsigned_to_nat(6u);
v___x_3256_ = lean_unsigned_to_nat(233u);
v___x_3257_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__1));
v___x_3258_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_3259_ = l_mkPanicMessageWithDecl(v___x_3258_, v___x_3257_, v___x_3256_, v___x_3255_, v___x_3254_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(lean_object* v_splitterName_3272_, lean_object* v_matchDeclName_3273_, lean_object* v_numParams_3274_, lean_object* v_val_3275_, lean_object* v___x_3276_, lean_object* v_numDiscrs_3277_, lean_object* v_baseName_3278_, lean_object* v_a_3279_, lean_object* v___x_3280_, lean_object* v___x_3281_, lean_object* v___x_3282_, lean_object* v_uElimPos_x3f_3283_, lean_object* v_discrInfos_3284_, lean_object* v_overlaps_3285_, lean_object* v___f_3286_, lean_object* v___x_3287_, lean_object* v_altInfos_3288_, lean_object* v_xs_3289_, lean_object* v___matchResultType_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; uint8_t v___y_3308_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v_lower_3316_; lean_object* v_upper_3317_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; uint8_t v___x_3373_; 
v___x_3310_ = lean_box(0);
v___x_3311_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3274_);
lean_inc_ref(v_xs_3289_);
v___x_3312_ = l_Array_toSubarray___redArg(v_xs_3289_, v___x_3311_, v_numParams_3274_);
v___x_3313_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_3275_);
v___x_3314_ = lean_array_get(v___x_3276_, v_xs_3289_, v___x_3313_);
lean_dec(v___x_3313_);
v___x_3370_ = lean_array_get_size(v_xs_3289_);
v___x_3371_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_3275_);
v___x_3372_ = lean_nat_sub(v___x_3370_, v___x_3371_);
lean_dec(v___x_3371_);
v___x_3373_ = lean_nat_dec_le(v___x_3372_, v___x_3311_);
if (v___x_3373_ == 0)
{
v_lower_3316_ = v___x_3372_;
v_upper_3317_ = v___x_3370_;
goto v___jp_3315_;
}
else
{
lean_dec(v___x_3372_);
v_lower_3316_ = v___x_3311_;
v_upper_3317_ = v___x_3370_;
goto v___jp_3315_;
}
v___jp_3296_:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3297_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3);
v___x_3298_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v___x_3297_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
return v___x_3298_;
}
v___jp_3299_:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3302_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3302_, 0, v___y_3300_);
lean_ctor_set(v___x_3302_, 1, v_splitterName_3272_);
lean_ctor_set(v___x_3302_, 2, v___y_3301_);
v___x_3303_ = l_Lean_Meta_Match_registerMatchEqns___redArg(v_matchDeclName_3273_, v___x_3302_, v___y_3294_);
return v___x_3303_;
}
v___jp_3304_:
{
lean_object* v___x_3309_; 
lean_inc(v_matchDeclName_3273_);
v___x_3309_ = l_Lean_Meta_Match_withMkMatcherInput___redArg(v_matchDeclName_3273_, v___y_3308_, v___y_3305_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_dec_ref_known(v___x_3309_, 1);
v___y_3300_ = v___y_3306_;
v___y_3301_ = v___y_3307_;
goto v___jp_3299_;
}
else
{
lean_dec_ref(v___y_3307_);
lean_dec(v___y_3306_);
lean_dec(v_matchDeclName_3273_);
lean_dec(v_splitterName_3272_);
return v___x_3309_;
}
}
v___jp_3315_:
{
lean_object* v___x_3318_; lean_object* v_start_3319_; lean_object* v_stop_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
lean_inc_ref(v_xs_3289_);
v___x_3318_ = l_Array_toSubarray___redArg(v_xs_3289_, v_lower_3316_, v_upper_3317_);
v_start_3319_ = lean_ctor_get(v___x_3318_, 1);
lean_inc(v_start_3319_);
v_stop_3320_ = lean_ctor_get(v___x_3318_, 2);
lean_inc(v_stop_3320_);
v___x_3321_ = lean_unsigned_to_nat(1u);
v___x_3322_ = lean_nat_add(v_numParams_3274_, v___x_3321_);
v___x_3323_ = lean_nat_add(v___x_3322_, v_numDiscrs_3277_);
v___x_3324_ = lean_nat_sub(v_stop_3320_, v_start_3319_);
lean_dec(v_start_3319_);
lean_dec(v_stop_3320_);
v___x_3325_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__7));
v___x_3326_ = l_Array_toSubarray___redArg(v_xs_3289_, v___x_3322_, v___x_3323_);
lean_inc(v___x_3281_);
lean_inc(v_matchDeclName_3273_);
lean_inc(v___x_3280_);
v___x_3327_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v___x_3324_, v_val_3275_, v_baseName_3278_, v___x_3326_, v_a_3279_, v___x_3280_, v___x_3312_, v___x_3314_, v_matchDeclName_3273_, v___x_3281_, v___x_3318_, v___x_3282_, v___x_3311_, v___x_3325_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
lean_dec(v___x_3324_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; lean_object* v_snd_3329_; lean_object* v_snd_3330_; lean_object* v_snd_3331_; lean_object* v_fst_3332_; lean_object* v_fst_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3360_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_a_3328_);
lean_dec_ref_known(v___x_3327_, 1);
v_snd_3329_ = lean_ctor_get(v_a_3328_, 1);
v_snd_3330_ = lean_ctor_get(v_snd_3329_, 1);
v_snd_3331_ = lean_ctor_get(v_snd_3330_, 1);
lean_inc(v_snd_3331_);
v_fst_3332_ = lean_ctor_get(v_a_3328_, 0);
lean_inc(v_fst_3332_);
lean_dec(v_a_3328_);
v_fst_3333_ = lean_ctor_get(v_snd_3331_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v_snd_3331_);
if (v_isSharedCheck_3360_ == 0)
{
lean_object* v_unused_3361_; 
v_unused_3361_ = lean_ctor_get(v_snd_3331_, 1);
lean_dec(v_unused_3361_);
v___x_3335_ = v_snd_3331_;
v_isShared_3336_ = v_isSharedCheck_3360_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_fst_3333_);
lean_dec(v_snd_3331_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3360_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3337_; uint8_t v___x_3338_; 
lean_inc_ref(v_overlaps_3285_);
lean_inc(v_fst_3333_);
v___x_3337_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3337_, 0, v_numParams_3274_);
lean_ctor_set(v___x_3337_, 1, v_numDiscrs_3277_);
lean_ctor_set(v___x_3337_, 2, v_fst_3333_);
lean_ctor_set(v___x_3337_, 3, v_uElimPos_x3f_3283_);
lean_ctor_set(v___x_3337_, 4, v_discrInfos_3284_);
lean_ctor_set(v___x_3337_, 5, v_overlaps_3285_);
v___x_3338_ = l_Lean_Meta_Match_Overlaps_isEmpty(v_overlaps_3285_);
lean_dec_ref(v_overlaps_3285_);
if (v___x_3338_ == 0)
{
uint8_t v___x_3339_; 
lean_del_object(v___x_3335_);
lean_dec(v_fst_3333_);
lean_dec_ref(v___x_3287_);
lean_dec(v___x_3281_);
lean_dec(v___x_3280_);
v___x_3339_ = 1;
v___y_3305_ = v___f_3286_;
v___y_3306_ = v_fst_3332_;
v___y_3307_ = v___x_3337_;
v___y_3308_ = v___x_3339_;
goto v___jp_3304_;
}
else
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__8));
v___x_3341_ = lean_find_expr(v___x_3340_, v___x_3287_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v___x_3342_; lean_object* v___x_3343_; uint8_t v___x_3344_; 
lean_dec_ref(v___f_3286_);
v___x_3342_ = lean_array_get_size(v_altInfos_3288_);
v___x_3343_ = lean_array_get_size(v_fst_3333_);
v___x_3344_ = lean_nat_dec_eq(v___x_3342_, v___x_3343_);
if (v___x_3344_ == 0)
{
lean_dec_ref_known(v___x_3337_, 6);
lean_del_object(v___x_3335_);
lean_dec(v_fst_3333_);
lean_dec(v_fst_3332_);
lean_dec_ref(v___x_3287_);
lean_dec(v___x_3281_);
lean_dec(v___x_3280_);
lean_dec(v_matchDeclName_3273_);
lean_dec(v_splitterName_3272_);
goto v___jp_3296_;
}
else
{
uint8_t v___x_3345_; 
v___x_3345_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_altInfos_3288_, v_fst_3333_, v___x_3342_);
lean_dec(v_fst_3333_);
if (v___x_3345_ == 0)
{
lean_dec_ref_known(v___x_3337_, 6);
lean_del_object(v___x_3335_);
lean_dec(v_fst_3332_);
lean_dec_ref(v___x_3287_);
lean_dec(v___x_3281_);
lean_dec(v___x_3280_);
lean_dec(v_matchDeclName_3273_);
lean_dec(v_splitterName_3272_);
goto v___jp_3296_;
}
else
{
uint8_t v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; uint8_t v___x_3350_; lean_object* v___x_3352_; 
v___x_3346_ = 0;
lean_inc_n(v_splitterName_3272_, 2);
v___x_3347_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3347_, 0, v_splitterName_3272_);
lean_ctor_set(v___x_3347_, 1, v___x_3281_);
lean_ctor_set(v___x_3347_, 2, v___x_3287_);
lean_inc(v_matchDeclName_3273_);
v___x_3348_ = l_Lean_mkConst(v_matchDeclName_3273_, v___x_3280_);
v___x_3349_ = lean_box(1);
v___x_3350_ = 1;
if (v_isShared_3336_ == 0)
{
lean_ctor_set_tag(v___x_3335_, 1);
lean_ctor_set(v___x_3335_, 1, v___x_3310_);
lean_ctor_set(v___x_3335_, 0, v_splitterName_3272_);
v___x_3352_ = v___x_3335_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_splitterName_3272_);
lean_ctor_set(v_reuseFailAlloc_3359_, 1, v___x_3310_);
v___x_3352_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3353_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3353_, 0, v___x_3347_);
lean_ctor_set(v___x_3353_, 1, v___x_3348_);
lean_ctor_set(v___x_3353_, 2, v___x_3349_);
lean_ctor_set(v___x_3353_, 3, v___x_3352_);
lean_ctor_set_uint8(v___x_3353_, sizeof(void*)*4, v___x_3350_);
v___x_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3353_);
lean_inc_ref(v___x_3354_);
v___x_3355_ = l_Lean_addDecl(v___x_3354_, v___x_3346_, v___y_3293_, v___y_3294_);
if (lean_obj_tag(v___x_3355_) == 0)
{
uint8_t v___x_3356_; lean_object* v___x_3357_; 
lean_dec_ref_known(v___x_3355_, 1);
v___x_3356_ = 0;
lean_inc(v_splitterName_3272_);
v___x_3357_ = l_Lean_Meta_setInlineAttribute(v_splitterName_3272_, v___x_3356_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v___x_3358_; 
lean_dec_ref_known(v___x_3357_, 1);
v___x_3358_ = l_Lean_compileDecl(v___x_3354_, v___x_3346_, v___y_3293_, v___y_3294_);
if (lean_obj_tag(v___x_3358_) == 0)
{
lean_dec_ref_known(v___x_3358_, 1);
v___y_3300_ = v_fst_3332_;
v___y_3301_ = v___x_3337_;
goto v___jp_3299_;
}
else
{
lean_dec_ref_known(v___x_3337_, 6);
lean_dec(v_fst_3332_);
lean_dec(v_matchDeclName_3273_);
lean_dec(v_splitterName_3272_);
return v___x_3358_;
}
}
else
{
lean_dec_ref_known(v___x_3354_, 1);
lean_dec_ref_known(v___x_3337_, 6);
lean_dec(v_fst_3332_);
lean_dec(v_matchDeclName_3273_);
lean_dec(v_splitterName_3272_);
return v___x_3357_;
}
}
else
{
lean_dec_ref_known(v___x_3354_, 1);
lean_dec_ref_known(v___x_3337_, 6);
lean_dec(v_fst_3332_);
lean_dec(v_matchDeclName_3273_);
lean_dec(v_splitterName_3272_);
return v___x_3355_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_3341_, 1);
lean_del_object(v___x_3335_);
lean_dec(v_fst_3333_);
lean_dec_ref(v___x_3287_);
lean_dec(v___x_3281_);
lean_dec(v___x_3280_);
v___y_3305_ = v___f_3286_;
v___y_3306_ = v_fst_3332_;
v___y_3307_ = v___x_3337_;
v___y_3308_ = v___x_3338_;
goto v___jp_3304_;
}
}
}
}
else
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3369_; 
lean_dec_ref(v___x_3287_);
lean_dec_ref(v___f_3286_);
lean_dec_ref(v_overlaps_3285_);
lean_dec_ref(v_discrInfos_3284_);
lean_dec(v_uElimPos_x3f_3283_);
lean_dec(v___x_3281_);
lean_dec(v___x_3280_);
lean_dec(v_numDiscrs_3277_);
lean_dec(v_numParams_3274_);
lean_dec(v_matchDeclName_3273_);
lean_dec(v_splitterName_3272_);
v_a_3362_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3364_ = v___x_3327_;
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3327_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3362_);
v___x_3367_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3366_;
}
v_reusejp_3366_:
{
return v___x_3367_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed(lean_object** _args){
lean_object* v_splitterName_3374_ = _args[0];
lean_object* v_matchDeclName_3375_ = _args[1];
lean_object* v_numParams_3376_ = _args[2];
lean_object* v_val_3377_ = _args[3];
lean_object* v___x_3378_ = _args[4];
lean_object* v_numDiscrs_3379_ = _args[5];
lean_object* v_baseName_3380_ = _args[6];
lean_object* v_a_3381_ = _args[7];
lean_object* v___x_3382_ = _args[8];
lean_object* v___x_3383_ = _args[9];
lean_object* v___x_3384_ = _args[10];
lean_object* v_uElimPos_x3f_3385_ = _args[11];
lean_object* v_discrInfos_3386_ = _args[12];
lean_object* v_overlaps_3387_ = _args[13];
lean_object* v___f_3388_ = _args[14];
lean_object* v___x_3389_ = _args[15];
lean_object* v_altInfos_3390_ = _args[16];
lean_object* v_xs_3391_ = _args[17];
lean_object* v___matchResultType_3392_ = _args[18];
lean_object* v___y_3393_ = _args[19];
lean_object* v___y_3394_ = _args[20];
lean_object* v___y_3395_ = _args[21];
lean_object* v___y_3396_ = _args[22];
lean_object* v___y_3397_ = _args[23];
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(v_splitterName_3374_, v_matchDeclName_3375_, v_numParams_3376_, v_val_3377_, v___x_3378_, v_numDiscrs_3379_, v_baseName_3380_, v_a_3381_, v___x_3382_, v___x_3383_, v___x_3384_, v_uElimPos_x3f_3385_, v_discrInfos_3386_, v_overlaps_3387_, v___f_3388_, v___x_3389_, v_altInfos_3390_, v_xs_3391_, v___matchResultType_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec_ref(v___matchResultType_3392_);
lean_dec_ref(v_altInfos_3390_);
lean_dec_ref(v___x_3378_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(lean_object* v_a_3399_, lean_object* v_a_3400_){
_start:
{
if (lean_obj_tag(v_a_3399_) == 0)
{
lean_object* v___x_3401_; 
v___x_3401_ = l_List_reverse___redArg(v_a_3400_);
return v___x_3401_;
}
else
{
lean_object* v_head_3402_; lean_object* v_tail_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3412_; 
v_head_3402_ = lean_ctor_get(v_a_3399_, 0);
v_tail_3403_ = lean_ctor_get(v_a_3399_, 1);
v_isSharedCheck_3412_ = !lean_is_exclusive(v_a_3399_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3405_ = v_a_3399_;
v_isShared_3406_ = v_isSharedCheck_3412_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_tail_3403_);
lean_inc(v_head_3402_);
lean_dec(v_a_3399_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3412_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3407_; lean_object* v___x_3409_; 
v___x_3407_ = l_Lean_mkLevelParam(v_head_3402_);
if (v_isShared_3406_ == 0)
{
lean_ctor_set(v___x_3405_, 1, v_a_3400_);
lean_ctor_set(v___x_3405_, 0, v___x_3407_);
v___x_3409_ = v___x_3405_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v___x_3407_);
lean_ctor_set(v_reuseFailAlloc_3411_, 1, v_a_3400_);
v___x_3409_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
v_a_3399_ = v_tail_3403_;
v_a_3400_ = v___x_3409_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_3413_; 
v___x_3413_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3413_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3414_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_3415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3414_);
return v___x_3415_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3416_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_3417_ = lean_unsigned_to_nat(0u);
v___x_3418_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3417_);
lean_ctor_set(v___x_3418_, 1, v___x_3417_);
lean_ctor_set(v___x_3418_, 2, v___x_3417_);
lean_ctor_set(v___x_3418_, 3, v___x_3417_);
lean_ctor_set(v___x_3418_, 4, v___x_3416_);
lean_ctor_set(v___x_3418_, 5, v___x_3416_);
lean_ctor_set(v___x_3418_, 6, v___x_3416_);
lean_ctor_set(v___x_3418_, 7, v___x_3416_);
lean_ctor_set(v___x_3418_, 8, v___x_3416_);
lean_ctor_set(v___x_3418_, 9, v___x_3416_);
lean_ctor_set(v___x_3418_, 10, v___x_3416_);
return v___x_3418_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3419_ = lean_box(1);
v___x_3420_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_3421_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_3422_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3421_);
lean_ctor_set(v___x_3422_, 1, v___x_3420_);
lean_ctor_set(v___x_3422_, 2, v___x_3419_);
return v___x_3422_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3424_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4));
v___x_3425_ = l_Lean_stringToMessageData(v___x_3424_);
return v___x_3425_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3427_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_3428_ = l_Lean_stringToMessageData(v___x_3427_);
return v___x_3428_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3430_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_3431_ = l_Lean_stringToMessageData(v___x_3430_);
return v___x_3431_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3433_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_3434_ = l_Lean_stringToMessageData(v___x_3433_);
return v___x_3434_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3436_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_3437_ = l_Lean_stringToMessageData(v___x_3436_);
return v___x_3437_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3439_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_3440_ = l_Lean_stringToMessageData(v___x_3439_);
return v___x_3440_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3442_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_3443_ = l_Lean_stringToMessageData(v___x_3442_);
return v___x_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_3444_, lean_object* v_declHint_3445_, lean_object* v___y_3446_){
_start:
{
lean_object* v___x_3448_; lean_object* v_env_3449_; uint8_t v___x_3450_; 
v___x_3448_ = lean_st_ref_get(v___y_3446_);
v_env_3449_ = lean_ctor_get(v___x_3448_, 0);
lean_inc_ref(v_env_3449_);
lean_dec(v___x_3448_);
v___x_3450_ = l_Lean_Name_isAnonymous(v_declHint_3445_);
if (v___x_3450_ == 0)
{
uint8_t v_isExporting_3451_; 
v_isExporting_3451_ = lean_ctor_get_uint8(v_env_3449_, sizeof(void*)*8);
if (v_isExporting_3451_ == 0)
{
lean_object* v___x_3452_; 
lean_dec_ref(v_env_3449_);
lean_dec(v_declHint_3445_);
v___x_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3452_, 0, v_msg_3444_);
return v___x_3452_;
}
else
{
lean_object* v___x_3453_; uint8_t v___x_3454_; 
lean_inc_ref(v_env_3449_);
v___x_3453_ = l_Lean_Environment_setExporting(v_env_3449_, v___x_3450_);
lean_inc(v_declHint_3445_);
lean_inc_ref(v___x_3453_);
v___x_3454_ = l_Lean_Environment_contains(v___x_3453_, v_declHint_3445_, v_isExporting_3451_);
if (v___x_3454_ == 0)
{
lean_object* v___x_3455_; 
lean_dec_ref(v___x_3453_);
lean_dec_ref(v_env_3449_);
lean_dec(v_declHint_3445_);
v___x_3455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3455_, 0, v_msg_3444_);
return v___x_3455_;
}
else
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v_c_3461_; lean_object* v___x_3462_; 
v___x_3456_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_3457_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_3458_ = l_Lean_Options_empty;
v___x_3459_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3453_);
lean_ctor_set(v___x_3459_, 1, v___x_3456_);
lean_ctor_set(v___x_3459_, 2, v___x_3457_);
lean_ctor_set(v___x_3459_, 3, v___x_3458_);
lean_inc(v_declHint_3445_);
v___x_3460_ = l_Lean_MessageData_ofConstName(v_declHint_3445_, v___x_3450_);
v_c_3461_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3461_, 0, v___x_3459_);
lean_ctor_set(v_c_3461_, 1, v___x_3460_);
v___x_3462_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3449_, v_declHint_3445_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
lean_dec_ref(v_env_3449_);
lean_dec(v_declHint_3445_);
v___x_3463_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_3464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3463_);
lean_ctor_set(v___x_3464_, 1, v_c_3461_);
v___x_3465_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_3466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3464_);
lean_ctor_set(v___x_3466_, 1, v___x_3465_);
v___x_3467_ = l_Lean_MessageData_note(v___x_3466_);
v___x_3468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3468_, 0, v_msg_3444_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
v___x_3469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
return v___x_3469_;
}
else
{
lean_object* v_val_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3505_; 
v_val_3470_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3472_ = v___x_3462_;
v_isShared_3473_ = v_isSharedCheck_3505_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_val_3470_);
lean_dec(v___x_3462_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3505_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v_mod_3477_; uint8_t v___x_3478_; 
v___x_3474_ = lean_box(0);
v___x_3475_ = l_Lean_Environment_header(v_env_3449_);
lean_dec_ref(v_env_3449_);
v___x_3476_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3475_);
v_mod_3477_ = lean_array_get(v___x_3474_, v___x_3476_, v_val_3470_);
lean_dec(v_val_3470_);
lean_dec_ref(v___x_3476_);
v___x_3478_ = l_Lean_isPrivateName(v_declHint_3445_);
lean_dec(v_declHint_3445_);
if (v___x_3478_ == 0)
{
lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3490_; 
v___x_3479_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_3480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3479_);
lean_ctor_set(v___x_3480_, 1, v_c_3461_);
v___x_3481_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_3482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3480_);
lean_ctor_set(v___x_3482_, 1, v___x_3481_);
v___x_3483_ = l_Lean_MessageData_ofName(v_mod_3477_);
v___x_3484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3482_);
lean_ctor_set(v___x_3484_, 1, v___x_3483_);
v___x_3485_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_3486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3484_);
lean_ctor_set(v___x_3486_, 1, v___x_3485_);
v___x_3487_ = l_Lean_MessageData_note(v___x_3486_);
v___x_3488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3488_, 0, v_msg_3444_);
lean_ctor_set(v___x_3488_, 1, v___x_3487_);
if (v_isShared_3473_ == 0)
{
lean_ctor_set_tag(v___x_3472_, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3488_);
v___x_3490_ = v___x_3472_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3488_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
else
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3503_; 
v___x_3492_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_3493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3492_);
lean_ctor_set(v___x_3493_, 1, v_c_3461_);
v___x_3494_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_3495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3493_);
lean_ctor_set(v___x_3495_, 1, v___x_3494_);
v___x_3496_ = l_Lean_MessageData_ofName(v_mod_3477_);
v___x_3497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3495_);
lean_ctor_set(v___x_3497_, 1, v___x_3496_);
v___x_3498_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_3499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3499_, 0, v___x_3497_);
lean_ctor_set(v___x_3499_, 1, v___x_3498_);
v___x_3500_ = l_Lean_MessageData_note(v___x_3499_);
v___x_3501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3501_, 0, v_msg_3444_);
lean_ctor_set(v___x_3501_, 1, v___x_3500_);
if (v_isShared_3473_ == 0)
{
lean_ctor_set_tag(v___x_3472_, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3501_);
v___x_3503_ = v___x_3472_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v___x_3501_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3506_; 
lean_dec_ref(v_env_3449_);
lean_dec(v_declHint_3445_);
v___x_3506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3506_, 0, v_msg_3444_);
return v___x_3506_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_3507_, lean_object* v_declHint_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3507_, v_declHint_3508_, v___y_3509_);
lean_dec(v___y_3509_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(lean_object* v_msg_3512_, lean_object* v_declHint_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v___x_3519_; lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3529_; 
v___x_3519_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3512_, v_declHint_3513_, v___y_3517_);
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3522_ = v___x_3519_;
v_isShared_3523_ = v_isSharedCheck_3529_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3519_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3529_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3527_; 
v___x_3524_ = l_Lean_unknownIdentifierMessageTag;
v___x_3525_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3524_);
lean_ctor_set(v___x_3525_, 1, v_a_3520_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3525_);
v___x_3527_ = v___x_3522_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3525_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12___boxed(lean_object* v_msg_3530_, lean_object* v_declHint_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
lean_object* v_res_3537_; 
v_res_3537_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3530_, v_declHint_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(lean_object* v_ref_3538_, lean_object* v_msg_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v_fileName_3545_; lean_object* v_fileMap_3546_; lean_object* v_options_3547_; lean_object* v_currRecDepth_3548_; lean_object* v_maxRecDepth_3549_; lean_object* v_ref_3550_; lean_object* v_currNamespace_3551_; lean_object* v_openDecls_3552_; lean_object* v_initHeartbeats_3553_; lean_object* v_maxHeartbeats_3554_; lean_object* v_quotContext_3555_; lean_object* v_currMacroScope_3556_; uint8_t v_diag_3557_; lean_object* v_cancelTk_x3f_3558_; uint8_t v_suppressElabErrors_3559_; lean_object* v_inheritedTraceOptions_3560_; lean_object* v_ref_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v_fileName_3545_ = lean_ctor_get(v___y_3542_, 0);
v_fileMap_3546_ = lean_ctor_get(v___y_3542_, 1);
v_options_3547_ = lean_ctor_get(v___y_3542_, 2);
v_currRecDepth_3548_ = lean_ctor_get(v___y_3542_, 3);
v_maxRecDepth_3549_ = lean_ctor_get(v___y_3542_, 4);
v_ref_3550_ = lean_ctor_get(v___y_3542_, 5);
v_currNamespace_3551_ = lean_ctor_get(v___y_3542_, 6);
v_openDecls_3552_ = lean_ctor_get(v___y_3542_, 7);
v_initHeartbeats_3553_ = lean_ctor_get(v___y_3542_, 8);
v_maxHeartbeats_3554_ = lean_ctor_get(v___y_3542_, 9);
v_quotContext_3555_ = lean_ctor_get(v___y_3542_, 10);
v_currMacroScope_3556_ = lean_ctor_get(v___y_3542_, 11);
v_diag_3557_ = lean_ctor_get_uint8(v___y_3542_, sizeof(void*)*14);
v_cancelTk_x3f_3558_ = lean_ctor_get(v___y_3542_, 12);
v_suppressElabErrors_3559_ = lean_ctor_get_uint8(v___y_3542_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3560_ = lean_ctor_get(v___y_3542_, 13);
v_ref_3561_ = l_Lean_replaceRef(v_ref_3538_, v_ref_3550_);
lean_inc_ref(v_inheritedTraceOptions_3560_);
lean_inc(v_cancelTk_x3f_3558_);
lean_inc(v_currMacroScope_3556_);
lean_inc(v_quotContext_3555_);
lean_inc(v_maxHeartbeats_3554_);
lean_inc(v_initHeartbeats_3553_);
lean_inc(v_openDecls_3552_);
lean_inc(v_currNamespace_3551_);
lean_inc(v_maxRecDepth_3549_);
lean_inc(v_currRecDepth_3548_);
lean_inc_ref(v_options_3547_);
lean_inc_ref(v_fileMap_3546_);
lean_inc_ref(v_fileName_3545_);
v___x_3562_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3562_, 0, v_fileName_3545_);
lean_ctor_set(v___x_3562_, 1, v_fileMap_3546_);
lean_ctor_set(v___x_3562_, 2, v_options_3547_);
lean_ctor_set(v___x_3562_, 3, v_currRecDepth_3548_);
lean_ctor_set(v___x_3562_, 4, v_maxRecDepth_3549_);
lean_ctor_set(v___x_3562_, 5, v_ref_3561_);
lean_ctor_set(v___x_3562_, 6, v_currNamespace_3551_);
lean_ctor_set(v___x_3562_, 7, v_openDecls_3552_);
lean_ctor_set(v___x_3562_, 8, v_initHeartbeats_3553_);
lean_ctor_set(v___x_3562_, 9, v_maxHeartbeats_3554_);
lean_ctor_set(v___x_3562_, 10, v_quotContext_3555_);
lean_ctor_set(v___x_3562_, 11, v_currMacroScope_3556_);
lean_ctor_set(v___x_3562_, 12, v_cancelTk_x3f_3558_);
lean_ctor_set(v___x_3562_, 13, v_inheritedTraceOptions_3560_);
lean_ctor_set_uint8(v___x_3562_, sizeof(void*)*14, v_diag_3557_);
lean_ctor_set_uint8(v___x_3562_, sizeof(void*)*14 + 1, v_suppressElabErrors_3559_);
v___x_3563_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v_msg_3539_, v___y_3540_, v___y_3541_, v___x_3562_, v___y_3543_);
lean_dec_ref_known(v___x_3562_, 14);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg___boxed(lean_object* v_ref_3564_, lean_object* v_msg_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_){
_start:
{
lean_object* v_res_3571_; 
v_res_3571_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3564_, v_msg_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec(v_ref_3564_);
return v_res_3571_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(lean_object* v_ref_3572_, lean_object* v_msg_3573_, lean_object* v_declHint_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_){
_start:
{
lean_object* v___x_3580_; lean_object* v_a_3581_; lean_object* v___x_3582_; 
v___x_3580_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3573_, v_declHint_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_);
v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
lean_inc(v_a_3581_);
lean_dec_ref(v___x_3580_);
v___x_3582_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3572_, v_a_3581_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object* v_ref_3583_, lean_object* v_msg_3584_, lean_object* v_declHint_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
lean_object* v_res_3591_; 
v_res_3591_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3583_, v_msg_3584_, v_declHint_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec(v_ref_3583_);
return v_res_3591_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3593_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_3594_ = l_Lean_stringToMessageData(v___x_3593_);
return v___x_3594_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3596_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_3597_ = l_Lean_stringToMessageData(v___x_3596_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_3598_, lean_object* v_constName_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v___x_3605_; uint8_t v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; 
v___x_3605_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_3606_ = 0;
lean_inc(v_constName_3599_);
v___x_3607_ = l_Lean_MessageData_ofConstName(v_constName_3599_, v___x_3606_);
v___x_3608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3605_);
lean_ctor_set(v___x_3608_, 1, v___x_3607_);
v___x_3609_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3608_);
lean_ctor_set(v___x_3610_, 1, v___x_3609_);
v___x_3611_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3598_, v___x_3610_, v_constName_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_3612_, lean_object* v_constName_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3612_, v_constName_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v_ref_3612_);
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(lean_object* v_constName_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
lean_object* v_ref_3626_; lean_object* v___x_3627_; 
v_ref_3626_ = lean_ctor_get(v___y_3623_, 5);
v___x_3627_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3626_, v_constName_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v_res_3634_; 
v_res_3634_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(lean_object* v_constName_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
lean_object* v___x_3641_; lean_object* v_env_3642_; uint8_t v___x_3643_; lean_object* v___x_3644_; 
v___x_3641_ = lean_st_ref_get(v___y_3639_);
v_env_3642_ = lean_ctor_get(v___x_3641_, 0);
lean_inc_ref(v_env_3642_);
lean_dec(v___x_3641_);
v___x_3643_ = 0;
lean_inc(v_constName_3635_);
v___x_3644_ = l_Lean_Environment_find_x3f(v_env_3642_, v_constName_3635_, v___x_3643_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v___x_3645_; 
v___x_3645_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_);
return v___x_3645_;
}
else
{
lean_object* v_val_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3653_; 
lean_dec(v_constName_3635_);
v_val_3646_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3648_ = v___x_3644_;
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_val_3646_);
lean_dec(v___x_3644_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3651_; 
if (v_isShared_3649_ == 0)
{
lean_ctor_set_tag(v___x_3648_, 0);
v___x_3651_ = v___x_3648_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_val_3646_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0___boxed(lean_object* v_constName_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
lean_object* v_res_3660_; 
v_res_3660_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_constName_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
lean_dec(v___y_3658_);
lean_dec_ref(v___y_3657_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
return v_res_3660_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1(void){
_start:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3662_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__0));
v___x_3663_ = l_Lean_stringToMessageData(v___x_3662_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(lean_object* v_matchDeclName_3664_, lean_object* v_baseName_3665_, lean_object* v_splitterName_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_){
_start:
{
lean_object* v___x_3672_; uint8_t v_foApprox_3673_; uint8_t v_ctxApprox_3674_; uint8_t v_quasiPatternApprox_3675_; uint8_t v_constApprox_3676_; uint8_t v_isDefEqStuckEx_3677_; uint8_t v_unificationHints_3678_; uint8_t v_proofIrrelevance_3679_; uint8_t v_assignSyntheticOpaque_3680_; uint8_t v_offsetCnstrs_3681_; uint8_t v_transparency_3682_; uint8_t v_univApprox_3683_; uint8_t v_iota_3684_; uint8_t v_beta_3685_; uint8_t v_proj_3686_; uint8_t v_zeta_3687_; uint8_t v_zetaDelta_3688_; uint8_t v_zetaUnused_3689_; uint8_t v_zetaHave_3690_; uint8_t v_canUnfoldPredicateConfig_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3754_; 
v___x_3672_ = l_Lean_Meta_Context_config(v_a_3667_);
v_foApprox_3673_ = lean_ctor_get_uint8(v___x_3672_, 0);
v_ctxApprox_3674_ = lean_ctor_get_uint8(v___x_3672_, 1);
v_quasiPatternApprox_3675_ = lean_ctor_get_uint8(v___x_3672_, 2);
v_constApprox_3676_ = lean_ctor_get_uint8(v___x_3672_, 3);
v_isDefEqStuckEx_3677_ = lean_ctor_get_uint8(v___x_3672_, 4);
v_unificationHints_3678_ = lean_ctor_get_uint8(v___x_3672_, 5);
v_proofIrrelevance_3679_ = lean_ctor_get_uint8(v___x_3672_, 6);
v_assignSyntheticOpaque_3680_ = lean_ctor_get_uint8(v___x_3672_, 7);
v_offsetCnstrs_3681_ = lean_ctor_get_uint8(v___x_3672_, 8);
v_transparency_3682_ = lean_ctor_get_uint8(v___x_3672_, 9);
v_univApprox_3683_ = lean_ctor_get_uint8(v___x_3672_, 11);
v_iota_3684_ = lean_ctor_get_uint8(v___x_3672_, 12);
v_beta_3685_ = lean_ctor_get_uint8(v___x_3672_, 13);
v_proj_3686_ = lean_ctor_get_uint8(v___x_3672_, 14);
v_zeta_3687_ = lean_ctor_get_uint8(v___x_3672_, 15);
v_zetaDelta_3688_ = lean_ctor_get_uint8(v___x_3672_, 16);
v_zetaUnused_3689_ = lean_ctor_get_uint8(v___x_3672_, 17);
v_zetaHave_3690_ = lean_ctor_get_uint8(v___x_3672_, 18);
v_canUnfoldPredicateConfig_3691_ = lean_ctor_get_uint8(v___x_3672_, 19);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3693_ = v___x_3672_;
v_isShared_3694_ = v_isSharedCheck_3754_;
goto v_resetjp_3692_;
}
else
{
lean_dec(v___x_3672_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3754_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
uint8_t v_trackZetaDelta_3695_; lean_object* v_zetaDeltaSet_3696_; lean_object* v_lctx_3697_; lean_object* v_localInstances_3698_; lean_object* v_defEqCtx_x3f_3699_; lean_object* v_synthPendingDepth_3700_; lean_object* v_customCanUnfoldPredicate_x3f_3701_; uint8_t v_univApprox_3702_; uint8_t v_inTypeClassResolution_3703_; uint8_t v_cacheInferType_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3752_; 
v_trackZetaDelta_3695_ = lean_ctor_get_uint8(v_a_3667_, sizeof(void*)*7);
v_zetaDeltaSet_3696_ = lean_ctor_get(v_a_3667_, 1);
v_lctx_3697_ = lean_ctor_get(v_a_3667_, 2);
v_localInstances_3698_ = lean_ctor_get(v_a_3667_, 3);
v_defEqCtx_x3f_3699_ = lean_ctor_get(v_a_3667_, 4);
v_synthPendingDepth_3700_ = lean_ctor_get(v_a_3667_, 5);
v_customCanUnfoldPredicate_x3f_3701_ = lean_ctor_get(v_a_3667_, 6);
v_univApprox_3702_ = lean_ctor_get_uint8(v_a_3667_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3703_ = lean_ctor_get_uint8(v_a_3667_, sizeof(void*)*7 + 2);
v_cacheInferType_3704_ = lean_ctor_get_uint8(v_a_3667_, sizeof(void*)*7 + 3);
v_isSharedCheck_3752_ = !lean_is_exclusive(v_a_3667_);
if (v_isSharedCheck_3752_ == 0)
{
lean_object* v_unused_3753_; 
v_unused_3753_ = lean_ctor_get(v_a_3667_, 0);
lean_dec(v_unused_3753_);
v___x_3706_ = v_a_3667_;
v_isShared_3707_ = v_isSharedCheck_3752_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3701_);
lean_inc(v_synthPendingDepth_3700_);
lean_inc(v_defEqCtx_x3f_3699_);
lean_inc(v_localInstances_3698_);
lean_inc(v_lctx_3697_);
lean_inc(v_zetaDeltaSet_3696_);
lean_dec(v_a_3667_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3752_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
uint8_t v___x_3708_; lean_object* v___x_3710_; 
v___x_3708_ = 2;
if (v_isShared_3694_ == 0)
{
v___x_3710_ = v___x_3693_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_3751_, 0, v_foApprox_3673_);
lean_ctor_set_uint8(v_reuseFailAlloc_3751_, 1, v_ctxApprox_3674_);
lean_ctor_set_uint8(v_reuseFailAlloc_3751_, 2, v_quasiPatternApprox_3675_);
lean_ctor_set_uint8(v_reuseFailAlloc_3751_, 3, v_constApprox_3676_);
lean_ctor_set_uint8(v_reuseFailAlloc_3751_, 4, v_isDefEqStuckEx_3677_);
lean_ctor_set_uint8(v_reuseFailAlloc_3751_, 5, v_unificationHints_3678_);
lean_ctor_set_uint8(v_reuseFailAlloc_3751_, 6, v_proofIrrelevance_3679_);
lean_ctor_set_uint8(v_reuseFailAlloc_3751_, 7, v_assignSyntheticOpaque_3680_);
lean_ctor_set_uint8(v_reuseFailAlloc_3751_, 8, v_offsetCnstrs_3681_);
lean_ctor_set_uint8(v_reuseFailAlloc_3751_, 9, v_transparency_3682_);
lean_ctor_set_uint8(v_reuseFailAlloc_3751_, 11, v_univApprox_3683_);
lean_ctor_set_uint8(v_reuseFailAlloc_3751_, 12, v_iota_3684_);
lean_ctor_set_uint8(v_reuseFailAlloc_3751_, 13, v_beta_3685_);
lean_ctor_set_uint8(v_reuseFailAlloc_3751_, 14, v_proj_3686_);
lean_ctor_set_uint8(v_reuseFailAlloc_3751_, 15, v_zeta_3687_);
lean_ctor_set_uint8(v_reuseFailAlloc_3751_, 16, v_zetaDelta_3688_);
lean_ctor_set_uint8(v_reuseFailAlloc_3751_, 17, v_zetaUnused_3689_);
lean_ctor_set_uint8(v_reuseFailAlloc_3751_, 18, v_zetaHave_3690_);
lean_ctor_set_uint8(v_reuseFailAlloc_3751_, 19, v_canUnfoldPredicateConfig_3691_);
v___x_3710_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
uint64_t v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3714_; 
lean_ctor_set_uint8(v___x_3710_, 10, v___x_3708_);
v___x_3711_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3710_);
v___x_3712_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3712_, 0, v___x_3710_);
lean_ctor_set_uint64(v___x_3712_, sizeof(void*)*1, v___x_3711_);
if (v_isShared_3707_ == 0)
{
lean_ctor_set(v___x_3706_, 0, v___x_3712_);
v___x_3714_ = v___x_3706_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3712_);
lean_ctor_set(v_reuseFailAlloc_3750_, 1, v_zetaDeltaSet_3696_);
lean_ctor_set(v_reuseFailAlloc_3750_, 2, v_lctx_3697_);
lean_ctor_set(v_reuseFailAlloc_3750_, 3, v_localInstances_3698_);
lean_ctor_set(v_reuseFailAlloc_3750_, 4, v_defEqCtx_x3f_3699_);
lean_ctor_set(v_reuseFailAlloc_3750_, 5, v_synthPendingDepth_3700_);
lean_ctor_set(v_reuseFailAlloc_3750_, 6, v_customCanUnfoldPredicate_x3f_3701_);
lean_ctor_set_uint8(v_reuseFailAlloc_3750_, sizeof(void*)*7, v_trackZetaDelta_3695_);
lean_ctor_set_uint8(v_reuseFailAlloc_3750_, sizeof(void*)*7 + 1, v_univApprox_3702_);
lean_ctor_set_uint8(v_reuseFailAlloc_3750_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3703_);
lean_ctor_set_uint8(v_reuseFailAlloc_3750_, sizeof(void*)*7 + 3, v_cacheInferType_3704_);
v___x_3714_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
lean_object* v___x_3715_; 
lean_inc(v_matchDeclName_3664_);
v___x_3715_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_3664_, v___x_3714_, v_a_3668_, v_a_3669_, v_a_3670_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_a_3716_; lean_object* v___x_3717_; lean_object* v_a_3718_; 
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
lean_inc(v_a_3716_);
lean_dec_ref_known(v___x_3715_, 1);
lean_inc(v_matchDeclName_3664_);
v___x_3717_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_3664_, v_a_3670_);
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref(v___x_3717_);
if (lean_obj_tag(v_a_3718_) == 1)
{
lean_object* v_val_3719_; lean_object* v_numParams_3720_; lean_object* v_numDiscrs_3721_; lean_object* v_altInfos_3722_; lean_object* v_uElimPos_x3f_3723_; lean_object* v_discrInfos_3724_; lean_object* v_overlaps_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___f_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___f_3733_; uint8_t v___x_3734_; lean_object* v___x_3735_; 
v_val_3719_ = lean_ctor_get(v_a_3718_, 0);
lean_inc(v_val_3719_);
lean_dec_ref_known(v_a_3718_, 1);
v_numParams_3720_ = lean_ctor_get(v_val_3719_, 0);
lean_inc(v_numParams_3720_);
v_numDiscrs_3721_ = lean_ctor_get(v_val_3719_, 1);
lean_inc(v_numDiscrs_3721_);
v_altInfos_3722_ = lean_ctor_get(v_val_3719_, 2);
lean_inc_ref(v_altInfos_3722_);
v_uElimPos_x3f_3723_ = lean_ctor_get(v_val_3719_, 3);
lean_inc(v_uElimPos_x3f_3723_);
v_discrInfos_3724_ = lean_ctor_get(v_val_3719_, 4);
lean_inc_ref(v_discrInfos_3724_);
v_overlaps_3725_ = lean_ctor_get(v_val_3719_, 5);
lean_inc_ref_n(v_overlaps_3725_, 2);
v___x_3726_ = l_Lean_instInhabitedExpr;
v___x_3727_ = l_Lean_ConstantInfo_levelParams(v_a_3716_);
v___x_3728_ = lean_box(0);
lean_inc(v___x_3727_);
v___x_3729_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(v___x_3727_, v___x_3728_);
lean_inc(v_splitterName_3666_);
v___f_3730_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3730_, 0, v_overlaps_3725_);
lean_closure_set(v___f_3730_, 1, v_splitterName_3666_);
v___x_3731_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_discrInfos_3724_);
v___x_3732_ = l_Lean_ConstantInfo_type(v_a_3716_);
lean_inc_ref(v___x_3732_);
v___f_3733_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed), 24, 17);
lean_closure_set(v___f_3733_, 0, v_splitterName_3666_);
lean_closure_set(v___f_3733_, 1, v_matchDeclName_3664_);
lean_closure_set(v___f_3733_, 2, v_numParams_3720_);
lean_closure_set(v___f_3733_, 3, v_val_3719_);
lean_closure_set(v___f_3733_, 4, v___x_3726_);
lean_closure_set(v___f_3733_, 5, v_numDiscrs_3721_);
lean_closure_set(v___f_3733_, 6, v_baseName_3665_);
lean_closure_set(v___f_3733_, 7, v_a_3716_);
lean_closure_set(v___f_3733_, 8, v___x_3729_);
lean_closure_set(v___f_3733_, 9, v___x_3727_);
lean_closure_set(v___f_3733_, 10, v___x_3731_);
lean_closure_set(v___f_3733_, 11, v_uElimPos_x3f_3723_);
lean_closure_set(v___f_3733_, 12, v_discrInfos_3724_);
lean_closure_set(v___f_3733_, 13, v_overlaps_3725_);
lean_closure_set(v___f_3733_, 14, v___f_3730_);
lean_closure_set(v___f_3733_, 15, v___x_3732_);
lean_closure_set(v___f_3733_, 16, v_altInfos_3722_);
v___x_3734_ = 0;
v___x_3735_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_3732_, v___f_3733_, v___x_3734_, v___x_3734_, v___x_3714_, v_a_3668_, v_a_3669_, v_a_3670_);
lean_dec_ref(v___x_3714_);
return v___x_3735_;
}
else
{
lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; 
lean_dec(v_a_3718_);
lean_dec(v_a_3716_);
lean_dec(v_splitterName_3666_);
lean_dec(v_baseName_3665_);
v___x_3736_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3737_ = l_Lean_MessageData_ofName(v_matchDeclName_3664_);
v___x_3738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3736_);
lean_ctor_set(v___x_3738_, 1, v___x_3737_);
v___x_3739_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_3740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3738_);
lean_ctor_set(v___x_3740_, 1, v___x_3739_);
v___x_3741_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_3740_, v___x_3714_, v_a_3668_, v_a_3669_, v_a_3670_);
lean_dec_ref(v___x_3714_);
return v___x_3741_;
}
}
else
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
lean_dec_ref(v___x_3714_);
lean_dec(v_splitterName_3666_);
lean_dec(v_baseName_3665_);
lean_dec(v_matchDeclName_3664_);
v_a_3742_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3744_ = v___x_3715_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3715_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3742_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed(lean_object* v_matchDeclName_3755_, lean_object* v_baseName_3756_, lean_object* v_splitterName_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_){
_start:
{
lean_object* v_res_3763_; 
v_res_3763_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(v_matchDeclName_3755_, v_baseName_3756_, v_splitterName_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_);
lean_dec(v_a_3761_);
lean_dec_ref(v_a_3760_);
lean_dec(v_a_3759_);
return v_res_3763_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(lean_object* v_xs_3764_, lean_object* v_ys_3765_, lean_object* v_hsz_3766_, lean_object* v_x_3767_, lean_object* v_x_3768_){
_start:
{
uint8_t v___x_3769_; 
v___x_3769_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_3764_, v_ys_3765_, v_x_3767_);
return v___x_3769_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___boxed(lean_object* v_xs_3770_, lean_object* v_ys_3771_, lean_object* v_hsz_3772_, lean_object* v_x_3773_, lean_object* v_x_3774_){
_start:
{
uint8_t v_res_3775_; lean_object* v_r_3776_; 
v_res_3775_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(v_xs_3770_, v_ys_3771_, v_hsz_3772_, v_x_3773_, v_x_3774_);
lean_dec_ref(v_ys_3771_);
lean_dec_ref(v_xs_3770_);
v_r_3776_ = lean_box(v_res_3775_);
return v_r_3776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6(lean_object* v_inst_3777_, lean_object* v_R_3778_, lean_object* v_a_3779_, lean_object* v_b_3780_){
_start:
{
lean_object* v___x_3781_; 
v___x_3781_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v_a_3779_, v_b_3780_);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(lean_object* v_upperBound_3782_, lean_object* v_val_3783_, lean_object* v_baseName_3784_, lean_object* v___x_3785_, lean_object* v_a_3786_, lean_object* v___x_3787_, lean_object* v___x_3788_, lean_object* v___x_3789_, lean_object* v_matchDeclName_3790_, lean_object* v___x_3791_, lean_object* v___x_3792_, lean_object* v___x_3793_, lean_object* v_inst_3794_, lean_object* v_R_3795_, lean_object* v_a_3796_, lean_object* v_b_3797_, lean_object* v_c_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_){
_start:
{
lean_object* v___x_3804_; 
v___x_3804_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3782_, v_val_3783_, v_baseName_3784_, v___x_3785_, v_a_3786_, v___x_3787_, v___x_3788_, v___x_3789_, v_matchDeclName_3790_, v___x_3791_, v___x_3792_, v___x_3793_, v_a_3796_, v_b_3797_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_);
return v___x_3804_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_3805_ = _args[0];
lean_object* v_val_3806_ = _args[1];
lean_object* v_baseName_3807_ = _args[2];
lean_object* v___x_3808_ = _args[3];
lean_object* v_a_3809_ = _args[4];
lean_object* v___x_3810_ = _args[5];
lean_object* v___x_3811_ = _args[6];
lean_object* v___x_3812_ = _args[7];
lean_object* v_matchDeclName_3813_ = _args[8];
lean_object* v___x_3814_ = _args[9];
lean_object* v___x_3815_ = _args[10];
lean_object* v___x_3816_ = _args[11];
lean_object* v_inst_3817_ = _args[12];
lean_object* v_R_3818_ = _args[13];
lean_object* v_a_3819_ = _args[14];
lean_object* v_b_3820_ = _args[15];
lean_object* v_c_3821_ = _args[16];
lean_object* v___y_3822_ = _args[17];
lean_object* v___y_3823_ = _args[18];
lean_object* v___y_3824_ = _args[19];
lean_object* v___y_3825_ = _args[20];
lean_object* v___y_3826_ = _args[21];
_start:
{
lean_object* v_res_3827_; 
v_res_3827_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(v_upperBound_3805_, v_val_3806_, v_baseName_3807_, v___x_3808_, v_a_3809_, v___x_3810_, v___x_3811_, v___x_3812_, v_matchDeclName_3813_, v___x_3814_, v___x_3815_, v___x_3816_, v_inst_3817_, v_R_3818_, v_a_3819_, v_b_3820_, v_c_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
lean_dec(v_upperBound_3805_);
return v_res_3827_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(lean_object* v_00_u03b1_3828_, lean_object* v_constName_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_){
_start:
{
lean_object* v___x_3835_; 
v___x_3835_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3836_, lean_object* v_constName_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_){
_start:
{
lean_object* v_res_3843_; 
v_res_3843_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(v_00_u03b1_3836_, v_constName_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_3844_, lean_object* v_ref_3845_, lean_object* v_constName_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
lean_object* v___x_3852_; 
v___x_3852_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3845_, v_constName_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_);
return v___x_3852_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_3853_, lean_object* v_ref_3854_, lean_object* v_constName_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_){
_start:
{
lean_object* v_res_3861_; 
v_res_3861_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(v_00_u03b1_3853_, v_ref_3854_, v_constName_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
lean_dec(v___y_3859_);
lean_dec_ref(v___y_3858_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec(v_ref_3854_);
return v_res_3861_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(lean_object* v_00_u03b1_3862_, lean_object* v_ref_3863_, lean_object* v_msg_3864_, lean_object* v_declHint_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_){
_start:
{
lean_object* v___x_3871_; 
v___x_3871_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3863_, v_msg_3864_, v_declHint_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_);
return v___x_3871_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___boxed(lean_object* v_00_u03b1_3872_, lean_object* v_ref_3873_, lean_object* v_msg_3874_, lean_object* v_declHint_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_){
_start:
{
lean_object* v_res_3881_; 
v_res_3881_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(v_00_u03b1_3872_, v_ref_3873_, v_msg_3874_, v_declHint_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
lean_dec(v___y_3877_);
lean_dec_ref(v___y_3876_);
lean_dec(v_ref_3873_);
return v_res_3881_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(lean_object* v_msg_3882_, lean_object* v_declHint_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v___x_3889_; 
v___x_3889_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3882_, v_declHint_3883_, v___y_3887_);
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_3890_, lean_object* v_declHint_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_){
_start:
{
lean_object* v_res_3897_; 
v_res_3897_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(v_msg_3890_, v_declHint_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(lean_object* v_00_u03b1_3898_, lean_object* v_ref_3899_, lean_object* v_msg_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_){
_start:
{
lean_object* v___x_3906_; 
v___x_3906_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3899_, v_msg_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_);
return v___x_3906_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___boxed(lean_object* v_00_u03b1_3907_, lean_object* v_ref_3908_, lean_object* v_msg_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(v_00_u03b1_3907_, v_ref_3908_, v_msg_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
lean_dec(v___y_3913_);
lean_dec_ref(v___y_3912_);
lean_dec(v___y_3911_);
lean_dec_ref(v___y_3910_);
lean_dec(v_ref_3908_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3916_, lean_object* v_vals_3917_, lean_object* v_i_3918_, lean_object* v_k_3919_){
_start:
{
lean_object* v___x_3920_; uint8_t v___x_3921_; 
v___x_3920_ = lean_array_get_size(v_keys_3916_);
v___x_3921_ = lean_nat_dec_lt(v_i_3918_, v___x_3920_);
if (v___x_3921_ == 0)
{
lean_object* v___x_3922_; 
lean_dec(v_i_3918_);
v___x_3922_ = lean_box(0);
return v___x_3922_;
}
else
{
lean_object* v_k_x27_3923_; uint8_t v___x_3924_; 
v_k_x27_3923_ = lean_array_fget_borrowed(v_keys_3916_, v_i_3918_);
v___x_3924_ = lean_name_eq(v_k_3919_, v_k_x27_3923_);
if (v___x_3924_ == 0)
{
lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3925_ = lean_unsigned_to_nat(1u);
v___x_3926_ = lean_nat_add(v_i_3918_, v___x_3925_);
lean_dec(v_i_3918_);
v_i_3918_ = v___x_3926_;
goto _start;
}
else
{
lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3928_ = lean_array_fget_borrowed(v_vals_3917_, v_i_3918_);
lean_dec(v_i_3918_);
lean_inc(v___x_3928_);
v___x_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3928_);
return v___x_3929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3930_, lean_object* v_vals_3931_, lean_object* v_i_3932_, lean_object* v_k_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_3930_, v_vals_3931_, v_i_3932_, v_k_3933_);
lean_dec(v_k_3933_);
lean_dec_ref(v_vals_3931_);
lean_dec_ref(v_keys_3930_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(lean_object* v_x_3935_, size_t v_x_3936_, lean_object* v_x_3937_){
_start:
{
if (lean_obj_tag(v_x_3935_) == 0)
{
lean_object* v_es_3938_; lean_object* v___x_3939_; size_t v___x_3940_; size_t v___x_3941_; lean_object* v_j_3942_; lean_object* v___x_3943_; 
v_es_3938_ = lean_ctor_get(v_x_3935_, 0);
v___x_3939_ = lean_box(2);
v___x_3940_ = ((size_t)31ULL);
v___x_3941_ = lean_usize_land(v_x_3936_, v___x_3940_);
v_j_3942_ = lean_usize_to_nat(v___x_3941_);
v___x_3943_ = lean_array_get_borrowed(v___x_3939_, v_es_3938_, v_j_3942_);
lean_dec(v_j_3942_);
switch(lean_obj_tag(v___x_3943_))
{
case 0:
{
lean_object* v_key_3944_; lean_object* v_val_3945_; uint8_t v___x_3946_; 
v_key_3944_ = lean_ctor_get(v___x_3943_, 0);
v_val_3945_ = lean_ctor_get(v___x_3943_, 1);
v___x_3946_ = lean_name_eq(v_x_3937_, v_key_3944_);
if (v___x_3946_ == 0)
{
lean_object* v___x_3947_; 
v___x_3947_ = lean_box(0);
return v___x_3947_;
}
else
{
lean_object* v___x_3948_; 
lean_inc(v_val_3945_);
v___x_3948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3948_, 0, v_val_3945_);
return v___x_3948_;
}
}
case 1:
{
lean_object* v_node_3949_; size_t v___x_3950_; size_t v___x_3951_; 
v_node_3949_ = lean_ctor_get(v___x_3943_, 0);
v___x_3950_ = ((size_t)5ULL);
v___x_3951_ = lean_usize_shift_right(v_x_3936_, v___x_3950_);
v_x_3935_ = v_node_3949_;
v_x_3936_ = v___x_3951_;
goto _start;
}
default: 
{
lean_object* v___x_3953_; 
v___x_3953_ = lean_box(0);
return v___x_3953_;
}
}
}
else
{
lean_object* v_ks_3954_; lean_object* v_vs_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
v_ks_3954_ = lean_ctor_get(v_x_3935_, 0);
v_vs_3955_ = lean_ctor_get(v_x_3935_, 1);
v___x_3956_ = lean_unsigned_to_nat(0u);
v___x_3957_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_ks_3954_, v_vs_3955_, v___x_3956_, v_x_3937_);
return v___x_3957_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_3958_, lean_object* v_x_3959_, lean_object* v_x_3960_){
_start:
{
size_t v_x_698__boxed_3961_; lean_object* v_res_3962_; 
v_x_698__boxed_3961_ = lean_unbox_usize(v_x_3959_);
lean_dec(v_x_3959_);
v_res_3962_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3958_, v_x_698__boxed_3961_, v_x_3960_);
lean_dec(v_x_3960_);
lean_dec_ref(v_x_3958_);
return v_res_3962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(lean_object* v_x_3963_, lean_object* v_x_3964_){
_start:
{
uint64_t v___y_3966_; 
if (lean_obj_tag(v_x_3964_) == 0)
{
uint64_t v___x_3969_; 
v___x_3969_ = 1723ULL;
v___y_3966_ = v___x_3969_;
goto v___jp_3965_;
}
else
{
uint64_t v_hash_3970_; 
v_hash_3970_ = lean_ctor_get_uint64(v_x_3964_, sizeof(void*)*2);
v___y_3966_ = v_hash_3970_;
goto v___jp_3965_;
}
v___jp_3965_:
{
size_t v___x_3967_; lean_object* v___x_3968_; 
v___x_3967_ = lean_uint64_to_usize(v___y_3966_);
v___x_3968_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3963_, v___x_3967_, v_x_3964_);
return v___x_3968_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___boxed(lean_object* v_x_3971_, lean_object* v_x_3972_){
_start:
{
lean_object* v_res_3973_; 
v_res_3973_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_3971_, v_x_3972_);
lean_dec(v_x_3972_);
lean_dec_ref(v_x_3971_);
return v_res_3973_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4(void){
_start:
{
lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3980_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__3));
v___x_3981_ = l_Lean_stringToMessageData(v___x_3980_);
return v___x_3981_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6(void){
_start:
{
lean_object* v___x_3983_; lean_object* v___x_3984_; 
v___x_3983_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__5));
v___x_3984_ = l_Lean_stringToMessageData(v___x_3983_);
return v___x_3984_;
}
}
LEAN_EXPORT lean_object* lean_get_match_equations_for(lean_object* v_matchDeclName_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_){
_start:
{
lean_object* v___x_3991_; lean_object* v_env_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; 
v___x_3991_ = lean_st_ref_get(v_a_3989_);
v_env_3992_ = lean_ctor_get(v___x_3991_, 0);
lean_inc_ref(v_env_3992_);
lean_dec(v___x_3991_);
lean_inc_n(v_matchDeclName_3985_, 3);
v___x_3993_ = l_Lean_mkPrivateName(v_env_3992_, v_matchDeclName_3985_);
lean_dec_ref(v_env_3992_);
v___x_3994_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__1));
lean_inc(v___x_3993_);
v___x_3995_ = l_Lean_Name_append(v___x_3993_, v___x_3994_);
lean_inc_n(v___x_3995_, 2);
v___x_3996_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed), 8, 3);
lean_closure_set(v___x_3996_, 0, v_matchDeclName_3985_);
lean_closure_set(v___x_3996_, 1, v___x_3993_);
lean_closure_set(v___x_3996_, 2, v___x_3995_);
v___x_3997_ = l_Lean_Meta_realizeConst(v_matchDeclName_3985_, v___x_3995_, v___x_3996_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4026_; 
v_isSharedCheck_4026_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4026_ == 0)
{
lean_object* v_unused_4027_; 
v_unused_4027_ = lean_ctor_get(v___x_3997_, 0);
lean_dec(v_unused_4027_);
v___x_3999_ = v___x_3997_;
v_isShared_4000_ = v_isSharedCheck_4026_;
goto v_resetjp_3998_;
}
else
{
lean_dec(v___x_3997_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4026_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4001_; lean_object* v_env_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v_map_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4024_; 
v___x_4001_ = lean_st_ref_get(v_a_3989_);
v_env_4002_ = lean_ctor_get(v___x_4001_, 0);
lean_inc_ref(v_env_4002_);
lean_dec(v___x_4001_);
v___x_4003_ = l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
v___x_4004_ = l_Lean_Meta_Match_matchEqnsExt;
v___x_4005_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__2));
v___x_4006_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_4003_, v___x_4004_, v_env_4002_, v___x_4005_, v___x_3995_);
v_map_4007_ = lean_ctor_get(v___x_4006_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4024_ == 0)
{
lean_object* v_unused_4025_; 
v_unused_4025_ = lean_ctor_get(v___x_4006_, 1);
lean_dec(v_unused_4025_);
v___x_4009_ = v___x_4006_;
v_isShared_4010_ = v_isSharedCheck_4024_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_map_4007_);
lean_dec(v___x_4006_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4024_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4011_; 
v___x_4011_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_map_4007_, v_matchDeclName_3985_);
lean_dec_ref(v_map_4007_);
if (lean_obj_tag(v___x_4011_) == 0)
{
lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4015_; 
lean_del_object(v___x_3999_);
v___x_4012_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__4, &l_Lean_Meta_Match_getEquationsForImpl___closed__4_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4);
v___x_4013_ = l_Lean_MessageData_ofName(v_matchDeclName_3985_);
if (v_isShared_4010_ == 0)
{
lean_ctor_set_tag(v___x_4009_, 7);
lean_ctor_set(v___x_4009_, 1, v___x_4013_);
lean_ctor_set(v___x_4009_, 0, v___x_4012_);
v___x_4015_ = v___x_4009_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v___x_4012_);
lean_ctor_set(v_reuseFailAlloc_4019_, 1, v___x_4013_);
v___x_4015_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
v___x_4016_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__6, &l_Lean_Meta_Match_getEquationsForImpl___closed__6_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6);
v___x_4017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4015_);
lean_ctor_set(v___x_4017_, 1, v___x_4016_);
v___x_4018_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_4017_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_);
lean_dec(v_a_3989_);
lean_dec_ref(v_a_3988_);
lean_dec(v_a_3987_);
lean_dec_ref(v_a_3986_);
return v___x_4018_;
}
}
else
{
lean_object* v_val_4020_; lean_object* v___x_4022_; 
lean_del_object(v___x_4009_);
lean_dec(v_a_3989_);
lean_dec_ref(v_a_3988_);
lean_dec(v_a_3987_);
lean_dec_ref(v_a_3986_);
lean_dec(v_matchDeclName_3985_);
v_val_4020_ = lean_ctor_get(v___x_4011_, 0);
lean_inc(v_val_4020_);
lean_dec_ref_known(v___x_4011_, 1);
if (v_isShared_4000_ == 0)
{
lean_ctor_set(v___x_3999_, 0, v_val_4020_);
v___x_4022_ = v___x_3999_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_val_4020_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
return v___x_4022_;
}
}
}
}
}
else
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
lean_dec(v___x_3995_);
lean_dec(v_a_3989_);
lean_dec_ref(v_a_3988_);
lean_dec(v_a_3987_);
lean_dec_ref(v_a_3986_);
lean_dec(v_matchDeclName_3985_);
v_a_4028_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___x_3997_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_3997_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4033_; 
if (v_isShared_4031_ == 0)
{
v___x_4033_ = v___x_4030_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_a_4028_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getEquationsForImpl___boxed(lean_object* v_matchDeclName_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_){
_start:
{
lean_object* v_res_4042_; 
v_res_4042_ = lean_get_match_equations_for(v_matchDeclName_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_);
return v_res_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(lean_object* v_00_u03b2_4043_, lean_object* v_x_4044_, lean_object* v_x_4045_){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_4044_, v_x_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___boxed(lean_object* v_00_u03b2_4047_, lean_object* v_x_4048_, lean_object* v_x_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(v_00_u03b2_4047_, v_x_4048_, v_x_4049_);
lean_dec(v_x_4049_);
lean_dec_ref(v_x_4048_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(lean_object* v_00_u03b2_4051_, lean_object* v_x_4052_, size_t v_x_4053_, lean_object* v_x_4054_){
_start:
{
lean_object* v___x_4055_; 
v___x_4055_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_4052_, v_x_4053_, v_x_4054_);
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4056_, lean_object* v_x_4057_, lean_object* v_x_4058_, lean_object* v_x_4059_){
_start:
{
size_t v_x_890__boxed_4060_; lean_object* v_res_4061_; 
v_x_890__boxed_4060_ = lean_unbox_usize(v_x_4058_);
lean_dec(v_x_4058_);
v_res_4061_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(v_00_u03b2_4056_, v_x_4057_, v_x_890__boxed_4060_, v_x_4059_);
lean_dec(v_x_4059_);
lean_dec_ref(v_x_4057_);
return v_res_4061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4062_, lean_object* v_keys_4063_, lean_object* v_vals_4064_, lean_object* v_heq_4065_, lean_object* v_i_4066_, lean_object* v_k_4067_){
_start:
{
lean_object* v___x_4068_; 
v___x_4068_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_4063_, v_vals_4064_, v_i_4066_, v_k_4067_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4069_, lean_object* v_keys_4070_, lean_object* v_vals_4071_, lean_object* v_heq_4072_, lean_object* v_i_4073_, lean_object* v_k_4074_){
_start:
{
lean_object* v_res_4075_; 
v_res_4075_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(v_00_u03b2_4069_, v_keys_4070_, v_vals_4071_, v_heq_4072_, v_i_4073_, v_k_4074_);
lean_dec(v_k_4074_);
lean_dec_ref(v_vals_4071_);
lean_dec_ref(v_keys_4070_);
return v_res_4075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(lean_object* v_type_4076_, lean_object* v_k_4077_, uint8_t v_cleanupAnnotations_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
lean_object* v___f_4084_; uint8_t v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___f_4084_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4084_, 0, v_k_4077_);
v___x_4085_ = 0;
v___x_4086_ = lean_box(0);
v___x_4087_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_4085_, v___x_4086_, v_type_4076_, v___f_4084_, v_cleanupAnnotations_4078_, v___x_4085_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
if (lean_obj_tag(v___x_4087_) == 0)
{
lean_object* v_a_4088_; lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4095_; 
v_a_4088_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4095_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4095_ == 0)
{
v___x_4090_ = v___x_4087_;
v_isShared_4091_ = v_isSharedCheck_4095_;
goto v_resetjp_4089_;
}
else
{
lean_inc(v_a_4088_);
lean_dec(v___x_4087_);
v___x_4090_ = lean_box(0);
v_isShared_4091_ = v_isSharedCheck_4095_;
goto v_resetjp_4089_;
}
v_resetjp_4089_:
{
lean_object* v___x_4093_; 
if (v_isShared_4091_ == 0)
{
v___x_4093_ = v___x_4090_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4094_; 
v_reuseFailAlloc_4094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4094_, 0, v_a_4088_);
v___x_4093_ = v_reuseFailAlloc_4094_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
return v___x_4093_;
}
}
}
else
{
lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4103_; 
v_a_4096_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4103_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4103_ == 0)
{
v___x_4098_ = v___x_4087_;
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4087_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4101_; 
if (v_isShared_4099_ == 0)
{
v___x_4101_ = v___x_4098_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v_a_4096_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
return v___x_4101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg___boxed(lean_object* v_type_4104_, lean_object* v_k_4105_, lean_object* v_cleanupAnnotations_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4112_; lean_object* v_res_4113_; 
v_cleanupAnnotations_boxed_4112_ = lean_unbox(v_cleanupAnnotations_4106_);
v_res_4113_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4104_, v_k_4105_, v_cleanupAnnotations_boxed_4112_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
return v_res_4113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(lean_object* v_00_u03b1_4114_, lean_object* v_type_4115_, lean_object* v_k_4116_, uint8_t v_cleanupAnnotations_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_){
_start:
{
lean_object* v___x_4123_; 
v___x_4123_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4115_, v_k_4116_, v_cleanupAnnotations_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4124_, lean_object* v_type_4125_, lean_object* v_k_4126_, lean_object* v_cleanupAnnotations_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4133_; lean_object* v_res_4134_; 
v_cleanupAnnotations_boxed_4133_ = lean_unbox(v_cleanupAnnotations_4127_);
v_res_4134_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(v_00_u03b1_4124_, v_type_4125_, v_k_4126_, v_cleanupAnnotations_boxed_4133_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
return v_res_4134_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(lean_object* v_msg_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_){
_start:
{
lean_object* v___f_4141_; lean_object* v___x_19934__overap_4142_; lean_object* v___x_4143_; 
v___f_4141_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_19934__overap_4142_ = lean_panic_fn_borrowed(v___f_4141_, v_msg_4135_);
lean_inc(v___y_4139_);
lean_inc_ref(v___y_4138_);
lean_inc(v___y_4137_);
lean_inc_ref(v___y_4136_);
v___x_4143_ = lean_apply_5(v___x_19934__overap_4142_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, lean_box(0));
return v___x_4143_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1___boxed(lean_object* v_msg_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
lean_object* v_res_4150_; 
v_res_4150_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v_msg_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
return v_res_4150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(lean_object* v_c_4151_){
_start:
{
uint8_t v_foApprox_4152_; uint8_t v_ctxApprox_4153_; uint8_t v_quasiPatternApprox_4154_; uint8_t v_constApprox_4155_; uint8_t v_isDefEqStuckEx_4156_; uint8_t v_unificationHints_4157_; uint8_t v_proofIrrelevance_4158_; uint8_t v_assignSyntheticOpaque_4159_; uint8_t v_offsetCnstrs_4160_; uint8_t v_transparency_4161_; uint8_t v_univApprox_4162_; uint8_t v_iota_4163_; uint8_t v_beta_4164_; uint8_t v_proj_4165_; uint8_t v_zeta_4166_; uint8_t v_zetaDelta_4167_; uint8_t v_zetaUnused_4168_; uint8_t v_zetaHave_4169_; uint8_t v_canUnfoldPredicateConfig_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4178_; 
v_foApprox_4152_ = lean_ctor_get_uint8(v_c_4151_, 0);
v_ctxApprox_4153_ = lean_ctor_get_uint8(v_c_4151_, 1);
v_quasiPatternApprox_4154_ = lean_ctor_get_uint8(v_c_4151_, 2);
v_constApprox_4155_ = lean_ctor_get_uint8(v_c_4151_, 3);
v_isDefEqStuckEx_4156_ = lean_ctor_get_uint8(v_c_4151_, 4);
v_unificationHints_4157_ = lean_ctor_get_uint8(v_c_4151_, 5);
v_proofIrrelevance_4158_ = lean_ctor_get_uint8(v_c_4151_, 6);
v_assignSyntheticOpaque_4159_ = lean_ctor_get_uint8(v_c_4151_, 7);
v_offsetCnstrs_4160_ = lean_ctor_get_uint8(v_c_4151_, 8);
v_transparency_4161_ = lean_ctor_get_uint8(v_c_4151_, 9);
v_univApprox_4162_ = lean_ctor_get_uint8(v_c_4151_, 11);
v_iota_4163_ = lean_ctor_get_uint8(v_c_4151_, 12);
v_beta_4164_ = lean_ctor_get_uint8(v_c_4151_, 13);
v_proj_4165_ = lean_ctor_get_uint8(v_c_4151_, 14);
v_zeta_4166_ = lean_ctor_get_uint8(v_c_4151_, 15);
v_zetaDelta_4167_ = lean_ctor_get_uint8(v_c_4151_, 16);
v_zetaUnused_4168_ = lean_ctor_get_uint8(v_c_4151_, 17);
v_zetaHave_4169_ = lean_ctor_get_uint8(v_c_4151_, 18);
v_canUnfoldPredicateConfig_4170_ = lean_ctor_get_uint8(v_c_4151_, 19);
v_isSharedCheck_4178_ = !lean_is_exclusive(v_c_4151_);
if (v_isSharedCheck_4178_ == 0)
{
v___x_4172_ = v_c_4151_;
v_isShared_4173_ = v_isSharedCheck_4178_;
goto v_resetjp_4171_;
}
else
{
lean_dec(v_c_4151_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4178_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
uint8_t v___x_4174_; lean_object* v___x_4176_; 
v___x_4174_ = 2;
if (v_isShared_4173_ == 0)
{
v___x_4176_ = v___x_4172_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_4177_, 0, v_foApprox_4152_);
lean_ctor_set_uint8(v_reuseFailAlloc_4177_, 1, v_ctxApprox_4153_);
lean_ctor_set_uint8(v_reuseFailAlloc_4177_, 2, v_quasiPatternApprox_4154_);
lean_ctor_set_uint8(v_reuseFailAlloc_4177_, 3, v_constApprox_4155_);
lean_ctor_set_uint8(v_reuseFailAlloc_4177_, 4, v_isDefEqStuckEx_4156_);
lean_ctor_set_uint8(v_reuseFailAlloc_4177_, 5, v_unificationHints_4157_);
lean_ctor_set_uint8(v_reuseFailAlloc_4177_, 6, v_proofIrrelevance_4158_);
lean_ctor_set_uint8(v_reuseFailAlloc_4177_, 7, v_assignSyntheticOpaque_4159_);
lean_ctor_set_uint8(v_reuseFailAlloc_4177_, 8, v_offsetCnstrs_4160_);
lean_ctor_set_uint8(v_reuseFailAlloc_4177_, 9, v_transparency_4161_);
lean_ctor_set_uint8(v_reuseFailAlloc_4177_, 11, v_univApprox_4162_);
lean_ctor_set_uint8(v_reuseFailAlloc_4177_, 12, v_iota_4163_);
lean_ctor_set_uint8(v_reuseFailAlloc_4177_, 13, v_beta_4164_);
lean_ctor_set_uint8(v_reuseFailAlloc_4177_, 14, v_proj_4165_);
lean_ctor_set_uint8(v_reuseFailAlloc_4177_, 15, v_zeta_4166_);
lean_ctor_set_uint8(v_reuseFailAlloc_4177_, 16, v_zetaDelta_4167_);
lean_ctor_set_uint8(v_reuseFailAlloc_4177_, 17, v_zetaUnused_4168_);
lean_ctor_set_uint8(v_reuseFailAlloc_4177_, 18, v_zetaHave_4169_);
lean_ctor_set_uint8(v_reuseFailAlloc_4177_, 19, v_canUnfoldPredicateConfig_4170_);
v___x_4176_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
lean_ctor_set_uint8(v___x_4176_, 10, v___x_4174_);
return v___x_4176_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(lean_object* v_x_4179_, lean_object* v_t_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_){
_start:
{
lean_object* v_dummy_4186_; lean_object* v_nargs_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
v_dummy_4186_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_4187_ = l_Lean_Expr_getAppNumArgs(v_t_4180_);
lean_inc(v_nargs_4187_);
v___x_4188_ = lean_mk_array(v_nargs_4187_, v_dummy_4186_);
v___x_4189_ = lean_unsigned_to_nat(1u);
v___x_4190_ = lean_nat_sub(v_nargs_4187_, v___x_4189_);
lean_dec(v_nargs_4187_);
v___x_4191_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_t_4180_, v___x_4188_, v___x_4190_);
v___x_4192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0___boxed(lean_object* v_x_4193_, lean_object* v_t_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
lean_object* v_res_4200_; 
v_res_4200_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(v_x_4193_, v_t_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
lean_dec(v___y_4198_);
lean_dec_ref(v___y_4197_);
lean_dec(v___y_4196_);
lean_dec_ref(v___y_4195_);
lean_dec_ref(v_x_4193_);
return v_res_4200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(lean_object* v_snd_4201_, lean_object* v_x_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
lean_object* v___x_4208_; 
v___x_4208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4208_, 0, v_snd_4201_);
return v___x_4208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed(lean_object* v_snd_4209_, lean_object* v_x_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
lean_object* v_res_4216_; 
v_res_4216_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(v_snd_4209_, v_x_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec_ref(v_x_4210_);
return v_res_4216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(size_t v_sz_4217_, size_t v_i_4218_, lean_object* v_bs_4219_){
_start:
{
uint8_t v___x_4220_; 
v___x_4220_ = lean_usize_dec_lt(v_i_4218_, v_sz_4217_);
if (v___x_4220_ == 0)
{
return v_bs_4219_;
}
else
{
lean_object* v_v_4221_; lean_object* v_fst_4222_; lean_object* v_snd_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4237_; 
v_v_4221_ = lean_array_uget(v_bs_4219_, v_i_4218_);
v_fst_4222_ = lean_ctor_get(v_v_4221_, 0);
v_snd_4223_ = lean_ctor_get(v_v_4221_, 1);
v_isSharedCheck_4237_ = !lean_is_exclusive(v_v_4221_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4225_ = v_v_4221_;
v_isShared_4226_ = v_isSharedCheck_4237_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_snd_4223_);
lean_inc(v_fst_4222_);
lean_dec(v_v_4221_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4237_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4227_; lean_object* v_bs_x27_4228_; lean_object* v___f_4229_; lean_object* v___x_4231_; 
v___x_4227_ = lean_unsigned_to_nat(0u);
v_bs_x27_4228_ = lean_array_uset(v_bs_4219_, v_i_4218_, v___x_4227_);
v___f_4229_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4229_, 0, v_snd_4223_);
if (v_isShared_4226_ == 0)
{
lean_ctor_set(v___x_4225_, 1, v___f_4229_);
v___x_4231_ = v___x_4225_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_fst_4222_);
lean_ctor_set(v_reuseFailAlloc_4236_, 1, v___f_4229_);
v___x_4231_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
size_t v___x_4232_; size_t v___x_4233_; lean_object* v___x_4234_; 
v___x_4232_ = ((size_t)1ULL);
v___x_4233_ = lean_usize_add(v_i_4218_, v___x_4232_);
v___x_4234_ = lean_array_uset(v_bs_x27_4228_, v_i_4218_, v___x_4231_);
v_i_4218_ = v___x_4233_;
v_bs_4219_ = v___x_4234_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___boxed(lean_object* v_sz_4238_, lean_object* v_i_4239_, lean_object* v_bs_4240_){
_start:
{
size_t v_sz_boxed_4241_; size_t v_i_boxed_4242_; lean_object* v_res_4243_; 
v_sz_boxed_4241_ = lean_unbox_usize(v_sz_4238_);
lean_dec(v_sz_4238_);
v_i_boxed_4242_ = lean_unbox_usize(v_i_4239_);
lean_dec(v_i_4239_);
v_res_4243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_boxed_4241_, v_i_boxed_4242_, v_bs_4240_);
return v_res_4243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(size_t v_sz_4244_, size_t v_i_4245_, lean_object* v_bs_4246_){
_start:
{
uint8_t v___x_4247_; 
v___x_4247_ = lean_usize_dec_lt(v_i_4245_, v_sz_4244_);
if (v___x_4247_ == 0)
{
return v_bs_4246_;
}
else
{
lean_object* v_v_4248_; lean_object* v_fst_4249_; lean_object* v_snd_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4266_; 
v_v_4248_ = lean_array_uget(v_bs_4246_, v_i_4245_);
v_fst_4249_ = lean_ctor_get(v_v_4248_, 0);
v_snd_4250_ = lean_ctor_get(v_v_4248_, 1);
v_isSharedCheck_4266_ = !lean_is_exclusive(v_v_4248_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4252_ = v_v_4248_;
v_isShared_4253_ = v_isSharedCheck_4266_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_snd_4250_);
lean_inc(v_fst_4249_);
lean_dec(v_v_4248_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4266_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v___x_4254_; lean_object* v_bs_x27_4255_; uint8_t v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4259_; 
v___x_4254_ = lean_unsigned_to_nat(0u);
v_bs_x27_4255_ = lean_array_uset(v_bs_4246_, v_i_4245_, v___x_4254_);
v___x_4256_ = 0;
v___x_4257_ = lean_box(v___x_4256_);
if (v_isShared_4253_ == 0)
{
lean_ctor_set(v___x_4252_, 0, v___x_4257_);
v___x_4259_ = v___x_4252_;
goto v_reusejp_4258_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v___x_4257_);
lean_ctor_set(v_reuseFailAlloc_4265_, 1, v_snd_4250_);
v___x_4259_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4258_;
}
v_reusejp_4258_:
{
lean_object* v___x_4260_; size_t v___x_4261_; size_t v___x_4262_; lean_object* v___x_4263_; 
v___x_4260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4260_, 0, v_fst_4249_);
lean_ctor_set(v___x_4260_, 1, v___x_4259_);
v___x_4261_ = ((size_t)1ULL);
v___x_4262_ = lean_usize_add(v_i_4245_, v___x_4261_);
v___x_4263_ = lean_array_uset(v_bs_x27_4255_, v_i_4245_, v___x_4260_);
v_i_4245_ = v___x_4262_;
v_bs_4246_ = v___x_4263_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6___boxed(lean_object* v_sz_4267_, lean_object* v_i_4268_, lean_object* v_bs_4269_){
_start:
{
size_t v_sz_boxed_4270_; size_t v_i_boxed_4271_; lean_object* v_res_4272_; 
v_sz_boxed_4270_ = lean_unbox_usize(v_sz_4267_);
lean_dec(v_sz_4267_);
v_i_boxed_4271_ = lean_unbox_usize(v_i_4268_);
lean_dec(v_i_4268_);
v_res_4272_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_boxed_4270_, v_i_boxed_4271_, v_bs_4269_);
return v_res_4272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(lean_object* v___x_4273_, lean_object* v_a_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_){
_start:
{
lean_object* v___x_4280_; lean_object* v___x_21856__overap_4281_; lean_object* v___x_4282_; 
v___x_4280_ = l_Lean_instInhabitedExpr;
v___x_21856__overap_4281_ = l_instInhabitedOfMonad___redArg(v___x_4273_, v___x_4280_);
lean_inc(v___y_4278_);
lean_inc_ref(v___y_4277_);
lean_inc(v___y_4276_);
lean_inc_ref(v___y_4275_);
v___x_4282_ = lean_apply_5(v___x_21856__overap_4281_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, lean_box(0));
return v___x_4282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed(lean_object* v___x_4283_, lean_object* v_a_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_){
_start:
{
lean_object* v_res_4290_; 
v_res_4290_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(v___x_4283_, v_a_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec(v___y_4286_);
lean_dec_ref(v___y_4285_);
lean_dec_ref(v_a_4284_);
return v_res_4290_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0(void){
_start:
{
lean_object* v___x_4291_; 
v___x_4291_ = l_instMonadEIO(lean_box(0));
return v___x_4291_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1(void){
_start:
{
lean_object* v___x_4292_; lean_object* v___x_4293_; 
v___x_4292_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0);
v___x_4293_ = l_StateRefT_x27_instMonad___redArg(v___x_4292_);
return v___x_4293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed(lean_object* v_acc_4298_, lean_object* v_declInfos_4299_, lean_object* v_k_4300_, lean_object* v_kind_4301_, lean_object* v_x_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_){
_start:
{
uint8_t v_kind_boxed_4308_; lean_object* v_res_4309_; 
v_kind_boxed_4308_ = lean_unbox(v_kind_4301_);
v_res_4309_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(v_acc_4298_, v_declInfos_4299_, v_k_4300_, v_kind_boxed_4308_, v_x_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
return v_res_4309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(lean_object* v_declInfos_4310_, lean_object* v_k_4311_, uint8_t v_kind_4312_, lean_object* v_acc_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_){
_start:
{
lean_object* v___x_4319_; lean_object* v_toApplicative_4320_; lean_object* v_toFunctor_4321_; lean_object* v_toSeq_4322_; lean_object* v_toSeqLeft_4323_; lean_object* v_toSeqRight_4324_; lean_object* v___f_4325_; lean_object* v___f_4326_; lean_object* v___f_4327_; lean_object* v___f_4328_; lean_object* v___x_4329_; lean_object* v___f_4330_; lean_object* v___f_4331_; lean_object* v___f_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v_toApplicative_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4385_; 
v___x_4319_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1);
v_toApplicative_4320_ = lean_ctor_get(v___x_4319_, 0);
v_toFunctor_4321_ = lean_ctor_get(v_toApplicative_4320_, 0);
v_toSeq_4322_ = lean_ctor_get(v_toApplicative_4320_, 2);
v_toSeqLeft_4323_ = lean_ctor_get(v_toApplicative_4320_, 3);
v_toSeqRight_4324_ = lean_ctor_get(v_toApplicative_4320_, 4);
v___f_4325_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__2));
v___f_4326_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_4321_, 2);
v___f_4327_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4327_, 0, v_toFunctor_4321_);
v___f_4328_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4328_, 0, v_toFunctor_4321_);
v___x_4329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4329_, 0, v___f_4327_);
lean_ctor_set(v___x_4329_, 1, v___f_4328_);
lean_inc(v_toSeqRight_4324_);
v___f_4330_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4330_, 0, v_toSeqRight_4324_);
lean_inc(v_toSeqLeft_4323_);
v___f_4331_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4331_, 0, v_toSeqLeft_4323_);
lean_inc(v_toSeq_4322_);
v___f_4332_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4332_, 0, v_toSeq_4322_);
v___x_4333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4333_, 0, v___x_4329_);
lean_ctor_set(v___x_4333_, 1, v___f_4325_);
lean_ctor_set(v___x_4333_, 2, v___f_4332_);
lean_ctor_set(v___x_4333_, 3, v___f_4331_);
lean_ctor_set(v___x_4333_, 4, v___f_4330_);
v___x_4334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4333_);
lean_ctor_set(v___x_4334_, 1, v___f_4326_);
v___x_4335_ = l_StateRefT_x27_instMonad___redArg(v___x_4334_);
v_toApplicative_4336_ = lean_ctor_get(v___x_4335_, 0);
v_isSharedCheck_4385_ = !lean_is_exclusive(v___x_4335_);
if (v_isSharedCheck_4385_ == 0)
{
lean_object* v_unused_4386_; 
v_unused_4386_ = lean_ctor_get(v___x_4335_, 1);
lean_dec(v_unused_4386_);
v___x_4338_ = v___x_4335_;
v_isShared_4339_ = v_isSharedCheck_4385_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_toApplicative_4336_);
lean_dec(v___x_4335_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4385_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v_toFunctor_4340_; lean_object* v_toSeq_4341_; lean_object* v_toSeqLeft_4342_; lean_object* v_toSeqRight_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4383_; 
v_toFunctor_4340_ = lean_ctor_get(v_toApplicative_4336_, 0);
v_toSeq_4341_ = lean_ctor_get(v_toApplicative_4336_, 2);
v_toSeqLeft_4342_ = lean_ctor_get(v_toApplicative_4336_, 3);
v_toSeqRight_4343_ = lean_ctor_get(v_toApplicative_4336_, 4);
v_isSharedCheck_4383_ = !lean_is_exclusive(v_toApplicative_4336_);
if (v_isSharedCheck_4383_ == 0)
{
lean_object* v_unused_4384_; 
v_unused_4384_ = lean_ctor_get(v_toApplicative_4336_, 1);
lean_dec(v_unused_4384_);
v___x_4345_ = v_toApplicative_4336_;
v_isShared_4346_ = v_isSharedCheck_4383_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_toSeqRight_4343_);
lean_inc(v_toSeqLeft_4342_);
lean_inc(v_toSeq_4341_);
lean_inc(v_toFunctor_4340_);
lean_dec(v_toApplicative_4336_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4383_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___f_4347_; lean_object* v___f_4348_; lean_object* v___f_4349_; lean_object* v___f_4350_; lean_object* v___x_4351_; lean_object* v___f_4352_; lean_object* v___f_4353_; lean_object* v___f_4354_; lean_object* v___x_4356_; 
v___f_4347_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__4));
v___f_4348_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__5));
lean_inc_ref(v_toFunctor_4340_);
v___f_4349_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4349_, 0, v_toFunctor_4340_);
v___f_4350_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4350_, 0, v_toFunctor_4340_);
v___x_4351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4351_, 0, v___f_4349_);
lean_ctor_set(v___x_4351_, 1, v___f_4350_);
v___f_4352_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4352_, 0, v_toSeqRight_4343_);
v___f_4353_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4353_, 0, v_toSeqLeft_4342_);
v___f_4354_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4354_, 0, v_toSeq_4341_);
if (v_isShared_4346_ == 0)
{
lean_ctor_set(v___x_4345_, 4, v___f_4352_);
lean_ctor_set(v___x_4345_, 3, v___f_4353_);
lean_ctor_set(v___x_4345_, 2, v___f_4354_);
lean_ctor_set(v___x_4345_, 1, v___f_4347_);
lean_ctor_set(v___x_4345_, 0, v___x_4351_);
v___x_4356_ = v___x_4345_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v___x_4351_);
lean_ctor_set(v_reuseFailAlloc_4382_, 1, v___f_4347_);
lean_ctor_set(v_reuseFailAlloc_4382_, 2, v___f_4354_);
lean_ctor_set(v_reuseFailAlloc_4382_, 3, v___f_4353_);
lean_ctor_set(v_reuseFailAlloc_4382_, 4, v___f_4352_);
v___x_4356_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
lean_object* v___x_4358_; 
if (v_isShared_4339_ == 0)
{
lean_ctor_set(v___x_4338_, 1, v___f_4348_);
lean_ctor_set(v___x_4338_, 0, v___x_4356_);
v___x_4358_ = v___x_4338_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4381_; 
v_reuseFailAlloc_4381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4381_, 0, v___x_4356_);
lean_ctor_set(v_reuseFailAlloc_4381_, 1, v___f_4348_);
v___x_4358_ = v_reuseFailAlloc_4381_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
lean_object* v___x_4359_; lean_object* v___x_4360_; uint8_t v___x_4361_; 
v___x_4359_ = lean_array_get_size(v_acc_4313_);
v___x_4360_ = lean_array_get_size(v_declInfos_4310_);
v___x_4361_ = lean_nat_dec_lt(v___x_4359_, v___x_4360_);
if (v___x_4361_ == 0)
{
lean_object* v___x_4362_; 
lean_dec_ref(v___x_4358_);
lean_dec_ref(v_declInfos_4310_);
lean_inc(v___y_4317_);
lean_inc_ref(v___y_4316_);
lean_inc(v___y_4315_);
lean_inc_ref(v___y_4314_);
v___x_4362_ = lean_apply_6(v_k_4311_, v_acc_4313_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, lean_box(0));
return v___x_4362_;
}
else
{
lean_object* v___f_4363_; lean_object* v___x_4364_; uint8_t v___x_4365_; lean_object* v___f_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v_snd_4371_; lean_object* v_fst_4372_; lean_object* v_fst_4373_; lean_object* v_snd_4374_; lean_object* v___x_4375_; 
v___f_4363_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4363_, 0, v___x_4358_);
v___x_4364_ = lean_box(0);
v___x_4365_ = 0;
v___f_4366_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4366_, 0, v___f_4363_);
v___x_4367_ = lean_box(v___x_4365_);
v___x_4368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4368_, 0, v___x_4367_);
lean_ctor_set(v___x_4368_, 1, v___f_4366_);
v___x_4369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4369_, 0, v___x_4364_);
lean_ctor_set(v___x_4369_, 1, v___x_4368_);
v___x_4370_ = lean_array_get(v___x_4369_, v_declInfos_4310_, v___x_4359_);
lean_dec_ref_known(v___x_4369_, 2);
v_snd_4371_ = lean_ctor_get(v___x_4370_, 1);
lean_inc(v_snd_4371_);
v_fst_4372_ = lean_ctor_get(v___x_4370_, 0);
lean_inc(v_fst_4372_);
lean_dec(v___x_4370_);
v_fst_4373_ = lean_ctor_get(v_snd_4371_, 0);
lean_inc(v_fst_4373_);
v_snd_4374_ = lean_ctor_get(v_snd_4371_, 1);
lean_inc(v_snd_4374_);
lean_dec(v_snd_4371_);
lean_inc(v___y_4317_);
lean_inc_ref(v___y_4316_);
lean_inc(v___y_4315_);
lean_inc_ref(v___y_4314_);
lean_inc_ref(v_acc_4313_);
v___x_4375_ = lean_apply_6(v_snd_4374_, v_acc_4313_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, lean_box(0));
if (lean_obj_tag(v___x_4375_) == 0)
{
lean_object* v_a_4376_; lean_object* v___x_4377_; lean_object* v___f_4378_; uint8_t v___x_4379_; lean_object* v___x_4380_; 
v_a_4376_ = lean_ctor_get(v___x_4375_, 0);
lean_inc(v_a_4376_);
lean_dec_ref_known(v___x_4375_, 1);
v___x_4377_ = lean_box(v_kind_4312_);
v___f_4378_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed), 10, 4);
lean_closure_set(v___f_4378_, 0, v_acc_4313_);
lean_closure_set(v___f_4378_, 1, v_declInfos_4310_);
lean_closure_set(v___f_4378_, 2, v_k_4311_);
lean_closure_set(v___f_4378_, 3, v___x_4377_);
v___x_4379_ = lean_unbox(v_fst_4373_);
lean_dec(v_fst_4373_);
v___x_4380_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_fst_4372_, v___x_4379_, v_a_4376_, v___f_4378_, v_kind_4312_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_);
return v___x_4380_;
}
else
{
lean_dec(v_fst_4373_);
lean_dec(v_fst_4372_);
lean_dec_ref(v_acc_4313_);
lean_dec_ref(v_k_4311_);
lean_dec_ref(v_declInfos_4310_);
return v___x_4375_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(lean_object* v_acc_4387_, lean_object* v_declInfos_4388_, lean_object* v_k_4389_, uint8_t v_kind_4390_, lean_object* v_x_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_){
_start:
{
lean_object* v___x_4397_; lean_object* v___x_4398_; 
v___x_4397_ = lean_array_push(v_acc_4387_, v_x_4391_);
v___x_4398_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4388_, v_k_4389_, v_kind_4390_, v___x_4397_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___boxed(lean_object* v_declInfos_4399_, lean_object* v_k_4400_, lean_object* v_kind_4401_, lean_object* v_acc_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_){
_start:
{
uint8_t v_kind_boxed_4408_; lean_object* v_res_4409_; 
v_kind_boxed_4408_ = lean_unbox(v_kind_4401_);
v_res_4409_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4399_, v_k_4400_, v_kind_boxed_4408_, v_acc_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
lean_dec(v___y_4406_);
lean_dec_ref(v___y_4405_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
return v_res_4409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(lean_object* v_declInfos_4410_, lean_object* v_k_4411_, uint8_t v_kind_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_){
_start:
{
lean_object* v___x_4418_; lean_object* v___x_4419_; 
v___x_4418_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4419_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4410_, v_k_4411_, v_kind_4412_, v___x_4418_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_);
return v___x_4419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7___boxed(lean_object* v_declInfos_4420_, lean_object* v_k_4421_, lean_object* v_kind_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_){
_start:
{
uint8_t v_kind_boxed_4428_; lean_object* v_res_4429_; 
v_kind_boxed_4428_ = lean_unbox(v_kind_4422_);
v_res_4429_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v_declInfos_4420_, v_k_4421_, v_kind_boxed_4428_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
lean_dec(v___y_4426_);
lean_dec_ref(v___y_4425_);
lean_dec(v___y_4424_);
lean_dec_ref(v___y_4423_);
return v_res_4429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(lean_object* v_declInfos_4430_, lean_object* v_k_4431_, uint8_t v_kind_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_){
_start:
{
size_t v_sz_4438_; size_t v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; 
v_sz_4438_ = lean_array_size(v_declInfos_4430_);
v___x_4439_ = ((size_t)0ULL);
v___x_4440_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_4438_, v___x_4439_, v_declInfos_4430_);
v___x_4441_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v___x_4440_, v_k_4431_, v_kind_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_);
return v___x_4441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5___boxed(lean_object* v_declInfos_4442_, lean_object* v_k_4443_, lean_object* v_kind_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_){
_start:
{
uint8_t v_kind_boxed_4450_; lean_object* v_res_4451_; 
v_kind_boxed_4450_ = lean_unbox(v_kind_4444_);
v_res_4451_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v_declInfos_4442_, v_k_4443_, v_kind_boxed_4450_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec(v___y_4446_);
lean_dec_ref(v___y_4445_);
return v_res_4451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(lean_object* v_declInfos_4452_, lean_object* v_k_4453_, uint8_t v_kind_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_){
_start:
{
size_t v_sz_4460_; size_t v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; 
v_sz_4460_ = lean_array_size(v_declInfos_4452_);
v___x_4461_ = ((size_t)0ULL);
v___x_4462_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_4460_, v___x_4461_, v_declInfos_4452_);
v___x_4463_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v___x_4462_, v_k_4453_, v_kind_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_);
return v___x_4463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4___boxed(lean_object* v_declInfos_4464_, lean_object* v_k_4465_, lean_object* v_kind_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_){
_start:
{
uint8_t v_kind_boxed_4472_; lean_object* v_res_4473_; 
v_kind_boxed_4472_ = lean_unbox(v_kind_4466_);
v_res_4473_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_declInfos_4464_, v_k_4465_, v_kind_boxed_4472_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_);
lean_dec(v___y_4470_);
lean_dec_ref(v___y_4469_);
lean_dec(v___y_4468_);
lean_dec_ref(v___y_4467_);
return v_res_4473_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(lean_object* v_a_4477_, lean_object* v_b_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_){
_start:
{
lean_object* v_array_4484_; lean_object* v_start_4485_; lean_object* v_stop_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4544_; 
v_array_4484_ = lean_ctor_get(v_a_4477_, 0);
v_start_4485_ = lean_ctor_get(v_a_4477_, 1);
v_stop_4486_ = lean_ctor_get(v_a_4477_, 2);
v_isSharedCheck_4544_ = !lean_is_exclusive(v_a_4477_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4488_ = v_a_4477_;
v_isShared_4489_ = v_isSharedCheck_4544_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_stop_4486_);
lean_inc(v_start_4485_);
lean_inc(v_array_4484_);
lean_dec(v_a_4477_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4544_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
uint8_t v___x_4490_; 
v___x_4490_ = lean_nat_dec_lt(v_start_4485_, v_stop_4486_);
if (v___x_4490_ == 0)
{
lean_object* v___x_4491_; 
lean_del_object(v___x_4488_);
lean_dec(v_stop_4486_);
lean_dec(v_start_4485_);
lean_dec_ref(v_array_4484_);
v___x_4491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4491_, 0, v_b_4478_);
return v___x_4491_;
}
else
{
lean_object* v_snd_4492_; lean_object* v_fst_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4543_; 
v_snd_4492_ = lean_ctor_get(v_b_4478_, 1);
v_fst_4493_ = lean_ctor_get(v_b_4478_, 0);
v_isSharedCheck_4543_ = !lean_is_exclusive(v_b_4478_);
if (v_isSharedCheck_4543_ == 0)
{
v___x_4495_ = v_b_4478_;
v_isShared_4496_ = v_isSharedCheck_4543_;
goto v_resetjp_4494_;
}
else
{
lean_inc(v_snd_4492_);
lean_inc(v_fst_4493_);
lean_dec(v_b_4478_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4543_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v_array_4497_; lean_object* v_start_4498_; lean_object* v_stop_4499_; uint8_t v___x_4500_; 
v_array_4497_ = lean_ctor_get(v_snd_4492_, 0);
v_start_4498_ = lean_ctor_get(v_snd_4492_, 1);
v_stop_4499_ = lean_ctor_get(v_snd_4492_, 2);
v___x_4500_ = lean_nat_dec_lt(v_start_4498_, v_stop_4499_);
if (v___x_4500_ == 0)
{
lean_object* v___x_4502_; 
lean_del_object(v___x_4488_);
lean_dec(v_stop_4486_);
lean_dec(v_start_4485_);
lean_dec_ref(v_array_4484_);
if (v_isShared_4496_ == 0)
{
v___x_4502_ = v___x_4495_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v_fst_4493_);
lean_ctor_set(v_reuseFailAlloc_4504_, 1, v_snd_4492_);
v___x_4502_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
lean_object* v___x_4503_; 
v___x_4503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4503_, 0, v___x_4502_);
return v___x_4503_;
}
}
else
{
lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4539_; 
lean_inc(v_stop_4499_);
lean_inc(v_start_4498_);
lean_inc_ref(v_array_4497_);
v_isSharedCheck_4539_ = !lean_is_exclusive(v_snd_4492_);
if (v_isSharedCheck_4539_ == 0)
{
lean_object* v_unused_4540_; lean_object* v_unused_4541_; lean_object* v_unused_4542_; 
v_unused_4540_ = lean_ctor_get(v_snd_4492_, 2);
lean_dec(v_unused_4540_);
v_unused_4541_ = lean_ctor_get(v_snd_4492_, 1);
lean_dec(v_unused_4541_);
v_unused_4542_ = lean_ctor_get(v_snd_4492_, 0);
lean_dec(v_unused_4542_);
v___x_4506_ = v_snd_4492_;
v_isShared_4507_ = v_isSharedCheck_4539_;
goto v_resetjp_4505_;
}
else
{
lean_dec(v_snd_4492_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4539_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; 
v___x_4508_ = lean_array_fget_borrowed(v_array_4484_, v_start_4485_);
v___x_4509_ = lean_array_fget_borrowed(v_array_4497_, v_start_4498_);
lean_inc(v___x_4509_);
lean_inc(v___x_4508_);
v___x_4510_ = l_Lean_Meta_mkEqHEq(v___x_4508_, v___x_4509_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
if (lean_obj_tag(v___x_4510_) == 0)
{
lean_object* v_a_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4515_; 
v_a_4511_ = lean_ctor_get(v___x_4510_, 0);
lean_inc(v_a_4511_);
lean_dec_ref_known(v___x_4510_, 1);
v___x_4512_ = lean_unsigned_to_nat(1u);
v___x_4513_ = lean_nat_add(v_start_4485_, v___x_4512_);
lean_dec(v_start_4485_);
if (v_isShared_4507_ == 0)
{
lean_ctor_set(v___x_4506_, 2, v_stop_4486_);
lean_ctor_set(v___x_4506_, 1, v___x_4513_);
lean_ctor_set(v___x_4506_, 0, v_array_4484_);
v___x_4515_ = v___x_4506_;
goto v_reusejp_4514_;
}
else
{
lean_object* v_reuseFailAlloc_4530_; 
v_reuseFailAlloc_4530_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4530_, 0, v_array_4484_);
lean_ctor_set(v_reuseFailAlloc_4530_, 1, v___x_4513_);
lean_ctor_set(v_reuseFailAlloc_4530_, 2, v_stop_4486_);
v___x_4515_ = v_reuseFailAlloc_4530_;
goto v_reusejp_4514_;
}
v_reusejp_4514_:
{
lean_object* v___x_4516_; lean_object* v___x_4518_; 
v___x_4516_ = lean_nat_add(v_start_4498_, v___x_4512_);
lean_dec(v_start_4498_);
if (v_isShared_4489_ == 0)
{
lean_ctor_set(v___x_4488_, 2, v_stop_4499_);
lean_ctor_set(v___x_4488_, 1, v___x_4516_);
lean_ctor_set(v___x_4488_, 0, v_array_4497_);
v___x_4518_ = v___x_4488_;
goto v_reusejp_4517_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_array_4497_);
lean_ctor_set(v_reuseFailAlloc_4529_, 1, v___x_4516_);
lean_ctor_set(v_reuseFailAlloc_4529_, 2, v_stop_4499_);
v___x_4518_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4517_;
}
v_reusejp_4517_:
{
lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4524_; 
v___x_4519_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg___closed__1));
v___x_4520_ = lean_array_get_size(v_fst_4493_);
v___x_4521_ = lean_nat_add(v___x_4520_, v___x_4512_);
v___x_4522_ = lean_name_append_index_after(v___x_4519_, v___x_4521_);
if (v_isShared_4496_ == 0)
{
lean_ctor_set(v___x_4495_, 1, v_a_4511_);
lean_ctor_set(v___x_4495_, 0, v___x_4522_);
v___x_4524_ = v___x_4495_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4528_; 
v_reuseFailAlloc_4528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4528_, 0, v___x_4522_);
lean_ctor_set(v_reuseFailAlloc_4528_, 1, v_a_4511_);
v___x_4524_ = v_reuseFailAlloc_4528_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
lean_object* v___x_4525_; lean_object* v___x_4526_; 
v___x_4525_ = lean_array_push(v_fst_4493_, v___x_4524_);
v___x_4526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4526_, 0, v___x_4525_);
lean_ctor_set(v___x_4526_, 1, v___x_4518_);
v_a_4477_ = v___x_4515_;
v_b_4478_ = v___x_4526_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4538_; 
lean_del_object(v___x_4506_);
lean_dec(v_stop_4499_);
lean_dec(v_start_4498_);
lean_dec_ref(v_array_4497_);
lean_del_object(v___x_4495_);
lean_dec(v_fst_4493_);
lean_del_object(v___x_4488_);
lean_dec(v_stop_4486_);
lean_dec(v_start_4485_);
lean_dec_ref(v_array_4484_);
v_a_4531_ = lean_ctor_get(v___x_4510_, 0);
v_isSharedCheck_4538_ = !lean_is_exclusive(v___x_4510_);
if (v_isSharedCheck_4538_ == 0)
{
v___x_4533_ = v___x_4510_;
v_isShared_4534_ = v_isSharedCheck_4538_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_a_4531_);
lean_dec(v___x_4510_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4538_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
lean_object* v___x_4536_; 
if (v_isShared_4534_ == 0)
{
v___x_4536_ = v___x_4533_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_a_4531_);
v___x_4536_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
return v___x_4536_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg___boxed(lean_object* v_a_4545_, lean_object* v_b_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_){
_start:
{
lean_object* v_res_4552_; 
v_res_4552_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(v_a_4545_, v_b_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
lean_dec(v___y_4548_);
lean_dec_ref(v___y_4547_);
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(lean_object* v___x_4553_, lean_object* v_a_4554_, lean_object* v___x_4555_, lean_object* v_as_4556_, size_t v_sz_4557_, size_t v_i_4558_, lean_object* v_b_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_){
_start:
{
uint8_t v___x_4565_; 
v___x_4565_ = lean_usize_dec_lt(v_i_4558_, v_sz_4557_);
if (v___x_4565_ == 0)
{
lean_object* v___x_4566_; 
lean_dec(v___x_4555_);
v___x_4566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4566_, 0, v_b_4559_);
return v___x_4566_;
}
else
{
lean_object* v___x_4567_; lean_object* v_a_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; 
v___x_4567_ = l_Lean_instInhabitedExpr;
v_a_4568_ = lean_array_uget_borrowed(v_as_4556_, v_i_4558_);
v___x_4569_ = lean_array_get_borrowed(v___x_4567_, v___x_4553_, v_a_4568_);
lean_inc(v___x_4569_);
v___x_4570_ = l_Lean_Meta_instantiateForall(v___x_4569_, v_a_4554_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_);
if (lean_obj_tag(v___x_4570_) == 0)
{
lean_object* v_a_4571_; lean_object* v___x_4572_; 
v_a_4571_ = lean_ctor_get(v___x_4570_, 0);
lean_inc(v_a_4571_);
lean_dec_ref_known(v___x_4570_, 1);
lean_inc(v___x_4555_);
v___x_4572_ = l_Lean_Meta_Match_simpH_x3f(v_a_4571_, v___x_4555_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_);
if (lean_obj_tag(v___x_4572_) == 0)
{
lean_object* v_a_4573_; lean_object* v_a_4575_; 
v_a_4573_ = lean_ctor_get(v___x_4572_, 0);
lean_inc(v_a_4573_);
lean_dec_ref_known(v___x_4572_, 1);
if (lean_obj_tag(v_a_4573_) == 1)
{
lean_object* v_val_4579_; lean_object* v___x_4580_; 
v_val_4579_ = lean_ctor_get(v_a_4573_, 0);
lean_inc(v_val_4579_);
lean_dec_ref_known(v_a_4573_, 1);
v___x_4580_ = lean_array_push(v_b_4559_, v_val_4579_);
v_a_4575_ = v___x_4580_;
goto v___jp_4574_;
}
else
{
lean_dec(v_a_4573_);
v_a_4575_ = v_b_4559_;
goto v___jp_4574_;
}
v___jp_4574_:
{
size_t v___x_4576_; size_t v___x_4577_; 
v___x_4576_ = ((size_t)1ULL);
v___x_4577_ = lean_usize_add(v_i_4558_, v___x_4576_);
v_i_4558_ = v___x_4577_;
v_b_4559_ = v_a_4575_;
goto _start;
}
}
else
{
lean_object* v_a_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4588_; 
lean_dec_ref(v_b_4559_);
lean_dec(v___x_4555_);
v_a_4581_ = lean_ctor_get(v___x_4572_, 0);
v_isSharedCheck_4588_ = !lean_is_exclusive(v___x_4572_);
if (v_isSharedCheck_4588_ == 0)
{
v___x_4583_ = v___x_4572_;
v_isShared_4584_ = v_isSharedCheck_4588_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_a_4581_);
lean_dec(v___x_4572_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4588_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v___x_4586_; 
if (v_isShared_4584_ == 0)
{
v___x_4586_ = v___x_4583_;
goto v_reusejp_4585_;
}
else
{
lean_object* v_reuseFailAlloc_4587_; 
v_reuseFailAlloc_4587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4587_, 0, v_a_4581_);
v___x_4586_ = v_reuseFailAlloc_4587_;
goto v_reusejp_4585_;
}
v_reusejp_4585_:
{
return v___x_4586_;
}
}
}
}
else
{
lean_object* v_a_4589_; lean_object* v___x_4591_; uint8_t v_isShared_4592_; uint8_t v_isSharedCheck_4596_; 
lean_dec_ref(v_b_4559_);
lean_dec(v___x_4555_);
v_a_4589_ = lean_ctor_get(v___x_4570_, 0);
v_isSharedCheck_4596_ = !lean_is_exclusive(v___x_4570_);
if (v_isSharedCheck_4596_ == 0)
{
v___x_4591_ = v___x_4570_;
v_isShared_4592_ = v_isSharedCheck_4596_;
goto v_resetjp_4590_;
}
else
{
lean_inc(v_a_4589_);
lean_dec(v___x_4570_);
v___x_4591_ = lean_box(0);
v_isShared_4592_ = v_isSharedCheck_4596_;
goto v_resetjp_4590_;
}
v_resetjp_4590_:
{
lean_object* v___x_4594_; 
if (v_isShared_4592_ == 0)
{
v___x_4594_ = v___x_4591_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4595_; 
v_reuseFailAlloc_4595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4595_, 0, v_a_4589_);
v___x_4594_ = v_reuseFailAlloc_4595_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
return v___x_4594_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___boxed(lean_object* v___x_4597_, lean_object* v_a_4598_, lean_object* v___x_4599_, lean_object* v_as_4600_, lean_object* v_sz_4601_, lean_object* v_i_4602_, lean_object* v_b_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_){
_start:
{
size_t v_sz_boxed_4609_; size_t v_i_boxed_4610_; lean_object* v_res_4611_; 
v_sz_boxed_4609_ = lean_unbox_usize(v_sz_4601_);
lean_dec(v_sz_4601_);
v_i_boxed_4610_ = lean_unbox_usize(v_i_4602_);
lean_dec(v_i_4602_);
v_res_4611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(v___x_4597_, v_a_4598_, v___x_4599_, v_as_4600_, v_sz_boxed_4609_, v_i_boxed_4610_, v_b_4603_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_);
lean_dec(v___y_4607_);
lean_dec_ref(v___y_4606_);
lean_dec(v___y_4605_);
lean_dec_ref(v___y_4604_);
lean_dec_ref(v_as_4600_);
lean_dec_ref(v_a_4598_);
lean_dec_ref(v___x_4597_);
return v_res_4611_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(lean_object* v___y_4612_, lean_object* v_args_4613_, lean_object* v___x_4614_, lean_object* v_overlaps_4615_, lean_object* v_a_4616_, lean_object* v_fst_4617_, lean_object* v_a_4618_, lean_object* v___x_4619_, lean_object* v___x_4620_, lean_object* v___x_4621_, lean_object* v___x_4622_, lean_object* v_altVars_4623_, uint8_t v___x_4624_, uint8_t v___x_4625_, lean_object* v_a_4626_, lean_object* v___x_4627_, lean_object* v___x_4628_, lean_object* v___x_4629_, lean_object* v___x_4630_, lean_object* v___x_4631_, lean_object* v___x_4632_, lean_object* v___x_4633_, lean_object* v_matchDeclName_4634_, lean_object* v___x_4635_, lean_object* v___x_4636_, lean_object* v___x_4637_, lean_object* v_heqs_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_){
_start:
{
lean_object* v___x_4644_; lean_object* v___x_4645_; 
v___x_4644_ = l_Lean_mkAppN(v___y_4612_, v_args_4613_);
lean_inc_ref(v_heqs_4638_);
v___x_4645_ = l_Lean_Meta_Match_mkAppDiscrEqs(v___x_4644_, v_heqs_4638_, v___x_4614_, v___y_4639_, v___y_4640_, v___y_4641_, v___y_4642_);
if (lean_obj_tag(v___x_4645_) == 0)
{
lean_object* v_a_4646_; lean_object* v___x_4647_; size_t v_sz_4648_; size_t v___x_4649_; lean_object* v___x_4650_; 
v_a_4646_ = lean_ctor_get(v___x_4645_, 0);
lean_inc(v_a_4646_);
lean_dec_ref_known(v___x_4645_, 1);
v___x_4647_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_4615_, v_a_4616_);
v_sz_4648_ = lean_array_size(v___x_4647_);
v___x_4649_ = ((size_t)0ULL);
lean_inc_ref(v___x_4620_);
v___x_4650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(v_fst_4617_, v_a_4618_, v___x_4619_, v___x_4647_, v_sz_4648_, v___x_4649_, v___x_4620_, v___y_4639_, v___y_4640_, v___y_4641_, v___y_4642_);
lean_dec_ref(v___x_4647_);
if (lean_obj_tag(v___x_4650_) == 0)
{
lean_object* v_a_4651_; lean_object* v___y_4653_; lean_object* v___y_4654_; lean_object* v___y_4655_; lean_object* v___y_4656_; lean_object* v_options_4763_; uint8_t v_hasTrace_4764_; 
v_a_4651_ = lean_ctor_get(v___x_4650_, 0);
lean_inc(v_a_4651_);
lean_dec_ref_known(v___x_4650_, 1);
v_options_4763_ = lean_ctor_get(v___y_4641_, 2);
v_hasTrace_4764_ = lean_ctor_get_uint8(v_options_4763_, sizeof(void*)*1);
if (v_hasTrace_4764_ == 0)
{
v___y_4653_ = v___y_4639_;
v___y_4654_ = v___y_4640_;
v___y_4655_ = v___y_4641_;
v___y_4656_ = v___y_4642_;
goto v___jp_4652_;
}
else
{
lean_object* v_inheritedTraceOptions_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; uint8_t v___x_4768_; 
v_inheritedTraceOptions_4765_ = lean_ctor_get(v___y_4641_, 13);
v___x_4766_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_4767_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_4768_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4765_, v_options_4763_, v___x_4767_);
if (v___x_4768_ == 0)
{
v___y_4653_ = v___y_4639_;
v___y_4654_ = v___y_4640_;
v___y_4655_ = v___y_4641_;
v___y_4656_ = v___y_4642_;
goto v___jp_4652_;
}
else
{
lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; 
v___x_4769_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_4651_);
v___x_4770_ = lean_array_to_list(v_a_4651_);
v___x_4771_ = lean_box(0);
v___x_4772_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_4770_, v___x_4771_);
v___x_4773_ = l_Lean_MessageData_ofList(v___x_4772_);
v___x_4774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4774_, 0, v___x_4769_);
lean_ctor_set(v___x_4774_, 1, v___x_4773_);
v___x_4775_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_4766_, v___x_4774_, v___y_4639_, v___y_4640_, v___y_4641_, v___y_4642_);
if (lean_obj_tag(v___x_4775_) == 0)
{
lean_dec_ref_known(v___x_4775_, 1);
v___y_4653_ = v___y_4639_;
v___y_4654_ = v___y_4640_;
v___y_4655_ = v___y_4641_;
v___y_4656_ = v___y_4642_;
goto v___jp_4652_;
}
else
{
lean_object* v_a_4776_; lean_object* v___x_4778_; uint8_t v_isShared_4779_; uint8_t v_isSharedCheck_4783_; 
lean_dec(v_a_4651_);
lean_dec(v_a_4646_);
lean_dec_ref(v_heqs_4638_);
lean_dec(v___x_4637_);
lean_dec(v___x_4636_);
lean_dec(v___x_4635_);
lean_dec(v_matchDeclName_4634_);
lean_dec_ref(v___x_4631_);
lean_dec_ref(v___x_4630_);
lean_dec_ref(v___x_4628_);
lean_dec(v___x_4627_);
lean_dec_ref(v___x_4622_);
lean_dec(v___x_4621_);
lean_dec_ref(v___x_4620_);
lean_dec_ref(v_a_4618_);
v_a_4776_ = lean_ctor_get(v___x_4775_, 0);
v_isSharedCheck_4783_ = !lean_is_exclusive(v___x_4775_);
if (v_isSharedCheck_4783_ == 0)
{
v___x_4778_ = v___x_4775_;
v_isShared_4779_ = v_isSharedCheck_4783_;
goto v_resetjp_4777_;
}
else
{
lean_inc(v_a_4776_);
lean_dec(v___x_4775_);
v___x_4778_ = lean_box(0);
v_isShared_4779_ = v_isSharedCheck_4783_;
goto v_resetjp_4777_;
}
v_resetjp_4777_:
{
lean_object* v___x_4781_; 
if (v_isShared_4779_ == 0)
{
v___x_4781_ = v___x_4778_;
goto v_reusejp_4780_;
}
else
{
lean_object* v_reuseFailAlloc_4782_; 
v_reuseFailAlloc_4782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4782_, 0, v_a_4776_);
v___x_4781_ = v_reuseFailAlloc_4782_;
goto v_reusejp_4780_;
}
v_reusejp_4780_:
{
return v___x_4781_;
}
}
}
}
}
v___jp_4652_:
{
lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; size_t v_sz_4664_; lean_object* v___x_4665_; 
v___x_4657_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
v___x_4658_ = l_Array_reverse___redArg(v_a_4618_);
v___x_4659_ = lean_array_get_size(v___x_4658_);
v___x_4660_ = l_Array_toSubarray___redArg(v___x_4658_, v___x_4621_, v___x_4659_);
lean_inc_ref(v___x_4622_);
v___x_4661_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_4622_, v___x_4620_);
v___x_4662_ = l_Array_reverse___redArg(v___x_4661_);
v___x_4663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4663_, 0, v___x_4657_);
lean_ctor_set(v___x_4663_, 1, v___x_4660_);
v_sz_4664_ = lean_array_size(v___x_4662_);
v___x_4665_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_4662_, v_sz_4664_, v___x_4649_, v___x_4663_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_);
lean_dec_ref(v___x_4662_);
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_object* v_a_4666_; lean_object* v_fst_4667_; lean_object* v___x_4669_; uint8_t v_isShared_4670_; uint8_t v_isSharedCheck_4753_; 
v_a_4666_ = lean_ctor_get(v___x_4665_, 0);
lean_inc(v_a_4666_);
lean_dec_ref_known(v___x_4665_, 1);
v_fst_4667_ = lean_ctor_get(v_a_4666_, 0);
v_isSharedCheck_4753_ = !lean_is_exclusive(v_a_4666_);
if (v_isSharedCheck_4753_ == 0)
{
lean_object* v_unused_4754_; 
v_unused_4754_ = lean_ctor_get(v_a_4666_, 1);
lean_dec(v_unused_4754_);
v___x_4669_ = v_a_4666_;
v_isShared_4670_ = v_isSharedCheck_4753_;
goto v_resetjp_4668_;
}
else
{
lean_inc(v_fst_4667_);
lean_dec(v_a_4666_);
v___x_4669_ = lean_box(0);
v_isShared_4670_ = v_isSharedCheck_4753_;
goto v_resetjp_4668_;
}
v_resetjp_4668_:
{
lean_object* v___x_4671_; lean_object* v___x_4672_; uint8_t v___x_4673_; lean_object* v___x_4674_; 
v___x_4671_ = l_Subarray_copy___redArg(v___x_4622_);
lean_inc_ref(v___x_4671_);
v___x_4672_ = l_Array_append___redArg(v___x_4671_, v_altVars_4623_);
v___x_4673_ = 1;
v___x_4674_ = l_Lean_Meta_mkForallFVars(v___x_4672_, v_fst_4667_, v___x_4624_, v___x_4625_, v___x_4625_, v___x_4673_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_);
lean_dec_ref(v___x_4672_);
if (lean_obj_tag(v___x_4674_) == 0)
{
lean_object* v_a_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; 
v_a_4675_ = lean_ctor_get(v___x_4674_, 0);
lean_inc(v_a_4675_);
lean_dec_ref_known(v___x_4674_, 1);
v___x_4676_ = l_Lean_ConstantInfo_name(v_a_4626_);
v___x_4677_ = l_Lean_mkConst(v___x_4676_, v___x_4627_);
lean_inc_ref(v___x_4628_);
v___x_4678_ = l_Subarray_copy___redArg(v___x_4628_);
v___x_4679_ = lean_mk_empty_array_with_capacity(v___x_4629_);
v___x_4680_ = lean_array_push(v___x_4679_, v___x_4630_);
v___x_4681_ = l_Array_append___redArg(v___x_4678_, v___x_4680_);
lean_dec_ref(v___x_4680_);
v___x_4682_ = l_Array_append___redArg(v___x_4681_, v___x_4671_);
lean_dec_ref(v___x_4671_);
v___x_4683_ = l_Subarray_copy___redArg(v___x_4631_);
v___x_4684_ = l_Array_append___redArg(v___x_4682_, v___x_4683_);
lean_dec_ref(v___x_4683_);
v___x_4685_ = l_Lean_mkAppN(v___x_4677_, v___x_4684_);
v___x_4686_ = l_Lean_Meta_mkHEq(v___x_4685_, v_a_4646_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_);
if (lean_obj_tag(v___x_4686_) == 0)
{
lean_object* v_a_4687_; lean_object* v___x_4688_; 
v_a_4687_ = lean_ctor_get(v___x_4686_, 0);
lean_inc(v_a_4687_);
lean_dec_ref_known(v___x_4686_, 1);
v___x_4688_ = l_Lean_mkArrowN(v_a_4651_, v_a_4687_, v___y_4655_, v___y_4656_);
lean_dec(v_a_4651_);
if (lean_obj_tag(v___x_4688_) == 0)
{
lean_object* v_a_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; 
v_a_4689_ = lean_ctor_get(v___x_4688_, 0);
lean_inc(v_a_4689_);
lean_dec_ref_known(v___x_4688_, 1);
v___x_4690_ = l_Array_append___redArg(v___x_4684_, v_altVars_4623_);
v___x_4691_ = l_Array_append___redArg(v___x_4690_, v_heqs_4638_);
v___x_4692_ = l_Lean_Meta_mkForallFVars(v___x_4691_, v_a_4689_, v___x_4624_, v___x_4625_, v___x_4625_, v___x_4673_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_);
lean_dec_ref(v___x_4691_);
if (lean_obj_tag(v___x_4692_) == 0)
{
lean_object* v_a_4693_; lean_object* v___x_4694_; 
v_a_4693_ = lean_ctor_get(v___x_4692_, 0);
lean_inc(v_a_4693_);
lean_dec_ref_known(v___x_4692_, 1);
v___x_4694_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_4693_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_);
if (lean_obj_tag(v___x_4694_) == 0)
{
lean_object* v_a_4695_; lean_object* v___x_4697_; uint8_t v_isShared_4698_; uint8_t v_isSharedCheck_4752_; 
v_a_4695_ = lean_ctor_get(v___x_4694_, 0);
v_isSharedCheck_4752_ = !lean_is_exclusive(v___x_4694_);
if (v_isSharedCheck_4752_ == 0)
{
v___x_4697_ = v___x_4694_;
v_isShared_4698_ = v_isSharedCheck_4752_;
goto v_resetjp_4696_;
}
else
{
lean_inc(v_a_4695_);
lean_dec(v___x_4694_);
v___x_4697_ = lean_box(0);
v_isShared_4698_ = v_isSharedCheck_4752_;
goto v_resetjp_4696_;
}
v_resetjp_4696_:
{
lean_object* v_start_4699_; lean_object* v_stop_4700_; lean_object* v___x_4702_; uint8_t v_isShared_4703_; uint8_t v_isSharedCheck_4750_; 
v_start_4699_ = lean_ctor_get(v___x_4628_, 1);
v_stop_4700_ = lean_ctor_get(v___x_4628_, 2);
v_isSharedCheck_4750_ = !lean_is_exclusive(v___x_4628_);
if (v_isSharedCheck_4750_ == 0)
{
lean_object* v_unused_4751_; 
v_unused_4751_ = lean_ctor_get(v___x_4628_, 0);
lean_dec(v_unused_4751_);
v___x_4702_ = v___x_4628_;
v_isShared_4703_ = v_isSharedCheck_4750_;
goto v_resetjp_4701_;
}
else
{
lean_inc(v_stop_4700_);
lean_inc(v_start_4699_);
lean_dec(v___x_4628_);
v___x_4702_ = lean_box(0);
v_isShared_4703_ = v_isSharedCheck_4750_;
goto v_resetjp_4701_;
}
v_resetjp_4701_:
{
lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; 
v___x_4704_ = lean_nat_sub(v_stop_4700_, v_start_4699_);
lean_dec(v_start_4699_);
lean_dec(v_stop_4700_);
v___x_4705_ = lean_nat_add(v___x_4704_, v___x_4629_);
lean_dec(v___x_4704_);
v___x_4706_ = lean_nat_add(v___x_4705_, v___x_4632_);
lean_dec(v___x_4705_);
v___x_4707_ = lean_nat_add(v___x_4706_, v___x_4633_);
lean_dec(v___x_4706_);
v___x_4708_ = lean_array_get_size(v_altVars_4623_);
v___x_4709_ = lean_nat_add(v___x_4707_, v___x_4708_);
lean_dec(v___x_4707_);
v___x_4710_ = lean_array_get_size(v_heqs_4638_);
lean_dec_ref(v_heqs_4638_);
lean_inc(v_a_4695_);
v___x_4711_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_4634_, v_a_4695_, v___x_4709_, v___x_4710_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_);
if (lean_obj_tag(v___x_4711_) == 0)
{
lean_object* v_a_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4749_; 
v_a_4712_ = lean_ctor_get(v___x_4711_, 0);
v_isSharedCheck_4749_ = !lean_is_exclusive(v___x_4711_);
if (v_isSharedCheck_4749_ == 0)
{
v___x_4714_ = v___x_4711_;
v_isShared_4715_ = v_isSharedCheck_4749_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_a_4712_);
lean_dec(v___x_4711_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4749_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v___x_4716_; lean_object* v_env_4717_; uint8_t v___x_4718_; 
v___x_4716_ = lean_st_ref_get(v___y_4656_);
v_env_4717_ = lean_ctor_get(v___x_4716_, 0);
lean_inc_ref(v_env_4717_);
lean_dec(v___x_4716_);
lean_inc(v___x_4635_);
v___x_4718_ = l_Lean_Environment_contains(v_env_4717_, v___x_4635_, v___x_4625_);
if (v___x_4718_ == 0)
{
lean_object* v___x_4720_; 
lean_del_object(v___x_4714_);
lean_inc(v___x_4635_);
if (v_isShared_4703_ == 0)
{
lean_ctor_set(v___x_4702_, 2, v_a_4695_);
lean_ctor_set(v___x_4702_, 1, v___x_4636_);
lean_ctor_set(v___x_4702_, 0, v___x_4635_);
v___x_4720_ = v___x_4702_;
goto v_reusejp_4719_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v___x_4635_);
lean_ctor_set(v_reuseFailAlloc_4745_, 1, v___x_4636_);
lean_ctor_set(v_reuseFailAlloc_4745_, 2, v_a_4695_);
v___x_4720_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4719_;
}
v_reusejp_4719_:
{
lean_object* v___x_4722_; 
if (v_isShared_4670_ == 0)
{
lean_ctor_set_tag(v___x_4669_, 1);
lean_ctor_set(v___x_4669_, 1, v___x_4637_);
lean_ctor_set(v___x_4669_, 0, v___x_4635_);
v___x_4722_ = v___x_4669_;
goto v_reusejp_4721_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v___x_4635_);
lean_ctor_set(v_reuseFailAlloc_4744_, 1, v___x_4637_);
v___x_4722_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4721_;
}
v_reusejp_4721_:
{
lean_object* v___x_4723_; lean_object* v___x_4725_; 
v___x_4723_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4723_, 0, v___x_4720_);
lean_ctor_set(v___x_4723_, 1, v_a_4712_);
lean_ctor_set(v___x_4723_, 2, v___x_4722_);
if (v_isShared_4698_ == 0)
{
lean_ctor_set_tag(v___x_4697_, 2);
lean_ctor_set(v___x_4697_, 0, v___x_4723_);
v___x_4725_ = v___x_4697_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v___x_4723_);
v___x_4725_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
lean_object* v___x_4726_; 
v___x_4726_ = l_Lean_addDecl(v___x_4725_, v___x_4624_, v___y_4655_, v___y_4656_);
if (lean_obj_tag(v___x_4726_) == 0)
{
lean_object* v___x_4728_; uint8_t v_isShared_4729_; uint8_t v_isSharedCheck_4733_; 
v_isSharedCheck_4733_ = !lean_is_exclusive(v___x_4726_);
if (v_isSharedCheck_4733_ == 0)
{
lean_object* v_unused_4734_; 
v_unused_4734_ = lean_ctor_get(v___x_4726_, 0);
lean_dec(v_unused_4734_);
v___x_4728_ = v___x_4726_;
v_isShared_4729_ = v_isSharedCheck_4733_;
goto v_resetjp_4727_;
}
else
{
lean_dec(v___x_4726_);
v___x_4728_ = lean_box(0);
v_isShared_4729_ = v_isSharedCheck_4733_;
goto v_resetjp_4727_;
}
v_resetjp_4727_:
{
lean_object* v___x_4731_; 
if (v_isShared_4729_ == 0)
{
lean_ctor_set(v___x_4728_, 0, v_a_4675_);
v___x_4731_ = v___x_4728_;
goto v_reusejp_4730_;
}
else
{
lean_object* v_reuseFailAlloc_4732_; 
v_reuseFailAlloc_4732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4732_, 0, v_a_4675_);
v___x_4731_ = v_reuseFailAlloc_4732_;
goto v_reusejp_4730_;
}
v_reusejp_4730_:
{
return v___x_4731_;
}
}
}
else
{
lean_object* v_a_4735_; lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4742_; 
lean_dec(v_a_4675_);
v_a_4735_ = lean_ctor_get(v___x_4726_, 0);
v_isSharedCheck_4742_ = !lean_is_exclusive(v___x_4726_);
if (v_isSharedCheck_4742_ == 0)
{
v___x_4737_ = v___x_4726_;
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
else
{
lean_inc(v_a_4735_);
lean_dec(v___x_4726_);
v___x_4737_ = lean_box(0);
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
v_resetjp_4736_:
{
lean_object* v___x_4740_; 
if (v_isShared_4738_ == 0)
{
v___x_4740_ = v___x_4737_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v_a_4735_);
v___x_4740_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
return v___x_4740_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4747_; 
lean_dec(v_a_4712_);
lean_del_object(v___x_4702_);
lean_del_object(v___x_4697_);
lean_dec(v_a_4695_);
lean_del_object(v___x_4669_);
lean_dec(v___x_4637_);
lean_dec(v___x_4636_);
lean_dec(v___x_4635_);
if (v_isShared_4715_ == 0)
{
lean_ctor_set(v___x_4714_, 0, v_a_4675_);
v___x_4747_ = v___x_4714_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_a_4675_);
v___x_4747_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
return v___x_4747_;
}
}
}
}
else
{
lean_del_object(v___x_4702_);
lean_del_object(v___x_4697_);
lean_dec(v_a_4695_);
lean_dec(v_a_4675_);
lean_del_object(v___x_4669_);
lean_dec(v___x_4637_);
lean_dec(v___x_4636_);
lean_dec(v___x_4635_);
return v___x_4711_;
}
}
}
}
else
{
lean_dec(v_a_4675_);
lean_del_object(v___x_4669_);
lean_dec_ref(v_heqs_4638_);
lean_dec(v___x_4637_);
lean_dec(v___x_4636_);
lean_dec(v___x_4635_);
lean_dec(v_matchDeclName_4634_);
lean_dec_ref(v___x_4628_);
return v___x_4694_;
}
}
else
{
lean_dec(v_a_4675_);
lean_del_object(v___x_4669_);
lean_dec_ref(v_heqs_4638_);
lean_dec(v___x_4637_);
lean_dec(v___x_4636_);
lean_dec(v___x_4635_);
lean_dec(v_matchDeclName_4634_);
lean_dec_ref(v___x_4628_);
return v___x_4692_;
}
}
else
{
lean_dec_ref(v___x_4684_);
lean_dec(v_a_4675_);
lean_del_object(v___x_4669_);
lean_dec_ref(v_heqs_4638_);
lean_dec(v___x_4637_);
lean_dec(v___x_4636_);
lean_dec(v___x_4635_);
lean_dec(v_matchDeclName_4634_);
lean_dec_ref(v___x_4628_);
return v___x_4688_;
}
}
else
{
lean_dec_ref(v___x_4684_);
lean_dec(v_a_4675_);
lean_del_object(v___x_4669_);
lean_dec(v_a_4651_);
lean_dec_ref(v_heqs_4638_);
lean_dec(v___x_4637_);
lean_dec(v___x_4636_);
lean_dec(v___x_4635_);
lean_dec(v_matchDeclName_4634_);
lean_dec_ref(v___x_4628_);
return v___x_4686_;
}
}
else
{
lean_dec_ref(v___x_4671_);
lean_del_object(v___x_4669_);
lean_dec(v_a_4651_);
lean_dec(v_a_4646_);
lean_dec_ref(v_heqs_4638_);
lean_dec(v___x_4637_);
lean_dec(v___x_4636_);
lean_dec(v___x_4635_);
lean_dec(v_matchDeclName_4634_);
lean_dec_ref(v___x_4631_);
lean_dec_ref(v___x_4630_);
lean_dec_ref(v___x_4628_);
lean_dec(v___x_4627_);
return v___x_4674_;
}
}
}
else
{
lean_object* v_a_4755_; lean_object* v___x_4757_; uint8_t v_isShared_4758_; uint8_t v_isSharedCheck_4762_; 
lean_dec(v_a_4651_);
lean_dec(v_a_4646_);
lean_dec_ref(v_heqs_4638_);
lean_dec(v___x_4637_);
lean_dec(v___x_4636_);
lean_dec(v___x_4635_);
lean_dec(v_matchDeclName_4634_);
lean_dec_ref(v___x_4631_);
lean_dec_ref(v___x_4630_);
lean_dec_ref(v___x_4628_);
lean_dec(v___x_4627_);
lean_dec_ref(v___x_4622_);
v_a_4755_ = lean_ctor_get(v___x_4665_, 0);
v_isSharedCheck_4762_ = !lean_is_exclusive(v___x_4665_);
if (v_isSharedCheck_4762_ == 0)
{
v___x_4757_ = v___x_4665_;
v_isShared_4758_ = v_isSharedCheck_4762_;
goto v_resetjp_4756_;
}
else
{
lean_inc(v_a_4755_);
lean_dec(v___x_4665_);
v___x_4757_ = lean_box(0);
v_isShared_4758_ = v_isSharedCheck_4762_;
goto v_resetjp_4756_;
}
v_resetjp_4756_:
{
lean_object* v___x_4760_; 
if (v_isShared_4758_ == 0)
{
v___x_4760_ = v___x_4757_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v_a_4755_);
v___x_4760_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
return v___x_4760_;
}
}
}
}
}
else
{
lean_object* v_a_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4791_; 
lean_dec(v_a_4646_);
lean_dec_ref(v_heqs_4638_);
lean_dec(v___x_4637_);
lean_dec(v___x_4636_);
lean_dec(v___x_4635_);
lean_dec(v_matchDeclName_4634_);
lean_dec_ref(v___x_4631_);
lean_dec_ref(v___x_4630_);
lean_dec_ref(v___x_4628_);
lean_dec(v___x_4627_);
lean_dec_ref(v___x_4622_);
lean_dec(v___x_4621_);
lean_dec_ref(v___x_4620_);
lean_dec_ref(v_a_4618_);
v_a_4784_ = lean_ctor_get(v___x_4650_, 0);
v_isSharedCheck_4791_ = !lean_is_exclusive(v___x_4650_);
if (v_isSharedCheck_4791_ == 0)
{
v___x_4786_ = v___x_4650_;
v_isShared_4787_ = v_isSharedCheck_4791_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_a_4784_);
lean_dec(v___x_4650_);
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
lean_dec_ref(v_heqs_4638_);
lean_dec(v___x_4637_);
lean_dec(v___x_4636_);
lean_dec(v___x_4635_);
lean_dec(v_matchDeclName_4634_);
lean_dec_ref(v___x_4631_);
lean_dec_ref(v___x_4630_);
lean_dec_ref(v___x_4628_);
lean_dec(v___x_4627_);
lean_dec_ref(v___x_4622_);
lean_dec(v___x_4621_);
lean_dec_ref(v___x_4620_);
lean_dec(v___x_4619_);
lean_dec_ref(v_a_4618_);
return v___x_4645_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___y_4792_ = _args[0];
lean_object* v_args_4793_ = _args[1];
lean_object* v___x_4794_ = _args[2];
lean_object* v_overlaps_4795_ = _args[3];
lean_object* v_a_4796_ = _args[4];
lean_object* v_fst_4797_ = _args[5];
lean_object* v_a_4798_ = _args[6];
lean_object* v___x_4799_ = _args[7];
lean_object* v___x_4800_ = _args[8];
lean_object* v___x_4801_ = _args[9];
lean_object* v___x_4802_ = _args[10];
lean_object* v_altVars_4803_ = _args[11];
lean_object* v___x_4804_ = _args[12];
lean_object* v___x_4805_ = _args[13];
lean_object* v_a_4806_ = _args[14];
lean_object* v___x_4807_ = _args[15];
lean_object* v___x_4808_ = _args[16];
lean_object* v___x_4809_ = _args[17];
lean_object* v___x_4810_ = _args[18];
lean_object* v___x_4811_ = _args[19];
lean_object* v___x_4812_ = _args[20];
lean_object* v___x_4813_ = _args[21];
lean_object* v_matchDeclName_4814_ = _args[22];
lean_object* v___x_4815_ = _args[23];
lean_object* v___x_4816_ = _args[24];
lean_object* v___x_4817_ = _args[25];
lean_object* v_heqs_4818_ = _args[26];
lean_object* v___y_4819_ = _args[27];
lean_object* v___y_4820_ = _args[28];
lean_object* v___y_4821_ = _args[29];
lean_object* v___y_4822_ = _args[30];
lean_object* v___y_4823_ = _args[31];
_start:
{
uint8_t v___x_22596__boxed_4824_; uint8_t v___x_22597__boxed_4825_; lean_object* v_res_4826_; 
v___x_22596__boxed_4824_ = lean_unbox(v___x_4804_);
v___x_22597__boxed_4825_ = lean_unbox(v___x_4805_);
v_res_4826_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(v___y_4792_, v_args_4793_, v___x_4794_, v_overlaps_4795_, v_a_4796_, v_fst_4797_, v_a_4798_, v___x_4799_, v___x_4800_, v___x_4801_, v___x_4802_, v_altVars_4803_, v___x_22596__boxed_4824_, v___x_22597__boxed_4825_, v_a_4806_, v___x_4807_, v___x_4808_, v___x_4809_, v___x_4810_, v___x_4811_, v___x_4812_, v___x_4813_, v_matchDeclName_4814_, v___x_4815_, v___x_4816_, v___x_4817_, v_heqs_4818_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_);
lean_dec(v___y_4822_);
lean_dec_ref(v___y_4821_);
lean_dec(v___y_4820_);
lean_dec_ref(v___y_4819_);
lean_dec(v___x_4813_);
lean_dec(v___x_4812_);
lean_dec(v___x_4809_);
lean_dec_ref(v_a_4806_);
lean_dec_ref(v_altVars_4803_);
lean_dec(v_fst_4797_);
lean_dec(v_a_4796_);
lean_dec_ref(v_overlaps_4795_);
lean_dec_ref(v_args_4793_);
return v_res_4826_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; 
v___x_4829_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__1));
v___x_4830_ = lean_unsigned_to_nat(8u);
v___x_4831_ = lean_unsigned_to_nat(295u);
v___x_4832_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__0));
v___x_4833_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_4834_ = l_mkPanicMessageWithDecl(v___x_4833_, v___x_4832_, v___x_4831_, v___x_4830_, v___x_4829_);
return v___x_4834_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(lean_object* v___f_4835_, lean_object* v___x_4836_, lean_object* v___x_4837_, lean_object* v___y_4838_, lean_object* v___x_4839_, lean_object* v_overlaps_4840_, lean_object* v_a_4841_, lean_object* v_fst_4842_, lean_object* v___x_4843_, lean_object* v_a_4844_, lean_object* v___x_4845_, lean_object* v___x_4846_, lean_object* v___x_4847_, lean_object* v___x_4848_, lean_object* v___x_4849_, lean_object* v___x_4850_, lean_object* v_matchDeclName_4851_, lean_object* v___x_4852_, lean_object* v___x_4853_, lean_object* v___x_4854_, lean_object* v_altVars_4855_, lean_object* v_args_4856_, lean_object* v___mask_4857_, lean_object* v_altResultType_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_){
_start:
{
uint8_t v___x_4864_; lean_object* v___x_4865_; 
v___x_4864_ = 0;
v___x_4865_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_altResultType_4858_, v___f_4835_, v___x_4864_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_);
if (lean_obj_tag(v___x_4865_) == 0)
{
lean_object* v_a_4866_; lean_object* v_start_4867_; lean_object* v_stop_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; uint8_t v___x_4871_; 
v_a_4866_ = lean_ctor_get(v___x_4865_, 0);
lean_inc(v_a_4866_);
lean_dec_ref_known(v___x_4865_, 1);
v_start_4867_ = lean_ctor_get(v___x_4836_, 1);
v_stop_4868_ = lean_ctor_get(v___x_4836_, 2);
v___x_4869_ = lean_array_get_size(v_a_4866_);
v___x_4870_ = lean_nat_sub(v_stop_4868_, v_start_4867_);
v___x_4871_ = lean_nat_dec_eq(v___x_4869_, v___x_4870_);
if (v___x_4871_ == 0)
{
lean_object* v___x_4872_; lean_object* v___x_4873_; 
lean_dec(v___x_4870_);
lean_dec(v_a_4866_);
lean_dec_ref(v_args_4856_);
lean_dec_ref(v_altVars_4855_);
lean_dec(v___x_4854_);
lean_dec(v___x_4853_);
lean_dec(v___x_4852_);
lean_dec(v_matchDeclName_4851_);
lean_dec(v___x_4850_);
lean_dec_ref(v___x_4849_);
lean_dec_ref(v___x_4848_);
lean_dec(v___x_4847_);
lean_dec_ref(v___x_4846_);
lean_dec(v___x_4845_);
lean_dec_ref(v_a_4844_);
lean_dec_ref(v___x_4843_);
lean_dec(v_fst_4842_);
lean_dec(v_a_4841_);
lean_dec_ref(v_overlaps_4840_);
lean_dec(v___x_4839_);
lean_dec_ref(v___y_4838_);
lean_dec(v___x_4837_);
lean_dec_ref(v___x_4836_);
v___x_4872_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2);
v___x_4873_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v___x_4872_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_);
return v___x_4873_;
}
else
{
lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; 
v___x_4874_ = lean_mk_empty_array_with_capacity(v___x_4837_);
lean_inc(v___x_4837_);
lean_inc(v_a_4866_);
v___x_4875_ = l_Array_toSubarray___redArg(v_a_4866_, v___x_4837_, v___x_4869_);
v___x_4876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4876_, 0, v___x_4874_);
lean_ctor_set(v___x_4876_, 1, v___x_4875_);
lean_inc_ref(v___x_4836_);
v___x_4877_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(v___x_4836_, v___x_4876_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_);
if (lean_obj_tag(v___x_4877_) == 0)
{
lean_object* v_a_4878_; lean_object* v_fst_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___f_4882_; uint8_t v___x_4883_; lean_object* v___x_4884_; 
v_a_4878_ = lean_ctor_get(v___x_4877_, 0);
lean_inc(v_a_4878_);
lean_dec_ref_known(v___x_4877_, 1);
v_fst_4879_ = lean_ctor_get(v_a_4878_, 0);
lean_inc(v_fst_4879_);
lean_dec(v_a_4878_);
v___x_4880_ = lean_box(v___x_4864_);
v___x_4881_ = lean_box(v___x_4871_);
v___f_4882_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed), 32, 26);
lean_closure_set(v___f_4882_, 0, v___y_4838_);
lean_closure_set(v___f_4882_, 1, v_args_4856_);
lean_closure_set(v___f_4882_, 2, v___x_4839_);
lean_closure_set(v___f_4882_, 3, v_overlaps_4840_);
lean_closure_set(v___f_4882_, 4, v_a_4841_);
lean_closure_set(v___f_4882_, 5, v_fst_4842_);
lean_closure_set(v___f_4882_, 6, v_a_4866_);
lean_closure_set(v___f_4882_, 7, v___x_4869_);
lean_closure_set(v___f_4882_, 8, v___x_4843_);
lean_closure_set(v___f_4882_, 9, v___x_4837_);
lean_closure_set(v___f_4882_, 10, v___x_4836_);
lean_closure_set(v___f_4882_, 11, v_altVars_4855_);
lean_closure_set(v___f_4882_, 12, v___x_4880_);
lean_closure_set(v___f_4882_, 13, v___x_4881_);
lean_closure_set(v___f_4882_, 14, v_a_4844_);
lean_closure_set(v___f_4882_, 15, v___x_4845_);
lean_closure_set(v___f_4882_, 16, v___x_4846_);
lean_closure_set(v___f_4882_, 17, v___x_4847_);
lean_closure_set(v___f_4882_, 18, v___x_4848_);
lean_closure_set(v___f_4882_, 19, v___x_4849_);
lean_closure_set(v___f_4882_, 20, v___x_4870_);
lean_closure_set(v___f_4882_, 21, v___x_4850_);
lean_closure_set(v___f_4882_, 22, v_matchDeclName_4851_);
lean_closure_set(v___f_4882_, 23, v___x_4852_);
lean_closure_set(v___f_4882_, 24, v___x_4853_);
lean_closure_set(v___f_4882_, 25, v___x_4854_);
v___x_4883_ = 0;
v___x_4884_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_fst_4879_, v___f_4882_, v___x_4883_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_);
return v___x_4884_;
}
else
{
lean_object* v_a_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4892_; 
lean_dec(v___x_4870_);
lean_dec(v_a_4866_);
lean_dec_ref(v_args_4856_);
lean_dec_ref(v_altVars_4855_);
lean_dec(v___x_4854_);
lean_dec(v___x_4853_);
lean_dec(v___x_4852_);
lean_dec(v_matchDeclName_4851_);
lean_dec(v___x_4850_);
lean_dec_ref(v___x_4849_);
lean_dec_ref(v___x_4848_);
lean_dec(v___x_4847_);
lean_dec_ref(v___x_4846_);
lean_dec(v___x_4845_);
lean_dec_ref(v_a_4844_);
lean_dec_ref(v___x_4843_);
lean_dec(v_fst_4842_);
lean_dec(v_a_4841_);
lean_dec_ref(v_overlaps_4840_);
lean_dec(v___x_4839_);
lean_dec_ref(v___y_4838_);
lean_dec(v___x_4837_);
lean_dec_ref(v___x_4836_);
v_a_4885_ = lean_ctor_get(v___x_4877_, 0);
v_isSharedCheck_4892_ = !lean_is_exclusive(v___x_4877_);
if (v_isSharedCheck_4892_ == 0)
{
v___x_4887_ = v___x_4877_;
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
else
{
lean_inc(v_a_4885_);
lean_dec(v___x_4877_);
v___x_4887_ = lean_box(0);
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
v_resetjp_4886_:
{
lean_object* v___x_4890_; 
if (v_isShared_4888_ == 0)
{
v___x_4890_ = v___x_4887_;
goto v_reusejp_4889_;
}
else
{
lean_object* v_reuseFailAlloc_4891_; 
v_reuseFailAlloc_4891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4891_, 0, v_a_4885_);
v___x_4890_ = v_reuseFailAlloc_4891_;
goto v_reusejp_4889_;
}
v_reusejp_4889_:
{
return v___x_4890_;
}
}
}
}
}
else
{
lean_object* v_a_4893_; lean_object* v___x_4895_; uint8_t v_isShared_4896_; uint8_t v_isSharedCheck_4900_; 
lean_dec_ref(v_args_4856_);
lean_dec_ref(v_altVars_4855_);
lean_dec(v___x_4854_);
lean_dec(v___x_4853_);
lean_dec(v___x_4852_);
lean_dec(v_matchDeclName_4851_);
lean_dec(v___x_4850_);
lean_dec_ref(v___x_4849_);
lean_dec_ref(v___x_4848_);
lean_dec(v___x_4847_);
lean_dec_ref(v___x_4846_);
lean_dec(v___x_4845_);
lean_dec_ref(v_a_4844_);
lean_dec_ref(v___x_4843_);
lean_dec(v_fst_4842_);
lean_dec(v_a_4841_);
lean_dec_ref(v_overlaps_4840_);
lean_dec(v___x_4839_);
lean_dec_ref(v___y_4838_);
lean_dec(v___x_4837_);
lean_dec_ref(v___x_4836_);
v_a_4893_ = lean_ctor_get(v___x_4865_, 0);
v_isSharedCheck_4900_ = !lean_is_exclusive(v___x_4865_);
if (v_isSharedCheck_4900_ == 0)
{
v___x_4895_ = v___x_4865_;
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
else
{
lean_inc(v_a_4893_);
lean_dec(v___x_4865_);
v___x_4895_ = lean_box(0);
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
v_resetjp_4894_:
{
lean_object* v___x_4898_; 
if (v_isShared_4896_ == 0)
{
v___x_4898_ = v___x_4895_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4899_; 
v_reuseFailAlloc_4899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4899_, 0, v_a_4893_);
v___x_4898_ = v_reuseFailAlloc_4899_;
goto v_reusejp_4897_;
}
v_reusejp_4897_:
{
return v___x_4898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___f_4901_ = _args[0];
lean_object* v___x_4902_ = _args[1];
lean_object* v___x_4903_ = _args[2];
lean_object* v___y_4904_ = _args[3];
lean_object* v___x_4905_ = _args[4];
lean_object* v_overlaps_4906_ = _args[5];
lean_object* v_a_4907_ = _args[6];
lean_object* v_fst_4908_ = _args[7];
lean_object* v___x_4909_ = _args[8];
lean_object* v_a_4910_ = _args[9];
lean_object* v___x_4911_ = _args[10];
lean_object* v___x_4912_ = _args[11];
lean_object* v___x_4913_ = _args[12];
lean_object* v___x_4914_ = _args[13];
lean_object* v___x_4915_ = _args[14];
lean_object* v___x_4916_ = _args[15];
lean_object* v_matchDeclName_4917_ = _args[16];
lean_object* v___x_4918_ = _args[17];
lean_object* v___x_4919_ = _args[18];
lean_object* v___x_4920_ = _args[19];
lean_object* v_altVars_4921_ = _args[20];
lean_object* v_args_4922_ = _args[21];
lean_object* v___mask_4923_ = _args[22];
lean_object* v_altResultType_4924_ = _args[23];
lean_object* v___y_4925_ = _args[24];
lean_object* v___y_4926_ = _args[25];
lean_object* v___y_4927_ = _args[26];
lean_object* v___y_4928_ = _args[27];
lean_object* v___y_4929_ = _args[28];
_start:
{
lean_object* v_res_4930_; 
v_res_4930_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(v___f_4901_, v___x_4902_, v___x_4903_, v___y_4904_, v___x_4905_, v_overlaps_4906_, v_a_4907_, v_fst_4908_, v___x_4909_, v_a_4910_, v___x_4911_, v___x_4912_, v___x_4913_, v___x_4914_, v___x_4915_, v___x_4916_, v_matchDeclName_4917_, v___x_4918_, v___x_4919_, v___x_4920_, v_altVars_4921_, v_args_4922_, v___mask_4923_, v_altResultType_4924_, v___y_4925_, v___y_4926_, v___y_4927_, v___y_4928_);
lean_dec(v___y_4928_);
lean_dec_ref(v___y_4927_);
lean_dec(v___y_4926_);
lean_dec_ref(v___y_4925_);
lean_dec_ref(v___mask_4923_);
return v_res_4930_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(lean_object* v_upperBound_4932_, lean_object* v_val_4933_, lean_object* v_matchDeclName_4934_, lean_object* v___x_4935_, lean_object* v___x_4936_, lean_object* v_a_4937_, lean_object* v___x_4938_, lean_object* v___x_4939_, lean_object* v___x_4940_, lean_object* v___x_4941_, lean_object* v___x_4942_, lean_object* v___x_4943_, lean_object* v_a_4944_, lean_object* v_b_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_){
_start:
{
uint8_t v___x_4951_; 
v___x_4951_ = lean_nat_dec_lt(v_a_4944_, v_upperBound_4932_);
if (v___x_4951_ == 0)
{
lean_object* v___x_4952_; 
lean_dec(v_a_4944_);
lean_dec(v___x_4943_);
lean_dec(v___x_4942_);
lean_dec_ref(v___x_4941_);
lean_dec_ref(v___x_4940_);
lean_dec_ref(v___x_4939_);
lean_dec(v___x_4938_);
lean_dec_ref(v_a_4937_);
lean_dec(v___x_4936_);
lean_dec_ref(v___x_4935_);
lean_dec(v_matchDeclName_4934_);
lean_dec_ref(v_val_4933_);
v___x_4952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4952_, 0, v_b_4945_);
return v___x_4952_;
}
else
{
lean_object* v_snd_4953_; lean_object* v_fst_4954_; lean_object* v___x_4956_; uint8_t v_isShared_4957_; uint8_t v_isSharedCheck_5017_; 
v_snd_4953_ = lean_ctor_get(v_b_4945_, 1);
v_fst_4954_ = lean_ctor_get(v_b_4945_, 0);
v_isSharedCheck_5017_ = !lean_is_exclusive(v_b_4945_);
if (v_isSharedCheck_5017_ == 0)
{
v___x_4956_ = v_b_4945_;
v_isShared_4957_ = v_isSharedCheck_5017_;
goto v_resetjp_4955_;
}
else
{
lean_inc(v_snd_4953_);
lean_inc(v_fst_4954_);
lean_dec(v_b_4945_);
v___x_4956_ = lean_box(0);
v_isShared_4957_ = v_isSharedCheck_5017_;
goto v_resetjp_4955_;
}
v_resetjp_4955_:
{
lean_object* v_fst_4958_; lean_object* v_snd_4959_; lean_object* v___x_4961_; uint8_t v_isShared_4962_; uint8_t v_isSharedCheck_5016_; 
v_fst_4958_ = lean_ctor_get(v_snd_4953_, 0);
v_snd_4959_ = lean_ctor_get(v_snd_4953_, 1);
v_isSharedCheck_5016_ = !lean_is_exclusive(v_snd_4953_);
if (v_isSharedCheck_5016_ == 0)
{
v___x_4961_ = v_snd_4953_;
v_isShared_4962_ = v_isSharedCheck_5016_;
goto v_resetjp_4960_;
}
else
{
lean_inc(v_snd_4959_);
lean_inc(v_fst_4958_);
lean_dec(v_snd_4953_);
v___x_4961_ = lean_box(0);
v_isShared_4962_ = v_isSharedCheck_5016_;
goto v_resetjp_4960_;
}
v_resetjp_4960_:
{
lean_object* v_altInfos_4963_; lean_object* v_overlaps_4964_; lean_object* v_start_4965_; lean_object* v_stop_4966_; lean_object* v___f_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___y_4979_; lean_object* v___x_5011_; uint8_t v___x_5012_; 
v_altInfos_4963_ = lean_ctor_get(v_val_4933_, 2);
v_overlaps_4964_ = lean_ctor_get(v_val_4933_, 5);
v_start_4965_ = lean_ctor_get(v___x_4941_, 1);
v_stop_4966_ = lean_ctor_get(v___x_4941_, 2);
v___f_4967_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___closed__0));
v___x_4968_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_4969_ = lean_unsigned_to_nat(0u);
v___x_4970_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4971_ = lean_unsigned_to_nat(1u);
v___x_4972_ = lean_box(0);
v___x_4973_ = lean_array_get_borrowed(v___x_4968_, v_altInfos_4963_, v_a_4944_);
v___x_4974_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_4934_);
v___x_4975_ = l_Lean_Name_str___override(v_matchDeclName_4934_, v___x_4974_);
lean_inc(v_snd_4959_);
v___x_4976_ = lean_name_append_index_after(v___x_4975_, v_snd_4959_);
lean_inc(v___x_4976_);
v___x_4977_ = lean_array_push(v_fst_4954_, v___x_4976_);
v___x_5011_ = lean_nat_sub(v_stop_4966_, v_start_4965_);
v___x_5012_ = lean_nat_dec_lt(v_a_4944_, v___x_5011_);
lean_dec(v___x_5011_);
if (v___x_5012_ == 0)
{
lean_object* v___x_5013_; lean_object* v___x_5014_; 
v___x_5013_ = l_Lean_instInhabitedExpr;
v___x_5014_ = l_outOfBounds___redArg(v___x_5013_);
v___y_4979_ = v___x_5014_;
goto v___jp_4978_;
}
else
{
lean_object* v___x_5015_; 
v___x_5015_ = l_Subarray_get___redArg(v___x_4941_, v_a_4944_);
v___y_4979_ = v___x_5015_;
goto v___jp_4978_;
}
v___jp_4978_:
{
lean_object* v___x_4980_; 
lean_inc(v___y_4949_);
lean_inc_ref(v___y_4948_);
lean_inc(v___y_4947_);
lean_inc_ref(v___y_4946_);
lean_inc_ref(v___y_4979_);
v___x_4980_ = lean_infer_type(v___y_4979_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_);
if (lean_obj_tag(v___x_4980_) == 0)
{
lean_object* v_a_4981_; lean_object* v___f_4982_; lean_object* v___x_4983_; 
v_a_4981_ = lean_ctor_get(v___x_4980_, 0);
lean_inc(v_a_4981_);
lean_dec_ref_known(v___x_4980_, 1);
lean_inc(v___x_4943_);
lean_inc(v_matchDeclName_4934_);
lean_inc(v___x_4942_);
lean_inc_ref(v___x_4941_);
lean_inc_ref(v___x_4940_);
lean_inc_ref(v___x_4939_);
lean_inc(v___x_4938_);
lean_inc_ref(v_a_4937_);
lean_inc(v_fst_4958_);
lean_inc(v_a_4944_);
lean_inc_ref(v_overlaps_4964_);
lean_inc(v___x_4936_);
lean_inc_ref(v___x_4935_);
v___f_4982_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed), 29, 20);
lean_closure_set(v___f_4982_, 0, v___f_4967_);
lean_closure_set(v___f_4982_, 1, v___x_4935_);
lean_closure_set(v___f_4982_, 2, v___x_4969_);
lean_closure_set(v___f_4982_, 3, v___y_4979_);
lean_closure_set(v___f_4982_, 4, v___x_4936_);
lean_closure_set(v___f_4982_, 5, v_overlaps_4964_);
lean_closure_set(v___f_4982_, 6, v_a_4944_);
lean_closure_set(v___f_4982_, 7, v_fst_4958_);
lean_closure_set(v___f_4982_, 8, v___x_4970_);
lean_closure_set(v___f_4982_, 9, v_a_4937_);
lean_closure_set(v___f_4982_, 10, v___x_4938_);
lean_closure_set(v___f_4982_, 11, v___x_4939_);
lean_closure_set(v___f_4982_, 12, v___x_4971_);
lean_closure_set(v___f_4982_, 13, v___x_4940_);
lean_closure_set(v___f_4982_, 14, v___x_4941_);
lean_closure_set(v___f_4982_, 15, v___x_4942_);
lean_closure_set(v___f_4982_, 16, v_matchDeclName_4934_);
lean_closure_set(v___f_4982_, 17, v___x_4976_);
lean_closure_set(v___f_4982_, 18, v___x_4943_);
lean_closure_set(v___f_4982_, 19, v___x_4972_);
lean_inc(v___x_4973_);
v___x_4983_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_a_4981_, v___x_4973_, v___f_4982_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_);
if (lean_obj_tag(v___x_4983_) == 0)
{
lean_object* v_a_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4988_; 
v_a_4984_ = lean_ctor_get(v___x_4983_, 0);
lean_inc(v_a_4984_);
lean_dec_ref_known(v___x_4983_, 1);
v___x_4985_ = lean_array_push(v_fst_4958_, v_a_4984_);
v___x_4986_ = lean_nat_add(v_snd_4959_, v___x_4971_);
lean_dec(v_snd_4959_);
if (v_isShared_4962_ == 0)
{
lean_ctor_set(v___x_4961_, 1, v___x_4986_);
lean_ctor_set(v___x_4961_, 0, v___x_4985_);
v___x_4988_ = v___x_4961_;
goto v_reusejp_4987_;
}
else
{
lean_object* v_reuseFailAlloc_4994_; 
v_reuseFailAlloc_4994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4994_, 0, v___x_4985_);
lean_ctor_set(v_reuseFailAlloc_4994_, 1, v___x_4986_);
v___x_4988_ = v_reuseFailAlloc_4994_;
goto v_reusejp_4987_;
}
v_reusejp_4987_:
{
lean_object* v___x_4990_; 
if (v_isShared_4957_ == 0)
{
lean_ctor_set(v___x_4956_, 1, v___x_4988_);
lean_ctor_set(v___x_4956_, 0, v___x_4977_);
v___x_4990_ = v___x_4956_;
goto v_reusejp_4989_;
}
else
{
lean_object* v_reuseFailAlloc_4993_; 
v_reuseFailAlloc_4993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4993_, 0, v___x_4977_);
lean_ctor_set(v_reuseFailAlloc_4993_, 1, v___x_4988_);
v___x_4990_ = v_reuseFailAlloc_4993_;
goto v_reusejp_4989_;
}
v_reusejp_4989_:
{
lean_object* v___x_4991_; 
v___x_4991_ = lean_nat_add(v_a_4944_, v___x_4971_);
lean_dec(v_a_4944_);
v_a_4944_ = v___x_4991_;
v_b_4945_ = v___x_4990_;
goto _start;
}
}
}
else
{
lean_object* v_a_4995_; lean_object* v___x_4997_; uint8_t v_isShared_4998_; uint8_t v_isSharedCheck_5002_; 
lean_dec_ref(v___x_4977_);
lean_del_object(v___x_4961_);
lean_dec(v_snd_4959_);
lean_dec(v_fst_4958_);
lean_del_object(v___x_4956_);
lean_dec(v_a_4944_);
lean_dec(v___x_4943_);
lean_dec(v___x_4942_);
lean_dec_ref(v___x_4941_);
lean_dec_ref(v___x_4940_);
lean_dec_ref(v___x_4939_);
lean_dec(v___x_4938_);
lean_dec_ref(v_a_4937_);
lean_dec(v___x_4936_);
lean_dec_ref(v___x_4935_);
lean_dec(v_matchDeclName_4934_);
lean_dec_ref(v_val_4933_);
v_a_4995_ = lean_ctor_get(v___x_4983_, 0);
v_isSharedCheck_5002_ = !lean_is_exclusive(v___x_4983_);
if (v_isSharedCheck_5002_ == 0)
{
v___x_4997_ = v___x_4983_;
v_isShared_4998_ = v_isSharedCheck_5002_;
goto v_resetjp_4996_;
}
else
{
lean_inc(v_a_4995_);
lean_dec(v___x_4983_);
v___x_4997_ = lean_box(0);
v_isShared_4998_ = v_isSharedCheck_5002_;
goto v_resetjp_4996_;
}
v_resetjp_4996_:
{
lean_object* v___x_5000_; 
if (v_isShared_4998_ == 0)
{
v___x_5000_ = v___x_4997_;
goto v_reusejp_4999_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5001_, 0, v_a_4995_);
v___x_5000_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4999_;
}
v_reusejp_4999_:
{
return v___x_5000_;
}
}
}
}
else
{
lean_object* v_a_5003_; lean_object* v___x_5005_; uint8_t v_isShared_5006_; uint8_t v_isSharedCheck_5010_; 
lean_dec_ref(v___y_4979_);
lean_dec_ref(v___x_4977_);
lean_dec(v___x_4976_);
lean_del_object(v___x_4961_);
lean_dec(v_snd_4959_);
lean_dec(v_fst_4958_);
lean_del_object(v___x_4956_);
lean_dec(v_a_4944_);
lean_dec(v___x_4943_);
lean_dec(v___x_4942_);
lean_dec_ref(v___x_4941_);
lean_dec_ref(v___x_4940_);
lean_dec_ref(v___x_4939_);
lean_dec(v___x_4938_);
lean_dec_ref(v_a_4937_);
lean_dec(v___x_4936_);
lean_dec_ref(v___x_4935_);
lean_dec(v_matchDeclName_4934_);
lean_dec_ref(v_val_4933_);
v_a_5003_ = lean_ctor_get(v___x_4980_, 0);
v_isSharedCheck_5010_ = !lean_is_exclusive(v___x_4980_);
if (v_isSharedCheck_5010_ == 0)
{
v___x_5005_ = v___x_4980_;
v_isShared_5006_ = v_isSharedCheck_5010_;
goto v_resetjp_5004_;
}
else
{
lean_inc(v_a_5003_);
lean_dec(v___x_4980_);
v___x_5005_ = lean_box(0);
v_isShared_5006_ = v_isSharedCheck_5010_;
goto v_resetjp_5004_;
}
v_resetjp_5004_:
{
lean_object* v___x_5008_; 
if (v_isShared_5006_ == 0)
{
v___x_5008_ = v___x_5005_;
goto v_reusejp_5007_;
}
else
{
lean_object* v_reuseFailAlloc_5009_; 
v_reuseFailAlloc_5009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5009_, 0, v_a_5003_);
v___x_5008_ = v_reuseFailAlloc_5009_;
goto v_reusejp_5007_;
}
v_reusejp_5007_:
{
return v___x_5008_;
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
lean_object* v_upperBound_5018_ = _args[0];
lean_object* v_val_5019_ = _args[1];
lean_object* v_matchDeclName_5020_ = _args[2];
lean_object* v___x_5021_ = _args[3];
lean_object* v___x_5022_ = _args[4];
lean_object* v_a_5023_ = _args[5];
lean_object* v___x_5024_ = _args[6];
lean_object* v___x_5025_ = _args[7];
lean_object* v___x_5026_ = _args[8];
lean_object* v___x_5027_ = _args[9];
lean_object* v___x_5028_ = _args[10];
lean_object* v___x_5029_ = _args[11];
lean_object* v_a_5030_ = _args[12];
lean_object* v_b_5031_ = _args[13];
lean_object* v___y_5032_ = _args[14];
lean_object* v___y_5033_ = _args[15];
lean_object* v___y_5034_ = _args[16];
lean_object* v___y_5035_ = _args[17];
lean_object* v___y_5036_ = _args[18];
_start:
{
lean_object* v_res_5037_; 
v_res_5037_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5018_, v_val_5019_, v_matchDeclName_5020_, v___x_5021_, v___x_5022_, v_a_5023_, v___x_5024_, v___x_5025_, v___x_5026_, v___x_5027_, v___x_5028_, v___x_5029_, v_a_5030_, v_b_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_);
lean_dec(v___y_5035_);
lean_dec_ref(v___y_5034_);
lean_dec(v___y_5033_);
lean_dec_ref(v___y_5032_);
lean_dec(v_upperBound_5018_);
return v_res_5037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(lean_object* v_val_5044_, lean_object* v___x_5045_, lean_object* v_matchDeclName_5046_, lean_object* v___x_5047_, lean_object* v_a_5048_, lean_object* v___x_5049_, lean_object* v___x_5050_, lean_object* v_xs_5051_, lean_object* v___matchResultType_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_){
_start:
{
lean_object* v_numParams_5058_; lean_object* v_numDiscrs_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v_lower_5065_; lean_object* v_upper_5066_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; uint8_t v___x_5097_; 
v_numParams_5058_ = lean_ctor_get(v_val_5044_, 0);
v_numDiscrs_5059_ = lean_ctor_get(v_val_5044_, 1);
v___x_5060_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5058_);
lean_inc_ref(v_xs_5051_);
v___x_5061_ = l_Array_toSubarray___redArg(v_xs_5051_, v___x_5060_, v_numParams_5058_);
v___x_5062_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_5044_);
v___x_5063_ = lean_array_get(v___x_5045_, v_xs_5051_, v___x_5062_);
lean_dec(v___x_5062_);
v___x_5094_ = lean_array_get_size(v_xs_5051_);
v___x_5095_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5044_);
v___x_5096_ = lean_nat_sub(v___x_5094_, v___x_5095_);
lean_dec(v___x_5095_);
v___x_5097_ = lean_nat_dec_le(v___x_5096_, v___x_5060_);
if (v___x_5097_ == 0)
{
v_lower_5065_ = v___x_5096_;
v_upper_5066_ = v___x_5094_;
goto v___jp_5064_;
}
else
{
lean_dec(v___x_5096_);
v_lower_5065_ = v___x_5060_;
v_upper_5066_ = v___x_5094_;
goto v___jp_5064_;
}
v___jp_5064_:
{
lean_object* v___x_5067_; lean_object* v_start_5068_; lean_object* v_stop_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; 
lean_inc_ref(v_xs_5051_);
v___x_5067_ = l_Array_toSubarray___redArg(v_xs_5051_, v_lower_5065_, v_upper_5066_);
v_start_5068_ = lean_ctor_get(v___x_5067_, 1);
lean_inc(v_start_5068_);
v_stop_5069_ = lean_ctor_get(v___x_5067_, 2);
lean_inc(v_stop_5069_);
v___x_5070_ = lean_unsigned_to_nat(1u);
v___x_5071_ = lean_nat_add(v_numParams_5058_, v___x_5070_);
v___x_5072_ = lean_nat_add(v___x_5071_, v_numDiscrs_5059_);
v___x_5073_ = lean_nat_sub(v_stop_5069_, v_start_5068_);
lean_dec(v_start_5068_);
lean_dec(v_stop_5069_);
v___x_5074_ = l_Array_toSubarray___redArg(v_xs_5051_, v___x_5071_, v___x_5072_);
v___x_5075_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__1));
lean_inc(v___x_5073_);
v___x_5076_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v___x_5073_, v_val_5044_, v_matchDeclName_5046_, v___x_5074_, v___x_5047_, v_a_5048_, v___x_5049_, v___x_5061_, v___x_5063_, v___x_5067_, v___x_5073_, v___x_5050_, v___x_5060_, v___x_5075_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_);
lean_dec(v___x_5073_);
if (lean_obj_tag(v___x_5076_) == 0)
{
lean_object* v___x_5078_; uint8_t v_isShared_5079_; uint8_t v_isSharedCheck_5084_; 
v_isSharedCheck_5084_ = !lean_is_exclusive(v___x_5076_);
if (v_isSharedCheck_5084_ == 0)
{
lean_object* v_unused_5085_; 
v_unused_5085_ = lean_ctor_get(v___x_5076_, 0);
lean_dec(v_unused_5085_);
v___x_5078_ = v___x_5076_;
v_isShared_5079_ = v_isSharedCheck_5084_;
goto v_resetjp_5077_;
}
else
{
lean_dec(v___x_5076_);
v___x_5078_ = lean_box(0);
v_isShared_5079_ = v_isSharedCheck_5084_;
goto v_resetjp_5077_;
}
v_resetjp_5077_:
{
lean_object* v___x_5080_; lean_object* v___x_5082_; 
v___x_5080_ = lean_box(0);
if (v_isShared_5079_ == 0)
{
lean_ctor_set(v___x_5078_, 0, v___x_5080_);
v___x_5082_ = v___x_5078_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v___x_5080_);
v___x_5082_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
return v___x_5082_;
}
}
}
else
{
lean_object* v_a_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5093_; 
v_a_5086_ = lean_ctor_get(v___x_5076_, 0);
v_isSharedCheck_5093_ = !lean_is_exclusive(v___x_5076_);
if (v_isSharedCheck_5093_ == 0)
{
v___x_5088_ = v___x_5076_;
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_a_5086_);
lean_dec(v___x_5076_);
v___x_5088_ = lean_box(0);
v_isShared_5089_ = v_isSharedCheck_5093_;
goto v_resetjp_5087_;
}
v_resetjp_5087_:
{
lean_object* v___x_5091_; 
if (v_isShared_5089_ == 0)
{
v___x_5091_ = v___x_5088_;
goto v_reusejp_5090_;
}
else
{
lean_object* v_reuseFailAlloc_5092_; 
v_reuseFailAlloc_5092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5092_, 0, v_a_5086_);
v___x_5091_ = v_reuseFailAlloc_5092_;
goto v_reusejp_5090_;
}
v_reusejp_5090_:
{
return v___x_5091_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed(lean_object* v_val_5098_, lean_object* v___x_5099_, lean_object* v_matchDeclName_5100_, lean_object* v___x_5101_, lean_object* v_a_5102_, lean_object* v___x_5103_, lean_object* v___x_5104_, lean_object* v_xs_5105_, lean_object* v___matchResultType_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_){
_start:
{
lean_object* v_res_5112_; 
v_res_5112_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(v_val_5098_, v___x_5099_, v_matchDeclName_5100_, v___x_5101_, v_a_5102_, v___x_5103_, v___x_5104_, v_xs_5105_, v___matchResultType_5106_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_);
lean_dec(v___y_5110_);
lean_dec_ref(v___y_5109_);
lean_dec(v___y_5108_);
lean_dec_ref(v___y_5107_);
lean_dec_ref(v___matchResultType_5106_);
lean_dec_ref(v___x_5099_);
return v_res_5112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(lean_object* v_matchDeclName_5113_, lean_object* v_a_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_){
_start:
{
uint8_t v_trackZetaDelta_5119_; lean_object* v_zetaDeltaSet_5120_; lean_object* v_lctx_5121_; lean_object* v_localInstances_5122_; lean_object* v_defEqCtx_x3f_5123_; lean_object* v_synthPendingDepth_5124_; lean_object* v_customCanUnfoldPredicate_x3f_5125_; uint8_t v_univApprox_5126_; uint8_t v_inTypeClassResolution_5127_; uint8_t v_cacheInferType_5128_; lean_object* v___x_5129_; lean_object* v___x_5131_; uint8_t v_isShared_5132_; uint8_t v_isSharedCheck_5172_; 
v_trackZetaDelta_5119_ = lean_ctor_get_uint8(v_a_5114_, sizeof(void*)*7);
v_zetaDeltaSet_5120_ = lean_ctor_get(v_a_5114_, 1);
lean_inc(v_zetaDeltaSet_5120_);
v_lctx_5121_ = lean_ctor_get(v_a_5114_, 2);
lean_inc_ref(v_lctx_5121_);
v_localInstances_5122_ = lean_ctor_get(v_a_5114_, 3);
lean_inc_ref(v_localInstances_5122_);
v_defEqCtx_x3f_5123_ = lean_ctor_get(v_a_5114_, 4);
lean_inc(v_defEqCtx_x3f_5123_);
v_synthPendingDepth_5124_ = lean_ctor_get(v_a_5114_, 5);
lean_inc(v_synthPendingDepth_5124_);
v_customCanUnfoldPredicate_x3f_5125_ = lean_ctor_get(v_a_5114_, 6);
lean_inc(v_customCanUnfoldPredicate_x3f_5125_);
v_univApprox_5126_ = lean_ctor_get_uint8(v_a_5114_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_5127_ = lean_ctor_get_uint8(v_a_5114_, sizeof(void*)*7 + 2);
v_cacheInferType_5128_ = lean_ctor_get_uint8(v_a_5114_, sizeof(void*)*7 + 3);
v___x_5129_ = l_Lean_Meta_Context_config(v_a_5114_);
v_isSharedCheck_5172_ = !lean_is_exclusive(v_a_5114_);
if (v_isSharedCheck_5172_ == 0)
{
lean_object* v_unused_5173_; lean_object* v_unused_5174_; lean_object* v_unused_5175_; lean_object* v_unused_5176_; lean_object* v_unused_5177_; lean_object* v_unused_5178_; lean_object* v_unused_5179_; 
v_unused_5173_ = lean_ctor_get(v_a_5114_, 6);
lean_dec(v_unused_5173_);
v_unused_5174_ = lean_ctor_get(v_a_5114_, 5);
lean_dec(v_unused_5174_);
v_unused_5175_ = lean_ctor_get(v_a_5114_, 4);
lean_dec(v_unused_5175_);
v_unused_5176_ = lean_ctor_get(v_a_5114_, 3);
lean_dec(v_unused_5176_);
v_unused_5177_ = lean_ctor_get(v_a_5114_, 2);
lean_dec(v_unused_5177_);
v_unused_5178_ = lean_ctor_get(v_a_5114_, 1);
lean_dec(v_unused_5178_);
v_unused_5179_ = lean_ctor_get(v_a_5114_, 0);
lean_dec(v_unused_5179_);
v___x_5131_ = v_a_5114_;
v_isShared_5132_ = v_isSharedCheck_5172_;
goto v_resetjp_5130_;
}
else
{
lean_dec(v_a_5114_);
v___x_5131_ = lean_box(0);
v_isShared_5132_ = v_isSharedCheck_5172_;
goto v_resetjp_5130_;
}
v_resetjp_5130_:
{
lean_object* v___x_5133_; uint64_t v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5137_; 
v___x_5133_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5129_);
v___x_5134_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5133_);
v___x_5135_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5135_, 0, v___x_5133_);
lean_ctor_set_uint64(v___x_5135_, sizeof(void*)*1, v___x_5134_);
lean_inc(v_customCanUnfoldPredicate_x3f_5125_);
lean_inc(v_synthPendingDepth_5124_);
lean_inc(v_defEqCtx_x3f_5123_);
lean_inc_ref(v_localInstances_5122_);
lean_inc_ref(v_lctx_5121_);
lean_inc(v_zetaDeltaSet_5120_);
if (v_isShared_5132_ == 0)
{
lean_ctor_set(v___x_5131_, 0, v___x_5135_);
v___x_5137_ = v___x_5131_;
goto v_reusejp_5136_;
}
else
{
lean_object* v_reuseFailAlloc_5171_; 
v_reuseFailAlloc_5171_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_5171_, 0, v___x_5135_);
lean_ctor_set(v_reuseFailAlloc_5171_, 1, v_zetaDeltaSet_5120_);
lean_ctor_set(v_reuseFailAlloc_5171_, 2, v_lctx_5121_);
lean_ctor_set(v_reuseFailAlloc_5171_, 3, v_localInstances_5122_);
lean_ctor_set(v_reuseFailAlloc_5171_, 4, v_defEqCtx_x3f_5123_);
lean_ctor_set(v_reuseFailAlloc_5171_, 5, v_synthPendingDepth_5124_);
lean_ctor_set(v_reuseFailAlloc_5171_, 6, v_customCanUnfoldPredicate_x3f_5125_);
lean_ctor_set_uint8(v_reuseFailAlloc_5171_, sizeof(void*)*7, v_trackZetaDelta_5119_);
lean_ctor_set_uint8(v_reuseFailAlloc_5171_, sizeof(void*)*7 + 1, v_univApprox_5126_);
lean_ctor_set_uint8(v_reuseFailAlloc_5171_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5127_);
lean_ctor_set_uint8(v_reuseFailAlloc_5171_, sizeof(void*)*7 + 3, v_cacheInferType_5128_);
v___x_5137_ = v_reuseFailAlloc_5171_;
goto v_reusejp_5136_;
}
v_reusejp_5136_:
{
lean_object* v___x_5138_; lean_object* v___x_5139_; uint64_t v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; 
v___x_5138_ = l_Lean_Meta_Context_config(v___x_5137_);
lean_dec_ref(v___x_5137_);
v___x_5139_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5138_);
v___x_5140_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5139_);
v___x_5141_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5141_, 0, v___x_5139_);
lean_ctor_set_uint64(v___x_5141_, sizeof(void*)*1, v___x_5140_);
v___x_5142_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5142_, 0, v___x_5141_);
lean_ctor_set(v___x_5142_, 1, v_zetaDeltaSet_5120_);
lean_ctor_set(v___x_5142_, 2, v_lctx_5121_);
lean_ctor_set(v___x_5142_, 3, v_localInstances_5122_);
lean_ctor_set(v___x_5142_, 4, v_defEqCtx_x3f_5123_);
lean_ctor_set(v___x_5142_, 5, v_synthPendingDepth_5124_);
lean_ctor_set(v___x_5142_, 6, v_customCanUnfoldPredicate_x3f_5125_);
lean_ctor_set_uint8(v___x_5142_, sizeof(void*)*7, v_trackZetaDelta_5119_);
lean_ctor_set_uint8(v___x_5142_, sizeof(void*)*7 + 1, v_univApprox_5126_);
lean_ctor_set_uint8(v___x_5142_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5127_);
lean_ctor_set_uint8(v___x_5142_, sizeof(void*)*7 + 3, v_cacheInferType_5128_);
lean_inc(v_matchDeclName_5113_);
v___x_5143_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_5113_, v___x_5142_, v_a_5115_, v_a_5116_, v_a_5117_);
if (lean_obj_tag(v___x_5143_) == 0)
{
lean_object* v_a_5144_; lean_object* v___x_5145_; lean_object* v_a_5146_; 
v_a_5144_ = lean_ctor_get(v___x_5143_, 0);
lean_inc(v_a_5144_);
lean_dec_ref_known(v___x_5143_, 1);
lean_inc(v_matchDeclName_5113_);
v___x_5145_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_5113_, v_a_5117_);
v_a_5146_ = lean_ctor_get(v___x_5145_, 0);
lean_inc(v_a_5146_);
lean_dec_ref(v___x_5145_);
if (lean_obj_tag(v_a_5146_) == 1)
{
lean_object* v_val_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___f_5153_; lean_object* v___x_5154_; uint8_t v___x_5155_; lean_object* v___x_5156_; 
v_val_5147_ = lean_ctor_get(v_a_5146_, 0);
lean_inc(v_val_5147_);
lean_dec_ref_known(v_a_5146_, 1);
v___x_5148_ = l_Lean_instInhabitedExpr;
v___x_5149_ = l_Lean_ConstantInfo_levelParams(v_a_5144_);
v___x_5150_ = lean_box(0);
lean_inc(v___x_5149_);
v___x_5151_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(v___x_5149_, v___x_5150_);
v___x_5152_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_5147_);
lean_inc(v_a_5144_);
v___f_5153_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed), 14, 7);
lean_closure_set(v___f_5153_, 0, v_val_5147_);
lean_closure_set(v___f_5153_, 1, v___x_5148_);
lean_closure_set(v___f_5153_, 2, v_matchDeclName_5113_);
lean_closure_set(v___f_5153_, 3, v___x_5152_);
lean_closure_set(v___f_5153_, 4, v_a_5144_);
lean_closure_set(v___f_5153_, 5, v___x_5151_);
lean_closure_set(v___f_5153_, 6, v___x_5149_);
v___x_5154_ = l_Lean_ConstantInfo_type(v_a_5144_);
lean_dec(v_a_5144_);
v___x_5155_ = 0;
v___x_5156_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_5154_, v___f_5153_, v___x_5155_, v___x_5155_, v___x_5142_, v_a_5115_, v_a_5116_, v_a_5117_);
lean_dec_ref_known(v___x_5142_, 7);
return v___x_5156_;
}
else
{
lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; 
lean_dec(v_a_5146_);
lean_dec(v_a_5144_);
v___x_5157_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5158_ = l_Lean_MessageData_ofName(v_matchDeclName_5113_);
v___x_5159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5159_, 0, v___x_5157_);
lean_ctor_set(v___x_5159_, 1, v___x_5158_);
v___x_5160_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5161_, 0, v___x_5159_);
lean_ctor_set(v___x_5161_, 1, v___x_5160_);
v___x_5162_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5161_, v___x_5142_, v_a_5115_, v_a_5116_, v_a_5117_);
lean_dec_ref_known(v___x_5142_, 7);
return v___x_5162_;
}
}
else
{
lean_object* v_a_5163_; lean_object* v___x_5165_; uint8_t v_isShared_5166_; uint8_t v_isSharedCheck_5170_; 
lean_dec_ref_known(v___x_5142_, 7);
lean_dec(v_matchDeclName_5113_);
v_a_5163_ = lean_ctor_get(v___x_5143_, 0);
v_isSharedCheck_5170_ = !lean_is_exclusive(v___x_5143_);
if (v_isSharedCheck_5170_ == 0)
{
v___x_5165_ = v___x_5143_;
v_isShared_5166_ = v_isSharedCheck_5170_;
goto v_resetjp_5164_;
}
else
{
lean_inc(v_a_5163_);
lean_dec(v___x_5143_);
v___x_5165_ = lean_box(0);
v_isShared_5166_ = v_isSharedCheck_5170_;
goto v_resetjp_5164_;
}
v_resetjp_5164_:
{
lean_object* v___x_5168_; 
if (v_isShared_5166_ == 0)
{
v___x_5168_ = v___x_5165_;
goto v_reusejp_5167_;
}
else
{
lean_object* v_reuseFailAlloc_5169_; 
v_reuseFailAlloc_5169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5169_, 0, v_a_5163_);
v___x_5168_ = v_reuseFailAlloc_5169_;
goto v_reusejp_5167_;
}
v_reusejp_5167_:
{
return v___x_5168_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed(lean_object* v_matchDeclName_5180_, lean_object* v_a_5181_, lean_object* v_a_5182_, lean_object* v_a_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_){
_start:
{
lean_object* v_res_5186_; 
v_res_5186_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(v_matchDeclName_5180_, v_a_5181_, v_a_5182_, v_a_5183_, v_a_5184_);
lean_dec(v_a_5184_);
lean_dec_ref(v_a_5183_);
lean_dec(v_a_5182_);
return v_res_5186_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(lean_object* v_inst_5187_, lean_object* v_R_5188_, lean_object* v_a_5189_, lean_object* v_b_5190_, lean_object* v_c_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_){
_start:
{
lean_object* v___x_5197_; 
v___x_5197_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___redArg(v_a_5189_, v_b_5190_, v___y_5192_, v___y_5193_, v___y_5194_, v___y_5195_);
return v___x_5197_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___boxed(lean_object* v_inst_5198_, lean_object* v_R_5199_, lean_object* v_a_5200_, lean_object* v_b_5201_, lean_object* v_c_5202_, lean_object* v___y_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_){
_start:
{
lean_object* v_res_5208_; 
v_res_5208_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(v_inst_5198_, v_R_5199_, v_a_5200_, v_b_5201_, v_c_5202_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_);
lean_dec(v___y_5206_);
lean_dec_ref(v___y_5205_);
lean_dec(v___y_5204_);
lean_dec_ref(v___y_5203_);
return v_res_5208_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(lean_object* v_upperBound_5209_, lean_object* v_val_5210_, lean_object* v_matchDeclName_5211_, lean_object* v___x_5212_, lean_object* v___x_5213_, lean_object* v_a_5214_, lean_object* v___x_5215_, lean_object* v___x_5216_, lean_object* v___x_5217_, lean_object* v___x_5218_, lean_object* v___x_5219_, lean_object* v___x_5220_, lean_object* v_inst_5221_, lean_object* v_R_5222_, lean_object* v_a_5223_, lean_object* v_b_5224_, lean_object* v_c_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_){
_start:
{
lean_object* v___x_5231_; 
v___x_5231_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5209_, v_val_5210_, v_matchDeclName_5211_, v___x_5212_, v___x_5213_, v_a_5214_, v___x_5215_, v___x_5216_, v___x_5217_, v___x_5218_, v___x_5219_, v___x_5220_, v_a_5223_, v_b_5224_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_);
return v___x_5231_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___boxed(lean_object** _args){
lean_object* v_upperBound_5232_ = _args[0];
lean_object* v_val_5233_ = _args[1];
lean_object* v_matchDeclName_5234_ = _args[2];
lean_object* v___x_5235_ = _args[3];
lean_object* v___x_5236_ = _args[4];
lean_object* v_a_5237_ = _args[5];
lean_object* v___x_5238_ = _args[6];
lean_object* v___x_5239_ = _args[7];
lean_object* v___x_5240_ = _args[8];
lean_object* v___x_5241_ = _args[9];
lean_object* v___x_5242_ = _args[10];
lean_object* v___x_5243_ = _args[11];
lean_object* v_inst_5244_ = _args[12];
lean_object* v_R_5245_ = _args[13];
lean_object* v_a_5246_ = _args[14];
lean_object* v_b_5247_ = _args[15];
lean_object* v_c_5248_ = _args[16];
lean_object* v___y_5249_ = _args[17];
lean_object* v___y_5250_ = _args[18];
lean_object* v___y_5251_ = _args[19];
lean_object* v___y_5252_ = _args[20];
lean_object* v___y_5253_ = _args[21];
_start:
{
lean_object* v_res_5254_; 
v_res_5254_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(v_upperBound_5232_, v_val_5233_, v_matchDeclName_5234_, v___x_5235_, v___x_5236_, v_a_5237_, v___x_5238_, v___x_5239_, v___x_5240_, v___x_5241_, v___x_5242_, v___x_5243_, v_inst_5244_, v_R_5245_, v_a_5246_, v_b_5247_, v_c_5248_, v___y_5249_, v___y_5250_, v___y_5251_, v___y_5252_);
lean_dec(v___y_5252_);
lean_dec_ref(v___y_5251_);
lean_dec(v___y_5250_);
lean_dec_ref(v___y_5249_);
lean_dec(v_upperBound_5232_);
return v_res_5254_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(lean_object* v_upperBound_5255_, lean_object* v_matchDeclName_5256_, lean_object* v_a_5257_, lean_object* v_b_5258_){
_start:
{
uint8_t v___x_5260_; 
v___x_5260_ = lean_nat_dec_lt(v_a_5257_, v_upperBound_5255_);
if (v___x_5260_ == 0)
{
lean_object* v___x_5261_; 
lean_dec(v_a_5257_);
lean_dec(v_matchDeclName_5256_);
v___x_5261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5261_, 0, v_b_5258_);
return v___x_5261_;
}
else
{
lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; 
v___x_5262_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_5256_);
v___x_5263_ = l_Lean_Name_str___override(v_matchDeclName_5256_, v___x_5262_);
v___x_5264_ = lean_unsigned_to_nat(1u);
v___x_5265_ = lean_nat_add(v_a_5257_, v___x_5264_);
lean_dec(v_a_5257_);
lean_inc(v___x_5265_);
v___x_5266_ = lean_name_append_index_after(v___x_5263_, v___x_5265_);
v___x_5267_ = lean_array_push(v_b_5258_, v___x_5266_);
v_a_5257_ = v___x_5265_;
v_b_5258_ = v___x_5267_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg___boxed(lean_object* v_upperBound_5269_, lean_object* v_matchDeclName_5270_, lean_object* v_a_5271_, lean_object* v_b_5272_, lean_object* v___y_5273_){
_start:
{
lean_object* v_res_5274_; 
v_res_5274_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5269_, v_matchDeclName_5270_, v_a_5271_, v_b_5272_);
lean_dec(v_upperBound_5269_);
return v_res_5274_;
}
}
LEAN_EXPORT lean_object* lean_get_congr_match_equations_for(lean_object* v_matchDeclName_5275_, lean_object* v_a_5276_, lean_object* v_a_5277_, lean_object* v_a_5278_, lean_object* v_a_5279_){
_start:
{
lean_object* v___x_5281_; lean_object* v_firstEqnName_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; 
v___x_5281_ = l_Lean_Meta_Match_congrEqn1ThmSuffix;
lean_inc_n(v_matchDeclName_5275_, 3);
v_firstEqnName_5282_ = l_Lean_Name_str___override(v_matchDeclName_5275_, v___x_5281_);
v___x_5283_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed), 6, 1);
lean_closure_set(v___x_5283_, 0, v_matchDeclName_5275_);
v___x_5284_ = l_Lean_Meta_realizeConst(v_matchDeclName_5275_, v_firstEqnName_5282_, v___x_5283_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_);
if (lean_obj_tag(v___x_5284_) == 0)
{
lean_object* v___x_5285_; lean_object* v_a_5286_; 
lean_dec_ref_known(v___x_5284_, 1);
lean_inc(v_matchDeclName_5275_);
v___x_5285_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1___redArg(v_matchDeclName_5275_, v_a_5279_);
v_a_5286_ = lean_ctor_get(v___x_5285_, 0);
lean_inc(v_a_5286_);
lean_dec_ref(v___x_5285_);
if (lean_obj_tag(v_a_5286_) == 1)
{
lean_object* v_val_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; 
lean_dec(v_a_5279_);
lean_dec_ref(v_a_5278_);
lean_dec(v_a_5277_);
lean_dec_ref(v_a_5276_);
v_val_5287_ = lean_ctor_get(v_a_5286_, 0);
lean_inc(v_val_5287_);
lean_dec_ref_known(v_a_5286_, 1);
v___x_5288_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5287_);
lean_dec(v_val_5287_);
v___x_5289_ = lean_unsigned_to_nat(0u);
v___x_5290_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___x_5291_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v___x_5288_, v_matchDeclName_5275_, v___x_5289_, v___x_5290_);
lean_dec(v___x_5288_);
return v___x_5291_;
}
else
{
lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; 
lean_dec(v_a_5286_);
v___x_5292_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5293_ = l_Lean_MessageData_ofName(v_matchDeclName_5275_);
v___x_5294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5294_, 0, v___x_5292_);
lean_ctor_set(v___x_5294_, 1, v___x_5293_);
v___x_5295_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5296_, 0, v___x_5294_);
lean_ctor_set(v___x_5296_, 1, v___x_5295_);
v___x_5297_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5296_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_);
lean_dec(v_a_5279_);
lean_dec_ref(v_a_5278_);
lean_dec(v_a_5277_);
lean_dec_ref(v_a_5276_);
return v___x_5297_;
}
}
else
{
lean_object* v_a_5298_; lean_object* v___x_5300_; uint8_t v_isShared_5301_; uint8_t v_isSharedCheck_5305_; 
lean_dec(v_a_5279_);
lean_dec_ref(v_a_5278_);
lean_dec(v_a_5277_);
lean_dec_ref(v_a_5276_);
lean_dec(v_matchDeclName_5275_);
v_a_5298_ = lean_ctor_get(v___x_5284_, 0);
v_isSharedCheck_5305_ = !lean_is_exclusive(v___x_5284_);
if (v_isSharedCheck_5305_ == 0)
{
v___x_5300_ = v___x_5284_;
v_isShared_5301_ = v_isSharedCheck_5305_;
goto v_resetjp_5299_;
}
else
{
lean_inc(v_a_5298_);
lean_dec(v___x_5284_);
v___x_5300_ = lean_box(0);
v_isShared_5301_ = v_isSharedCheck_5305_;
goto v_resetjp_5299_;
}
v_resetjp_5299_:
{
lean_object* v___x_5303_; 
if (v_isShared_5301_ == 0)
{
v___x_5303_ = v___x_5300_;
goto v_reusejp_5302_;
}
else
{
lean_object* v_reuseFailAlloc_5304_; 
v_reuseFailAlloc_5304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5304_, 0, v_a_5298_);
v___x_5303_ = v_reuseFailAlloc_5304_;
goto v_reusejp_5302_;
}
v_reusejp_5302_:
{
return v___x_5303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_genMatchCongrEqnsImpl___boxed(lean_object* v_matchDeclName_5306_, lean_object* v_a_5307_, lean_object* v_a_5308_, lean_object* v_a_5309_, lean_object* v_a_5310_, lean_object* v_a_5311_){
_start:
{
lean_object* v_res_5312_; 
v_res_5312_ = lean_get_congr_match_equations_for(v_matchDeclName_5306_, v_a_5307_, v_a_5308_, v_a_5309_, v_a_5310_);
return v_res_5312_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(lean_object* v_upperBound_5313_, lean_object* v_matchDeclName_5314_, lean_object* v_inst_5315_, lean_object* v_R_5316_, lean_object* v_a_5317_, lean_object* v_b_5318_, lean_object* v_c_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_){
_start:
{
lean_object* v___x_5325_; 
v___x_5325_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5313_, v_matchDeclName_5314_, v_a_5317_, v_b_5318_);
return v___x_5325_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___boxed(lean_object* v_upperBound_5326_, lean_object* v_matchDeclName_5327_, lean_object* v_inst_5328_, lean_object* v_R_5329_, lean_object* v_a_5330_, lean_object* v_b_5331_, lean_object* v_c_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_){
_start:
{
lean_object* v_res_5338_; 
v_res_5338_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(v_upperBound_5326_, v_matchDeclName_5327_, v_inst_5328_, v_R_5329_, v_a_5330_, v_b_5331_, v_c_5332_, v___y_5333_, v___y_5334_, v___y_5335_, v___y_5336_);
lean_dec(v___y_5336_);
lean_dec_ref(v___y_5335_);
lean_dec(v___y_5334_);
lean_dec_ref(v___y_5333_);
lean_dec(v_upperBound_5326_);
return v_res_5338_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; 
v___x_5389_ = lean_unsigned_to_nat(3248161880u);
v___x_5390_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__19_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5391_ = l_Lean_Name_num___override(v___x_5390_, v___x_5389_);
return v___x_5391_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; 
v___x_5393_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__21_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5394_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5395_ = l_Lean_Name_str___override(v___x_5394_, v___x_5393_);
return v___x_5395_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; 
v___x_5397_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__23_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5398_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5399_ = l_Lean_Name_str___override(v___x_5398_, v___x_5397_);
return v___x_5399_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5400_; lean_object* v___x_5401_; lean_object* v___x_5402_; 
v___x_5400_ = lean_unsigned_to_nat(2u);
v___x_5401_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5402_ = l_Lean_Name_num___override(v___x_5401_, v___x_5400_);
return v___x_5402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5404_; uint8_t v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; 
v___x_5404_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_5405_ = 0;
v___x_5406_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5407_ = l_Lean_registerTraceClass(v___x_5404_, v___x_5405_, v___x_5406_);
return v___x_5407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2____boxed(lean_object* v_a_5408_){
_start:
{
lean_object* v_res_5409_; 
v_res_5409_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_();
return v_res_5409_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(lean_object* v_env_5410_, lean_object* v_n_5411_){
_start:
{
if (lean_obj_tag(v_n_5411_) == 1)
{
lean_object* v_pre_5412_; lean_object* v_str_5413_; uint8_t v___y_5415_; uint8_t v___x_5421_; 
v_pre_5412_ = lean_ctor_get(v_n_5411_, 0);
lean_inc(v_pre_5412_);
v_str_5413_ = lean_ctor_get(v_n_5411_, 1);
lean_inc_ref_n(v_str_5413_, 2);
lean_dec_ref_known(v_n_5411_, 2);
v___x_5421_ = l_Lean_Meta_isEqnReservedNameSuffix(v_str_5413_);
if (v___x_5421_ == 0)
{
lean_object* v___x_5422_; uint8_t v___x_5423_; 
v___x_5422_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__0));
v___x_5423_ = lean_string_dec_eq(v_str_5413_, v___x_5422_);
lean_dec_ref(v_str_5413_);
v___y_5415_ = v___x_5423_;
goto v___jp_5414_;
}
else
{
lean_dec_ref(v_str_5413_);
v___y_5415_ = v___x_5421_;
goto v___jp_5414_;
}
v___jp_5414_:
{
if (v___y_5415_ == 0)
{
lean_object* v___x_5416_; 
lean_dec(v_pre_5412_);
lean_dec_ref(v_env_5410_);
v___x_5416_ = lean_box(0);
return v___x_5416_;
}
else
{
lean_object* v___x_5417_; 
v___x_5417_ = l_Lean_privateToUserName_x3f(v_pre_5412_);
if (lean_obj_tag(v___x_5417_) == 0)
{
lean_dec_ref(v_env_5410_);
return v___x_5417_;
}
else
{
lean_object* v_val_5418_; uint8_t v___x_5419_; 
v_val_5418_ = lean_ctor_get(v___x_5417_, 0);
lean_inc(v_val_5418_);
v___x_5419_ = l_Lean_Meta_isMatcherCore(v_env_5410_, v_val_5418_);
if (v___x_5419_ == 0)
{
lean_object* v___x_5420_; 
lean_dec_ref_known(v___x_5417_, 1);
v___x_5420_ = lean_box(0);
return v___x_5420_;
}
else
{
return v___x_5417_;
}
}
}
}
}
else
{
lean_object* v___x_5424_; 
lean_dec(v_n_5411_);
lean_dec_ref(v_env_5410_);
v___x_5424_ = lean_box(0);
return v___x_5424_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(lean_object* v_x1_5425_, lean_object* v_x2_5426_){
_start:
{
lean_object* v___x_5427_; 
v___x_5427_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_x1_5425_, v_x2_5426_);
if (lean_obj_tag(v___x_5427_) == 0)
{
uint8_t v___x_5428_; 
v___x_5428_ = 0;
return v___x_5428_;
}
else
{
uint8_t v___x_5429_; 
lean_dec_ref_known(v___x_5427_, 1);
v___x_5429_ = 1;
return v___x_5429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_x1_5430_, lean_object* v_x2_5431_){
_start:
{
uint8_t v_res_5432_; lean_object* v_r_5433_; 
v_res_5432_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(v_x1_5430_, v_x2_5431_);
v_r_5433_ = lean_box(v_res_5432_);
return v_r_5433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5436_; lean_object* v___x_5437_; 
v___f_5436_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_));
v___x_5437_ = l_Lean_registerReservedNamePredicate(v___f_5436_);
return v___x_5437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_a_5438_){
_start:
{
lean_object* v_res_5439_; 
v_res_5439_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_();
return v_res_5439_;
}
}
static uint64_t _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5446_; uint64_t v___x_5447_; 
v___x_5446_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5447_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5446_);
return v___x_5447_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; 
v___x_5448_ = lean_uint64_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5449_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5450_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5450_, 0, v___x_5449_);
lean_ctor_set_uint64(v___x_5450_, sizeof(void*)*1, v___x_5448_);
return v___x_5450_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; 
v___x_5453_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5454_ = lean_unsigned_to_nat(0u);
v___x_5455_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_5455_, 0, v___x_5454_);
lean_ctor_set(v___x_5455_, 1, v___x_5454_);
lean_ctor_set(v___x_5455_, 2, v___x_5454_);
lean_ctor_set(v___x_5455_, 3, v___x_5454_);
lean_ctor_set(v___x_5455_, 4, v___x_5453_);
lean_ctor_set(v___x_5455_, 5, v___x_5453_);
lean_ctor_set(v___x_5455_, 6, v___x_5453_);
lean_ctor_set(v___x_5455_, 7, v___x_5453_);
lean_ctor_set(v___x_5455_, 8, v___x_5453_);
lean_ctor_set(v___x_5455_, 9, v___x_5453_);
lean_ctor_set(v___x_5455_, 10, v___x_5453_);
return v___x_5455_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5456_; lean_object* v___x_5457_; 
v___x_5456_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5457_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5457_, 0, v___x_5456_);
lean_ctor_set(v___x_5457_, 1, v___x_5456_);
lean_ctor_set(v___x_5457_, 2, v___x_5456_);
lean_ctor_set(v___x_5457_, 3, v___x_5456_);
lean_ctor_set(v___x_5457_, 4, v___x_5456_);
lean_ctor_set(v___x_5457_, 5, v___x_5456_);
return v___x_5457_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5458_; lean_object* v___x_5459_; 
v___x_5458_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5459_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5459_, 0, v___x_5458_);
lean_ctor_set(v___x_5459_, 1, v___x_5458_);
lean_ctor_set(v___x_5459_, 2, v___x_5458_);
lean_ctor_set(v___x_5459_, 3, v___x_5458_);
lean_ctor_set(v___x_5459_, 4, v___x_5458_);
return v___x_5459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(lean_object* v___x_5460_, lean_object* v_name_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_){
_start:
{
lean_object* v___x_5465_; lean_object* v_env_5466_; lean_object* v___x_5467_; 
v___x_5465_ = lean_st_ref_get(v___y_5463_);
v_env_5466_ = lean_ctor_get(v___x_5465_, 0);
lean_inc_ref(v_env_5466_);
lean_dec(v___x_5465_);
v___x_5467_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_env_5466_, v_name_5461_);
if (lean_obj_tag(v___x_5467_) == 1)
{
lean_object* v_val_5468_; uint8_t v___x_5469_; uint8_t v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; 
v_val_5468_ = lean_ctor_get(v___x_5467_, 0);
lean_inc(v_val_5468_);
lean_dec_ref_known(v___x_5467_, 1);
v___x_5469_ = 0;
v___x_5470_ = 1;
v___x_5471_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5472_ = lean_unsigned_to_nat(0u);
v___x_5473_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5474_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5475_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5476_ = lean_box(0);
lean_inc(v___x_5460_);
v___x_5477_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5477_, 0, v___x_5471_);
lean_ctor_set(v___x_5477_, 1, v___x_5460_);
lean_ctor_set(v___x_5477_, 2, v___x_5474_);
lean_ctor_set(v___x_5477_, 3, v___x_5475_);
lean_ctor_set(v___x_5477_, 4, v___x_5476_);
lean_ctor_set(v___x_5477_, 5, v___x_5472_);
lean_ctor_set(v___x_5477_, 6, v___x_5476_);
lean_ctor_set_uint8(v___x_5477_, sizeof(void*)*7, v___x_5469_);
lean_ctor_set_uint8(v___x_5477_, sizeof(void*)*7 + 1, v___x_5469_);
lean_ctor_set_uint8(v___x_5477_, sizeof(void*)*7 + 2, v___x_5469_);
lean_ctor_set_uint8(v___x_5477_, sizeof(void*)*7 + 3, v___x_5470_);
v___x_5478_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5479_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5480_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5481_, 0, v___x_5478_);
lean_ctor_set(v___x_5481_, 1, v___x_5479_);
lean_ctor_set(v___x_5481_, 2, v___x_5460_);
lean_ctor_set(v___x_5481_, 3, v___x_5473_);
lean_ctor_set(v___x_5481_, 4, v___x_5480_);
v___x_5482_ = lean_st_mk_ref(v___x_5481_);
lean_inc(v___y_5463_);
lean_inc_ref(v___y_5462_);
lean_inc(v___x_5482_);
v___x_5483_ = lean_get_match_equations_for(v_val_5468_, v___x_5477_, v___x_5482_, v___y_5462_, v___y_5463_);
if (lean_obj_tag(v___x_5483_) == 0)
{
lean_object* v___x_5485_; uint8_t v_isShared_5486_; uint8_t v_isSharedCheck_5492_; 
v_isSharedCheck_5492_ = !lean_is_exclusive(v___x_5483_);
if (v_isSharedCheck_5492_ == 0)
{
lean_object* v_unused_5493_; 
v_unused_5493_ = lean_ctor_get(v___x_5483_, 0);
lean_dec(v_unused_5493_);
v___x_5485_ = v___x_5483_;
v_isShared_5486_ = v_isSharedCheck_5492_;
goto v_resetjp_5484_;
}
else
{
lean_dec(v___x_5483_);
v___x_5485_ = lean_box(0);
v_isShared_5486_ = v_isSharedCheck_5492_;
goto v_resetjp_5484_;
}
v_resetjp_5484_:
{
lean_object* v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5490_; 
v___x_5487_ = lean_st_ref_get(v___x_5482_);
lean_dec(v___x_5482_);
lean_dec(v___x_5487_);
v___x_5488_ = lean_box(v___x_5470_);
if (v_isShared_5486_ == 0)
{
lean_ctor_set(v___x_5485_, 0, v___x_5488_);
v___x_5490_ = v___x_5485_;
goto v_reusejp_5489_;
}
else
{
lean_object* v_reuseFailAlloc_5491_; 
v_reuseFailAlloc_5491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5491_, 0, v___x_5488_);
v___x_5490_ = v_reuseFailAlloc_5491_;
goto v_reusejp_5489_;
}
v_reusejp_5489_:
{
return v___x_5490_;
}
}
}
else
{
lean_dec(v___x_5482_);
if (lean_obj_tag(v___x_5483_) == 0)
{
lean_object* v___x_5495_; uint8_t v_isShared_5496_; uint8_t v_isSharedCheck_5501_; 
v_isSharedCheck_5501_ = !lean_is_exclusive(v___x_5483_);
if (v_isSharedCheck_5501_ == 0)
{
lean_object* v_unused_5502_; 
v_unused_5502_ = lean_ctor_get(v___x_5483_, 0);
lean_dec(v_unused_5502_);
v___x_5495_ = v___x_5483_;
v_isShared_5496_ = v_isSharedCheck_5501_;
goto v_resetjp_5494_;
}
else
{
lean_dec(v___x_5483_);
v___x_5495_ = lean_box(0);
v_isShared_5496_ = v_isSharedCheck_5501_;
goto v_resetjp_5494_;
}
v_resetjp_5494_:
{
lean_object* v___x_5497_; lean_object* v___x_5499_; 
v___x_5497_ = lean_box(v___x_5470_);
if (v_isShared_5496_ == 0)
{
lean_ctor_set_tag(v___x_5495_, 0);
lean_ctor_set(v___x_5495_, 0, v___x_5497_);
v___x_5499_ = v___x_5495_;
goto v_reusejp_5498_;
}
else
{
lean_object* v_reuseFailAlloc_5500_; 
v_reuseFailAlloc_5500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5500_, 0, v___x_5497_);
v___x_5499_ = v_reuseFailAlloc_5500_;
goto v_reusejp_5498_;
}
v_reusejp_5498_:
{
return v___x_5499_;
}
}
}
else
{
lean_object* v_a_5503_; lean_object* v___x_5505_; uint8_t v_isShared_5506_; uint8_t v_isSharedCheck_5510_; 
v_a_5503_ = lean_ctor_get(v___x_5483_, 0);
v_isSharedCheck_5510_ = !lean_is_exclusive(v___x_5483_);
if (v_isSharedCheck_5510_ == 0)
{
v___x_5505_ = v___x_5483_;
v_isShared_5506_ = v_isSharedCheck_5510_;
goto v_resetjp_5504_;
}
else
{
lean_inc(v_a_5503_);
lean_dec(v___x_5483_);
v___x_5505_ = lean_box(0);
v_isShared_5506_ = v_isSharedCheck_5510_;
goto v_resetjp_5504_;
}
v_resetjp_5504_:
{
lean_object* v___x_5508_; 
if (v_isShared_5506_ == 0)
{
v___x_5508_ = v___x_5505_;
goto v_reusejp_5507_;
}
else
{
lean_object* v_reuseFailAlloc_5509_; 
v_reuseFailAlloc_5509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5509_, 0, v_a_5503_);
v___x_5508_ = v_reuseFailAlloc_5509_;
goto v_reusejp_5507_;
}
v_reusejp_5507_:
{
return v___x_5508_;
}
}
}
}
}
else
{
uint8_t v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; 
lean_dec(v___x_5467_);
lean_dec(v___x_5460_);
v___x_5511_ = 0;
v___x_5512_ = lean_box(v___x_5511_);
v___x_5513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5513_, 0, v___x_5512_);
return v___x_5513_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v___x_5514_, lean_object* v_name_5515_, lean_object* v___y_5516_, lean_object* v___y_5517_, lean_object* v___y_5518_){
_start:
{
lean_object* v_res_5519_; 
v_res_5519_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(v___x_5514_, v_name_5515_, v___y_5516_, v___y_5517_);
lean_dec(v___y_5517_);
lean_dec_ref(v___y_5516_);
return v_res_5519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5523_; lean_object* v___x_5524_; 
v___f_5523_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5524_ = l_Lean_registerReservedNameAction(v___f_5523_);
return v___x_5524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v_a_5525_){
_start:
{
lean_object* v_res_5526_; 
v_res_5526_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_();
return v_res_5526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(lean_object* v_env_5527_, lean_object* v_n_5528_){
_start:
{
if (lean_obj_tag(v_n_5528_) == 1)
{
lean_object* v_pre_5529_; lean_object* v_str_5530_; uint8_t v___x_5531_; 
v_pre_5529_ = lean_ctor_get(v_n_5528_, 0);
lean_inc(v_pre_5529_);
v_str_5530_ = lean_ctor_get(v_n_5528_, 1);
lean_inc_ref(v_str_5530_);
lean_dec_ref_known(v_n_5528_, 2);
v___x_5531_ = l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(v_str_5530_);
if (v___x_5531_ == 0)
{
lean_object* v___x_5532_; 
lean_dec(v_pre_5529_);
lean_dec_ref(v_env_5527_);
v___x_5532_ = lean_box(0);
return v___x_5532_;
}
else
{
uint8_t v___x_5533_; 
lean_inc(v_pre_5529_);
v___x_5533_ = l_Lean_Meta_isMatcherCore(v_env_5527_, v_pre_5529_);
if (v___x_5533_ == 0)
{
lean_object* v___x_5534_; 
lean_dec(v_pre_5529_);
v___x_5534_ = lean_box(0);
return v___x_5534_;
}
else
{
lean_object* v___x_5535_; 
v___x_5535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5535_, 0, v_pre_5529_);
return v___x_5535_;
}
}
}
else
{
lean_object* v___x_5536_; 
lean_dec(v_n_5528_);
lean_dec_ref(v_env_5527_);
v___x_5536_ = lean_box(0);
return v___x_5536_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(lean_object* v_x1_5537_, lean_object* v_x2_5538_){
_start:
{
lean_object* v___x_5539_; 
v___x_5539_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_x1_5537_, v_x2_5538_);
if (lean_obj_tag(v___x_5539_) == 0)
{
uint8_t v___x_5540_; 
v___x_5540_ = 0;
return v___x_5540_;
}
else
{
uint8_t v___x_5541_; 
lean_dec_ref_known(v___x_5539_, 1);
v___x_5541_ = 1;
return v___x_5541_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_x1_5542_, lean_object* v_x2_5543_){
_start:
{
uint8_t v_res_5544_; lean_object* v_r_5545_; 
v_res_5544_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(v_x1_5542_, v_x2_5543_);
v_r_5545_ = lean_box(v_res_5544_);
return v_r_5545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5548_; lean_object* v___x_5549_; 
v___f_5548_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_));
v___x_5549_ = l_Lean_registerReservedNamePredicate(v___f_5548_);
return v___x_5549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_a_5550_){
_start:
{
lean_object* v_res_5551_; 
v_res_5551_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_();
return v_res_5551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(lean_object* v___x_5552_, lean_object* v_name_5553_, lean_object* v___y_5554_, lean_object* v___y_5555_){
_start:
{
lean_object* v___x_5557_; lean_object* v_env_5558_; lean_object* v___x_5559_; 
v___x_5557_ = lean_st_ref_get(v___y_5555_);
v_env_5558_ = lean_ctor_get(v___x_5557_, 0);
lean_inc_ref(v_env_5558_);
lean_dec(v___x_5557_);
v___x_5559_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_env_5558_, v_name_5553_);
if (lean_obj_tag(v___x_5559_) == 1)
{
lean_object* v_val_5560_; uint8_t v___x_5561_; uint8_t v___x_5562_; lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___x_5572_; lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; 
v_val_5560_ = lean_ctor_get(v___x_5559_, 0);
lean_inc(v_val_5560_);
lean_dec_ref_known(v___x_5559_, 1);
v___x_5561_ = 0;
v___x_5562_ = 1;
v___x_5563_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5564_ = lean_unsigned_to_nat(32u);
v___x_5565_ = lean_mk_empty_array_with_capacity(v___x_5564_);
lean_dec_ref(v___x_5565_);
v___x_5566_ = lean_unsigned_to_nat(0u);
v___x_5567_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5568_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5569_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5570_ = lean_box(0);
lean_inc(v___x_5552_);
v___x_5571_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5571_, 0, v___x_5563_);
lean_ctor_set(v___x_5571_, 1, v___x_5552_);
lean_ctor_set(v___x_5571_, 2, v___x_5568_);
lean_ctor_set(v___x_5571_, 3, v___x_5569_);
lean_ctor_set(v___x_5571_, 4, v___x_5570_);
lean_ctor_set(v___x_5571_, 5, v___x_5566_);
lean_ctor_set(v___x_5571_, 6, v___x_5570_);
lean_ctor_set_uint8(v___x_5571_, sizeof(void*)*7, v___x_5561_);
lean_ctor_set_uint8(v___x_5571_, sizeof(void*)*7 + 1, v___x_5561_);
lean_ctor_set_uint8(v___x_5571_, sizeof(void*)*7 + 2, v___x_5561_);
lean_ctor_set_uint8(v___x_5571_, sizeof(void*)*7 + 3, v___x_5562_);
v___x_5572_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5573_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5574_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5575_, 0, v___x_5572_);
lean_ctor_set(v___x_5575_, 1, v___x_5573_);
lean_ctor_set(v___x_5575_, 2, v___x_5552_);
lean_ctor_set(v___x_5575_, 3, v___x_5567_);
lean_ctor_set(v___x_5575_, 4, v___x_5574_);
v___x_5576_ = lean_st_mk_ref(v___x_5575_);
lean_inc(v___y_5555_);
lean_inc_ref(v___y_5554_);
lean_inc(v___x_5576_);
v___x_5577_ = lean_get_congr_match_equations_for(v_val_5560_, v___x_5571_, v___x_5576_, v___y_5554_, v___y_5555_);
if (lean_obj_tag(v___x_5577_) == 0)
{
lean_object* v___x_5579_; uint8_t v_isShared_5580_; uint8_t v_isSharedCheck_5586_; 
v_isSharedCheck_5586_ = !lean_is_exclusive(v___x_5577_);
if (v_isSharedCheck_5586_ == 0)
{
lean_object* v_unused_5587_; 
v_unused_5587_ = lean_ctor_get(v___x_5577_, 0);
lean_dec(v_unused_5587_);
v___x_5579_ = v___x_5577_;
v_isShared_5580_ = v_isSharedCheck_5586_;
goto v_resetjp_5578_;
}
else
{
lean_dec(v___x_5577_);
v___x_5579_ = lean_box(0);
v_isShared_5580_ = v_isSharedCheck_5586_;
goto v_resetjp_5578_;
}
v_resetjp_5578_:
{
lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v___x_5584_; 
v___x_5581_ = lean_st_ref_get(v___x_5576_);
lean_dec(v___x_5576_);
lean_dec(v___x_5581_);
v___x_5582_ = lean_box(v___x_5562_);
if (v_isShared_5580_ == 0)
{
lean_ctor_set(v___x_5579_, 0, v___x_5582_);
v___x_5584_ = v___x_5579_;
goto v_reusejp_5583_;
}
else
{
lean_object* v_reuseFailAlloc_5585_; 
v_reuseFailAlloc_5585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5585_, 0, v___x_5582_);
v___x_5584_ = v_reuseFailAlloc_5585_;
goto v_reusejp_5583_;
}
v_reusejp_5583_:
{
return v___x_5584_;
}
}
}
else
{
lean_dec(v___x_5576_);
if (lean_obj_tag(v___x_5577_) == 0)
{
lean_object* v___x_5589_; uint8_t v_isShared_5590_; uint8_t v_isSharedCheck_5595_; 
v_isSharedCheck_5595_ = !lean_is_exclusive(v___x_5577_);
if (v_isSharedCheck_5595_ == 0)
{
lean_object* v_unused_5596_; 
v_unused_5596_ = lean_ctor_get(v___x_5577_, 0);
lean_dec(v_unused_5596_);
v___x_5589_ = v___x_5577_;
v_isShared_5590_ = v_isSharedCheck_5595_;
goto v_resetjp_5588_;
}
else
{
lean_dec(v___x_5577_);
v___x_5589_ = lean_box(0);
v_isShared_5590_ = v_isSharedCheck_5595_;
goto v_resetjp_5588_;
}
v_resetjp_5588_:
{
lean_object* v___x_5591_; lean_object* v___x_5593_; 
v___x_5591_ = lean_box(v___x_5562_);
if (v_isShared_5590_ == 0)
{
lean_ctor_set_tag(v___x_5589_, 0);
lean_ctor_set(v___x_5589_, 0, v___x_5591_);
v___x_5593_ = v___x_5589_;
goto v_reusejp_5592_;
}
else
{
lean_object* v_reuseFailAlloc_5594_; 
v_reuseFailAlloc_5594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5594_, 0, v___x_5591_);
v___x_5593_ = v_reuseFailAlloc_5594_;
goto v_reusejp_5592_;
}
v_reusejp_5592_:
{
return v___x_5593_;
}
}
}
else
{
lean_object* v_a_5597_; lean_object* v___x_5599_; uint8_t v_isShared_5600_; uint8_t v_isSharedCheck_5604_; 
v_a_5597_ = lean_ctor_get(v___x_5577_, 0);
v_isSharedCheck_5604_ = !lean_is_exclusive(v___x_5577_);
if (v_isSharedCheck_5604_ == 0)
{
v___x_5599_ = v___x_5577_;
v_isShared_5600_ = v_isSharedCheck_5604_;
goto v_resetjp_5598_;
}
else
{
lean_inc(v_a_5597_);
lean_dec(v___x_5577_);
v___x_5599_ = lean_box(0);
v_isShared_5600_ = v_isSharedCheck_5604_;
goto v_resetjp_5598_;
}
v_resetjp_5598_:
{
lean_object* v___x_5602_; 
if (v_isShared_5600_ == 0)
{
v___x_5602_ = v___x_5599_;
goto v_reusejp_5601_;
}
else
{
lean_object* v_reuseFailAlloc_5603_; 
v_reuseFailAlloc_5603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5603_, 0, v_a_5597_);
v___x_5602_ = v_reuseFailAlloc_5603_;
goto v_reusejp_5601_;
}
v_reusejp_5601_:
{
return v___x_5602_;
}
}
}
}
}
else
{
uint8_t v___x_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; 
lean_dec(v___x_5559_);
lean_dec(v___x_5552_);
v___x_5605_ = 0;
v___x_5606_ = lean_box(v___x_5605_);
v___x_5607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5607_, 0, v___x_5606_);
return v___x_5607_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v___x_5608_, lean_object* v_name_5609_, lean_object* v___y_5610_, lean_object* v___y_5611_, lean_object* v___y_5612_){
_start:
{
lean_object* v_res_5613_; 
v_res_5613_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(v___x_5608_, v_name_5609_, v___y_5610_, v___y_5611_);
lean_dec(v___y_5611_);
lean_dec_ref(v___y_5610_);
return v_res_5613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5617_; lean_object* v___x_5618_; 
v___f_5617_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_));
v___x_5618_ = l_Lean_registerReservedNameAction(v___f_5617_);
return v___x_5618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v_a_5619_){
_start:
{
lean_object* v_res_5620_; 
v_res_5620_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_();
return v_res_5620_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_MatchEqs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
