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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_deltaTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(lean_object*);
uint8_t l_Lean_Meta_isMatcherCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Overlaps_overlapping(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_simpH_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrowN(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_unfoldNamedPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
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
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_eqnThmSuffixBase;
lean_object* l_Lean_Meta_Match_forallAltTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16;
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "heq"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 249, 62, 128, 70, 197, 241, 171)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed(lean_object**);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 77, .m_capacity = 77, .m_length = 76, .m_data = "_private.Lean.Meta.Match.MatchEqs.0.Lean.Meta.Match.genMatchCongrEqnsImpl.go"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "assertion violation: patterns.size == discrs.size\n        "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__1_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_7_; lean_object* v_env_8_; lean_object* v___x_9_; lean_object* v_toCold_10_; lean_object* v_mctx_11_; lean_object* v_lctx_12_; lean_object* v_options_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = lean_st_ref_get(v___y_3_);
v_toCold_10_ = lean_ctor_get(v___y_4_, 0);
v_mctx_11_ = lean_ctor_get(v___x_9_, 0);
lean_inc_ref(v_mctx_11_);
lean_dec(v___x_9_);
v_lctx_12_ = lean_ctor_get(v___y_2_, 2);
v_options_13_ = lean_ctor_get(v_toCold_10_, 2);
lean_inc_ref(v_options_13_);
lean_inc_ref(v_lctx_12_);
v___x_14_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_14_, 0, v_env_8_);
lean_ctor_set(v___x_14_, 1, v_mctx_11_);
lean_ctor_set(v___x_14_, 2, v_lctx_12_);
lean_ctor_set(v___x_14_, 3, v_options_13_);
v___x_15_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v_msgData_1_);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2___boxed(lean_object* v_msgData_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2(v_msgData_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
lean_dec(v___y_19_);
lean_dec_ref(v___y_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(lean_object* v_msg_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_ref_30_; lean_object* v___x_31_; lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_40_; 
v_ref_30_ = lean_ctor_get(v___y_27_, 2);
v___x_31_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2(v_msg_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
v_a_32_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_40_ == 0)
{
v___x_34_ = v___x_31_;
v_isShared_35_ = v_isSharedCheck_40_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_31_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_40_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_36_; lean_object* v___x_38_; 
lean_inc(v_ref_30_);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v_ref_30_);
lean_ctor_set(v___x_36_, 1, v_a_32_);
if (v_isShared_35_ == 0)
{
lean_ctor_set_tag(v___x_34_, 1);
lean_ctor_set(v___x_34_, 0, v___x_36_);
v___x_38_ = v___x_34_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_36_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg___boxed(lean_object* v_msg_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v_msg_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(lean_object* v_a_48_, lean_object* v_a_49_){
_start:
{
if (lean_obj_tag(v_a_48_) == 0)
{
lean_object* v___x_50_; 
v___x_50_ = l_List_reverse___redArg(v_a_49_);
return v___x_50_;
}
else
{
lean_object* v_head_51_; lean_object* v_tail_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_61_; 
v_head_51_ = lean_ctor_get(v_a_48_, 0);
v_tail_52_ = lean_ctor_get(v_a_48_, 1);
v_isSharedCheck_61_ = !lean_is_exclusive(v_a_48_);
if (v_isSharedCheck_61_ == 0)
{
v___x_54_ = v_a_48_;
v_isShared_55_ = v_isSharedCheck_61_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_tail_52_);
lean_inc(v_head_51_);
lean_dec(v_a_48_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_61_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_56_; lean_object* v___x_58_; 
v___x_56_ = l_Lean_MessageData_ofExpr(v_head_51_);
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 1, v_a_49_);
lean_ctor_set(v___x_54_, 0, v___x_56_);
v___x_58_ = v___x_54_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v___x_56_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v_a_49_);
v___x_58_ = v_reuseFailAlloc_60_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
v_a_48_ = v_tail_52_;
v_a_49_ = v___x_58_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__1(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__0));
v___x_67_ = l_Lean_stringToMessageData(v___x_66_);
return v___x_67_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__3(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__2));
v___x_70_ = l_Lean_stringToMessageData(v___x_69_);
return v___x_70_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__5(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__4));
v___x_73_ = l_Lean_stringToMessageData(v___x_72_);
return v___x_73_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__7(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__6));
v___x_76_ = l_Lean_stringToMessageData(v___x_75_);
return v___x_76_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__9(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__8));
v___x_79_ = l_Lean_stringToMessageData(v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go(lean_object* v_alt_80_, lean_object* v_heqs_81_, lean_object* v_numDiscrEqs_82_, lean_object* v_e_83_, lean_object* v_ty_84_, lean_object* v_i_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
uint8_t v___x_91_; 
v___x_91_ = lean_nat_dec_lt(v_i_85_, v_numDiscrEqs_82_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; 
lean_dec_ref(v_ty_84_);
lean_dec(v_numDiscrEqs_82_);
lean_dec_ref(v_heqs_81_);
lean_dec_ref(v_alt_80_);
v___x_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_92_, 0, v_e_83_);
return v___x_92_;
}
else
{
if (lean_obj_tag(v_ty_84_) == 7)
{
lean_object* v_binderName_93_; lean_object* v_binderType_94_; lean_object* v_body_95_; lean_object* v___x_96_; size_t v_sz_97_; size_t v___x_98_; lean_object* v___x_99_; 
v_binderName_93_ = lean_ctor_get(v_ty_84_, 0);
lean_inc(v_binderName_93_);
v_binderType_94_ = lean_ctor_get(v_ty_84_, 1);
lean_inc_ref_n(v_binderType_94_, 2);
v_body_95_ = lean_ctor_get(v_ty_84_, 2);
lean_inc_ref(v_body_95_);
lean_dec_ref_known(v_ty_84_, 3);
v___x_96_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0___closed__0));
v_sz_97_ = lean_array_size(v_heqs_81_);
v___x_98_ = ((size_t)0ULL);
lean_inc_ref(v_heqs_81_);
v___x_99_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0(v_binderType_94_, v_e_83_, v_body_95_, v_i_85_, v_alt_80_, v_heqs_81_, v_numDiscrEqs_82_, v_heqs_81_, v_sz_97_, v___x_98_, v___x_96_, v_a_86_, v_a_87_, v_a_88_, v_a_89_);
lean_dec_ref(v_body_95_);
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_131_; 
v_a_100_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_131_ == 0)
{
v___x_102_ = v___x_99_;
v_isShared_103_ = v_isSharedCheck_131_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v___x_99_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_131_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v_fst_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_129_; 
v_fst_104_ = lean_ctor_get(v_a_100_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v_a_100_);
if (v_isSharedCheck_129_ == 0)
{
lean_object* v_unused_130_; 
v_unused_130_ = lean_ctor_get(v_a_100_, 1);
lean_dec(v_unused_130_);
v___x_106_ = v_a_100_;
v_isShared_107_ = v_isSharedCheck_129_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_fst_104_);
lean_dec(v_a_100_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_129_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
if (lean_obj_tag(v_fst_104_) == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_111_; 
lean_del_object(v___x_102_);
v___x_108_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__1);
v___x_109_ = l_Lean_MessageData_ofName(v_binderName_93_);
if (v_isShared_107_ == 0)
{
lean_ctor_set_tag(v___x_106_, 7);
lean_ctor_set(v___x_106_, 1, v___x_109_);
lean_ctor_set(v___x_106_, 0, v___x_108_);
v___x_111_ = v___x_106_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_108_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v___x_109_);
v___x_111_ = v_reuseFailAlloc_124_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_112_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__3);
v___x_113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_111_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
v___x_114_ = l_Lean_MessageData_ofExpr(v_binderType_94_);
v___x_115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_113_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
v___x_116_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__5, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__5_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__5);
v___x_117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_115_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
v___x_118_ = lean_array_to_list(v_heqs_81_);
v___x_119_ = lean_box(0);
v___x_120_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_118_, v___x_119_);
v___x_121_ = l_Lean_MessageData_ofList(v___x_120_);
v___x_122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_117_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
v___x_123_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_122_, v_a_86_, v_a_87_, v_a_88_, v_a_89_);
return v___x_123_;
}
}
else
{
lean_object* v_val_125_; lean_object* v___x_127_; 
lean_del_object(v___x_106_);
lean_dec_ref(v_binderType_94_);
lean_dec(v_binderName_93_);
lean_dec_ref(v_heqs_81_);
v_val_125_ = lean_ctor_get(v_fst_104_, 0);
lean_inc(v_val_125_);
lean_dec_ref_known(v_fst_104_, 1);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 0, v_val_125_);
v___x_127_ = v___x_102_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_val_125_);
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
}
else
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_139_; 
lean_dec_ref(v_binderType_94_);
lean_dec(v_binderName_93_);
lean_dec_ref(v_heqs_81_);
v_a_132_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_139_ == 0)
{
v___x_134_ = v___x_99_;
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_99_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_137_; 
if (v_isShared_135_ == 0)
{
v___x_137_ = v___x_134_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_a_132_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
else
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
lean_dec_ref(v_ty_84_);
lean_dec_ref(v_e_83_);
lean_dec_ref(v_heqs_81_);
v___x_140_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__7, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__7_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__7);
v___x_141_ = l_Nat_reprFast(v_numDiscrEqs_82_);
v___x_142_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
v___x_143_ = l_Lean_MessageData_ofFormat(v___x_142_);
v___x_144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_140_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
v___x_145_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__9, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__9_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___closed__9);
v___x_146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_144_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
v___x_147_ = l_Lean_indentExpr(v_alt_80_);
v___x_148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_146_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_148_, v_a_86_, v_a_87_, v_a_88_, v_a_89_);
return v___x_149_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0(lean_object* v_binderType_150_, lean_object* v_e_151_, lean_object* v_body_152_, lean_object* v_i_153_, lean_object* v_alt_154_, lean_object* v_heqs_155_, lean_object* v_numDiscrEqs_156_, lean_object* v_as_157_, size_t v_sz_158_, size_t v_i_159_, lean_object* v_b_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
uint8_t v___x_166_; 
v___x_166_ = lean_usize_dec_lt(v_i_159_, v_sz_158_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; 
lean_dec(v_numDiscrEqs_156_);
lean_dec_ref(v_heqs_155_);
lean_dec_ref(v_alt_154_);
lean_dec_ref(v_e_151_);
lean_dec_ref(v_binderType_150_);
v___x_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_167_, 0, v_b_160_);
return v___x_167_;
}
else
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v_a_170_; lean_object* v___x_171_; 
lean_dec_ref(v_b_160_);
v___x_168_ = lean_box(0);
v___x_169_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0___closed__0));
v_a_170_ = lean_array_uget_borrowed(v_as_157_, v_i_159_);
lean_inc(v___y_164_);
lean_inc_ref(v___y_163_);
lean_inc(v___y_162_);
lean_inc_ref(v___y_161_);
lean_inc(v_a_170_);
v___x_171_ = lean_infer_type(v_a_170_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v_a_172_; lean_object* v___x_173_; 
v_a_172_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_a_172_);
lean_dec_ref_known(v___x_171_, 1);
lean_inc_ref(v_binderType_150_);
v___x_173_ = l_Lean_Meta_isExprDefEq(v_a_172_, v_binderType_150_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; uint8_t v___x_175_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_a_174_);
lean_dec_ref_known(v___x_173_, 1);
v___x_175_ = lean_unbox(v_a_174_);
lean_dec(v_a_174_);
if (v___x_175_ == 0)
{
size_t v___x_176_; size_t v___x_177_; 
v___x_176_ = ((size_t)1ULL);
v___x_177_ = lean_usize_add(v_i_159_, v___x_176_);
v_i_159_ = v___x_177_;
v_b_160_ = v___x_169_;
goto _start;
}
else
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
lean_dec_ref(v_binderType_150_);
lean_inc(v_a_170_);
v___x_179_ = l_Lean_Expr_app___override(v_e_151_, v_a_170_);
v___x_180_ = lean_expr_instantiate1(v_body_152_, v_a_170_);
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = lean_nat_add(v_i_153_, v___x_181_);
v___x_183_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go(v_alt_154_, v_heqs_155_, v_numDiscrEqs_156_, v___x_179_, v___x_180_, v___x_182_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
lean_dec(v___x_182_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_193_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_193_ == 0)
{
v___x_186_ = v___x_183_;
v_isShared_187_ = v_isSharedCheck_193_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_183_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_193_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_188_, 0, v_a_184_);
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v___x_168_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_189_);
v___x_191_ = v___x_186_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
else
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_201_; 
v_a_194_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_201_ == 0)
{
v___x_196_ = v___x_183_;
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_183_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_194_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec(v_numDiscrEqs_156_);
lean_dec_ref(v_heqs_155_);
lean_dec_ref(v_alt_154_);
lean_dec_ref(v_e_151_);
lean_dec_ref(v_binderType_150_);
v_a_202_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_173_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_173_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
else
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
lean_dec(v_numDiscrEqs_156_);
lean_dec_ref(v_heqs_155_);
lean_dec_ref(v_alt_154_);
lean_dec_ref(v_e_151_);
lean_dec_ref(v_binderType_150_);
v_a_210_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_171_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_171_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0___boxed(lean_object* v_binderType_218_, lean_object* v_e_219_, lean_object* v_body_220_, lean_object* v_i_221_, lean_object* v_alt_222_, lean_object* v_heqs_223_, lean_object* v_numDiscrEqs_224_, lean_object* v_as_225_, lean_object* v_sz_226_, lean_object* v_i_227_, lean_object* v_b_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
size_t v_sz_boxed_234_; size_t v_i_boxed_235_; lean_object* v_res_236_; 
v_sz_boxed_234_ = lean_unbox_usize(v_sz_226_);
lean_dec(v_sz_226_);
v_i_boxed_235_ = lean_unbox_usize(v_i_227_);
lean_dec(v_i_227_);
v_res_236_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__0(v_binderType_218_, v_e_219_, v_body_220_, v_i_221_, v_alt_222_, v_heqs_223_, v_numDiscrEqs_224_, v_as_225_, v_sz_boxed_234_, v_i_boxed_235_, v_b_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec_ref(v_as_225_);
lean_dec(v_i_221_);
lean_dec_ref(v_body_220_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go___boxed(lean_object* v_alt_237_, lean_object* v_heqs_238_, lean_object* v_numDiscrEqs_239_, lean_object* v_e_240_, lean_object* v_ty_241_, lean_object* v_i_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go(v_alt_237_, v_heqs_238_, v_numDiscrEqs_239_, v_e_240_, v_ty_241_, v_i_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_i_242_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2(lean_object* v_00_u03b1_249_, lean_object* v_msg_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v_msg_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___boxed(lean_object* v_00_u03b1_257_, lean_object* v_msg_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2(v_00_u03b1_257_, v_msg_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkAppDiscrEqs(lean_object* v_alt_265_, lean_object* v_heqs_266_, lean_object* v_numDiscrEqs_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
lean_object* v___x_273_; 
lean_inc(v_a_271_);
lean_inc_ref(v_a_270_);
lean_inc(v_a_269_);
lean_inc_ref(v_a_268_);
lean_inc_ref(v_alt_265_);
v___x_273_ = lean_infer_type(v_alt_265_, v_a_268_, v_a_269_, v_a_270_, v_a_271_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_a_274_);
lean_dec_ref_known(v___x_273_, 1);
v___x_275_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_alt_265_);
v___x_276_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go(v_alt_265_, v_heqs_266_, v_numDiscrEqs_267_, v_alt_265_, v_a_274_, v___x_275_, v_a_268_, v_a_269_, v_a_270_, v_a_271_);
return v___x_276_;
}
else
{
lean_dec(v_numDiscrEqs_267_);
lean_dec_ref(v_heqs_266_);
lean_dec_ref(v_alt_265_);
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_mkAppDiscrEqs___boxed(lean_object* v_alt_277_, lean_object* v_heqs_278_, lean_object* v_numDiscrEqs_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Meta_Match_mkAppDiscrEqs(v_alt_277_, v_heqs_278_, v_numDiscrEqs_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
return v_res_285_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__0(lean_object* v_x_286_){
_start:
{
uint8_t v___x_287_; 
v___x_287_ = 0;
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__0___boxed(lean_object* v_x_288_){
_start:
{
uint8_t v_res_289_; lean_object* v_r_290_; 
v_res_289_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__0(v_x_288_);
lean_dec(v_x_288_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__1(lean_object* v_fvarId_291_, lean_object* v_x_292_){
_start:
{
uint8_t v___x_293_; 
v___x_293_ = l_Lean_instBEqFVarId_beq(v_fvarId_291_, v_x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__1___boxed(lean_object* v_fvarId_294_, lean_object* v_x_295_){
_start:
{
uint8_t v_res_296_; lean_object* v_r_297_; 
v_res_296_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__1(v_fvarId_294_, v_x_295_);
lean_dec(v_x_295_);
lean_dec(v_fvarId_294_);
v_r_297_ = lean_box(v_res_296_);
return v_r_297_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = lean_box(0);
v___x_300_ = lean_unsigned_to_nat(16u);
v___x_301_ = lean_mk_array(v___x_300_, v___x_299_);
return v___x_301_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_302_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__1, &l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__1);
v___x_303_ = lean_unsigned_to_nat(0u);
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set(v___x_304_, 1, v___x_302_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(lean_object* v_e_305_, lean_object* v_fvarId_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___f_309_; lean_object* v___f_310_; lean_object* v___x_311_; uint8_t v_fst_313_; lean_object* v_mctx_314_; lean_object* v___y_332_; lean_object* v_mctx_337_; lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v___f_309_ = ((lean_object*)(l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__0));
v___f_310_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_310_, 0, v_fvarId_306_);
v___x_311_ = lean_st_ref_get(v___y_307_);
v_mctx_337_ = lean_ctor_get(v___x_311_, 0);
lean_inc_ref_n(v_mctx_337_, 2);
lean_dec(v___x_311_);
v___x_338_ = lean_obj_once(&l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2, &l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___closed__2);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v_mctx_337_);
v___x_340_ = l_Lean_Expr_hasFVar(v_e_305_);
if (v___x_340_ == 0)
{
uint8_t v___x_341_; 
v___x_341_ = l_Lean_Expr_hasMVar(v_e_305_);
if (v___x_341_ == 0)
{
lean_dec_ref_known(v___x_339_, 2);
lean_dec_ref(v___f_310_);
lean_dec_ref(v_e_305_);
v_fst_313_ = v___x_341_;
v_mctx_314_ = v_mctx_337_;
goto v___jp_312_;
}
else
{
lean_object* v___x_342_; 
lean_dec_ref(v_mctx_337_);
v___x_342_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_310_, v___f_309_, v_e_305_, v___x_339_);
v___y_332_ = v___x_342_;
goto v___jp_331_;
}
}
else
{
lean_object* v___x_343_; 
lean_dec_ref(v_mctx_337_);
v___x_343_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_310_, v___f_309_, v_e_305_, v___x_339_);
v___y_332_ = v___x_343_;
goto v___jp_331_;
}
v___jp_312_:
{
lean_object* v___x_315_; lean_object* v_cache_316_; lean_object* v_zetaDeltaFVarIds_317_; lean_object* v_postponed_318_; lean_object* v_diag_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_329_; 
v___x_315_ = lean_st_ref_take(v___y_307_);
v_cache_316_ = lean_ctor_get(v___x_315_, 1);
v_zetaDeltaFVarIds_317_ = lean_ctor_get(v___x_315_, 2);
v_postponed_318_ = lean_ctor_get(v___x_315_, 3);
v_diag_319_ = lean_ctor_get(v___x_315_, 4);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_329_ == 0)
{
lean_object* v_unused_330_; 
v_unused_330_ = lean_ctor_get(v___x_315_, 0);
lean_dec(v_unused_330_);
v___x_321_ = v___x_315_;
v_isShared_322_ = v_isSharedCheck_329_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_diag_319_);
lean_inc(v_postponed_318_);
lean_inc(v_zetaDeltaFVarIds_317_);
lean_inc(v_cache_316_);
lean_dec(v___x_315_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_329_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v_mctx_314_);
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_mctx_314_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_cache_316_);
lean_ctor_set(v_reuseFailAlloc_328_, 2, v_zetaDeltaFVarIds_317_);
lean_ctor_set(v_reuseFailAlloc_328_, 3, v_postponed_318_);
lean_ctor_set(v_reuseFailAlloc_328_, 4, v_diag_319_);
v___x_324_ = v_reuseFailAlloc_328_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_325_ = lean_st_ref_put(v___y_307_, v___x_324_);
v___x_326_ = lean_box(v_fst_313_);
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
return v___x_327_;
}
}
}
v___jp_331_:
{
lean_object* v_snd_333_; lean_object* v_fst_334_; lean_object* v_mctx_335_; uint8_t v___x_336_; 
v_snd_333_ = lean_ctor_get(v___y_332_, 1);
lean_inc(v_snd_333_);
v_fst_334_ = lean_ctor_get(v___y_332_, 0);
lean_inc(v_fst_334_);
lean_dec_ref(v___y_332_);
v_mctx_335_ = lean_ctor_get(v_snd_333_, 1);
lean_inc_ref(v_mctx_335_);
lean_dec(v_snd_333_);
v___x_336_ = lean_unbox(v_fst_334_);
lean_dec(v_fst_334_);
v_fst_313_ = v___x_336_;
v_mctx_314_ = v_mctx_335_;
goto v___jp_312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg___boxed(lean_object* v_e_344_, lean_object* v_fvarId_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_e_344_, v_fvarId_345_, v___y_346_);
lean_dec(v___y_346_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0(lean_object* v_e_349_, lean_object* v_fvarId_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_e_349_, v_fvarId_350_, v___y_352_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___boxed(lean_object* v_e_357_, lean_object* v_fvarId_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0(v_e_357_, v_fvarId_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg(lean_object* v_mvarId_365_, lean_object* v_x_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_365_, v_x_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
v_a_381_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_372_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_372_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg___boxed(lean_object* v_mvarId_389_, lean_object* v_x_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg(v_mvarId_389_, v_x_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2(lean_object* v_00_u03b1_397_, lean_object* v_mvarId_398_, lean_object* v_x_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg(v_mvarId_398_, v_x_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___boxed(lean_object* v_00_u03b1_406_, lean_object* v_mvarId_407_, lean_object* v_x_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2(v_00_u03b1_406_, v_mvarId_407_, v_x_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5(lean_object* v_mvarId_418_, lean_object* v_as_419_, size_t v_sz_420_, size_t v_i_421_, lean_object* v_b_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
uint8_t v___x_428_; 
v___x_428_ = lean_usize_dec_lt(v_i_421_, v_sz_420_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; 
lean_dec(v_mvarId_418_);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v_b_422_);
return v___x_429_;
}
else
{
lean_object* v_snd_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_532_; 
v_snd_430_ = lean_ctor_get(v_b_422_, 1);
v_isSharedCheck_532_ = !lean_is_exclusive(v_b_422_);
if (v_isSharedCheck_532_ == 0)
{
lean_object* v_unused_533_; 
v_unused_533_ = lean_ctor_get(v_b_422_, 0);
lean_dec(v_unused_533_);
v___x_432_ = v_b_422_;
v_isShared_433_ = v_isSharedCheck_532_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_snd_430_);
lean_dec(v_b_422_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_532_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; lean_object* v_a_436_; lean_object* v_a_443_; 
v___x_434_ = lean_box(0);
v_a_443_ = lean_array_uget(v_as_419_, v_i_421_);
if (lean_obj_tag(v_a_443_) == 0)
{
v_a_436_ = v_snd_430_;
goto v___jp_435_;
}
else
{
lean_object* v_val_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_531_; 
v_val_444_ = lean_ctor_get(v_a_443_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v_a_443_);
if (v_isSharedCheck_531_ == 0)
{
v___x_446_ = v_a_443_;
v_isShared_447_ = v_isSharedCheck_531_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_val_444_);
lean_dec(v_a_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_531_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_448_ = lean_box(0);
v___x_449_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5___closed__0));
v___x_450_ = l_Lean_LocalDecl_type(v_val_444_);
lean_dec(v_val_444_);
v___x_451_ = l_Lean_Meta_matchEq_x3f(v___x_450_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_a_452_);
lean_dec_ref_known(v___x_451_, 1);
if (lean_obj_tag(v_a_452_) == 1)
{
lean_object* v_val_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_522_; 
v_val_453_ = lean_ctor_get(v_a_452_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v_a_452_);
if (v_isSharedCheck_522_ == 0)
{
v___x_455_ = v_a_452_;
v_isShared_456_ = v_isSharedCheck_522_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_val_453_);
lean_dec(v_a_452_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_522_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v_snd_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_520_; 
v_snd_457_ = lean_ctor_get(v_val_453_, 1);
v_isSharedCheck_520_ = !lean_is_exclusive(v_val_453_);
if (v_isSharedCheck_520_ == 0)
{
lean_object* v_unused_521_; 
v_unused_521_ = lean_ctor_get(v_val_453_, 0);
lean_dec(v_unused_521_);
v___x_459_ = v_val_453_;
v_isShared_460_ = v_isSharedCheck_520_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_snd_457_);
lean_dec(v_val_453_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_520_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v_fst_461_; lean_object* v_snd_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_519_; 
v_fst_461_ = lean_ctor_get(v_snd_457_, 0);
v_snd_462_ = lean_ctor_get(v_snd_457_, 1);
v_isSharedCheck_519_ = !lean_is_exclusive(v_snd_457_);
if (v_isSharedCheck_519_ == 0)
{
v___x_464_ = v_snd_457_;
v_isShared_465_ = v_isSharedCheck_519_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_snd_462_);
lean_inc(v_fst_461_);
lean_dec(v_snd_457_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_519_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
uint8_t v___x_466_; 
v___x_466_ = l_Lean_Expr_isFVar(v_fst_461_);
if (v___x_466_ == 0)
{
lean_del_object(v___x_464_);
lean_dec(v_snd_462_);
lean_dec(v_fst_461_);
lean_del_object(v___x_459_);
lean_del_object(v___x_455_);
lean_del_object(v___x_446_);
lean_dec(v_snd_430_);
v_a_436_ = v___x_449_;
goto v___jp_435_;
}
else
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = l_Lean_Expr_fvarId_x21(v_fst_461_);
lean_dec(v_fst_461_);
lean_inc(v___x_467_);
v___x_468_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_462_, v___x_467_, v___y_424_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; uint8_t v___x_470_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref_known(v___x_468_, 1);
v___x_470_ = lean_unbox(v_a_469_);
lean_dec(v_a_469_);
if (v___x_470_ == 0)
{
if (v___x_466_ == 0)
{
lean_dec(v___x_467_);
lean_del_object(v___x_464_);
lean_del_object(v___x_459_);
lean_del_object(v___x_455_);
lean_del_object(v___x_446_);
lean_dec(v_snd_430_);
v_a_436_ = v___x_449_;
goto v___jp_435_;
}
else
{
lean_object* v___x_471_; 
lean_inc(v_mvarId_418_);
v___x_471_ = l_Lean_Meta_subst_x3f(v_mvarId_418_, v___x_467_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_502_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_502_ == 0)
{
v___x_474_ = v___x_471_;
v_isShared_475_ = v_isSharedCheck_502_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_471_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_502_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
if (lean_obj_tag(v_a_472_) == 0)
{
lean_del_object(v___x_474_);
lean_del_object(v___x_464_);
lean_del_object(v___x_459_);
lean_del_object(v___x_455_);
lean_del_object(v___x_446_);
lean_dec(v_snd_430_);
v_a_436_ = v___x_449_;
goto v___jp_435_;
}
else
{
lean_object* v_val_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_501_; 
lean_del_object(v___x_432_);
lean_dec(v_mvarId_418_);
v_val_476_ = lean_ctor_get(v_a_472_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v_a_472_);
if (v_isSharedCheck_501_ == 0)
{
v___x_478_ = v_a_472_;
v_isShared_479_ = v_isSharedCheck_501_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_val_476_);
lean_dec(v_a_472_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_501_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = lean_mk_empty_array_with_capacity(v___x_480_);
v___x_482_ = lean_array_push(v___x_481_, v_val_476_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 0, v___x_482_);
v___x_484_ = v___x_478_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_482_);
v___x_484_ = v_reuseFailAlloc_500_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
lean_object* v___x_486_; 
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 1, v___x_448_);
lean_ctor_set(v___x_464_, 0, v___x_484_);
v___x_486_ = v___x_464_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v___x_448_);
v___x_486_ = v_reuseFailAlloc_499_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_488_; 
if (v_isShared_447_ == 0)
{
lean_ctor_set_tag(v___x_446_, 0);
lean_ctor_set(v___x_446_, 0, v___x_486_);
v___x_488_ = v___x_446_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_486_);
v___x_488_ = v_reuseFailAlloc_498_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_490_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 0, v___x_488_);
v___x_490_ = v___x_455_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_488_);
v___x_490_ = v_reuseFailAlloc_497_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_492_; 
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 1, v_snd_430_);
lean_ctor_set(v___x_459_, 0, v___x_490_);
v___x_492_ = v___x_459_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_snd_430_);
v___x_492_ = v_reuseFailAlloc_496_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_494_; 
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_492_);
v___x_494_ = v___x_474_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
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
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
lean_del_object(v___x_464_);
lean_del_object(v___x_459_);
lean_del_object(v___x_455_);
lean_del_object(v___x_446_);
lean_del_object(v___x_432_);
lean_dec(v_snd_430_);
lean_dec(v_mvarId_418_);
v_a_503_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_471_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_471_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
}
else
{
lean_dec(v___x_467_);
lean_del_object(v___x_464_);
lean_del_object(v___x_459_);
lean_del_object(v___x_455_);
lean_del_object(v___x_446_);
lean_dec(v_snd_430_);
v_a_436_ = v___x_449_;
goto v___jp_435_;
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
lean_dec(v___x_467_);
lean_del_object(v___x_464_);
lean_del_object(v___x_459_);
lean_del_object(v___x_455_);
lean_del_object(v___x_446_);
lean_del_object(v___x_432_);
lean_dec(v_snd_430_);
lean_dec(v_mvarId_418_);
v_a_511_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_468_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_468_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
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
lean_dec(v_a_452_);
lean_del_object(v___x_446_);
lean_dec(v_snd_430_);
v_a_436_ = v___x_449_;
goto v___jp_435_;
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_del_object(v___x_446_);
lean_del_object(v___x_432_);
lean_dec(v_snd_430_);
lean_dec(v_mvarId_418_);
v_a_523_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_451_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_451_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
}
v___jp_435_:
{
lean_object* v___x_438_; 
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 1, v_a_436_);
lean_ctor_set(v___x_432_, 0, v___x_434_);
v___x_438_ = v___x_432_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_a_436_);
v___x_438_ = v_reuseFailAlloc_442_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
size_t v___x_439_; size_t v___x_440_; 
v___x_439_ = ((size_t)1ULL);
v___x_440_ = lean_usize_add(v_i_421_, v___x_439_);
v_i_421_ = v___x_440_;
v_b_422_ = v___x_438_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5___boxed(lean_object* v_mvarId_534_, lean_object* v_as_535_, lean_object* v_sz_536_, lean_object* v_i_537_, lean_object* v_b_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
size_t v_sz_boxed_544_; size_t v_i_boxed_545_; lean_object* v_res_546_; 
v_sz_boxed_544_ = lean_unbox_usize(v_sz_536_);
lean_dec(v_sz_536_);
v_i_boxed_545_ = lean_unbox_usize(v_i_537_);
lean_dec(v_i_537_);
v_res_546_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5(v_mvarId_534_, v_as_535_, v_sz_boxed_544_, v_i_boxed_545_, v_b_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec_ref(v_as_535_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4(lean_object* v_mvarId_547_, lean_object* v_as_548_, size_t v_sz_549_, size_t v_i_550_, lean_object* v_b_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
uint8_t v___x_557_; 
v___x_557_ = lean_usize_dec_lt(v_i_550_, v_sz_549_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; 
lean_dec(v_mvarId_547_);
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v_b_551_);
return v___x_558_;
}
else
{
lean_object* v_snd_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_661_; 
v_snd_559_ = lean_ctor_get(v_b_551_, 1);
v_isSharedCheck_661_ = !lean_is_exclusive(v_b_551_);
if (v_isSharedCheck_661_ == 0)
{
lean_object* v_unused_662_; 
v_unused_662_ = lean_ctor_get(v_b_551_, 0);
lean_dec(v_unused_662_);
v___x_561_ = v_b_551_;
v_isShared_562_ = v_isSharedCheck_661_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_snd_559_);
lean_dec(v_b_551_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_661_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v_a_565_; lean_object* v_a_572_; 
v___x_563_ = lean_box(0);
v_a_572_ = lean_array_uget(v_as_548_, v_i_550_);
if (lean_obj_tag(v_a_572_) == 0)
{
v_a_565_ = v_snd_559_;
goto v___jp_564_;
}
else
{
lean_object* v_val_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_660_; 
v_val_573_ = lean_ctor_get(v_a_572_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v_a_572_);
if (v_isSharedCheck_660_ == 0)
{
v___x_575_ = v_a_572_;
v_isShared_576_ = v_isSharedCheck_660_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_val_573_);
lean_dec(v_a_572_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_660_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_577_ = lean_box(0);
v___x_578_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5___closed__0));
v___x_579_ = l_Lean_LocalDecl_type(v_val_573_);
lean_dec(v_val_573_);
v___x_580_ = l_Lean_Meta_matchEq_x3f(v___x_579_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
lean_dec_ref_known(v___x_580_, 1);
if (lean_obj_tag(v_a_581_) == 1)
{
lean_object* v_val_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_651_; 
v_val_582_ = lean_ctor_get(v_a_581_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v_a_581_);
if (v_isSharedCheck_651_ == 0)
{
v___x_584_ = v_a_581_;
v_isShared_585_ = v_isSharedCheck_651_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_val_582_);
lean_dec(v_a_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_651_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v_snd_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_649_; 
v_snd_586_ = lean_ctor_get(v_val_582_, 1);
v_isSharedCheck_649_ = !lean_is_exclusive(v_val_582_);
if (v_isSharedCheck_649_ == 0)
{
lean_object* v_unused_650_; 
v_unused_650_ = lean_ctor_get(v_val_582_, 0);
lean_dec(v_unused_650_);
v___x_588_ = v_val_582_;
v_isShared_589_ = v_isSharedCheck_649_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_snd_586_);
lean_dec(v_val_582_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_649_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v_fst_590_; lean_object* v_snd_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_648_; 
v_fst_590_ = lean_ctor_get(v_snd_586_, 0);
v_snd_591_ = lean_ctor_get(v_snd_586_, 1);
v_isSharedCheck_648_ = !lean_is_exclusive(v_snd_586_);
if (v_isSharedCheck_648_ == 0)
{
v___x_593_ = v_snd_586_;
v_isShared_594_ = v_isSharedCheck_648_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_snd_591_);
lean_inc(v_fst_590_);
lean_dec(v_snd_586_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_648_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
uint8_t v___x_595_; 
v___x_595_ = l_Lean_Expr_isFVar(v_fst_590_);
if (v___x_595_ == 0)
{
lean_del_object(v___x_593_);
lean_dec(v_snd_591_);
lean_dec(v_fst_590_);
lean_del_object(v___x_588_);
lean_del_object(v___x_584_);
lean_del_object(v___x_575_);
lean_dec(v_snd_559_);
v_a_565_ = v___x_578_;
goto v___jp_564_;
}
else
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = l_Lean_Expr_fvarId_x21(v_fst_590_);
lean_dec(v_fst_590_);
lean_inc(v___x_596_);
v___x_597_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_591_, v___x_596_, v___y_553_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; uint8_t v___x_599_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_a_598_);
lean_dec_ref_known(v___x_597_, 1);
v___x_599_ = lean_unbox(v_a_598_);
lean_dec(v_a_598_);
if (v___x_599_ == 0)
{
if (v___x_595_ == 0)
{
lean_dec(v___x_596_);
lean_del_object(v___x_593_);
lean_del_object(v___x_588_);
lean_del_object(v___x_584_);
lean_del_object(v___x_575_);
lean_dec(v_snd_559_);
v_a_565_ = v___x_578_;
goto v___jp_564_;
}
else
{
lean_object* v___x_600_; 
lean_inc(v_mvarId_547_);
v___x_600_ = l_Lean_Meta_subst_x3f(v_mvarId_547_, v___x_596_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_631_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_631_ == 0)
{
v___x_603_ = v___x_600_;
v_isShared_604_ = v_isSharedCheck_631_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_600_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_631_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
if (lean_obj_tag(v_a_601_) == 0)
{
lean_del_object(v___x_603_);
lean_del_object(v___x_593_);
lean_del_object(v___x_588_);
lean_del_object(v___x_584_);
lean_del_object(v___x_575_);
lean_dec(v_snd_559_);
v_a_565_ = v___x_578_;
goto v___jp_564_;
}
else
{
lean_object* v_val_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_630_; 
lean_del_object(v___x_561_);
lean_dec(v_mvarId_547_);
v_val_605_ = lean_ctor_get(v_a_601_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v_a_601_);
if (v_isSharedCheck_630_ == 0)
{
v___x_607_ = v_a_601_;
v_isShared_608_ = v_isSharedCheck_630_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_val_605_);
lean_dec(v_a_601_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_630_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_609_ = lean_unsigned_to_nat(1u);
v___x_610_ = lean_mk_empty_array_with_capacity(v___x_609_);
v___x_611_ = lean_array_push(v___x_610_, v_val_605_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_611_);
v___x_613_ = v___x_607_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_611_);
v___x_613_ = v_reuseFailAlloc_629_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_615_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 1, v___x_577_);
lean_ctor_set(v___x_593_, 0, v___x_613_);
v___x_615_ = v___x_593_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v___x_577_);
v___x_615_ = v_reuseFailAlloc_628_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_617_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set_tag(v___x_575_, 0);
lean_ctor_set(v___x_575_, 0, v___x_615_);
v___x_617_ = v___x_575_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_615_);
v___x_617_ = v_reuseFailAlloc_627_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_619_; 
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_617_);
v___x_619_ = v___x_584_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_617_);
v___x_619_ = v_reuseFailAlloc_626_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_621_; 
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 1, v_snd_559_);
lean_ctor_set(v___x_588_, 0, v___x_619_);
v___x_621_ = v___x_588_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_snd_559_);
v___x_621_ = v_reuseFailAlloc_625_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_623_; 
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_621_);
v___x_623_ = v___x_603_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
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
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_del_object(v___x_593_);
lean_del_object(v___x_588_);
lean_del_object(v___x_584_);
lean_del_object(v___x_575_);
lean_del_object(v___x_561_);
lean_dec(v_snd_559_);
lean_dec(v_mvarId_547_);
v_a_632_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_600_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_600_);
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
}
else
{
lean_dec(v___x_596_);
lean_del_object(v___x_593_);
lean_del_object(v___x_588_);
lean_del_object(v___x_584_);
lean_del_object(v___x_575_);
lean_dec(v_snd_559_);
v_a_565_ = v___x_578_;
goto v___jp_564_;
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec(v___x_596_);
lean_del_object(v___x_593_);
lean_del_object(v___x_588_);
lean_del_object(v___x_584_);
lean_del_object(v___x_575_);
lean_del_object(v___x_561_);
lean_dec(v_snd_559_);
lean_dec(v_mvarId_547_);
v_a_640_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_597_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_597_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
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
lean_dec(v_a_581_);
lean_del_object(v___x_575_);
lean_dec(v_snd_559_);
v_a_565_ = v___x_578_;
goto v___jp_564_;
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_del_object(v___x_575_);
lean_del_object(v___x_561_);
lean_dec(v_snd_559_);
lean_dec(v_mvarId_547_);
v_a_652_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_580_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_580_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
}
v___jp_564_:
{
lean_object* v___x_567_; 
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 1, v_a_565_);
lean_ctor_set(v___x_561_, 0, v___x_563_);
v___x_567_ = v___x_561_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_a_565_);
v___x_567_ = v_reuseFailAlloc_571_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
size_t v___x_568_; size_t v___x_569_; lean_object* v___x_570_; 
v___x_568_ = ((size_t)1ULL);
v___x_569_ = lean_usize_add(v_i_550_, v___x_568_);
v___x_570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4_spec__5(v_mvarId_547_, v_as_548_, v_sz_549_, v___x_569_, v___x_567_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
return v___x_570_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4___boxed(lean_object* v_mvarId_663_, lean_object* v_as_664_, lean_object* v_sz_665_, lean_object* v_i_666_, lean_object* v_b_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
size_t v_sz_boxed_673_; size_t v_i_boxed_674_; lean_object* v_res_675_; 
v_sz_boxed_673_ = lean_unbox_usize(v_sz_665_);
lean_dec(v_sz_665_);
v_i_boxed_674_ = lean_unbox_usize(v_i_666_);
lean_dec(v_i_666_);
v_res_675_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4(v_mvarId_663_, v_as_664_, v_sz_boxed_673_, v_i_boxed_674_, v_b_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec_ref(v_as_664_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(lean_object* v_init_676_, lean_object* v_mvarId_677_, lean_object* v_n_678_, lean_object* v_b_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
if (lean_obj_tag(v_n_678_) == 0)
{
lean_object* v_cs_685_; lean_object* v___x_686_; lean_object* v___x_687_; size_t v_sz_688_; size_t v___x_689_; lean_object* v___x_690_; 
v_cs_685_ = lean_ctor_get(v_n_678_, 0);
v___x_686_ = lean_box(0);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
lean_ctor_set(v___x_687_, 1, v_b_679_);
v_sz_688_ = lean_array_size(v_cs_685_);
v___x_689_ = ((size_t)0ULL);
v___x_690_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(v_init_676_, v_mvarId_677_, v_cs_685_, v_sz_688_, v___x_689_, v___x_687_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_705_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_705_ == 0)
{
v___x_693_ = v___x_690_;
v_isShared_694_ = v_isSharedCheck_705_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_690_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_705_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v_fst_695_; 
v_fst_695_ = lean_ctor_get(v_a_691_, 0);
if (lean_obj_tag(v_fst_695_) == 0)
{
lean_object* v_snd_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v_snd_696_ = lean_ctor_get(v_a_691_, 1);
lean_inc(v_snd_696_);
lean_dec(v_a_691_);
v___x_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_697_, 0, v_snd_696_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_697_);
v___x_699_ = v___x_693_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
else
{
lean_object* v_val_701_; lean_object* v___x_703_; 
lean_inc_ref(v_fst_695_);
lean_dec(v_a_691_);
v_val_701_ = lean_ctor_get(v_fst_695_, 0);
lean_inc(v_val_701_);
lean_dec_ref_known(v_fst_695_, 1);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v_val_701_);
v___x_703_ = v___x_693_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_val_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
v_a_706_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_690_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_690_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
else
{
lean_object* v_vs_714_; lean_object* v___x_715_; lean_object* v___x_716_; size_t v_sz_717_; size_t v___x_718_; lean_object* v___x_719_; 
v_vs_714_ = lean_ctor_get(v_n_678_, 0);
v___x_715_ = lean_box(0);
v___x_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
lean_ctor_set(v___x_716_, 1, v_b_679_);
v_sz_717_ = lean_array_size(v_vs_714_);
v___x_718_ = ((size_t)0ULL);
v___x_719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__4(v_mvarId_677_, v_vs_714_, v_sz_717_, v___x_718_, v___x_716_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_734_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_734_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_734_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_734_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v_fst_724_; 
v_fst_724_ = lean_ctor_get(v_a_720_, 0);
if (lean_obj_tag(v_fst_724_) == 0)
{
lean_object* v_snd_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v_snd_725_ = lean_ctor_get(v_a_720_, 1);
lean_inc(v_snd_725_);
lean_dec(v_a_720_);
v___x_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_726_, 0, v_snd_725_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_726_);
v___x_728_ = v___x_722_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
else
{
lean_object* v_val_730_; lean_object* v___x_732_; 
lean_inc_ref(v_fst_724_);
lean_dec(v_a_720_);
v_val_730_ = lean_ctor_get(v_fst_724_, 0);
lean_inc(v_val_730_);
lean_dec_ref_known(v_fst_724_, 1);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v_val_730_);
v___x_732_ = v___x_722_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_val_730_);
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
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
v_a_735_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_719_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_719_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(lean_object* v_init_743_, lean_object* v_mvarId_744_, lean_object* v_as_745_, size_t v_sz_746_, size_t v_i_747_, lean_object* v_b_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
uint8_t v___x_754_; 
v___x_754_ = lean_usize_dec_lt(v_i_747_, v_sz_746_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; 
lean_dec(v_mvarId_744_);
v___x_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_755_, 0, v_b_748_);
return v___x_755_;
}
else
{
lean_object* v_snd_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_790_; 
v_snd_756_ = lean_ctor_get(v_b_748_, 1);
v_isSharedCheck_790_ = !lean_is_exclusive(v_b_748_);
if (v_isSharedCheck_790_ == 0)
{
lean_object* v_unused_791_; 
v_unused_791_ = lean_ctor_get(v_b_748_, 0);
lean_dec(v_unused_791_);
v___x_758_ = v_b_748_;
v_isShared_759_ = v_isSharedCheck_790_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_snd_756_);
lean_dec(v_b_748_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_790_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; lean_object* v_a_761_; lean_object* v___x_762_; 
v___x_760_ = lean_box(0);
v_a_761_ = lean_array_uget_borrowed(v_as_745_, v_i_747_);
lean_inc(v_snd_756_);
lean_inc(v_mvarId_744_);
v___x_762_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_init_743_, v_mvarId_744_, v_a_761_, v_snd_756_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_781_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_781_ == 0)
{
v___x_765_ = v___x_762_;
v_isShared_766_ = v_isSharedCheck_781_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_781_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
if (lean_obj_tag(v_a_763_) == 0)
{
lean_object* v___x_767_; lean_object* v___x_769_; 
lean_dec(v_mvarId_744_);
v___x_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_767_, 0, v_a_763_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v___x_767_);
v___x_769_ = v___x_758_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_snd_756_);
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
lean_object* v_a_774_; lean_object* v___x_776_; 
lean_del_object(v___x_765_);
lean_dec(v_snd_756_);
v_a_774_ = lean_ctor_get(v_a_763_, 0);
lean_inc(v_a_774_);
lean_dec_ref_known(v_a_763_, 1);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 1, v_a_774_);
lean_ctor_set(v___x_758_, 0, v___x_760_);
v___x_776_ = v___x_758_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_760_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_a_774_);
v___x_776_ = v_reuseFailAlloc_780_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
size_t v___x_777_; size_t v___x_778_; 
v___x_777_ = ((size_t)1ULL);
v___x_778_ = lean_usize_add(v_i_747_, v___x_777_);
v_i_747_ = v___x_778_;
v_b_748_ = v___x_776_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
lean_del_object(v___x_758_);
lean_dec(v_snd_756_);
lean_dec(v_mvarId_744_);
v_a_782_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_762_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_762_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3___boxed(lean_object* v_init_792_, lean_object* v_mvarId_793_, lean_object* v_as_794_, lean_object* v_sz_795_, lean_object* v_i_796_, lean_object* v_b_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
size_t v_sz_boxed_803_; size_t v_i_boxed_804_; lean_object* v_res_805_; 
v_sz_boxed_803_ = lean_unbox_usize(v_sz_795_);
lean_dec(v_sz_795_);
v_i_boxed_804_ = lean_unbox_usize(v_i_796_);
lean_dec(v_i_796_);
v_res_805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1_spec__3(v_init_792_, v_mvarId_793_, v_as_794_, v_sz_boxed_803_, v_i_boxed_804_, v_b_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec_ref(v_as_794_);
lean_dec_ref(v_init_792_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1___boxed(lean_object* v_init_806_, lean_object* v_mvarId_807_, lean_object* v_n_808_, lean_object* v_b_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_init_806_, v_mvarId_807_, v_n_808_, v_b_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec_ref(v_n_808_);
lean_dec_ref(v_init_806_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(lean_object* v_mvarId_819_, lean_object* v_as_820_, size_t v_sz_821_, size_t v_i_822_, lean_object* v_b_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
uint8_t v___x_829_; 
v___x_829_ = lean_usize_dec_lt(v_i_822_, v_sz_821_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; 
lean_dec(v_mvarId_819_);
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v_b_823_);
return v___x_830_;
}
else
{
lean_object* v_snd_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_926_; 
v_snd_831_ = lean_ctor_get(v_b_823_, 1);
v_isSharedCheck_926_ = !lean_is_exclusive(v_b_823_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; 
v_unused_927_ = lean_ctor_get(v_b_823_, 0);
lean_dec(v_unused_927_);
v___x_833_ = v_b_823_;
v_isShared_834_ = v_isSharedCheck_926_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_snd_831_);
lean_dec(v_b_823_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_926_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v_a_837_; lean_object* v_a_844_; 
v___x_835_ = lean_box(0);
v_a_844_ = lean_array_uget_borrowed(v_as_820_, v_i_822_);
if (lean_obj_tag(v_a_844_) == 0)
{
v_a_837_ = v_snd_831_;
goto v___jp_836_;
}
else
{
lean_object* v_val_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_val_845_ = lean_ctor_get(v_a_844_, 0);
v___x_846_ = lean_box(0);
v___x_847_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___closed__0));
v___x_848_ = l_Lean_LocalDecl_type(v_val_845_);
v___x_849_ = l_Lean_Meta_matchEq_x3f(v___x_848_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_a_850_);
lean_dec_ref_known(v___x_849_, 1);
if (lean_obj_tag(v_a_850_) == 1)
{
lean_object* v_val_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_917_; 
v_val_851_ = lean_ctor_get(v_a_850_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v_a_850_);
if (v_isSharedCheck_917_ == 0)
{
v___x_853_ = v_a_850_;
v_isShared_854_ = v_isSharedCheck_917_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_val_851_);
lean_dec(v_a_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_917_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v_snd_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_915_; 
v_snd_855_ = lean_ctor_get(v_val_851_, 1);
v_isSharedCheck_915_ = !lean_is_exclusive(v_val_851_);
if (v_isSharedCheck_915_ == 0)
{
lean_object* v_unused_916_; 
v_unused_916_ = lean_ctor_get(v_val_851_, 0);
lean_dec(v_unused_916_);
v___x_857_ = v_val_851_;
v_isShared_858_ = v_isSharedCheck_915_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_snd_855_);
lean_dec(v_val_851_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_915_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v_fst_859_; lean_object* v_snd_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_914_; 
v_fst_859_ = lean_ctor_get(v_snd_855_, 0);
v_snd_860_ = lean_ctor_get(v_snd_855_, 1);
v_isSharedCheck_914_ = !lean_is_exclusive(v_snd_855_);
if (v_isSharedCheck_914_ == 0)
{
v___x_862_ = v_snd_855_;
v_isShared_863_ = v_isSharedCheck_914_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_snd_860_);
lean_inc(v_fst_859_);
lean_dec(v_snd_855_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_914_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
uint8_t v___x_864_; 
v___x_864_ = l_Lean_Expr_isFVar(v_fst_859_);
if (v___x_864_ == 0)
{
lean_del_object(v___x_862_);
lean_dec(v_snd_860_);
lean_dec(v_fst_859_);
lean_del_object(v___x_857_);
lean_del_object(v___x_853_);
lean_dec(v_snd_831_);
v_a_837_ = v___x_847_;
goto v___jp_836_;
}
else
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = l_Lean_Expr_fvarId_x21(v_fst_859_);
lean_dec(v_fst_859_);
lean_inc(v___x_865_);
v___x_866_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_860_, v___x_865_, v___y_825_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; uint8_t v___x_868_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref_known(v___x_866_, 1);
v___x_868_ = lean_unbox(v_a_867_);
lean_dec(v_a_867_);
if (v___x_868_ == 0)
{
if (v___x_864_ == 0)
{
lean_dec(v___x_865_);
lean_del_object(v___x_862_);
lean_del_object(v___x_857_);
lean_del_object(v___x_853_);
lean_dec(v_snd_831_);
v_a_837_ = v___x_847_;
goto v___jp_836_;
}
else
{
lean_object* v___x_869_; 
lean_inc(v_mvarId_819_);
v___x_869_ = l_Lean_Meta_subst_x3f(v_mvarId_819_, v___x_865_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_897_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_897_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_897_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_897_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
if (lean_obj_tag(v_a_870_) == 0)
{
lean_del_object(v___x_872_);
lean_del_object(v___x_862_);
lean_del_object(v___x_857_);
lean_del_object(v___x_853_);
lean_dec(v_snd_831_);
v_a_837_ = v___x_847_;
goto v___jp_836_;
}
else
{
lean_object* v_val_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_896_; 
lean_del_object(v___x_833_);
lean_dec(v_mvarId_819_);
v_val_874_ = lean_ctor_get(v_a_870_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v_a_870_);
if (v_isSharedCheck_896_ == 0)
{
v___x_876_ = v_a_870_;
v_isShared_877_ = v_isSharedCheck_896_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_val_874_);
lean_dec(v_a_870_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_896_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_878_ = lean_unsigned_to_nat(1u);
v___x_879_ = lean_mk_empty_array_with_capacity(v___x_878_);
v___x_880_ = lean_array_push(v___x_879_, v_val_874_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_880_);
v___x_882_ = v___x_876_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_880_);
v___x_882_ = v_reuseFailAlloc_895_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_884_; 
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 1, v___x_846_);
lean_ctor_set(v___x_862_, 0, v___x_882_);
v___x_884_ = v___x_862_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v___x_846_);
v___x_884_ = v_reuseFailAlloc_894_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_886_; 
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_884_);
v___x_886_ = v___x_853_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_893_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_888_; 
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 1, v_snd_831_);
lean_ctor_set(v___x_857_, 0, v___x_886_);
v___x_888_ = v___x_857_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_snd_831_);
v___x_888_ = v_reuseFailAlloc_892_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_890_; 
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_888_);
v___x_890_ = v___x_872_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
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
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
lean_del_object(v___x_862_);
lean_del_object(v___x_857_);
lean_del_object(v___x_853_);
lean_del_object(v___x_833_);
lean_dec(v_snd_831_);
lean_dec(v_mvarId_819_);
v_a_898_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_869_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_869_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
}
else
{
lean_dec(v___x_865_);
lean_del_object(v___x_862_);
lean_del_object(v___x_857_);
lean_del_object(v___x_853_);
lean_dec(v_snd_831_);
v_a_837_ = v___x_847_;
goto v___jp_836_;
}
}
else
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
lean_dec(v___x_865_);
lean_del_object(v___x_862_);
lean_del_object(v___x_857_);
lean_del_object(v___x_853_);
lean_del_object(v___x_833_);
lean_dec(v_snd_831_);
lean_dec(v_mvarId_819_);
v_a_906_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_913_ == 0)
{
v___x_908_ = v___x_866_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_866_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_906_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
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
lean_dec(v_a_850_);
lean_dec(v_snd_831_);
v_a_837_ = v___x_847_;
goto v___jp_836_;
}
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_del_object(v___x_833_);
lean_dec(v_snd_831_);
lean_dec(v_mvarId_819_);
v_a_918_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_849_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_849_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
v___jp_836_:
{
lean_object* v___x_839_; 
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 1, v_a_837_);
lean_ctor_set(v___x_833_, 0, v___x_835_);
v___x_839_ = v___x_833_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_835_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_a_837_);
v___x_839_ = v_reuseFailAlloc_843_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
size_t v___x_840_; size_t v___x_841_; 
v___x_840_ = ((size_t)1ULL);
v___x_841_ = lean_usize_add(v_i_822_, v___x_840_);
v_i_822_ = v___x_841_;
v_b_823_ = v___x_839_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___boxed(lean_object* v_mvarId_928_, lean_object* v_as_929_, lean_object* v_sz_930_, lean_object* v_i_931_, lean_object* v_b_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
size_t v_sz_boxed_938_; size_t v_i_boxed_939_; lean_object* v_res_940_; 
v_sz_boxed_938_ = lean_unbox_usize(v_sz_930_);
lean_dec(v_sz_930_);
v_i_boxed_939_ = lean_unbox_usize(v_i_931_);
lean_dec(v_i_931_);
v_res_940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(v_mvarId_928_, v_as_929_, v_sz_boxed_938_, v_i_boxed_939_, v_b_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec_ref(v_as_929_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(lean_object* v_mvarId_941_, lean_object* v_as_942_, size_t v_sz_943_, size_t v_i_944_, lean_object* v_b_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
uint8_t v___x_951_; 
v___x_951_ = lean_usize_dec_lt(v_i_944_, v_sz_943_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; 
lean_dec(v_mvarId_941_);
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v_b_945_);
return v___x_952_;
}
else
{
lean_object* v_snd_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_1048_; 
v_snd_953_ = lean_ctor_get(v_b_945_, 1);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_b_945_);
if (v_isSharedCheck_1048_ == 0)
{
lean_object* v_unused_1049_; 
v_unused_1049_ = lean_ctor_get(v_b_945_, 0);
lean_dec(v_unused_1049_);
v___x_955_ = v_b_945_;
v_isShared_956_ = v_isSharedCheck_1048_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_snd_953_);
lean_dec(v_b_945_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_1048_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v_a_959_; lean_object* v_a_966_; 
v___x_957_ = lean_box(0);
v_a_966_ = lean_array_uget_borrowed(v_as_942_, v_i_944_);
if (lean_obj_tag(v_a_966_) == 0)
{
v_a_959_ = v_snd_953_;
goto v___jp_958_;
}
else
{
lean_object* v_val_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v_val_967_ = lean_ctor_get(v_a_966_, 0);
v___x_968_ = lean_box(0);
v___x_969_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6___closed__0));
v___x_970_ = l_Lean_LocalDecl_type(v_val_967_);
v___x_971_ = l_Lean_Meta_matchEq_x3f(v___x_970_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref_known(v___x_971_, 1);
if (lean_obj_tag(v_a_972_) == 1)
{
lean_object* v_val_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1039_; 
v_val_973_ = lean_ctor_get(v_a_972_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_a_972_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_975_ = v_a_972_;
v_isShared_976_ = v_isSharedCheck_1039_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_val_973_);
lean_dec(v_a_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_1039_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v_snd_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_1037_; 
v_snd_977_ = lean_ctor_get(v_val_973_, 1);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_val_973_);
if (v_isSharedCheck_1037_ == 0)
{
lean_object* v_unused_1038_; 
v_unused_1038_ = lean_ctor_get(v_val_973_, 0);
lean_dec(v_unused_1038_);
v___x_979_ = v_val_973_;
v_isShared_980_ = v_isSharedCheck_1037_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_snd_977_);
lean_dec(v_val_973_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_1037_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v_fst_981_; lean_object* v_snd_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_1036_; 
v_fst_981_ = lean_ctor_get(v_snd_977_, 0);
v_snd_982_ = lean_ctor_get(v_snd_977_, 1);
v_isSharedCheck_1036_ = !lean_is_exclusive(v_snd_977_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_984_ = v_snd_977_;
v_isShared_985_ = v_isSharedCheck_1036_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_snd_982_);
lean_inc(v_fst_981_);
lean_dec(v_snd_977_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_1036_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
uint8_t v___x_986_; 
v___x_986_ = l_Lean_Expr_isFVar(v_fst_981_);
if (v___x_986_ == 0)
{
lean_del_object(v___x_984_);
lean_dec(v_snd_982_);
lean_dec(v_fst_981_);
lean_del_object(v___x_979_);
lean_del_object(v___x_975_);
lean_dec(v_snd_953_);
v_a_959_ = v___x_969_;
goto v___jp_958_;
}
else
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = l_Lean_Expr_fvarId_x21(v_fst_981_);
lean_dec(v_fst_981_);
lean_inc(v___x_987_);
v___x_988_ = l_Lean_exprDependsOn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__0___redArg(v_snd_982_, v___x_987_, v___y_947_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; uint8_t v___x_990_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_a_989_);
lean_dec_ref_known(v___x_988_, 1);
v___x_990_ = lean_unbox(v_a_989_);
lean_dec(v_a_989_);
if (v___x_990_ == 0)
{
if (v___x_986_ == 0)
{
lean_dec(v___x_987_);
lean_del_object(v___x_984_);
lean_del_object(v___x_979_);
lean_del_object(v___x_975_);
lean_dec(v_snd_953_);
v_a_959_ = v___x_969_;
goto v___jp_958_;
}
else
{
lean_object* v___x_991_; 
lean_inc(v_mvarId_941_);
v___x_991_ = l_Lean_Meta_subst_x3f(v_mvarId_941_, v___x_987_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1019_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_994_ = v___x_991_;
v_isShared_995_ = v_isSharedCheck_1019_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1019_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
if (lean_obj_tag(v_a_992_) == 0)
{
lean_del_object(v___x_994_);
lean_del_object(v___x_984_);
lean_del_object(v___x_979_);
lean_del_object(v___x_975_);
lean_dec(v_snd_953_);
v_a_959_ = v___x_969_;
goto v___jp_958_;
}
else
{
lean_object* v_val_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1018_; 
lean_del_object(v___x_955_);
lean_dec(v_mvarId_941_);
v_val_996_ = lean_ctor_get(v_a_992_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_a_992_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_998_ = v_a_992_;
v_isShared_999_ = v_isSharedCheck_1018_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_val_996_);
lean_dec(v_a_992_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1018_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1004_; 
v___x_1000_ = lean_unsigned_to_nat(1u);
v___x_1001_ = lean_mk_empty_array_with_capacity(v___x_1000_);
v___x_1002_ = lean_array_push(v___x_1001_, v_val_996_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v___x_1002_);
v___x_1004_ = v___x_998_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v___x_1006_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 1, v___x_968_);
lean_ctor_set(v___x_984_, 0, v___x_1004_);
v___x_1006_ = v___x_984_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v___x_968_);
v___x_1006_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1008_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_1006_);
v___x_1008_ = v___x_975_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1006_);
v___x_1008_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
lean_object* v___x_1010_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 1, v_snd_953_);
lean_ctor_set(v___x_979_, 0, v___x_1008_);
v___x_1010_ = v___x_979_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1014_, 1, v_snd_953_);
v___x_1010_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___x_1012_; 
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v___x_1010_);
v___x_1012_ = v___x_994_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
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
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
lean_del_object(v___x_984_);
lean_del_object(v___x_979_);
lean_del_object(v___x_975_);
lean_del_object(v___x_955_);
lean_dec(v_snd_953_);
lean_dec(v_mvarId_941_);
v_a_1020_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_991_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_991_);
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
else
{
lean_dec(v___x_987_);
lean_del_object(v___x_984_);
lean_del_object(v___x_979_);
lean_del_object(v___x_975_);
lean_dec(v_snd_953_);
v_a_959_ = v___x_969_;
goto v___jp_958_;
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_dec(v___x_987_);
lean_del_object(v___x_984_);
lean_del_object(v___x_979_);
lean_del_object(v___x_975_);
lean_del_object(v___x_955_);
lean_dec(v_snd_953_);
lean_dec(v_mvarId_941_);
v_a_1028_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_988_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_988_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
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
lean_dec(v_a_972_);
lean_dec(v_snd_953_);
v_a_959_ = v___x_969_;
goto v___jp_958_;
}
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
lean_del_object(v___x_955_);
lean_dec(v_snd_953_);
lean_dec(v_mvarId_941_);
v_a_1040_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_971_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_971_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
v___jp_958_:
{
lean_object* v___x_961_; 
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v_a_959_);
lean_ctor_set(v___x_955_, 0, v___x_957_);
v___x_961_ = v___x_955_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_a_959_);
v___x_961_ = v_reuseFailAlloc_965_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
size_t v___x_962_; size_t v___x_963_; lean_object* v___x_964_; 
v___x_962_ = ((size_t)1ULL);
v___x_963_ = lean_usize_add(v_i_944_, v___x_962_);
v___x_964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2_spec__6(v_mvarId_941_, v_as_942_, v_sz_943_, v___x_963_, v___x_961_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
return v___x_964_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2___boxed(lean_object* v_mvarId_1050_, lean_object* v_as_1051_, lean_object* v_sz_1052_, lean_object* v_i_1053_, lean_object* v_b_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
size_t v_sz_boxed_1060_; size_t v_i_boxed_1061_; lean_object* v_res_1062_; 
v_sz_boxed_1060_ = lean_unbox_usize(v_sz_1052_);
lean_dec(v_sz_1052_);
v_i_boxed_1061_ = lean_unbox_usize(v_i_1053_);
lean_dec(v_i_1053_);
v_res_1062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(v_mvarId_1050_, v_as_1051_, v_sz_boxed_1060_, v_i_boxed_1061_, v_b_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec_ref(v_as_1051_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(lean_object* v_mvarId_1063_, lean_object* v_t_1064_, lean_object* v_init_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v_root_1071_; lean_object* v_tail_1072_; lean_object* v___x_1073_; 
v_root_1071_ = lean_ctor_get(v_t_1064_, 0);
v_tail_1072_ = lean_ctor_get(v_t_1064_, 1);
lean_inc(v_mvarId_1063_);
lean_inc_ref(v_init_1065_);
v___x_1073_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__1(v_init_1065_, v_mvarId_1063_, v_root_1071_, v_init_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec_ref(v_init_1065_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1110_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1076_ = v___x_1073_;
v_isShared_1077_ = v_isSharedCheck_1110_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1073_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1110_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
if (lean_obj_tag(v_a_1074_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1080_; 
lean_dec(v_mvarId_1063_);
v_a_1078_ = lean_ctor_get(v_a_1074_, 0);
lean_inc(v_a_1078_);
lean_dec_ref_known(v_a_1074_, 1);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v_a_1078_);
v___x_1080_ = v___x_1076_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; size_t v_sz_1085_; size_t v___x_1086_; lean_object* v___x_1087_; 
lean_del_object(v___x_1076_);
v_a_1082_ = lean_ctor_get(v_a_1074_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v_a_1074_, 1);
v___x_1083_ = lean_box(0);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v_a_1082_);
v_sz_1085_ = lean_array_size(v_tail_1072_);
v___x_1086_ = ((size_t)0ULL);
v___x_1087_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1_spec__2(v_mvarId_1063_, v_tail_1072_, v_sz_1085_, v___x_1086_, v___x_1084_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1101_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1090_ = v___x_1087_;
v_isShared_1091_ = v_isSharedCheck_1101_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1087_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1101_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v_fst_1092_; 
v_fst_1092_ = lean_ctor_get(v_a_1088_, 0);
if (lean_obj_tag(v_fst_1092_) == 0)
{
lean_object* v_snd_1093_; lean_object* v___x_1095_; 
v_snd_1093_ = lean_ctor_get(v_a_1088_, 1);
lean_inc(v_snd_1093_);
lean_dec(v_a_1088_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v_snd_1093_);
v___x_1095_ = v___x_1090_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_snd_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
else
{
lean_object* v_val_1097_; lean_object* v___x_1099_; 
lean_inc_ref(v_fst_1092_);
lean_dec(v_a_1088_);
v_val_1097_ = lean_ctor_get(v_fst_1092_, 0);
lean_inc(v_val_1097_);
lean_dec_ref_known(v_fst_1092_, 1);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 0, v_val_1097_);
v___x_1099_ = v___x_1090_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_val_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
v_a_1102_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1087_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1087_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
}
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec(v_mvarId_1063_);
v_a_1111_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1073_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1073_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1___boxed(lean_object* v_mvarId_1119_, lean_object* v_t_1120_, lean_object* v_init_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(v_mvarId_1119_, v_t_1120_, v_init_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec_ref(v_t_1120_);
return v_res_1127_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__1));
v___x_1133_ = l_Lean_stringToMessageData(v___x_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0(lean_object* v_mvarId_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_lctx_1140_; lean_object* v_decls_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v_lctx_1140_ = lean_ctor_get(v___y_1135_, 2);
v_decls_1141_ = lean_ctor_get(v_lctx_1140_, 1);
v___x_1142_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__0));
v___x_1143_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__1(v_mvarId_1134_, v_decls_1141_, v___x_1142_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1155_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1146_ = v___x_1143_;
v_isShared_1147_ = v_isSharedCheck_1155_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1143_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1155_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v_fst_1148_; 
v_fst_1148_ = lean_ctor_get(v_a_1144_, 0);
lean_inc(v_fst_1148_);
lean_dec(v_a_1144_);
if (lean_obj_tag(v_fst_1148_) == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
lean_del_object(v___x_1146_);
v___x_1149_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___closed__2);
v___x_1150_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1149_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
return v___x_1150_;
}
else
{
lean_object* v_val_1151_; lean_object* v___x_1153_; 
v_val_1151_ = lean_ctor_get(v_fst_1148_, 0);
lean_inc(v_val_1151_);
lean_dec_ref_known(v_fst_1148_, 1);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v_val_1151_);
v___x_1153_ = v___x_1146_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_val_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___boxed(lean_object* v_mvarId_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0(v_mvarId_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(lean_object* v_mvarId_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v___f_1177_; lean_object* v___x_1178_; 
lean_inc(v_mvarId_1171_);
v___f_1177_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1177_, 0, v_mvarId_1171_);
v___x_1178_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar_spec__2___redArg(v_mvarId_1171_, v___f_1177_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar___boxed(lean_object* v_mvarId_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(v_mvarId_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
return v_res_1185_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0(lean_object* v_x_1193_){
_start:
{
lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__3));
v___x_1195_ = lean_name_eq(v_x_1193_, v___x_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___boxed(lean_object* v_x_1196_){
_start:
{
uint8_t v_res_1197_; lean_object* v_r_1198_; 
v_res_1197_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0(v_x_1196_);
lean_dec(v_x_1196_);
v_r_1198_ = lean_box(v_res_1197_);
return v_r_1198_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1(lean_object* v_e_1199_){
_start:
{
lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1200_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__0___closed__3));
v___x_1201_ = l_Lean_Expr_isConstOf(v_e_1199_, v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1___boxed(lean_object* v_e_1202_){
_start:
{
uint8_t v_res_1203_; lean_object* v_r_1204_; 
v_res_1203_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___lam__1(v_e_1202_);
lean_dec_ref(v_e_1202_);
v_r_1204_ = lean_box(v_res_1203_);
return v_r_1204_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__2));
v___x_1209_ = l_Lean_stringToMessageData(v___x_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(lean_object* v_mvarId_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v___f_1216_; lean_object* v___f_1217_; lean_object* v___x_1218_; 
v___f_1216_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__0));
v___f_1217_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__1));
lean_inc(v_mvarId_1210_);
v___x_1218_ = l_Lean_MVarId_getType(v_mvarId_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1220_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_a_1219_);
lean_dec_ref_known(v___x_1218_, 1);
v___x_1220_ = lean_find_expr(v___f_1217_, v_a_1219_);
lean_dec(v_a_1219_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec(v_mvarId_1210_);
v___x_1221_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___closed__3);
v___x_1222_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1221_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1222_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1222_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
else
{
lean_object* v___x_1231_; 
lean_dec_ref_known(v___x_1220_, 1);
v___x_1231_ = l_Lean_MVarId_deltaTarget(v_mvarId_1210_, v___f_1216_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
return v___x_1231_;
}
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec(v_mvarId_1210_);
v_a_1232_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1218_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1218_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset___boxed(lean_object* v_mvarId_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(v_mvarId_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
return v_res_1246_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = l_Lean_maxRecDepthErrorMessage;
v___x_1253_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
return v___x_1253_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__3);
v___x_1255_ = l_Lean_MessageData_ofFormat(v___x_1254_);
return v___x_1255_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1256_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__4);
v___x_1257_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__2));
v___x_1258_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
lean_ctor_set(v___x_1258_, 1, v___x_1256_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(lean_object* v_ref_1259_){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1261_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___closed__5);
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v_ref_1259_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg___boxed(lean_object* v_ref_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1264_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(lean_object* v_00_u03b1_1267_, lean_object* v_ref_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1268_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___boxed(lean_object* v_00_u03b1_1275_, lean_object* v_ref_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2(v_00_u03b1_1275_, v_ref_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(lean_object* v_a_1283_, lean_object* v_____r_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1290_ = lean_unsigned_to_nat(1u);
v___x_1291_ = lean_mk_empty_array_with_capacity(v___x_1290_);
v___x_1292_ = lean_array_push(v___x_1291_, v_a_1283_);
v___x_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0___boxed(lean_object* v_a_1294_, lean_object* v_____r_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1294_, v_____r_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
return v_res_1301_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1302_; double v___x_1303_; 
v___x_1302_ = lean_unsigned_to_nat(0u);
v___x_1303_ = lean_float_of_nat(v___x_1302_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(lean_object* v_cls_1307_, lean_object* v_msg_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_ref_1314_; lean_object* v___x_1315_; lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1361_; 
v_ref_1314_ = lean_ctor_get(v___y_1311_, 2);
v___x_1315_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2_spec__2(v_msg_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1318_ = v___x_1315_;
v_isShared_1319_ = v_isSharedCheck_1361_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1315_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1361_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v_traceState_1321_; lean_object* v_env_1322_; lean_object* v_nextMacroScope_1323_; lean_object* v_ngen_1324_; lean_object* v_auxDeclNGen_1325_; lean_object* v_cache_1326_; lean_object* v_recordedDeps_1327_; lean_object* v_messages_1328_; lean_object* v_infoState_1329_; lean_object* v_snapshotTasks_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1360_; 
v___x_1320_ = lean_st_ref_take(v___y_1312_);
v_traceState_1321_ = lean_ctor_get(v___x_1320_, 4);
v_env_1322_ = lean_ctor_get(v___x_1320_, 0);
v_nextMacroScope_1323_ = lean_ctor_get(v___x_1320_, 1);
v_ngen_1324_ = lean_ctor_get(v___x_1320_, 2);
v_auxDeclNGen_1325_ = lean_ctor_get(v___x_1320_, 3);
v_cache_1326_ = lean_ctor_get(v___x_1320_, 5);
v_recordedDeps_1327_ = lean_ctor_get(v___x_1320_, 6);
v_messages_1328_ = lean_ctor_get(v___x_1320_, 7);
v_infoState_1329_ = lean_ctor_get(v___x_1320_, 8);
v_snapshotTasks_1330_ = lean_ctor_get(v___x_1320_, 9);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1332_ = v___x_1320_;
v_isShared_1333_ = v_isSharedCheck_1360_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_snapshotTasks_1330_);
lean_inc(v_infoState_1329_);
lean_inc(v_messages_1328_);
lean_inc(v_recordedDeps_1327_);
lean_inc(v_cache_1326_);
lean_inc(v_traceState_1321_);
lean_inc(v_auxDeclNGen_1325_);
lean_inc(v_ngen_1324_);
lean_inc(v_nextMacroScope_1323_);
lean_inc(v_env_1322_);
lean_dec(v___x_1320_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1360_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
uint64_t v_tid_1334_; lean_object* v_traces_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1359_; 
v_tid_1334_ = lean_ctor_get_uint64(v_traceState_1321_, sizeof(void*)*1);
v_traces_1335_ = lean_ctor_get(v_traceState_1321_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v_traceState_1321_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1337_ = v_traceState_1321_;
v_isShared_1338_ = v_isSharedCheck_1359_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_traces_1335_);
lean_dec(v_traceState_1321_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1359_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; double v___x_1341_; uint8_t v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1339_ = lean_box(0);
v___x_1340_ = lean_box(0);
v___x_1341_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__0);
v___x_1342_ = 0;
v___x_1343_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__1));
v___x_1344_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1344_, 0, v_cls_1307_);
lean_ctor_set(v___x_1344_, 1, v___x_1340_);
lean_ctor_set(v___x_1344_, 2, v___x_1343_);
lean_ctor_set_float(v___x_1344_, sizeof(void*)*3, v___x_1341_);
lean_ctor_set_float(v___x_1344_, sizeof(void*)*3 + 8, v___x_1341_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 16, v___x_1342_);
v___x_1345_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1___closed__2));
v___x_1346_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1344_);
lean_ctor_set(v___x_1346_, 1, v_a_1316_);
lean_ctor_set(v___x_1346_, 2, v___x_1345_);
lean_inc(v_ref_1314_);
v___x_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1347_, 0, v_ref_1314_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
v___x_1348_ = l_Lean_PersistentArray_push___redArg(v_traces_1335_, v___x_1347_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v___x_1348_);
v___x_1350_ = v___x_1337_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1348_);
lean_ctor_set_uint64(v_reuseFailAlloc_1358_, sizeof(void*)*1, v_tid_1334_);
v___x_1350_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1352_; 
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 4, v___x_1350_);
v___x_1352_ = v___x_1332_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_env_1322_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_nextMacroScope_1323_);
lean_ctor_set(v_reuseFailAlloc_1357_, 2, v_ngen_1324_);
lean_ctor_set(v_reuseFailAlloc_1357_, 3, v_auxDeclNGen_1325_);
lean_ctor_set(v_reuseFailAlloc_1357_, 4, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1357_, 5, v_cache_1326_);
lean_ctor_set(v_reuseFailAlloc_1357_, 6, v_recordedDeps_1327_);
lean_ctor_set(v_reuseFailAlloc_1357_, 7, v_messages_1328_);
lean_ctor_set(v_reuseFailAlloc_1357_, 8, v_infoState_1329_);
lean_ctor_set(v_reuseFailAlloc_1357_, 9, v_snapshotTasks_1330_);
v___x_1352_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1353_; lean_object* v___x_1355_; 
v___x_1353_ = lean_st_ref_put(v___y_1312_, v___x_1352_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v___x_1339_);
v___x_1355_ = v___x_1318_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1339_);
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
lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v_a_1414_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; uint8_t v___y_1451_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; uint8_t v___y_1476_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v_a_1500_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; uint8_t v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; uint8_t v___y_1512_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; uint8_t v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v_a_1554_; lean_object* v___y_1558_; lean_object* v___y_1559_; uint8_t v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; uint8_t v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; uint8_t v___y_1577_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___y_1603_; uint8_t v___y_1604_; lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; uint8_t v___y_1609_; lean_object* v___y_1626_; lean_object* v___y_1627_; uint8_t v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1633_; uint8_t v___y_1634_; lean_object* v___y_1651_; lean_object* v___y_1652_; uint8_t v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; uint8_t v___y_1659_; lean_object* v___y_1677_; lean_object* v___y_1678_; lean_object* v___y_1679_; uint8_t v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; uint8_t v___y_1685_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; uint8_t v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; uint8_t v___y_1714_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v_toCold_1765_; lean_object* v_currRecDepth_1766_; lean_object* v_ref_1767_; uint16_t v_optionFlags_1768_; uint8_t v_suppressElabErrors_1769_; uint8_t v_isRecordingDeps_1770_; lean_object* v_options_1771_; lean_object* v_maxRecDepth_1772_; lean_object* v_inheritedTraceOptions_1773_; lean_object* v_cls_1774_; lean_object* v___x_1786_; uint8_t v___x_1787_; 
v_toCold_1765_ = lean_ctor_get(v_a_1406_, 0);
v_currRecDepth_1766_ = lean_ctor_get(v_a_1406_, 1);
v_ref_1767_ = lean_ctor_get(v_a_1406_, 2);
v_optionFlags_1768_ = lean_ctor_get_uint16(v_a_1406_, sizeof(void*)*3);
v_suppressElabErrors_1769_ = lean_ctor_get_uint8(v_a_1406_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1770_ = lean_ctor_get_uint8(v_a_1406_, sizeof(void*)*3 + 3);
v_options_1771_ = lean_ctor_get(v_toCold_1765_, 2);
v_maxRecDepth_1772_ = lean_ctor_get(v_toCold_1765_, 3);
v_inheritedTraceOptions_1773_ = lean_ctor_get(v_toCold_1765_, 11);
v_cls_1774_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_1786_ = lean_unsigned_to_nat(0u);
v___x_1787_ = lean_nat_dec_eq(v_maxRecDepth_1772_, v___x_1786_);
if (v___x_1787_ == 0)
{
uint8_t v___x_1788_; 
v___x_1788_ = lean_nat_dec_eq(v_currRecDepth_1766_, v_maxRecDepth_1772_);
if (v___x_1788_ == 0)
{
goto v___jp_1775_;
}
else
{
lean_object* v___x_1789_; 
lean_dec(v_mvarId_1402_);
lean_dec(v_matchDeclName_1401_);
lean_inc(v_ref_1767_);
v___x_1789_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__2___redArg(v_ref_1767_);
return v___x_1789_;
}
}
else
{
goto v___jp_1775_;
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
v___x_1424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1403_, v_matchDeclName_1401_, v_a_1414_, v___x_1422_, v___x_1423_, v___x_1417_, v___y_1413_, v___y_1412_, v___y_1411_, v___y_1410_);
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
v___x_1427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1403_, v_matchDeclName_1401_, v_a_1414_, v___x_1425_, v___x_1426_, v___x_1417_, v___y_1413_, v___y_1412_, v___y_1411_, v___y_1410_);
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
lean_dec_ref(v___y_1447_);
v___x_1452_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1450_, v___y_1446_, v___y_1444_);
lean_dec_ref(v___y_1450_);
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
lean_ctor_set(v___x_1454_, 0, v___y_1449_);
v___x_1462_ = v___x_1454_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___y_1449_);
v___x_1462_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1460_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v___x_1464_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1463_, v___y_1448_, v___y_1446_, v___y_1445_, v___y_1444_);
v___y_1429_ = v___y_1444_;
v___y_1430_ = v___y_1445_;
v___y_1431_ = v___y_1446_;
v___y_1432_ = v___y_1448_;
v___y_1433_ = v___x_1464_;
goto v___jp_1428_;
}
}
}
else
{
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1445_);
lean_dec(v_matchDeclName_1401_);
return v___x_1452_;
}
}
else
{
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
v___y_1429_ = v___y_1444_;
v___y_1430_ = v___y_1445_;
v___y_1431_ = v___y_1446_;
v___y_1432_ = v___y_1448_;
v___y_1433_ = v___y_1447_;
goto v___jp_1428_;
}
}
v___jp_1468_:
{
if (v___y_1476_ == 0)
{
lean_object* v___x_1477_; 
lean_dec_ref(v___y_1473_);
v___x_1477_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1471_, v___y_1472_, v___y_1469_);
lean_dec_ref(v___y_1471_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v___x_1478_; 
lean_dec_ref_known(v___x_1477_, 1);
v___x_1478_ = l_Lean_Meta_saveState___redArg(v___y_1472_, v___y_1469_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1480_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref_known(v___x_1478_, 1);
lean_inc(v___y_1475_);
v___x_1480_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_substSomeVar(v___y_1475_, v___y_1474_, v___y_1472_, v___y_1470_, v___y_1469_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_dec(v_a_1479_);
lean_dec(v___y_1475_);
v___y_1429_ = v___y_1469_;
v___y_1430_ = v___y_1470_;
v___y_1431_ = v___y_1472_;
v___y_1432_ = v___y_1474_;
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
v___y_1445_ = v___y_1470_;
v___y_1446_ = v___y_1472_;
v___y_1447_ = v___x_1480_;
v___y_1448_ = v___y_1474_;
v___y_1449_ = v___y_1475_;
v___y_1450_ = v_a_1479_;
v___y_1451_ = v___x_1483_;
goto v___jp_1443_;
}
else
{
lean_dec(v_a_1481_);
v___y_1444_ = v___y_1469_;
v___y_1445_ = v___y_1470_;
v___y_1446_ = v___y_1472_;
v___y_1447_ = v___x_1480_;
v___y_1448_ = v___y_1474_;
v___y_1449_ = v___y_1475_;
v___y_1450_ = v_a_1479_;
v___y_1451_ = v___x_1482_;
goto v___jp_1443_;
}
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1470_);
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
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1470_);
lean_dec(v_matchDeclName_1401_);
return v___x_1477_;
}
}
else
{
lean_object* v___x_1492_; 
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v_matchDeclName_1401_);
v___x_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1492_, 0, v___y_1473_);
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
v___y_1470_ = v___y_1495_;
v___y_1471_ = v___y_1496_;
v___y_1472_ = v___y_1497_;
v___y_1473_ = v_a_1500_;
v___y_1474_ = v___y_1498_;
v___y_1475_ = v___y_1499_;
v___y_1476_ = v___x_1502_;
goto v___jp_1468_;
}
else
{
v___y_1469_ = v___y_1494_;
v___y_1470_ = v___y_1495_;
v___y_1471_ = v___y_1496_;
v___y_1472_ = v___y_1497_;
v___y_1473_ = v_a_1500_;
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
lean_dec_ref(v___y_1506_);
v___x_1513_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1511_, v___y_1508_, v___y_1504_);
lean_dec_ref(v___y_1511_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
lean_dec_ref_known(v___x_1513_, 1);
v___x_1514_ = lean_box(0);
v___x_1515_ = l_Lean_Meta_saveState___redArg(v___y_1508_, v___y_1504_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1517_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1516_);
lean_dec_ref_known(v___x_1515_, 1);
lean_inc(v___y_1510_);
v___x_1517_ = l_Lean_Meta_splitIfTarget_x3f(v___y_1510_, v___x_1514_, v___y_1507_, v___y_1509_, v___y_1508_, v___y_1505_, v___y_1504_);
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
v___x_1524_ = l_Lean_Meta_trySubst(v_mvarId_1522_, v_fvarId_1523_, v___y_1509_, v___y_1508_, v___y_1505_, v___y_1504_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v_mvarId_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_dec(v_a_1516_);
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
v___y_1411_ = v___y_1505_;
v___y_1412_ = v___y_1508_;
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
v___y_1495_ = v___y_1505_;
v___y_1496_ = v_a_1516_;
v___y_1497_ = v___y_1508_;
v___y_1498_ = v___y_1509_;
v___y_1499_ = v___y_1510_;
v_a_1500_ = v_a_1531_;
goto v___jp_1493_;
}
}
else
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_dec(v_a_1518_);
v___x_1532_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__5);
v___x_1533_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1532_, v___y_1509_, v___y_1508_, v___y_1505_, v___y_1504_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; 
lean_dec(v_a_1516_);
lean_dec(v___y_1510_);
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1533_, 1);
v___y_1410_ = v___y_1504_;
v___y_1411_ = v___y_1505_;
v___y_1412_ = v___y_1508_;
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
v___y_1495_ = v___y_1505_;
v___y_1496_ = v_a_1516_;
v___y_1497_ = v___y_1508_;
v___y_1498_ = v___y_1509_;
v___y_1499_ = v___y_1510_;
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
v___y_1495_ = v___y_1505_;
v___y_1496_ = v_a_1516_;
v___y_1497_ = v___y_1508_;
v___y_1498_ = v___y_1509_;
v___y_1499_ = v___y_1510_;
v_a_1500_ = v_a_1536_;
goto v___jp_1493_;
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1505_);
lean_dec(v_matchDeclName_1401_);
v_a_1537_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1515_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1515_);
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
lean_dec_ref(v___y_1505_);
lean_dec(v_matchDeclName_1401_);
return v___x_1513_;
}
}
else
{
lean_object* v___x_1545_; 
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1505_);
lean_dec(v_matchDeclName_1401_);
v___x_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1545_, 0, v___y_1506_);
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
v___y_1506_ = v_a_1554_;
v___y_1507_ = v___y_1550_;
v___y_1508_ = v___y_1549_;
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
v___y_1506_ = v_a_1554_;
v___y_1507_ = v___y_1550_;
v___y_1508_ = v___y_1549_;
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
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
v_a_1566_ = lean_ctor_get(v___y_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___y_1565_, 1);
v___y_1410_ = v___y_1558_;
v___y_1411_ = v___y_1559_;
v___y_1412_ = v___y_1561_;
v___y_1413_ = v___y_1562_;
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
v___y_1549_ = v___y_1561_;
v___y_1550_ = v___y_1560_;
v___y_1551_ = v___y_1562_;
v___y_1552_ = v___y_1563_;
v___y_1553_ = v___y_1564_;
v_a_1554_ = v_a_1567_;
goto v___jp_1546_;
}
}
v___jp_1568_:
{
if (v___y_1577_ == 0)
{
lean_object* v___x_1578_; 
lean_dec_ref(v___y_1572_);
v___x_1578_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1571_, v___y_1574_, v___y_1569_);
lean_dec_ref(v___y_1571_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v___x_1579_; 
lean_dec_ref_known(v___x_1578_, 1);
v___x_1579_ = l_Lean_Meta_saveState___redArg(v___y_1574_, v___y_1569_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1581_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
lean_inc(v___y_1576_);
v___x_1581_ = l_Lean_Meta_simpIfTarget(v___y_1576_, v___y_1573_, v___y_1573_, v___y_1575_, v___y_1574_, v___y_1570_, v___y_1569_);
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
v___x_1585_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1582_, v___x_1584_, v___y_1575_, v___y_1574_, v___y_1570_, v___y_1569_);
v___y_1558_ = v___y_1569_;
v___y_1559_ = v___y_1570_;
v___y_1560_ = v___y_1573_;
v___y_1561_ = v___y_1574_;
v___y_1562_ = v___y_1575_;
v___y_1563_ = v___y_1576_;
v___y_1564_ = v_a_1580_;
v___y_1565_ = v___x_1585_;
goto v___jp_1557_;
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__7);
v___x_1587_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_1586_, v___y_1575_, v___y_1574_, v___y_1570_, v___y_1569_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1589_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v___x_1589_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___lam__0(v_a_1582_, v_a_1588_, v___y_1575_, v___y_1574_, v___y_1570_, v___y_1569_);
v___y_1558_ = v___y_1569_;
v___y_1559_ = v___y_1570_;
v___y_1560_ = v___y_1573_;
v___y_1561_ = v___y_1574_;
v___y_1562_ = v___y_1575_;
v___y_1563_ = v___y_1576_;
v___y_1564_ = v_a_1580_;
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
v___y_1547_ = v___y_1569_;
v___y_1548_ = v___y_1570_;
v___y_1549_ = v___y_1574_;
v___y_1550_ = v___y_1573_;
v___y_1551_ = v___y_1575_;
v___y_1552_ = v___y_1576_;
v___y_1553_ = v_a_1580_;
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
v___y_1547_ = v___y_1569_;
v___y_1548_ = v___y_1570_;
v___y_1549_ = v___y_1574_;
v___y_1550_ = v___y_1573_;
v___y_1551_ = v___y_1575_;
v___y_1552_ = v___y_1576_;
v___y_1553_ = v_a_1580_;
v_a_1554_ = v_a_1591_;
goto v___jp_1546_;
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1570_);
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
lean_dec_ref(v___y_1570_);
lean_dec(v_matchDeclName_1401_);
return v___x_1578_;
}
}
else
{
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1571_);
v___y_1429_ = v___y_1569_;
v___y_1430_ = v___y_1570_;
v___y_1431_ = v___y_1574_;
v___y_1432_ = v___y_1575_;
v___y_1433_ = v___y_1572_;
goto v___jp_1428_;
}
}
v___jp_1600_:
{
if (v___y_1609_ == 0)
{
lean_object* v___x_1610_; 
lean_dec_ref(v___y_1602_);
v___x_1610_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1608_, v___y_1605_, v___y_1601_);
lean_dec_ref(v___y_1608_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v___x_1611_; 
lean_dec_ref_known(v___x_1610_, 1);
v___x_1611_ = l_Lean_Meta_saveState___redArg(v___y_1605_, v___y_1601_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v___x_1613_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
lean_inc(v_a_1612_);
lean_dec_ref_known(v___x_1611_, 1);
lean_inc(v___y_1607_);
v___x_1613_ = l_Lean_Meta_splitSparseCasesOn(v___y_1607_, v___y_1606_, v___y_1605_, v___y_1603_, v___y_1601_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_dec(v_a_1612_);
lean_dec(v___y_1607_);
v___y_1429_ = v___y_1601_;
v___y_1430_ = v___y_1603_;
v___y_1431_ = v___y_1605_;
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
v___y_1569_ = v___y_1601_;
v___y_1570_ = v___y_1603_;
v___y_1571_ = v_a_1612_;
v___y_1572_ = v___x_1613_;
v___y_1573_ = v___y_1604_;
v___y_1574_ = v___y_1605_;
v___y_1575_ = v___y_1606_;
v___y_1576_ = v___y_1607_;
v___y_1577_ = v___x_1616_;
goto v___jp_1568_;
}
else
{
lean_dec(v_a_1614_);
v___y_1569_ = v___y_1601_;
v___y_1570_ = v___y_1603_;
v___y_1571_ = v_a_1612_;
v___y_1572_ = v___x_1613_;
v___y_1573_ = v___y_1604_;
v___y_1574_ = v___y_1605_;
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
lean_dec_ref(v___y_1603_);
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
lean_dec_ref(v___y_1603_);
lean_dec(v_matchDeclName_1401_);
return v___x_1610_;
}
}
else
{
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
v___y_1429_ = v___y_1601_;
v___y_1430_ = v___y_1603_;
v___y_1431_ = v___y_1605_;
v___y_1432_ = v___y_1606_;
v___y_1433_ = v___y_1602_;
goto v___jp_1428_;
}
}
v___jp_1625_:
{
if (v___y_1634_ == 0)
{
lean_object* v___x_1635_; 
lean_dec_ref(v___y_1632_);
v___x_1635_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1633_, v___y_1629_, v___y_1626_);
lean_dec_ref(v___y_1633_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v___x_1636_; 
lean_dec_ref_known(v___x_1635_, 1);
v___x_1636_ = l_Lean_Meta_saveState___redArg(v___y_1629_, v___y_1626_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1638_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1636_, 1);
lean_inc(v___y_1631_);
v___x_1638_ = l_Lean_Meta_reduceSparseCasesOn(v___y_1631_, v___y_1630_, v___y_1629_, v___y_1627_, v___y_1626_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_dec(v_a_1637_);
lean_dec(v___y_1631_);
v___y_1429_ = v___y_1626_;
v___y_1430_ = v___y_1627_;
v___y_1431_ = v___y_1629_;
v___y_1432_ = v___y_1630_;
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
v___y_1601_ = v___y_1626_;
v___y_1602_ = v___x_1638_;
v___y_1603_ = v___y_1627_;
v___y_1604_ = v___y_1628_;
v___y_1605_ = v___y_1629_;
v___y_1606_ = v___y_1630_;
v___y_1607_ = v___y_1631_;
v___y_1608_ = v_a_1637_;
v___y_1609_ = v___x_1641_;
goto v___jp_1600_;
}
else
{
lean_dec(v_a_1639_);
v___y_1601_ = v___y_1626_;
v___y_1602_ = v___x_1638_;
v___y_1603_ = v___y_1627_;
v___y_1604_ = v___y_1628_;
v___y_1605_ = v___y_1629_;
v___y_1606_ = v___y_1630_;
v___y_1607_ = v___y_1631_;
v___y_1608_ = v_a_1637_;
v___y_1609_ = v___x_1640_;
goto v___jp_1600_;
}
}
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1627_);
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
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1627_);
lean_dec(v_matchDeclName_1401_);
return v___x_1635_;
}
}
else
{
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1631_);
v___y_1429_ = v___y_1626_;
v___y_1430_ = v___y_1627_;
v___y_1431_ = v___y_1629_;
v___y_1432_ = v___y_1630_;
v___y_1433_ = v___y_1632_;
goto v___jp_1428_;
}
}
v___jp_1650_:
{
if (v___y_1659_ == 0)
{
lean_object* v___x_1660_; 
lean_dec_ref(v___y_1655_);
v___x_1660_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1658_, v___y_1654_, v___y_1651_);
lean_dec_ref(v___y_1658_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v___x_1661_; 
lean_dec_ref_known(v___x_1660_, 1);
v___x_1661_ = l_Lean_Meta_saveState___redArg(v___y_1654_, v___y_1651_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1663_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref_known(v___x_1661_, 1);
lean_inc(v___y_1657_);
v___x_1663_ = l_Lean_Meta_casesOnStuckLHS(v___y_1657_, v___y_1656_, v___y_1654_, v___y_1652_, v___y_1651_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_dec(v_a_1662_);
lean_dec(v___y_1657_);
v___y_1429_ = v___y_1651_;
v___y_1430_ = v___y_1652_;
v___y_1431_ = v___y_1654_;
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
v___y_1626_ = v___y_1651_;
v___y_1627_ = v___y_1652_;
v___y_1628_ = v___y_1653_;
v___y_1629_ = v___y_1654_;
v___y_1630_ = v___y_1656_;
v___y_1631_ = v___y_1657_;
v___y_1632_ = v___x_1663_;
v___y_1633_ = v_a_1662_;
v___y_1634_ = v___x_1666_;
goto v___jp_1625_;
}
else
{
lean_dec(v_a_1664_);
v___y_1626_ = v___y_1651_;
v___y_1627_ = v___y_1652_;
v___y_1628_ = v___y_1653_;
v___y_1629_ = v___y_1654_;
v___y_1630_ = v___y_1656_;
v___y_1631_ = v___y_1657_;
v___y_1632_ = v___x_1663_;
v___y_1633_ = v_a_1662_;
v___y_1634_ = v___x_1665_;
goto v___jp_1625_;
}
}
}
else
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1652_);
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
lean_dec_ref(v___y_1652_);
lean_dec(v_matchDeclName_1401_);
return v___x_1660_;
}
}
else
{
lean_object* v___x_1675_; 
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1652_);
lean_dec(v_matchDeclName_1401_);
v___x_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___y_1655_);
return v___x_1675_;
}
}
v___jp_1676_:
{
if (v___y_1685_ == 0)
{
lean_object* v___x_1686_; 
lean_dec_ref(v___y_1678_);
v___x_1686_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1682_, v___y_1681_, v___y_1677_);
lean_dec_ref(v___y_1682_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v___x_1687_; 
lean_dec_ref_known(v___x_1686_, 1);
v___x_1687_ = l_Lean_Meta_saveState___redArg(v___y_1681_, v___y_1677_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1689_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1688_);
lean_dec_ref_known(v___x_1687_, 1);
lean_inc(v___y_1684_);
v___x_1689_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_unfoldElimOffset(v___y_1684_, v___y_1683_, v___y_1681_, v___y_1679_, v___y_1677_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
lean_dec(v_a_1688_);
lean_dec(v___y_1684_);
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1690_);
lean_dec_ref_known(v___x_1689_, 1);
v___x_1691_ = lean_unsigned_to_nat(1u);
v___x_1692_ = lean_mk_empty_array_with_capacity(v___x_1691_);
v___x_1693_ = lean_array_push(v___x_1692_, v_a_1690_);
v___y_1410_ = v___y_1677_;
v___y_1411_ = v___y_1679_;
v___y_1412_ = v___y_1681_;
v___y_1413_ = v___y_1683_;
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
v___y_1651_ = v___y_1677_;
v___y_1652_ = v___y_1679_;
v___y_1653_ = v___y_1680_;
v___y_1654_ = v___y_1681_;
v___y_1655_ = v_a_1694_;
v___y_1656_ = v___y_1683_;
v___y_1657_ = v___y_1684_;
v___y_1658_ = v_a_1688_;
v___y_1659_ = v___x_1696_;
goto v___jp_1650_;
}
else
{
v___y_1651_ = v___y_1677_;
v___y_1652_ = v___y_1679_;
v___y_1653_ = v___y_1680_;
v___y_1654_ = v___y_1681_;
v___y_1655_ = v_a_1694_;
v___y_1656_ = v___y_1683_;
v___y_1657_ = v___y_1684_;
v___y_1658_ = v_a_1688_;
v___y_1659_ = v___x_1695_;
goto v___jp_1650_;
}
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1679_);
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
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1679_);
lean_dec(v_matchDeclName_1401_);
return v___x_1686_;
}
}
else
{
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1682_);
lean_dec_ref(v___y_1679_);
lean_dec(v_matchDeclName_1401_);
return v___y_1678_;
}
}
v___jp_1705_:
{
if (v___y_1714_ == 0)
{
lean_object* v___x_1715_; 
lean_dec_ref(v___y_1712_);
v___x_1715_ = l_Lean_Meta_SavedState_restore___redArg(v___y_1707_, v___y_1710_, v___y_1706_);
lean_dec_ref(v___y_1707_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
lean_dec_ref_known(v___x_1715_, 1);
v___x_1716_ = lean_unsigned_to_nat(16u);
v___x_1717_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
lean_ctor_set_uint8(v___x_1717_, sizeof(void*)*1, v___y_1709_);
lean_ctor_set_uint8(v___x_1717_, sizeof(void*)*1 + 1, v___y_1709_);
lean_ctor_set_uint8(v___x_1717_, sizeof(void*)*1 + 2, v___y_1709_);
v___x_1718_ = l_Lean_Meta_saveState___redArg(v___y_1710_, v___y_1706_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1720_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref_known(v___x_1718_, 1);
lean_inc(v___y_1713_);
v___x_1720_ = l_Lean_MVarId_contradiction(v___y_1713_, v___x_1717_, v___y_1711_, v___y_1710_, v___y_1708_, v___y_1706_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v___x_1721_; 
lean_dec_ref_known(v___x_1720_, 1);
lean_dec(v_a_1719_);
lean_dec(v___y_1713_);
v___x_1721_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___y_1410_ = v___y_1706_;
v___y_1411_ = v___y_1708_;
v___y_1412_ = v___y_1710_;
v___y_1413_ = v___y_1711_;
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
v___y_1677_ = v___y_1706_;
v___y_1678_ = v___x_1720_;
v___y_1679_ = v___y_1708_;
v___y_1680_ = v___y_1709_;
v___y_1681_ = v___y_1710_;
v___y_1682_ = v_a_1719_;
v___y_1683_ = v___y_1711_;
v___y_1684_ = v___y_1713_;
v___y_1685_ = v___x_1724_;
goto v___jp_1676_;
}
else
{
lean_dec(v_a_1722_);
v___y_1677_ = v___y_1706_;
v___y_1678_ = v___x_1720_;
v___y_1679_ = v___y_1708_;
v___y_1680_ = v___y_1709_;
v___y_1681_ = v___y_1710_;
v___y_1682_ = v_a_1719_;
v___y_1683_ = v___y_1711_;
v___y_1684_ = v___y_1713_;
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
lean_dec_ref(v___y_1708_);
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
lean_dec_ref(v___y_1708_);
lean_dec(v_matchDeclName_1401_);
return v___x_1715_;
}
}
else
{
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v_matchDeclName_1401_);
return v___y_1712_;
}
}
v___jp_1733_:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1738_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__9));
v___x_1739_ = l_Lean_MVarId_modifyTargetEqLHS(v_mvarId_1402_, v___x_1738_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; uint8_t v___x_1741_; lean_object* v___x_1742_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1739_, 1);
v___x_1741_ = 1;
v___x_1742_ = l_Lean_Meta_saveState___redArg(v___y_1735_, v___y_1737_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v___x_1744_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1743_);
lean_dec_ref_known(v___x_1742_, 1);
lean_inc(v_a_1740_);
v___x_1744_ = l_Lean_MVarId_refl(v_a_1740_, v___x_1741_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v___x_1745_; 
lean_dec_ref_known(v___x_1744_, 1);
lean_dec(v_a_1743_);
lean_dec(v_a_1740_);
v___x_1745_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___y_1410_ = v___y_1737_;
v___y_1411_ = v___y_1736_;
v___y_1412_ = v___y_1735_;
v___y_1413_ = v___y_1734_;
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
v___y_1706_ = v___y_1737_;
v___y_1707_ = v_a_1743_;
v___y_1708_ = v___y_1736_;
v___y_1709_ = v___x_1741_;
v___y_1710_ = v___y_1735_;
v___y_1711_ = v___y_1734_;
v___y_1712_ = v___x_1744_;
v___y_1713_ = v_a_1740_;
v___y_1714_ = v___x_1748_;
goto v___jp_1705_;
}
else
{
lean_dec(v_a_1746_);
v___y_1706_ = v___y_1737_;
v___y_1707_ = v_a_1743_;
v___y_1708_ = v___y_1736_;
v___y_1709_ = v___x_1741_;
v___y_1710_ = v___y_1735_;
v___y_1711_ = v___y_1734_;
v___y_1712_ = v___x_1744_;
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
v_a_1749_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1751_ = v___x_1742_;
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1742_);
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
v___jp_1775_:
{
uint8_t v_hasTrace_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v_hasTrace_1776_ = lean_ctor_get_uint8(v_options_1771_, sizeof(void*)*1);
v___x_1777_ = lean_unsigned_to_nat(1u);
v___x_1778_ = lean_nat_add(v_currRecDepth_1766_, v___x_1777_);
lean_inc(v_ref_1767_);
lean_inc_ref(v_toCold_1765_);
v___x_1779_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1779_, 0, v_toCold_1765_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
lean_ctor_set(v___x_1779_, 2, v_ref_1767_);
lean_ctor_set_uint16(v___x_1779_, sizeof(void*)*3, v_optionFlags_1768_);
lean_ctor_set_uint8(v___x_1779_, sizeof(void*)*3 + 2, v_suppressElabErrors_1769_);
lean_ctor_set_uint8(v___x_1779_, sizeof(void*)*3 + 3, v_isRecordingDeps_1770_);
if (v_hasTrace_1776_ == 0)
{
v___y_1734_ = v_a_1404_;
v___y_1735_ = v_a_1405_;
v___y_1736_ = v___x_1779_;
v___y_1737_ = v_a_1407_;
goto v___jp_1733_;
}
else
{
lean_object* v___x_1780_; uint8_t v___x_1781_; 
v___x_1780_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_1781_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1773_, v_options_1771_, v___x_1780_);
if (v___x_1781_ == 0)
{
v___y_1734_ = v_a_1404_;
v___y_1735_ = v_a_1405_;
v___y_1736_ = v___x_1779_;
v___y_1737_ = v_a_1407_;
goto v___jp_1733_;
}
else
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1782_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__18);
lean_inc(v_mvarId_1402_);
v___x_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1783_, 0, v_mvarId_1402_);
v___x_1784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1782_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
v___x_1785_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v_cls_1774_, v___x_1784_, v_a_1404_, v_a_1405_, v___x_1779_, v_a_1407_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_dec_ref_known(v___x_1785_, 1);
v___y_1734_ = v_a_1404_;
v___y_1735_ = v_a_1405_;
v___y_1736_ = v___x_1779_;
v___y_1737_ = v_a_1407_;
goto v___jp_1733_;
}
else
{
lean_dec_ref_known(v___x_1779_, 3);
lean_dec(v_mvarId_1402_);
lean_dec(v_matchDeclName_1401_);
return v___x_1785_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(lean_object* v_depth_1790_, lean_object* v_matchDeclName_1791_, lean_object* v_as_1792_, size_t v_i_1793_, size_t v_stop_1794_, lean_object* v_b_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
uint8_t v___x_1801_; 
v___x_1801_ = lean_usize_dec_eq(v_i_1793_, v_stop_1794_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1802_ = lean_array_uget_borrowed(v_as_1792_, v_i_1793_);
v___x_1803_ = lean_unsigned_to_nat(1u);
v___x_1804_ = lean_nat_add(v_depth_1790_, v___x_1803_);
lean_inc(v___x_1802_);
lean_inc(v_matchDeclName_1791_);
v___x_1805_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1791_, v___x_1802_, v___x_1804_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
lean_dec(v___x_1804_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; size_t v___x_1807_; size_t v___x_1808_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1806_);
lean_dec_ref_known(v___x_1805_, 1);
v___x_1807_ = ((size_t)1ULL);
v___x_1808_ = lean_usize_add(v_i_1793_, v___x_1807_);
v_i_1793_ = v___x_1808_;
v_b_1795_ = v_a_1806_;
goto _start;
}
else
{
lean_dec(v_matchDeclName_1791_);
return v___x_1805_;
}
}
else
{
lean_object* v___x_1810_; 
lean_dec(v_matchDeclName_1791_);
v___x_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1810_, 0, v_b_1795_);
return v___x_1810_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0___boxed(lean_object* v_depth_1811_, lean_object* v_matchDeclName_1812_, lean_object* v_as_1813_, lean_object* v_i_1814_, lean_object* v_stop_1815_, lean_object* v_b_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
size_t v_i_boxed_1822_; size_t v_stop_boxed_1823_; lean_object* v_res_1824_; 
v_i_boxed_1822_ = lean_unbox_usize(v_i_1814_);
lean_dec(v_i_1814_);
v_stop_boxed_1823_ = lean_unbox_usize(v_stop_1815_);
lean_dec(v_stop_1815_);
v_res_1824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__0(v_depth_1811_, v_matchDeclName_1812_, v_as_1813_, v_i_boxed_1822_, v_stop_boxed_1823_, v_b_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec_ref(v_as_1813_);
lean_dec(v_depth_1811_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___boxed(lean_object* v_matchDeclName_1825_, lean_object* v_mvarId_1826_, lean_object* v_depth_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1825_, v_mvarId_1826_, v_depth_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_);
lean_dec(v_a_1831_);
lean_dec_ref(v_a_1830_);
lean_dec(v_a_1829_);
lean_dec_ref(v_a_1828_);
lean_dec(v_depth_1827_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(lean_object* v_e_1834_, lean_object* v___y_1835_){
_start:
{
uint8_t v___x_1837_; 
v___x_1837_ = l_Lean_Expr_hasMVar(v_e_1834_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; 
v___x_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1838_, 0, v_e_1834_);
return v___x_1838_;
}
else
{
lean_object* v___x_1839_; lean_object* v_mctx_1840_; lean_object* v___x_1841_; lean_object* v_fst_1842_; lean_object* v_snd_1843_; lean_object* v___x_1844_; lean_object* v_cache_1845_; lean_object* v_zetaDeltaFVarIds_1846_; lean_object* v_postponed_1847_; lean_object* v_diag_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1857_; 
v___x_1839_ = lean_st_ref_get(v___y_1835_);
v_mctx_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc_ref(v_mctx_1840_);
lean_dec(v___x_1839_);
v___x_1841_ = l_Lean_instantiateMVarsCore(v_mctx_1840_, v_e_1834_);
v_fst_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_fst_1842_);
v_snd_1843_ = lean_ctor_get(v___x_1841_, 1);
lean_inc(v_snd_1843_);
lean_dec_ref(v___x_1841_);
v___x_1844_ = lean_st_ref_take(v___y_1835_);
v_cache_1845_ = lean_ctor_get(v___x_1844_, 1);
v_zetaDeltaFVarIds_1846_ = lean_ctor_get(v___x_1844_, 2);
v_postponed_1847_ = lean_ctor_get(v___x_1844_, 3);
v_diag_1848_ = lean_ctor_get(v___x_1844_, 4);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1857_ == 0)
{
lean_object* v_unused_1858_; 
v_unused_1858_ = lean_ctor_get(v___x_1844_, 0);
lean_dec(v_unused_1858_);
v___x_1850_ = v___x_1844_;
v_isShared_1851_ = v_isSharedCheck_1857_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_diag_1848_);
lean_inc(v_postponed_1847_);
lean_inc(v_zetaDeltaFVarIds_1846_);
lean_inc(v_cache_1845_);
lean_dec(v___x_1844_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1857_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v_snd_1843_);
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_snd_1843_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v_cache_1845_);
lean_ctor_set(v_reuseFailAlloc_1856_, 2, v_zetaDeltaFVarIds_1846_);
lean_ctor_set(v_reuseFailAlloc_1856_, 3, v_postponed_1847_);
lean_ctor_set(v_reuseFailAlloc_1856_, 4, v_diag_1848_);
v___x_1853_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = lean_st_ref_put(v___y_1835_, v___x_1853_);
v___x_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1855_, 0, v_fst_1842_);
return v___x_1855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg___boxed(lean_object* v_e_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1859_, v___y_1860_);
lean_dec(v___y_1860_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(lean_object* v_e_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_e_1863_, v___y_1865_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___boxed(lean_object* v_e_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0(v_e_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(lean_object* v_lctx_1877_, lean_object* v_localInsts_1878_, lean_object* v_x_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_1877_, v_localInsts_1878_, v_x_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1885_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1885_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
v_a_1894_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1885_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1885_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg___boxed(lean_object* v_lctx_1902_, lean_object* v_localInsts_1903_, lean_object* v_x_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1902_, v_localInsts_1903_, v_x_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(lean_object* v_00_u03b1_1911_, lean_object* v_lctx_1912_, lean_object* v_localInsts_1913_, lean_object* v_x_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v_lctx_1912_, v_localInsts_1913_, v_x_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___boxed(lean_object* v_00_u03b1_1921_, lean_object* v_lctx_1922_, lean_object* v_localInsts_1923_, lean_object* v_x_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2(v_00_u03b1_1921_, v_lctx_1922_, v_localInsts_1923_, v_x_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
return v_res_1930_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Match_proveCondEqThm___lam__0(lean_object* v_matchDeclName_1931_, lean_object* v_x_1932_){
_start:
{
uint8_t v___x_1933_; 
v___x_1933_ = lean_name_eq(v_x_1932_, v_matchDeclName_1931_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed(lean_object* v_matchDeclName_1934_, lean_object* v_x_1935_){
_start:
{
uint8_t v_res_1936_; lean_object* v_r_1937_; 
v_res_1936_ = l_Lean_Meta_Match_proveCondEqThm___lam__0(v_matchDeclName_1934_, v_x_1935_);
lean_dec(v_x_1935_);
lean_dec(v_matchDeclName_1934_);
v_r_1937_ = lean_box(v_res_1936_);
return v_r_1937_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(lean_object* v_upperBound_1938_, lean_object* v_a_1939_, lean_object* v_b_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
uint8_t v___x_1946_; 
v___x_1946_ = lean_nat_dec_lt(v_a_1939_, v_upperBound_1938_);
if (v___x_1946_ == 0)
{
lean_object* v___x_1947_; 
lean_dec(v_a_1939_);
v___x_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1947_, 0, v_b_1940_);
return v___x_1947_;
}
else
{
uint8_t v___x_1948_; lean_object* v___x_1949_; 
v___x_1948_ = 0;
v___x_1949_ = l_Lean_Meta_introSubstEq(v_b_1940_, v___x_1948_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_a_1950_; lean_object* v_snd_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref_known(v___x_1949_, 1);
v_snd_1951_ = lean_ctor_get(v_a_1950_, 1);
lean_inc(v_snd_1951_);
lean_dec(v_a_1950_);
v___x_1952_ = lean_unsigned_to_nat(1u);
v___x_1953_ = lean_nat_add(v_a_1939_, v___x_1952_);
lean_dec(v_a_1939_);
v_a_1939_ = v___x_1953_;
v_b_1940_ = v_snd_1951_;
goto _start;
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_dec(v_a_1939_);
v_a_1955_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1949_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1949_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg___boxed(lean_object* v_upperBound_1963_, lean_object* v_a_1964_, lean_object* v_b_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_1963_, v_a_1964_, v_b_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v_upperBound_1963_);
return v_res_1971_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1973_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__0));
v___x_1974_ = l_Lean_stringToMessageData(v___x_1973_);
return v___x_1974_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__2));
v___x_1977_ = l_Lean_stringToMessageData(v___x_1976_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1(lean_object* v_type_1978_, lean_object* v___f_1979_, lean_object* v_matchDeclName_1980_, lean_object* v___x_1981_, lean_object* v_heqNum_1982_, lean_object* v_heqPos_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v___x_1989_; lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2143_; 
v___x_1989_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_type_1978_, v___y_1985_);
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_1992_ = v___x_1989_;
v_isShared_1993_ = v_isSharedCheck_2143_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2143_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1994_ = lean_box(0);
v___x_1995_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1990_, v___x_1994_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2142_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_1998_ = v___x_1995_;
v_isShared_1999_ = v_isSharedCheck_2142_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2142_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; uint8_t v___y_2007_; lean_object* v_mvarId_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v_toCold_2064_; lean_object* v_options_2065_; lean_object* v_inheritedTraceOptions_2066_; uint8_t v_hasTrace_2067_; lean_object* v___x_2068_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v___y_2073_; 
v_toCold_2064_ = lean_ctor_get(v___y_1986_, 0);
v_options_2065_ = lean_ctor_get(v_toCold_2064_, 2);
v_inheritedTraceOptions_2066_ = lean_ctor_get(v_toCold_2064_, 11);
v_hasTrace_2067_ = lean_ctor_get_uint8(v_options_2065_, sizeof(void*)*1);
v___x_2068_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
if (v_hasTrace_2067_ == 0)
{
v___y_2070_ = v___y_1984_;
v___y_2071_ = v___y_1985_;
v___y_2072_ = v___y_1986_;
v___y_2073_ = v___y_1987_;
goto v___jp_2069_;
}
else
{
lean_object* v___x_2127_; uint8_t v___x_2128_; 
v___x_2127_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_2128_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2066_, v_options_2065_, v___x_2127_);
if (v___x_2128_ == 0)
{
v___y_2070_ = v___y_1984_;
v___y_2071_ = v___y_1985_;
v___y_2072_ = v___y_1986_;
v___y_2073_ = v___y_1987_;
goto v___jp_2069_;
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2129_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__3);
v___x_2130_ = l_Lean_Expr_mvarId_x21(v_a_1996_);
v___x_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
v___x_2132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2129_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v___x_2133_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2068_, v___x_2132_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_dec_ref_known(v___x_2133_, 1);
v___y_2070_ = v___y_1984_;
v___y_2071_ = v___y_1985_;
v___y_2072_ = v___y_1986_;
v___y_2073_ = v___y_1987_;
goto v___jp_2069_;
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_del_object(v___x_1998_);
lean_dec(v_a_1996_);
lean_del_object(v___x_1992_);
lean_dec(v_heqPos_1983_);
lean_dec(v___x_1981_);
lean_dec(v_matchDeclName_1980_);
lean_dec_ref(v___f_1979_);
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
}
v___jp_2000_:
{
if (v___y_2007_ == 0)
{
lean_object* v___x_2008_; 
lean_dec_ref(v___y_2002_);
lean_del_object(v___x_1998_);
v___x_2008_ = l_Lean_MVarId_deltaTarget(v___y_2004_, v___f_1979_, v___y_2005_, v___y_2006_, v___y_2003_, v___y_2001_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2010_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2009_);
lean_dec_ref_known(v___x_2008_, 1);
v___x_2010_ = l_Lean_MVarId_heqOfEq(v_a_2009_, v___y_2005_, v___y_2006_, v___y_2003_, v___y_2001_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2012_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_2010_, 1);
v___x_2012_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go(v_matchDeclName_1980_, v_a_2011_, v___x_1981_, v___y_2005_, v___y_2006_, v___y_2003_, v___y_2001_);
lean_dec(v___x_1981_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v___x_2013_; 
lean_dec_ref_known(v___x_2012_, 1);
v___x_2013_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_1996_, v___y_2006_);
return v___x_2013_;
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2021_; 
lean_dec(v_a_1996_);
v_a_2014_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2016_ = v___x_2012_;
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_2012_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_2014_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_dec(v_a_1996_);
lean_dec(v___x_1981_);
lean_dec(v_matchDeclName_1980_);
v_a_2022_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_2010_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2010_);
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
lean_dec(v_a_1996_);
lean_dec(v___x_1981_);
lean_dec(v_matchDeclName_1980_);
v_a_2030_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_2008_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2008_);
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
lean_object* v___x_2039_; 
lean_dec(v___y_2004_);
lean_dec(v_a_1996_);
lean_dec(v___x_1981_);
lean_dec(v_matchDeclName_1980_);
lean_dec_ref(v___f_1979_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set_tag(v___x_1998_, 1);
lean_ctor_set(v___x_1998_, 0, v___y_2002_);
v___x_2039_ = v___x_1998_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___y_2002_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
v___jp_2041_:
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Lean_MVarId_intros(v_mvarId_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v_snd_2049_; uint8_t v___x_2050_; lean_object* v___x_2051_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref_known(v___x_2047_, 1);
v_snd_2049_ = lean_ctor_get(v_a_2048_, 1);
lean_inc_n(v_snd_2049_, 2);
lean_dec(v_a_2048_);
v___x_2050_ = 1;
v___x_2051_ = l_Lean_MVarId_refl(v_snd_2049_, v___x_2050_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v___x_2052_; 
lean_dec_ref_known(v___x_2051_, 1);
lean_dec(v_snd_2049_);
lean_del_object(v___x_1998_);
lean_dec(v___x_1981_);
lean_dec(v_matchDeclName_1980_);
lean_dec_ref(v___f_1979_);
v___x_2052_ = l_Lean_instantiateMVars___at___00Lean_Meta_Match_proveCondEqThm_spec__0___redArg(v_a_1996_, v___y_2044_);
return v___x_2052_;
}
else
{
lean_object* v_a_2053_; uint8_t v___x_2054_; 
v_a_2053_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2053_);
lean_dec_ref_known(v___x_2051_, 1);
v___x_2054_ = l_Lean_Exception_isInterrupt(v_a_2053_);
if (v___x_2054_ == 0)
{
uint8_t v___x_2055_; 
lean_inc(v_a_2053_);
v___x_2055_ = l_Lean_Exception_isRuntime(v_a_2053_);
v___y_2001_ = v___y_2046_;
v___y_2002_ = v_a_2053_;
v___y_2003_ = v___y_2045_;
v___y_2004_ = v_snd_2049_;
v___y_2005_ = v___y_2043_;
v___y_2006_ = v___y_2044_;
v___y_2007_ = v___x_2055_;
goto v___jp_2000_;
}
else
{
v___y_2001_ = v___y_2046_;
v___y_2002_ = v_a_2053_;
v___y_2003_ = v___y_2045_;
v___y_2004_ = v_snd_2049_;
v___y_2005_ = v___y_2043_;
v___y_2006_ = v___y_2044_;
v___y_2007_ = v___x_2054_;
goto v___jp_2000_;
}
}
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_del_object(v___x_1998_);
lean_dec(v_a_1996_);
lean_dec(v___x_1981_);
lean_dec(v_matchDeclName_1980_);
lean_dec_ref(v___f_1979_);
v_a_2056_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2047_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2047_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
v___jp_2069_:
{
lean_object* v___x_2074_; uint8_t v___x_2075_; 
v___x_2074_ = l_Lean_Expr_mvarId_x21(v_a_1996_);
v___x_2075_ = lean_nat_dec_lt(v___x_1981_, v_heqNum_1982_);
if (v___x_2075_ == 0)
{
lean_del_object(v___x_1992_);
lean_dec(v_heqPos_1983_);
v_mvarId_2042_ = v___x_2074_;
v___y_2043_ = v___y_2070_;
v___y_2044_ = v___y_2071_;
v___y_2045_ = v___y_2072_;
v___y_2046_ = v___y_2073_;
goto v___jp_2041_;
}
else
{
lean_object* v___x_2076_; uint8_t v___x_2077_; lean_object* v___x_2078_; 
v___x_2076_ = lean_box(0);
v___x_2077_ = 0;
v___x_2078_ = l_Lean_Meta_introNCore(v___x_2074_, v_heqPos_1983_, v___x_2076_, v___x_2077_, v___x_2077_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v_snd_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2117_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2079_);
lean_dec_ref_known(v___x_2078_, 1);
v_snd_2080_ = lean_ctor_get(v_a_2079_, 1);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_a_2079_);
if (v_isSharedCheck_2117_ == 0)
{
lean_object* v_unused_2118_; 
v_unused_2118_ = lean_ctor_get(v_a_2079_, 0);
lean_dec(v_unused_2118_);
v___x_2082_ = v_a_2079_;
v_isShared_2083_ = v_isSharedCheck_2117_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_snd_2080_);
lean_dec(v_a_2079_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2117_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2084_; 
lean_inc(v___x_1981_);
v___x_2084_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_heqNum_1982_, v___x_1981_, v_snd_2080_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_toCold_2085_; lean_object* v_options_2086_; uint8_t v_hasTrace_2087_; 
v_toCold_2085_ = lean_ctor_get(v___y_2072_, 0);
v_options_2086_ = lean_ctor_get(v_toCold_2085_, 2);
v_hasTrace_2087_ = lean_ctor_get_uint8(v_options_2086_, sizeof(void*)*1);
if (v_hasTrace_2087_ == 0)
{
lean_object* v_a_2088_; 
lean_del_object(v___x_2082_);
lean_del_object(v___x_1992_);
v_a_2088_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2088_);
lean_dec_ref_known(v___x_2084_, 1);
v_mvarId_2042_ = v_a_2088_;
v___y_2043_ = v___y_2070_;
v___y_2044_ = v___y_2071_;
v___y_2045_ = v___y_2072_;
v___y_2046_ = v___y_2073_;
goto v___jp_2041_;
}
else
{
lean_object* v_a_2089_; lean_object* v_inheritedTraceOptions_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; 
v_a_2089_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2089_);
lean_dec_ref_known(v___x_2084_, 1);
v_inheritedTraceOptions_2090_ = lean_ctor_get(v_toCold_2085_, 11);
v___x_2091_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_2092_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2090_, v_options_2086_, v___x_2091_);
if (v___x_2092_ == 0)
{
lean_del_object(v___x_2082_);
lean_del_object(v___x_1992_);
v_mvarId_2042_ = v_a_2089_;
v___y_2043_ = v___y_2070_;
v___y_2044_ = v___y_2071_;
v___y_2045_ = v___y_2072_;
v___y_2046_ = v___y_2073_;
goto v___jp_2041_;
}
else
{
lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2093_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1, &l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___lam__1___closed__1);
lean_inc(v_a_2089_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set_tag(v___x_1992_, 1);
lean_ctor_set(v___x_1992_, 0, v_a_2089_);
v___x_2095_ = v___x_1992_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2089_);
v___x_2095_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v___x_2097_; 
if (v_isShared_2083_ == 0)
{
lean_ctor_set_tag(v___x_2082_, 7);
lean_ctor_set(v___x_2082_, 1, v___x_2095_);
lean_ctor_set(v___x_2082_, 0, v___x_2093_);
v___x_2097_ = v___x_2082_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2093_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v___x_2098_; 
v___x_2098_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_2068_, v___x_2097_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_dec_ref_known(v___x_2098_, 1);
v_mvarId_2042_ = v_a_2089_;
v___y_2043_ = v___y_2070_;
v___y_2044_ = v___y_2071_;
v___y_2045_ = v___y_2072_;
v___y_2046_ = v___y_2073_;
goto v___jp_2041_;
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec(v_a_2089_);
lean_del_object(v___x_1998_);
lean_dec(v_a_1996_);
lean_dec(v___x_1981_);
lean_dec(v_matchDeclName_1980_);
lean_dec_ref(v___f_1979_);
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
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
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_del_object(v___x_2082_);
lean_del_object(v___x_1998_);
lean_dec(v_a_1996_);
lean_del_object(v___x_1992_);
lean_dec(v___x_1981_);
lean_dec(v_matchDeclName_1980_);
lean_dec_ref(v___f_1979_);
v_a_2109_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2084_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2084_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_del_object(v___x_1998_);
lean_dec(v_a_1996_);
lean_del_object(v___x_1992_);
lean_dec(v___x_1981_);
lean_dec(v_matchDeclName_1980_);
lean_dec_ref(v___f_1979_);
v_a_2119_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2078_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2078_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1992_);
lean_dec(v_heqPos_1983_);
lean_dec(v___x_1981_);
lean_dec(v_matchDeclName_1980_);
lean_dec_ref(v___f_1979_);
return v___x_1995_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed(lean_object* v_type_2144_, lean_object* v___f_2145_, lean_object* v_matchDeclName_2146_, lean_object* v___x_2147_, lean_object* v_heqNum_2148_, lean_object* v_heqPos_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l_Lean_Meta_Match_proveCondEqThm___lam__1(v_type_2144_, v___f_2145_, v_matchDeclName_2146_, v___x_2147_, v_heqNum_2148_, v_heqPos_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v_heqNum_2148_);
return v_res_2155_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__0(void){
_start:
{
lean_object* v___x_2156_; 
v___x_2156_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2156_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__1(void){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__0, &l_Lean_Meta_Match_proveCondEqThm___closed__0_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__0);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
return v___x_2158_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__2(void){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2159_ = lean_unsigned_to_nat(32u);
v___x_2160_ = lean_mk_empty_array_with_capacity(v___x_2159_);
v___x_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
return v___x_2161_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__3(void){
_start:
{
size_t v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2162_ = ((size_t)5ULL);
v___x_2163_ = lean_unsigned_to_nat(0u);
v___x_2164_ = lean_unsigned_to_nat(32u);
v___x_2165_ = lean_mk_empty_array_with_capacity(v___x_2164_);
v___x_2166_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__2, &l_Lean_Meta_Match_proveCondEqThm___closed__2_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__2);
v___x_2167_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2167_, 0, v___x_2166_);
lean_ctor_set(v___x_2167_, 1, v___x_2165_);
lean_ctor_set(v___x_2167_, 2, v___x_2163_);
lean_ctor_set(v___x_2167_, 3, v___x_2163_);
lean_ctor_set_usize(v___x_2167_, 4, v___x_2162_);
return v___x_2167_;
}
}
static lean_object* _init_l_Lean_Meta_Match_proveCondEqThm___closed__4(void){
_start:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2168_ = lean_box(1);
v___x_2169_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_2170_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_2171_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
lean_ctor_set(v___x_2171_, 1, v___x_2169_);
lean_ctor_set(v___x_2171_, 2, v___x_2168_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm(lean_object* v_matchDeclName_2174_, lean_object* v_type_2175_, lean_object* v_heqPos_2176_, lean_object* v_heqNum_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_){
_start:
{
lean_object* v___f_2183_; lean_object* v___x_2184_; lean_object* v___f_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
lean_inc(v_matchDeclName_2174_);
v___f_2183_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2183_, 0, v_matchDeclName_2174_);
v___x_2184_ = lean_unsigned_to_nat(0u);
v___f_2185_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_proveCondEqThm___lam__1___boxed), 11, 6);
lean_closure_set(v___f_2185_, 0, v_type_2175_);
lean_closure_set(v___f_2185_, 1, v___f_2183_);
lean_closure_set(v___f_2185_, 2, v_matchDeclName_2174_);
lean_closure_set(v___f_2185_, 3, v___x_2184_);
lean_closure_set(v___f_2185_, 4, v_heqNum_2177_);
lean_closure_set(v___f_2185_, 5, v_heqPos_2176_);
v___x_2186_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_2187_ = ((lean_object*)(l_Lean_Meta_Match_proveCondEqThm___closed__5));
v___x_2188_ = l_Lean_Meta_withLCtx___at___00Lean_Meta_Match_proveCondEqThm_spec__2___redArg(v___x_2186_, v___x_2187_, v___f_2185_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_proveCondEqThm___boxed(lean_object* v_matchDeclName_2189_, lean_object* v_type_2190_, lean_object* v_heqPos_2191_, lean_object* v_heqNum_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2189_, v_type_2190_, v_heqPos_2191_, v_heqNum_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(lean_object* v_upperBound_2199_, lean_object* v_inst_2200_, lean_object* v_R_2201_, lean_object* v_a_2202_, lean_object* v_b_2203_, lean_object* v_c_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v___x_2210_; 
v___x_2210_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___redArg(v_upperBound_2199_, v_a_2202_, v_b_2203_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1___boxed(lean_object* v_upperBound_2211_, lean_object* v_inst_2212_, lean_object* v_R_2213_, lean_object* v_a_2214_, lean_object* v_b_2215_, lean_object* v_c_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_proveCondEqThm_spec__1(v_upperBound_2211_, v_inst_2212_, v_R_2213_, v_a_2214_, v_b_2215_, v_c_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v_upperBound_2211_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(lean_object* v_k_2223_, lean_object* v_b_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v___x_2230_; 
lean_inc(v___y_2228_);
lean_inc_ref(v___y_2227_);
lean_inc(v___y_2226_);
lean_inc_ref(v___y_2225_);
v___x_2230_ = lean_apply_6(v_k_2223_, v_b_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, lean_box(0));
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_2231_, lean_object* v_b_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0(v_k_2231_, v_b_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(lean_object* v_name_2239_, uint8_t v_bi_2240_, lean_object* v_type_2241_, lean_object* v_k_2242_, uint8_t v_kind_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v___f_2249_; lean_object* v___x_2250_; 
v___f_2249_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2249_, 0, v_k_2242_);
v___x_2250_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2239_, v_bi_2240_, v_type_2241_, v___f_2249_, v_kind_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2250_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2250_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
v_a_2259_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2250_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2250_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg___boxed(lean_object* v_name_2267_, lean_object* v_bi_2268_, lean_object* v_type_2269_, lean_object* v_k_2270_, lean_object* v_kind_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
uint8_t v_bi_boxed_2277_; uint8_t v_kind_boxed_2278_; lean_object* v_res_2279_; 
v_bi_boxed_2277_ = lean_unbox(v_bi_2268_);
v_kind_boxed_2278_ = lean_unbox(v_kind_2271_);
v_res_2279_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_name_2267_, v_bi_boxed_2277_, v_type_2269_, v_k_2270_, v_kind_boxed_2278_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(lean_object* v_00_u03b1_2280_, lean_object* v_name_2281_, uint8_t v_bi_2282_, lean_object* v_type_2283_, lean_object* v_k_2284_, uint8_t v_kind_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_name_2281_, v_bi_2282_, v_type_2283_, v_k_2284_, v_kind_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___boxed(lean_object* v_00_u03b1_2292_, lean_object* v_name_2293_, lean_object* v_bi_2294_, lean_object* v_type_2295_, lean_object* v_k_2296_, lean_object* v_kind_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
uint8_t v_bi_boxed_2303_; uint8_t v_kind_boxed_2304_; lean_object* v_res_2305_; 
v_bi_boxed_2303_ = lean_unbox(v_bi_2294_);
v_kind_boxed_2304_ = lean_unbox(v_kind_2297_);
v_res_2305_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0(v_00_u03b1_2292_, v_name_2293_, v_bi_boxed_2303_, v_type_2295_, v_k_2296_, v_kind_boxed_2304_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed(lean_object* v_i_2306_, lean_object* v_altsNew_2307_, lean_object* v_discrs_2308_, lean_object* v_patterns_2309_, lean_object* v_alts_2310_, lean_object* v_k_2311_, lean_object* v_altNew_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(v_i_2306_, v_altsNew_2307_, v_discrs_2308_, v_patterns_2309_, v_alts_2310_, v_k_2311_, v_altNew_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v_i_2306_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(lean_object* v_discrs_2319_, lean_object* v_patterns_2320_, lean_object* v_alts_2321_, lean_object* v_k_2322_, lean_object* v_i_2323_, lean_object* v_altsNew_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v___x_2330_; uint8_t v___x_2331_; 
v___x_2330_ = lean_array_get_size(v_alts_2321_);
v___x_2331_ = lean_nat_dec_lt(v_i_2323_, v___x_2330_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2332_; 
lean_dec(v_i_2323_);
lean_dec_ref(v_alts_2321_);
lean_dec_ref(v_patterns_2320_);
lean_dec_ref(v_discrs_2319_);
lean_inc(v_a_2328_);
lean_inc_ref(v_a_2327_);
lean_inc(v_a_2326_);
lean_inc_ref(v_a_2325_);
v___x_2332_ = lean_apply_6(v_k_2322_, v_altsNew_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, lean_box(0));
return v___x_2332_;
}
else
{
lean_object* v___f_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
lean_inc_ref(v_alts_2321_);
lean_inc_ref(v_patterns_2320_);
lean_inc_ref(v_discrs_2319_);
lean_inc(v_i_2323_);
v___f_2333_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_2333_, 0, v_i_2323_);
lean_closure_set(v___f_2333_, 1, v_altsNew_2324_);
lean_closure_set(v___f_2333_, 2, v_discrs_2319_);
lean_closure_set(v___f_2333_, 3, v_patterns_2320_);
lean_closure_set(v___f_2333_, 4, v_alts_2321_);
lean_closure_set(v___f_2333_, 5, v_k_2322_);
v___x_2334_ = lean_array_fget(v_alts_2321_, v_i_2323_);
lean_dec(v_i_2323_);
lean_dec_ref(v_alts_2321_);
v___x_2335_ = l_Lean_Meta_getFVarLocalDecl___redArg(v___x_2334_, v_a_2325_, v_a_2327_, v_a_2328_);
lean_dec(v___x_2334_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; uint8_t v___x_2341_; lean_object* v___x_2342_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2336_);
lean_dec_ref_known(v___x_2335_, 1);
v___x_2337_ = l_Lean_LocalDecl_type(v_a_2336_);
v___x_2338_ = l_Lean_Expr_replaceFVars(v___x_2337_, v_discrs_2319_, v_patterns_2320_);
lean_dec_ref(v_patterns_2320_);
lean_dec_ref(v_discrs_2319_);
lean_dec_ref(v___x_2337_);
v___x_2339_ = l_Lean_LocalDecl_userName(v_a_2336_);
v___x_2340_ = l_Lean_LocalDecl_binderInfo(v_a_2336_);
lean_dec(v_a_2336_);
v___x_2341_ = 0;
v___x_2342_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v___x_2339_, v___x_2340_, v___x_2338_, v___f_2333_, v___x_2341_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_);
return v___x_2342_;
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec_ref(v___f_2333_);
lean_dec_ref(v_patterns_2320_);
lean_dec_ref(v_discrs_2319_);
v_a_2343_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2335_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2335_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___lam__0(lean_object* v_i_2351_, lean_object* v_altsNew_2352_, lean_object* v_discrs_2353_, lean_object* v_patterns_2354_, lean_object* v_alts_2355_, lean_object* v_k_2356_, lean_object* v_altNew_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2363_ = lean_unsigned_to_nat(1u);
v___x_2364_ = lean_nat_add(v_i_2351_, v___x_2363_);
v___x_2365_ = lean_array_push(v_altsNew_2352_, v_altNew_2357_);
v___x_2366_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2353_, v_patterns_2354_, v_alts_2355_, v_k_2356_, v___x_2364_, v___x_2365_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg___boxed(lean_object* v_discrs_2367_, lean_object* v_patterns_2368_, lean_object* v_alts_2369_, lean_object* v_k_2370_, lean_object* v_i_2371_, lean_object* v_altsNew_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2367_, v_patterns_2368_, v_alts_2369_, v_k_2370_, v_i_2371_, v_altsNew_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
lean_dec(v_a_2374_);
lean_dec_ref(v_a_2373_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(lean_object* v_00_u03b1_2379_, lean_object* v_discrs_2380_, lean_object* v_patterns_2381_, lean_object* v_alts_2382_, lean_object* v_k_2383_, lean_object* v_i_2384_, lean_object* v_altsNew_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2380_, v_patterns_2381_, v_alts_2382_, v_k_2383_, v_i_2384_, v_altsNew_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___boxed(lean_object* v_00_u03b1_2392_, lean_object* v_discrs_2393_, lean_object* v_patterns_2394_, lean_object* v_alts_2395_, lean_object* v_k_2396_, lean_object* v_i_2397_, lean_object* v_altsNew_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go(v_00_u03b1_2392_, v_discrs_2393_, v_patterns_2394_, v_alts_2395_, v_k_2396_, v_i_2397_, v_altsNew_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
lean_dec(v_a_2400_);
lean_dec_ref(v_a_2399_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(lean_object* v_numDiscrEqs_2407_, lean_object* v_discrs_2408_, lean_object* v_patterns_2409_, lean_object* v_alts_2410_, lean_object* v_k_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_){
_start:
{
lean_object* v___x_2417_; uint8_t v___x_2418_; 
v___x_2417_ = lean_unsigned_to_nat(0u);
v___x_2418_ = lean_nat_dec_eq(v_numDiscrEqs_2407_, v___x_2417_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_2420_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go___redArg(v_discrs_2408_, v_patterns_2409_, v_alts_2410_, v_k_2411_, v___x_2417_, v___x_2419_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_);
return v___x_2420_;
}
else
{
lean_object* v___x_2421_; 
lean_dec_ref(v_patterns_2409_);
lean_dec_ref(v_discrs_2408_);
lean_inc(v_a_2415_);
lean_inc_ref(v_a_2414_);
lean_inc(v_a_2413_);
lean_inc_ref(v_a_2412_);
v___x_2421_ = lean_apply_6(v_k_2411_, v_alts_2410_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, lean_box(0));
return v___x_2421_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___boxed(lean_object* v_numDiscrEqs_2422_, lean_object* v_discrs_2423_, lean_object* v_patterns_2424_, lean_object* v_alts_2425_, lean_object* v_k_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v_numDiscrEqs_2422_, v_discrs_2423_, v_patterns_2424_, v_alts_2425_, v_k_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
lean_dec(v_a_2430_);
lean_dec_ref(v_a_2429_);
lean_dec(v_a_2428_);
lean_dec_ref(v_a_2427_);
lean_dec(v_numDiscrEqs_2422_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(lean_object* v_00_u03b1_2433_, lean_object* v_numDiscrEqs_2434_, lean_object* v_discrs_2435_, lean_object* v_patterns_2436_, lean_object* v_alts_2437_, lean_object* v_k_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v_numDiscrEqs_2434_, v_discrs_2435_, v_patterns_2436_, v_alts_2437_, v_k_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___boxed(lean_object* v_00_u03b1_2445_, lean_object* v_numDiscrEqs_2446_, lean_object* v_discrs_2447_, lean_object* v_patterns_2448_, lean_object* v_alts_2449_, lean_object* v_k_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts(v_00_u03b1_2445_, v_numDiscrEqs_2446_, v_discrs_2447_, v_patterns_2448_, v_alts_2449_, v_k_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
lean_dec(v_a_2454_);
lean_dec_ref(v_a_2453_);
lean_dec(v_a_2452_);
lean_dec_ref(v_a_2451_);
lean_dec(v_numDiscrEqs_2446_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(lean_object* v_declName_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v___x_2460_; lean_object* v_env_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2460_ = lean_st_ref_get(v___y_2458_);
v_env_2461_ = lean_ctor_get(v___x_2460_, 0);
lean_inc_ref(v_env_2461_);
lean_dec(v___x_2460_);
v___x_2462_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2461_, v_declName_2457_);
v___x_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg___boxed(lean_object* v_declName_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_declName_2464_, v___y_2465_);
lean_dec(v___y_2465_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(lean_object* v_declName_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_declName_2468_, v___y_2472_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___boxed(lean_object* v_declName_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2(v_declName_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(lean_object* v_msg_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
lean_object* v___f_2489_; lean_object* v___x_14362__overap_2490_; lean_object* v___x_2491_; 
v___f_2489_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_14362__overap_2490_ = lean_panic_fn_borrowed(v___f_2489_, v_msg_2483_);
lean_inc(v___y_2487_);
lean_inc_ref(v___y_2486_);
lean_inc(v___y_2485_);
lean_inc_ref(v___y_2484_);
v___x_2491_ = lean_apply_5(v___x_14362__overap_2490_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, lean_box(0));
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___boxed(lean_object* v_msg_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v_msg_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(lean_object* v_k_2499_, lean_object* v_b_2500_, lean_object* v_c_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v___x_2507_; 
lean_inc(v___y_2505_);
lean_inc_ref(v___y_2504_);
lean_inc(v___y_2503_);
lean_inc_ref(v___y_2502_);
v___x_2507_ = lean_apply_7(v_k_2499_, v_b_2500_, v_c_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, lean_box(0));
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed(lean_object* v_k_2508_, lean_object* v_b_2509_, lean_object* v_c_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0(v_k_2508_, v_b_2509_, v_c_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(lean_object* v_type_2517_, lean_object* v_k_2518_, uint8_t v_cleanupAnnotations_2519_, uint8_t v_whnfType_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v___f_2526_; lean_object* v___x_2527_; 
v___f_2526_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2526_, 0, v_k_2518_);
v___x_2527_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_2517_, v___f_2526_, v_cleanupAnnotations_2519_, v_whnfType_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2527_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2527_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
v_a_2536_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2527_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2527_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___boxed(lean_object* v_type_2544_, lean_object* v_k_2545_, lean_object* v_cleanupAnnotations_2546_, lean_object* v_whnfType_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2553_; uint8_t v_whnfType_boxed_2554_; lean_object* v_res_2555_; 
v_cleanupAnnotations_boxed_2553_ = lean_unbox(v_cleanupAnnotations_2546_);
v_whnfType_boxed_2554_ = lean_unbox(v_whnfType_2547_);
v_res_2555_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v_type_2544_, v_k_2545_, v_cleanupAnnotations_boxed_2553_, v_whnfType_boxed_2554_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(lean_object* v_00_u03b1_2556_, lean_object* v_type_2557_, lean_object* v_k_2558_, uint8_t v_cleanupAnnotations_2559_, uint8_t v_whnfType_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v___x_2566_; 
v___x_2566_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v_type_2557_, v_k_2558_, v_cleanupAnnotations_2559_, v_whnfType_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___boxed(lean_object* v_00_u03b1_2567_, lean_object* v_type_2568_, lean_object* v_k_2569_, lean_object* v_cleanupAnnotations_2570_, lean_object* v_whnfType_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2577_; uint8_t v_whnfType_boxed_2578_; lean_object* v_res_2579_; 
v_cleanupAnnotations_boxed_2577_ = lean_unbox(v_cleanupAnnotations_2570_);
v_whnfType_boxed_2578_ = lean_unbox(v_whnfType_2571_);
v_res_2579_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9(v_00_u03b1_2567_, v_type_2568_, v_k_2569_, v_cleanupAnnotations_boxed_2577_, v_whnfType_boxed_2578_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(lean_object* v_overlaps_2580_, lean_object* v_splitterName_2581_, lean_object* v_matcherInput_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v_matchType_2588_; lean_object* v_discrInfos_2589_; lean_object* v_lhss_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2610_; 
v_matchType_2588_ = lean_ctor_get(v_matcherInput_2582_, 1);
v_discrInfos_2589_ = lean_ctor_get(v_matcherInput_2582_, 2);
v_lhss_2590_ = lean_ctor_get(v_matcherInput_2582_, 3);
v_isSharedCheck_2610_ = !lean_is_exclusive(v_matcherInput_2582_);
if (v_isSharedCheck_2610_ == 0)
{
lean_object* v_unused_2611_; lean_object* v_unused_2612_; 
v_unused_2611_ = lean_ctor_get(v_matcherInput_2582_, 4);
lean_dec(v_unused_2611_);
v_unused_2612_ = lean_ctor_get(v_matcherInput_2582_, 0);
lean_dec(v_unused_2612_);
v___x_2592_ = v_matcherInput_2582_;
v_isShared_2593_ = v_isSharedCheck_2610_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_lhss_2590_);
lean_inc(v_discrInfos_2589_);
lean_inc(v_matchType_2588_);
lean_dec(v_matcherInput_2582_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2610_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2594_; lean_object* v___x_2596_; 
v___x_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2594_, 0, v_overlaps_2580_);
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 4, v___x_2594_);
lean_ctor_set(v___x_2592_, 0, v_splitterName_2581_);
v___x_2596_ = v___x_2592_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_splitterName_2581_);
lean_ctor_set(v_reuseFailAlloc_2609_, 1, v_matchType_2588_);
lean_ctor_set(v_reuseFailAlloc_2609_, 2, v_discrInfos_2589_);
lean_ctor_set(v_reuseFailAlloc_2609_, 3, v_lhss_2590_);
lean_ctor_set(v_reuseFailAlloc_2609_, 4, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
lean_object* v___x_2597_; 
v___x_2597_ = l_Lean_Meta_Match_mkMatcher(v___x_2596_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v_addMatcher_2599_; lean_object* v___x_2600_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
lean_dec_ref_known(v___x_2597_, 1);
v_addMatcher_2599_ = lean_ctor_get(v_a_2598_, 3);
lean_inc_ref(v_addMatcher_2599_);
lean_dec(v_a_2598_);
lean_inc(v___y_2586_);
lean_inc_ref(v___y_2585_);
lean_inc(v___y_2584_);
lean_inc_ref(v___y_2583_);
v___x_2600_ = lean_apply_5(v_addMatcher_2599_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, lean_box(0));
return v___x_2600_;
}
else
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2608_; 
v_a_2601_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2603_ = v___x_2597_;
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2597_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2606_; 
if (v_isShared_2604_ == 0)
{
v___x_2606_ = v___x_2603_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_a_2601_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed(lean_object* v_overlaps_2613_, lean_object* v_splitterName_2614_, lean_object* v_matcherInput_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0(v_overlaps_2613_, v_splitterName_2614_, v_matcherInput_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
return v_res_2621_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(lean_object* v_xs_2622_, lean_object* v_ys_2623_, lean_object* v_x_2624_){
_start:
{
lean_object* v_zero_2625_; uint8_t v_isZero_2626_; 
v_zero_2625_ = lean_unsigned_to_nat(0u);
v_isZero_2626_ = lean_nat_dec_eq(v_x_2624_, v_zero_2625_);
if (v_isZero_2626_ == 1)
{
lean_dec(v_x_2624_);
return v_isZero_2626_;
}
else
{
lean_object* v_one_2627_; lean_object* v_n_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; uint8_t v___x_2631_; 
v_one_2627_ = lean_unsigned_to_nat(1u);
v_n_2628_ = lean_nat_sub(v_x_2624_, v_one_2627_);
lean_dec(v_x_2624_);
v___x_2629_ = lean_array_fget_borrowed(v_xs_2622_, v_n_2628_);
v___x_2630_ = lean_array_fget_borrowed(v_ys_2623_, v_n_2628_);
v___x_2631_ = l_Lean_Meta_Match_instBEqAltParamInfo_beq(v___x_2629_, v___x_2630_);
if (v___x_2631_ == 0)
{
lean_dec(v_n_2628_);
return v___x_2631_;
}
else
{
v_x_2624_ = v_n_2628_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg___boxed(lean_object* v_xs_2633_, lean_object* v_ys_2634_, lean_object* v_x_2635_){
_start:
{
uint8_t v_res_2636_; lean_object* v_r_2637_; 
v_res_2636_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_2633_, v_ys_2634_, v_x_2635_);
lean_dec_ref(v_ys_2634_);
lean_dec_ref(v_xs_2633_);
v_r_2637_ = lean_box(v_res_2636_);
return v_r_2637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(lean_object* v_a_2638_, lean_object* v_b_2639_){
_start:
{
lean_object* v_array_2640_; lean_object* v_start_2641_; lean_object* v_stop_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2655_; 
v_array_2640_ = lean_ctor_get(v_a_2638_, 0);
v_start_2641_ = lean_ctor_get(v_a_2638_, 1);
v_stop_2642_ = lean_ctor_get(v_a_2638_, 2);
v_isSharedCheck_2655_ = !lean_is_exclusive(v_a_2638_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2644_ = v_a_2638_;
v_isShared_2645_ = v_isSharedCheck_2655_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_stop_2642_);
lean_inc(v_start_2641_);
lean_inc(v_array_2640_);
lean_dec(v_a_2638_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2655_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
uint8_t v___x_2646_; 
v___x_2646_ = lean_nat_dec_lt(v_start_2641_, v_stop_2642_);
if (v___x_2646_ == 0)
{
lean_del_object(v___x_2644_);
lean_dec(v_stop_2642_);
lean_dec(v_start_2641_);
lean_dec_ref(v_array_2640_);
return v_b_2639_;
}
else
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2650_; 
v___x_2647_ = lean_unsigned_to_nat(1u);
v___x_2648_ = lean_nat_add(v_start_2641_, v___x_2647_);
lean_inc_ref(v_array_2640_);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 1, v___x_2648_);
v___x_2650_ = v___x_2644_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_array_2640_);
lean_ctor_set(v_reuseFailAlloc_2654_, 1, v___x_2648_);
lean_ctor_set(v_reuseFailAlloc_2654_, 2, v_stop_2642_);
v___x_2650_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = lean_array_fget(v_array_2640_, v_start_2641_);
lean_dec(v_start_2641_);
lean_dec_ref(v_array_2640_);
v___x_2652_ = lean_array_push(v_b_2639_, v___x_2651_);
v_a_2638_ = v___x_2650_;
v_b_2639_ = v___x_2652_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(lean_object* v_as_2656_, size_t v_sz_2657_, size_t v_i_2658_, lean_object* v_b_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
uint8_t v___x_2665_; 
v___x_2665_ = lean_usize_dec_lt(v_i_2658_, v_sz_2657_);
if (v___x_2665_ == 0)
{
lean_object* v___x_2666_; 
v___x_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2666_, 0, v_b_2659_);
return v___x_2666_;
}
else
{
lean_object* v_snd_2667_; lean_object* v_fst_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2720_; 
v_snd_2667_ = lean_ctor_get(v_b_2659_, 1);
v_fst_2668_ = lean_ctor_get(v_b_2659_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v_b_2659_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2670_ = v_b_2659_;
v_isShared_2671_ = v_isSharedCheck_2720_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_snd_2667_);
lean_inc(v_fst_2668_);
lean_dec(v_b_2659_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2720_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v_array_2672_; lean_object* v_start_2673_; lean_object* v_stop_2674_; uint8_t v___x_2675_; 
v_array_2672_ = lean_ctor_get(v_snd_2667_, 0);
v_start_2673_ = lean_ctor_get(v_snd_2667_, 1);
v_stop_2674_ = lean_ctor_get(v_snd_2667_, 2);
v___x_2675_ = lean_nat_dec_lt(v_start_2673_, v_stop_2674_);
if (v___x_2675_ == 0)
{
lean_object* v___x_2677_; 
if (v_isShared_2671_ == 0)
{
v___x_2677_ = v___x_2670_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_fst_2668_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v_snd_2667_);
v___x_2677_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
lean_object* v___x_2678_; 
v___x_2678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2677_);
return v___x_2678_;
}
}
else
{
lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2716_; 
lean_inc(v_stop_2674_);
lean_inc(v_start_2673_);
lean_inc_ref(v_array_2672_);
v_isSharedCheck_2716_ = !lean_is_exclusive(v_snd_2667_);
if (v_isSharedCheck_2716_ == 0)
{
lean_object* v_unused_2717_; lean_object* v_unused_2718_; lean_object* v_unused_2719_; 
v_unused_2717_ = lean_ctor_get(v_snd_2667_, 2);
lean_dec(v_unused_2717_);
v_unused_2718_ = lean_ctor_get(v_snd_2667_, 1);
lean_dec(v_unused_2718_);
v_unused_2719_ = lean_ctor_get(v_snd_2667_, 0);
lean_dec(v_unused_2719_);
v___x_2681_ = v_snd_2667_;
v_isShared_2682_ = v_isSharedCheck_2716_;
goto v_resetjp_2680_;
}
else
{
lean_dec(v_snd_2667_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2716_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v_a_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2688_; 
v_a_2683_ = lean_array_uget_borrowed(v_as_2656_, v_i_2658_);
v___x_2684_ = lean_array_fget(v_array_2672_, v_start_2673_);
v___x_2685_ = lean_unsigned_to_nat(1u);
v___x_2686_ = lean_nat_add(v_start_2673_, v___x_2685_);
lean_dec(v_start_2673_);
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 1, v___x_2686_);
v___x_2688_ = v___x_2681_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_array_2672_);
lean_ctor_set(v_reuseFailAlloc_2715_, 1, v___x_2686_);
lean_ctor_set(v_reuseFailAlloc_2715_, 2, v_stop_2674_);
v___x_2688_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
lean_object* v___x_2689_; 
lean_inc(v_a_2683_);
v___x_2689_ = l_Lean_Meta_mkEqHEq(v_a_2683_, v___x_2684_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; lean_object* v___x_2691_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2690_);
lean_dec_ref_known(v___x_2689_, 1);
v___x_2691_ = l_Lean_mkArrow(v_a_2690_, v_fst_2668_, v___y_2662_, v___y_2663_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; lean_object* v___x_2694_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2692_);
lean_dec_ref_known(v___x_2691_, 1);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 1, v___x_2688_);
lean_ctor_set(v___x_2670_, 0, v_a_2692_);
v___x_2694_ = v___x_2670_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v___x_2688_);
v___x_2694_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
size_t v___x_2695_; size_t v___x_2696_; 
v___x_2695_ = ((size_t)1ULL);
v___x_2696_ = lean_usize_add(v_i_2658_, v___x_2695_);
v_i_2658_ = v___x_2696_;
v_b_2659_ = v___x_2694_;
goto _start;
}
}
else
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
lean_dec_ref(v___x_2688_);
lean_del_object(v___x_2670_);
v_a_2699_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2691_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2691_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2702_ == 0)
{
v___x_2704_ = v___x_2701_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_a_2699_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
lean_dec_ref(v___x_2688_);
lean_del_object(v___x_2670_);
lean_dec(v_fst_2668_);
v_a_2707_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2689_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2689_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7___boxed(lean_object* v_as_2721_, lean_object* v_sz_2722_, lean_object* v_i_2723_, lean_object* v_b_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
size_t v_sz_boxed_2730_; size_t v_i_boxed_2731_; lean_object* v_res_2732_; 
v_sz_boxed_2730_ = lean_unbox_usize(v_sz_2722_);
lean_dec(v_sz_2722_);
v_i_boxed_2731_ = lean_unbox_usize(v_i_2723_);
lean_dec(v_i_2723_);
v_res_2732_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v_as_2721_, v_sz_boxed_2730_, v_i_boxed_2731_, v_b_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec_ref(v_as_2721_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(lean_object* v___x_2733_, lean_object* v___x_2734_, lean_object* v_as_2735_, size_t v_sz_2736_, size_t v_i_2737_, lean_object* v_b_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v_a_2745_; uint8_t v___x_2749_; 
v___x_2749_ = lean_usize_dec_lt(v_i_2737_, v_sz_2736_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; 
v___x_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2750_, 0, v_b_2738_);
return v___x_2750_;
}
else
{
lean_object* v___x_2751_; lean_object* v_a_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2751_ = l_Lean_instInhabitedExpr;
v_a_2752_ = lean_array_uget_borrowed(v_as_2735_, v_i_2737_);
v___x_2753_ = lean_array_get_borrowed(v___x_2751_, v___x_2733_, v_a_2752_);
lean_inc(v___x_2753_);
v___x_2754_ = l_Lean_Meta_instantiateForall(v___x_2753_, v___x_2734_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_a_2755_);
lean_dec_ref_known(v___x_2754_, 1);
v___x_2756_ = lean_array_get_size(v___x_2734_);
v___x_2757_ = l_Lean_Meta_Match_simpH_x3f(v_a_2755_, v___x_2756_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2758_; 
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
lean_inc(v_a_2758_);
lean_dec_ref_known(v___x_2757_, 1);
if (lean_obj_tag(v_a_2758_) == 1)
{
lean_object* v_val_2759_; lean_object* v___x_2760_; 
v_val_2759_ = lean_ctor_get(v_a_2758_, 0);
lean_inc(v_val_2759_);
lean_dec_ref_known(v_a_2758_, 1);
v___x_2760_ = lean_array_push(v_b_2738_, v_val_2759_);
v_a_2745_ = v___x_2760_;
goto v___jp_2744_;
}
else
{
lean_dec(v_a_2758_);
v_a_2745_ = v_b_2738_;
goto v___jp_2744_;
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
lean_dec_ref(v_b_2738_);
v_a_2761_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2757_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2757_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
lean_dec_ref(v_b_2738_);
v_a_2769_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2754_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2754_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
v___jp_2744_:
{
size_t v___x_2746_; size_t v___x_2747_; 
v___x_2746_ = ((size_t)1ULL);
v___x_2747_ = lean_usize_add(v_i_2737_, v___x_2746_);
v_i_2737_ = v___x_2747_;
v_b_2738_ = v_a_2745_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5___boxed(lean_object* v___x_2777_, lean_object* v___x_2778_, lean_object* v_as_2779_, lean_object* v_sz_2780_, lean_object* v_i_2781_, lean_object* v_b_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
size_t v_sz_boxed_2788_; size_t v_i_boxed_2789_; lean_object* v_res_2790_; 
v_sz_boxed_2788_ = lean_unbox_usize(v_sz_2780_);
lean_dec(v_sz_2780_);
v_i_boxed_2789_ = lean_unbox_usize(v_i_2781_);
lean_dec(v_i_2781_);
v_res_2790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(v___x_2777_, v___x_2778_, v_as_2779_, v_sz_boxed_2788_, v_i_boxed_2789_, v_b_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec_ref(v_as_2779_);
lean_dec_ref(v___x_2778_);
lean_dec_ref(v___x_2777_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(lean_object* v___x_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v___x_2794_, lean_object* v___x_2795_, lean_object* v___x_2796_, lean_object* v___x_2797_, lean_object* v___x_2798_, lean_object* v_rhsArgs_2799_, lean_object* v_a_2800_, lean_object* v_ys_2801_, uint8_t v___x_2802_, uint8_t v___x_2803_, uint8_t v___x_2804_, lean_object* v_matchDeclName_2805_, lean_object* v___x_2806_, lean_object* v___x_2807_, lean_object* v___x_2808_, lean_object* v___x_2809_, lean_object* v___x_2810_, lean_object* v_argMask_2811_, lean_object* v_a_2812_, lean_object* v_alts_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2819_ = lean_array_get_borrowed(v___x_2791_, v_alts_2813_, v_a_2792_);
v___x_2820_ = l_Lean_ConstantInfo_name(v_a_2793_);
v___x_2821_ = l_Lean_mkConst(v___x_2820_, v___x_2794_);
v___x_2822_ = l_Subarray_copy___redArg(v___x_2795_);
v___x_2823_ = lean_mk_empty_array_with_capacity(v___x_2796_);
v___x_2824_ = lean_array_push(v___x_2823_, v___x_2797_);
v___x_2825_ = l_Array_append___redArg(v___x_2822_, v___x_2824_);
lean_dec_ref(v___x_2824_);
lean_inc_ref(v___x_2825_);
v___x_2826_ = l_Array_append___redArg(v___x_2825_, v___x_2798_);
v___x_2827_ = l_Array_append___redArg(v___x_2826_, v_alts_2813_);
v___x_2828_ = l_Lean_mkAppN(v___x_2821_, v___x_2827_);
lean_dec_ref(v___x_2827_);
lean_inc(v___x_2819_);
v___x_2829_ = l_Lean_mkAppN(v___x_2819_, v_rhsArgs_2799_);
v___x_2830_ = l_Lean_Meta_mkEq(v___x_2828_, v___x_2829_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v___x_2832_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2830_, 1);
v___x_2832_ = l_Lean_mkArrowN(v_a_2800_, v_a_2831_, v___y_2816_, v___y_2817_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v_a_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_a_2833_);
lean_dec_ref_known(v___x_2832_, 1);
v___x_2834_ = l_Array_append___redArg(v___x_2825_, v_ys_2801_);
v___x_2835_ = l_Array_append___redArg(v___x_2834_, v_alts_2813_);
v___x_2836_ = l_Lean_Meta_mkForallFVars(v___x_2835_, v_a_2833_, v___x_2802_, v___x_2803_, v___x_2803_, v___x_2804_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
lean_dec_ref(v___x_2835_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2837_; lean_object* v___x_2838_; 
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_a_2837_);
lean_dec_ref_known(v___x_2836_, 1);
v___x_2838_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_2837_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2840_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc_n(v_a_2839_, 2);
lean_dec_ref_known(v___x_2838_, 1);
lean_inc(v___x_2806_);
v___x_2840_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_2805_, v_a_2839_, v___x_2806_, v___x_2806_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
lean_inc(v_a_2841_);
lean_dec_ref_known(v___x_2840_, 1);
lean_inc(v___x_2807_);
v___x_2842_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2807_);
lean_ctor_set(v___x_2842_, 1, v___x_2808_);
lean_ctor_set(v___x_2842_, 2, v_a_2839_);
v___x_2843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2807_);
lean_ctor_set(v___x_2843_, 1, v___x_2809_);
v___x_2844_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2842_);
lean_ctor_set(v___x_2844_, 1, v_a_2841_);
lean_ctor_set(v___x_2844_, 2, v___x_2843_);
v___x_2845_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2844_);
v___x_2846_ = l_Lean_addDecl(v___x_2845_, v___x_2802_, v___y_2816_, v___y_2817_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2855_; 
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2855_ == 0)
{
lean_object* v_unused_2856_; 
v_unused_2856_ = lean_ctor_get(v___x_2846_, 0);
lean_dec(v_unused_2856_);
v___x_2848_ = v___x_2846_;
v_isShared_2849_ = v_isSharedCheck_2855_;
goto v_resetjp_2847_;
}
else
{
lean_dec(v___x_2846_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2855_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2853_; 
v___x_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2810_);
lean_ctor_set(v___x_2850_, 1, v_argMask_2811_);
v___x_2851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2851_, 0, v_a_2812_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
if (v_isShared_2849_ == 0)
{
lean_ctor_set(v___x_2848_, 0, v___x_2851_);
v___x_2853_ = v___x_2848_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v___x_2851_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_dec_ref(v_a_2812_);
lean_dec_ref(v_argMask_2811_);
lean_dec_ref(v___x_2810_);
v_a_2857_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2846_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2846_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
lean_dec(v_a_2839_);
lean_dec_ref(v_a_2812_);
lean_dec_ref(v_argMask_2811_);
lean_dec_ref(v___x_2810_);
lean_dec(v___x_2809_);
lean_dec(v___x_2808_);
lean_dec(v___x_2807_);
v_a_2865_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2840_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2840_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2880_; 
lean_dec_ref(v_a_2812_);
lean_dec_ref(v_argMask_2811_);
lean_dec_ref(v___x_2810_);
lean_dec(v___x_2809_);
lean_dec(v___x_2808_);
lean_dec(v___x_2807_);
lean_dec(v___x_2806_);
lean_dec(v_matchDeclName_2805_);
v_a_2873_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2838_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2838_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2878_; 
if (v_isShared_2876_ == 0)
{
v___x_2878_ = v___x_2875_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2873_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
else
{
lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2888_; 
lean_dec_ref(v_a_2812_);
lean_dec_ref(v_argMask_2811_);
lean_dec_ref(v___x_2810_);
lean_dec(v___x_2809_);
lean_dec(v___x_2808_);
lean_dec(v___x_2807_);
lean_dec(v___x_2806_);
lean_dec(v_matchDeclName_2805_);
v_a_2881_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2883_ = v___x_2836_;
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v___x_2836_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2886_; 
if (v_isShared_2884_ == 0)
{
v___x_2886_ = v___x_2883_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2881_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
else
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
lean_dec_ref(v___x_2825_);
lean_dec_ref(v_a_2812_);
lean_dec_ref(v_argMask_2811_);
lean_dec_ref(v___x_2810_);
lean_dec(v___x_2809_);
lean_dec(v___x_2808_);
lean_dec(v___x_2807_);
lean_dec(v___x_2806_);
lean_dec(v_matchDeclName_2805_);
v_a_2889_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2832_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2832_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2889_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
lean_dec_ref(v___x_2825_);
lean_dec_ref(v_a_2812_);
lean_dec_ref(v_argMask_2811_);
lean_dec_ref(v___x_2810_);
lean_dec(v___x_2809_);
lean_dec(v___x_2808_);
lean_dec(v___x_2807_);
lean_dec(v___x_2806_);
lean_dec(v_matchDeclName_2805_);
v_a_2897_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2830_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2830_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_2905_ = _args[0];
lean_object* v_a_2906_ = _args[1];
lean_object* v_a_2907_ = _args[2];
lean_object* v___x_2908_ = _args[3];
lean_object* v___x_2909_ = _args[4];
lean_object* v___x_2910_ = _args[5];
lean_object* v___x_2911_ = _args[6];
lean_object* v___x_2912_ = _args[7];
lean_object* v_rhsArgs_2913_ = _args[8];
lean_object* v_a_2914_ = _args[9];
lean_object* v_ys_2915_ = _args[10];
lean_object* v___x_2916_ = _args[11];
lean_object* v___x_2917_ = _args[12];
lean_object* v___x_2918_ = _args[13];
lean_object* v_matchDeclName_2919_ = _args[14];
lean_object* v___x_2920_ = _args[15];
lean_object* v___x_2921_ = _args[16];
lean_object* v___x_2922_ = _args[17];
lean_object* v___x_2923_ = _args[18];
lean_object* v___x_2924_ = _args[19];
lean_object* v_argMask_2925_ = _args[20];
lean_object* v_a_2926_ = _args[21];
lean_object* v_alts_2927_ = _args[22];
lean_object* v___y_2928_ = _args[23];
lean_object* v___y_2929_ = _args[24];
lean_object* v___y_2930_ = _args[25];
lean_object* v___y_2931_ = _args[26];
lean_object* v___y_2932_ = _args[27];
_start:
{
uint8_t v___x_18496__boxed_2933_; uint8_t v___x_18497__boxed_2934_; uint8_t v___x_18498__boxed_2935_; lean_object* v_res_2936_; 
v___x_18496__boxed_2933_ = lean_unbox(v___x_2916_);
v___x_18497__boxed_2934_ = lean_unbox(v___x_2917_);
v___x_18498__boxed_2935_ = lean_unbox(v___x_2918_);
v_res_2936_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0(v___x_2905_, v_a_2906_, v_a_2907_, v___x_2908_, v___x_2909_, v___x_2910_, v___x_2911_, v___x_2912_, v_rhsArgs_2913_, v_a_2914_, v_ys_2915_, v___x_18496__boxed_2933_, v___x_18497__boxed_2934_, v___x_18498__boxed_2935_, v_matchDeclName_2919_, v___x_2920_, v___x_2921_, v___x_2922_, v___x_2923_, v___x_2924_, v_argMask_2925_, v_a_2926_, v_alts_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec_ref(v_alts_2927_);
lean_dec_ref(v_ys_2915_);
lean_dec_ref(v_a_2914_);
lean_dec_ref(v_rhsArgs_2913_);
lean_dec_ref(v___x_2912_);
lean_dec(v___x_2910_);
lean_dec_ref(v_a_2907_);
lean_dec(v_a_2906_);
lean_dec_ref(v___x_2905_);
return v_res_2936_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2937_; lean_object* v_dummy_2938_; 
v___x_2937_ = lean_box(0);
v_dummy_2938_ = l_Lean_Expr_sort___override(v___x_2937_);
return v_dummy_2938_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2942_ = lean_box(0);
v___x_2943_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__2));
v___x_2944_ = l_Lean_mkConst(v___x_2943_, v___x_2942_);
return v___x_2944_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2946_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__4));
v___x_2947_ = l_Lean_stringToMessageData(v___x_2946_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(lean_object* v___x_2948_, lean_object* v_overlaps_2949_, lean_object* v_a_2950_, lean_object* v_fst_2951_, lean_object* v___x_2952_, lean_object* v___x_2953_, lean_object* v___x_2954_, uint8_t v___x_2955_, lean_object* v___x_2956_, lean_object* v_a_2957_, lean_object* v___x_2958_, lean_object* v___x_2959_, lean_object* v___x_2960_, lean_object* v_matchDeclName_2961_, lean_object* v___x_2962_, lean_object* v___x_2963_, lean_object* v___x_2964_, lean_object* v___x_2965_, lean_object* v___x_2966_, lean_object* v_ys_2967_, lean_object* v___eqs_2968_, lean_object* v_rhsArgs_2969_, lean_object* v_argMask_2970_, lean_object* v_altResultType_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
lean_object* v_dummy_2977_; lean_object* v_nargs_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; size_t v_sz_2983_; size_t v___x_2984_; lean_object* v___x_2985_; 
v_dummy_2977_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_2978_ = l_Lean_Expr_getAppNumArgs(v_altResultType_2971_);
lean_inc(v_nargs_2978_);
v___x_2979_ = lean_mk_array(v_nargs_2978_, v_dummy_2977_);
v___x_2980_ = lean_nat_sub(v_nargs_2978_, v___x_2948_);
lean_dec(v_nargs_2978_);
v___x_2981_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_altResultType_2971_, v___x_2979_, v___x_2980_);
v___x_2982_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_2949_, v_a_2950_);
v_sz_2983_ = lean_array_size(v___x_2982_);
v___x_2984_ = ((size_t)0ULL);
lean_inc_ref(v___x_2952_);
v___x_2985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__5(v_fst_2951_, v___x_2981_, v___x_2982_, v_sz_2983_, v___x_2984_, v___x_2952_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_);
lean_dec_ref(v___x_2982_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; uint8_t v___y_2992_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v_toCold_3045_; lean_object* v_options_3046_; uint8_t v_hasTrace_3047_; 
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_a_2986_);
lean_dec_ref_known(v___x_2985_, 1);
v_toCold_3045_ = lean_ctor_get(v___y_2974_, 0);
v_options_3046_ = lean_ctor_get(v_toCold_3045_, 2);
v_hasTrace_3047_ = lean_ctor_get_uint8(v_options_3046_, sizeof(void*)*1);
if (v_hasTrace_3047_ == 0)
{
v___y_3036_ = v___y_2972_;
v___y_3037_ = v___y_2973_;
v___y_3038_ = v___y_2974_;
v___y_3039_ = v___y_2975_;
goto v___jp_3035_;
}
else
{
lean_object* v_inheritedTraceOptions_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; uint8_t v___x_3051_; 
v_inheritedTraceOptions_3048_ = lean_ctor_get(v_toCold_3045_, 11);
v___x_3049_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_3050_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_3051_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3048_, v_options_3046_, v___x_3050_);
if (v___x_3051_ == 0)
{
v___y_3036_ = v___y_2972_;
v___y_3037_ = v___y_2973_;
v___y_3038_ = v___y_2974_;
v___y_3039_ = v___y_2975_;
goto v___jp_3035_;
}
else
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3052_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_2986_);
v___x_3053_ = lean_array_to_list(v_a_2986_);
v___x_3054_ = lean_box(0);
v___x_3055_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_3053_, v___x_3054_);
v___x_3056_ = l_Lean_MessageData_ofList(v___x_3055_);
v___x_3057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3052_);
lean_ctor_set(v___x_3057_, 1, v___x_3056_);
v___x_3058_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_3049_, v___x_3057_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_dec_ref_known(v___x_3058_, 1);
v___y_3036_ = v___y_2972_;
v___y_3037_ = v___y_2973_;
v___y_3038_ = v___y_2974_;
v___y_3039_ = v___y_2975_;
goto v___jp_3035_;
}
else
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3066_; 
lean_dec(v_a_2986_);
lean_dec_ref(v___x_2981_);
lean_dec_ref(v_argMask_2970_);
lean_dec_ref(v_rhsArgs_2969_);
lean_dec_ref(v_ys_2967_);
lean_dec_ref(v___x_2965_);
lean_dec(v___x_2964_);
lean_dec(v___x_2963_);
lean_dec(v___x_2962_);
lean_dec(v_matchDeclName_2961_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v___x_2959_);
lean_dec(v___x_2958_);
lean_dec_ref(v_a_2957_);
lean_dec_ref(v___x_2956_);
lean_dec_ref(v___x_2954_);
lean_dec(v___x_2953_);
lean_dec_ref(v___x_2952_);
lean_dec(v_a_2950_);
lean_dec(v___x_2948_);
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3061_ = v___x_3058_;
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3058_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3066_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3064_; 
if (v_isShared_3062_ == 0)
{
v___x_3064_ = v___x_3061_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_a_3059_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
}
v___jp_2987_:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; size_t v_sz_3003_; lean_object* v___x_3004_; 
v___x_2993_ = lean_array_get_size(v_ys_2967_);
v___x_2994_ = lean_array_get_size(v_a_2986_);
v___x_2995_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2995_, 0, v___x_2993_);
lean_ctor_set(v___x_2995_, 1, v___x_2994_);
lean_ctor_set_uint8(v___x_2995_, sizeof(void*)*2, v___y_2992_);
v___x_2996_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
lean_inc_ref(v___x_2981_);
v___x_2997_ = l_Array_reverse___redArg(v___x_2981_);
v___x_2998_ = lean_array_get_size(v___x_2997_);
lean_inc(v___x_2953_);
v___x_2999_ = l_Array_toSubarray___redArg(v___x_2997_, v___x_2953_, v___x_2998_);
lean_inc_ref(v___x_2954_);
v___x_3000_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_2954_, v___x_2952_);
v___x_3001_ = l_Array_reverse___redArg(v___x_3000_);
v___x_3002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3002_, 0, v___x_2996_);
lean_ctor_set(v___x_3002_, 1, v___x_2999_);
v_sz_3003_ = lean_array_size(v___x_3001_);
v___x_3004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_3001_, v_sz_3003_, v___x_2984_, v___x_3002_, v___y_2991_, v___y_2990_, v___y_2988_, v___y_2989_);
lean_dec_ref(v___x_3001_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v_fst_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; uint8_t v___x_3010_; lean_object* v___x_3011_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref_known(v___x_3004_, 1);
v_fst_3006_ = lean_ctor_get(v_a_3005_, 0);
lean_inc(v_fst_3006_);
lean_dec(v_a_3005_);
v___x_3007_ = l_Subarray_copy___redArg(v___x_2954_);
lean_inc_ref(v___x_3007_);
v___x_3008_ = l_Array_append___redArg(v___x_3007_, v_ys_2967_);
v___x_3009_ = 0;
v___x_3010_ = 1;
v___x_3011_ = l_Lean_Meta_mkForallFVars(v___x_3008_, v_fst_3006_, v___x_3009_, v___x_2955_, v___x_2955_, v___x_3010_, v___y_2991_, v___y_2990_, v___y_2988_, v___y_2989_);
lean_dec_ref(v___x_3008_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___f_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_a_3012_);
lean_dec_ref_known(v___x_3011_, 1);
v___x_3013_ = lean_box(v___x_3009_);
v___x_3014_ = lean_box(v___x_2955_);
v___x_3015_ = lean_box(v___x_3010_);
lean_inc_ref(v___x_2981_);
v___f_3016_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__0___boxed), 28, 22);
lean_closure_set(v___f_3016_, 0, v___x_2956_);
lean_closure_set(v___f_3016_, 1, v_a_2950_);
lean_closure_set(v___f_3016_, 2, v_a_2957_);
lean_closure_set(v___f_3016_, 3, v___x_2958_);
lean_closure_set(v___f_3016_, 4, v___x_2959_);
lean_closure_set(v___f_3016_, 5, v___x_2948_);
lean_closure_set(v___f_3016_, 6, v___x_2960_);
lean_closure_set(v___f_3016_, 7, v___x_2981_);
lean_closure_set(v___f_3016_, 8, v_rhsArgs_2969_);
lean_closure_set(v___f_3016_, 9, v_a_2986_);
lean_closure_set(v___f_3016_, 10, v_ys_2967_);
lean_closure_set(v___f_3016_, 11, v___x_3013_);
lean_closure_set(v___f_3016_, 12, v___x_3014_);
lean_closure_set(v___f_3016_, 13, v___x_3015_);
lean_closure_set(v___f_3016_, 14, v_matchDeclName_2961_);
lean_closure_set(v___f_3016_, 15, v___x_2953_);
lean_closure_set(v___f_3016_, 16, v___x_2962_);
lean_closure_set(v___f_3016_, 17, v___x_2963_);
lean_closure_set(v___f_3016_, 18, v___x_2964_);
lean_closure_set(v___f_3016_, 19, v___x_2995_);
lean_closure_set(v___f_3016_, 20, v_argMask_2970_);
lean_closure_set(v___f_3016_, 21, v_a_3012_);
v___x_3017_ = l_Subarray_copy___redArg(v___x_2965_);
v___x_3018_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg(v___x_2966_, v___x_3007_, v___x_2981_, v___x_3017_, v___f_3016_, v___y_2991_, v___y_2990_, v___y_2988_, v___y_2989_);
return v___x_3018_;
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec_ref(v___x_3007_);
lean_dec_ref_known(v___x_2995_, 2);
lean_dec(v_a_2986_);
lean_dec_ref(v___x_2981_);
lean_dec_ref(v_argMask_2970_);
lean_dec_ref(v_rhsArgs_2969_);
lean_dec_ref(v_ys_2967_);
lean_dec_ref(v___x_2965_);
lean_dec(v___x_2964_);
lean_dec(v___x_2963_);
lean_dec(v___x_2962_);
lean_dec(v_matchDeclName_2961_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v___x_2959_);
lean_dec(v___x_2958_);
lean_dec_ref(v_a_2957_);
lean_dec_ref(v___x_2956_);
lean_dec(v___x_2953_);
lean_dec(v_a_2950_);
lean_dec(v___x_2948_);
v_a_3019_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_3011_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3011_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec_ref_known(v___x_2995_, 2);
lean_dec(v_a_2986_);
lean_dec_ref(v___x_2981_);
lean_dec_ref(v_argMask_2970_);
lean_dec_ref(v_rhsArgs_2969_);
lean_dec_ref(v_ys_2967_);
lean_dec_ref(v___x_2965_);
lean_dec(v___x_2964_);
lean_dec(v___x_2963_);
lean_dec(v___x_2962_);
lean_dec(v_matchDeclName_2961_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v___x_2959_);
lean_dec(v___x_2958_);
lean_dec_ref(v_a_2957_);
lean_dec_ref(v___x_2956_);
lean_dec_ref(v___x_2954_);
lean_dec(v___x_2953_);
lean_dec(v_a_2950_);
lean_dec(v___x_2948_);
v_a_3027_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_3004_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3004_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
v___jp_3035_:
{
lean_object* v___x_3040_; uint8_t v___x_3041_; 
v___x_3040_ = lean_array_get_size(v_ys_2967_);
v___x_3041_ = lean_nat_dec_eq(v___x_3040_, v___x_2953_);
if (v___x_3041_ == 0)
{
v___y_2988_ = v___y_3038_;
v___y_2989_ = v___y_3039_;
v___y_2990_ = v___y_3037_;
v___y_2991_ = v___y_3036_;
v___y_2992_ = v___x_3041_;
goto v___jp_2987_;
}
else
{
lean_object* v___x_3042_; uint8_t v___x_3043_; 
v___x_3042_ = lean_array_get_size(v_a_2986_);
v___x_3043_ = lean_nat_dec_eq(v___x_3042_, v___x_2953_);
if (v___x_3043_ == 0)
{
v___y_2988_ = v___y_3038_;
v___y_2989_ = v___y_3039_;
v___y_2990_ = v___y_3037_;
v___y_2991_ = v___y_3036_;
v___y_2992_ = v___x_3043_;
goto v___jp_2987_;
}
else
{
uint8_t v___x_3044_; 
v___x_3044_ = lean_nat_dec_eq(v___x_2966_, v___x_2953_);
v___y_2988_ = v___y_3038_;
v___y_2989_ = v___y_3039_;
v___y_2990_ = v___y_3037_;
v___y_2991_ = v___y_3036_;
v___y_2992_ = v___x_3044_;
goto v___jp_2987_;
}
}
}
}
else
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
lean_dec_ref(v___x_2981_);
lean_dec_ref(v_argMask_2970_);
lean_dec_ref(v_rhsArgs_2969_);
lean_dec_ref(v_ys_2967_);
lean_dec_ref(v___x_2965_);
lean_dec(v___x_2964_);
lean_dec(v___x_2963_);
lean_dec(v___x_2962_);
lean_dec(v_matchDeclName_2961_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v___x_2959_);
lean_dec(v___x_2958_);
lean_dec_ref(v_a_2957_);
lean_dec_ref(v___x_2956_);
lean_dec_ref(v___x_2954_);
lean_dec(v___x_2953_);
lean_dec_ref(v___x_2952_);
lean_dec(v_a_2950_);
lean_dec(v___x_2948_);
v_a_3067_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_2985_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_2985_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_3075_ = _args[0];
lean_object* v_overlaps_3076_ = _args[1];
lean_object* v_a_3077_ = _args[2];
lean_object* v_fst_3078_ = _args[3];
lean_object* v___x_3079_ = _args[4];
lean_object* v___x_3080_ = _args[5];
lean_object* v___x_3081_ = _args[6];
lean_object* v___x_3082_ = _args[7];
lean_object* v___x_3083_ = _args[8];
lean_object* v_a_3084_ = _args[9];
lean_object* v___x_3085_ = _args[10];
lean_object* v___x_3086_ = _args[11];
lean_object* v___x_3087_ = _args[12];
lean_object* v_matchDeclName_3088_ = _args[13];
lean_object* v___x_3089_ = _args[14];
lean_object* v___x_3090_ = _args[15];
lean_object* v___x_3091_ = _args[16];
lean_object* v___x_3092_ = _args[17];
lean_object* v___x_3093_ = _args[18];
lean_object* v_ys_3094_ = _args[19];
lean_object* v___eqs_3095_ = _args[20];
lean_object* v_rhsArgs_3096_ = _args[21];
lean_object* v_argMask_3097_ = _args[22];
lean_object* v_altResultType_3098_ = _args[23];
lean_object* v___y_3099_ = _args[24];
lean_object* v___y_3100_ = _args[25];
lean_object* v___y_3101_ = _args[26];
lean_object* v___y_3102_ = _args[27];
lean_object* v___y_3103_ = _args[28];
_start:
{
uint8_t v___x_18764__boxed_3104_; lean_object* v_res_3105_; 
v___x_18764__boxed_3104_ = lean_unbox(v___x_3082_);
v_res_3105_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1(v___x_3075_, v_overlaps_3076_, v_a_3077_, v_fst_3078_, v___x_3079_, v___x_3080_, v___x_3081_, v___x_18764__boxed_3104_, v___x_3083_, v_a_3084_, v___x_3085_, v___x_3086_, v___x_3087_, v_matchDeclName_3088_, v___x_3089_, v___x_3090_, v___x_3091_, v___x_3092_, v___x_3093_, v_ys_3094_, v___eqs_3095_, v_rhsArgs_3096_, v_argMask_3097_, v_altResultType_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec_ref(v___eqs_3095_);
lean_dec(v___x_3093_);
lean_dec(v_fst_3078_);
lean_dec_ref(v_overlaps_3076_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(lean_object* v_upperBound_3106_, lean_object* v_val_3107_, lean_object* v_baseName_3108_, lean_object* v___x_3109_, lean_object* v_a_3110_, lean_object* v___x_3111_, lean_object* v___x_3112_, lean_object* v___x_3113_, lean_object* v_matchDeclName_3114_, lean_object* v___x_3115_, lean_object* v___x_3116_, lean_object* v___x_3117_, lean_object* v_a_3118_, lean_object* v_b_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
uint8_t v___x_3125_; 
v___x_3125_ = lean_nat_dec_lt(v_a_3118_, v_upperBound_3106_);
if (v___x_3125_ == 0)
{
lean_object* v___x_3126_; 
lean_dec(v_a_3118_);
lean_dec(v___x_3117_);
lean_dec_ref(v___x_3116_);
lean_dec(v___x_3115_);
lean_dec(v_matchDeclName_3114_);
lean_dec_ref(v___x_3113_);
lean_dec_ref(v___x_3112_);
lean_dec(v___x_3111_);
lean_dec_ref(v_a_3110_);
lean_dec_ref(v___x_3109_);
lean_dec(v_baseName_3108_);
lean_dec_ref(v_val_3107_);
v___x_3126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3126_, 0, v_b_3119_);
return v___x_3126_;
}
else
{
lean_object* v_snd_3127_; lean_object* v_snd_3128_; lean_object* v_snd_3129_; lean_object* v_fst_3130_; lean_object* v_fst_3131_; lean_object* v_fst_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3215_; 
v_snd_3127_ = lean_ctor_get(v_b_3119_, 1);
lean_inc(v_snd_3127_);
v_snd_3128_ = lean_ctor_get(v_snd_3127_, 1);
lean_inc(v_snd_3128_);
v_snd_3129_ = lean_ctor_get(v_snd_3128_, 1);
lean_inc(v_snd_3129_);
v_fst_3130_ = lean_ctor_get(v_b_3119_, 0);
lean_inc(v_fst_3130_);
lean_dec_ref(v_b_3119_);
v_fst_3131_ = lean_ctor_get(v_snd_3127_, 0);
lean_inc(v_fst_3131_);
lean_dec(v_snd_3127_);
v_fst_3132_ = lean_ctor_get(v_snd_3128_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v_snd_3128_);
if (v_isSharedCheck_3215_ == 0)
{
lean_object* v_unused_3216_; 
v_unused_3216_ = lean_ctor_get(v_snd_3128_, 1);
lean_dec(v_unused_3216_);
v___x_3134_ = v_snd_3128_;
v_isShared_3135_ = v_isSharedCheck_3215_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_fst_3132_);
lean_dec(v_snd_3128_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3215_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v_fst_3136_; lean_object* v_snd_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3214_; 
v_fst_3136_ = lean_ctor_get(v_snd_3129_, 0);
v_snd_3137_ = lean_ctor_get(v_snd_3129_, 1);
v_isSharedCheck_3214_ = !lean_is_exclusive(v_snd_3129_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3139_ = v_snd_3129_;
v_isShared_3140_ = v_isSharedCheck_3214_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_snd_3137_);
lean_inc(v_fst_3136_);
lean_dec(v_snd_3129_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3214_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v_altInfos_3141_; lean_object* v_overlaps_3142_; lean_object* v_start_3143_; lean_object* v_stop_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___f_3156_; lean_object* v___x_3157_; lean_object* v___y_3159_; lean_object* v___x_3210_; uint8_t v___x_3211_; 
v_altInfos_3141_ = lean_ctor_get(v_val_3107_, 2);
v_overlaps_3142_ = lean_ctor_get(v_val_3107_, 5);
v_start_3143_ = lean_ctor_get(v___x_3116_, 1);
v_stop_3144_ = lean_ctor_get(v___x_3116_, 2);
v___x_3145_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_3146_ = l_Lean_instInhabitedExpr;
v___x_3147_ = lean_unsigned_to_nat(0u);
v___x_3148_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_3149_ = lean_box(0);
v___x_3150_ = lean_unsigned_to_nat(1u);
v___x_3151_ = lean_array_get_borrowed(v___x_3145_, v_altInfos_3141_, v_a_3118_);
v___x_3152_ = l_Lean_Meta_eqnThmSuffixBase;
lean_inc(v_baseName_3108_);
v___x_3153_ = l_Lean_Name_str___override(v_baseName_3108_, v___x_3152_);
lean_inc(v_fst_3132_);
v___x_3154_ = lean_name_append_index_after(v___x_3153_, v_fst_3132_);
v___x_3155_ = lean_box(v___x_3125_);
lean_inc(v___x_3117_);
lean_inc_ref(v___x_3116_);
lean_inc(v___x_3115_);
lean_inc(v___x_3154_);
lean_inc(v_matchDeclName_3114_);
lean_inc_ref(v___x_3113_);
lean_inc_ref(v___x_3112_);
lean_inc(v___x_3111_);
lean_inc_ref(v_a_3110_);
lean_inc_ref(v___x_3109_);
lean_inc(v_fst_3131_);
lean_inc(v_a_3118_);
lean_inc_ref(v_overlaps_3142_);
v___f_3156_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___boxed), 29, 19);
lean_closure_set(v___f_3156_, 0, v___x_3150_);
lean_closure_set(v___f_3156_, 1, v_overlaps_3142_);
lean_closure_set(v___f_3156_, 2, v_a_3118_);
lean_closure_set(v___f_3156_, 3, v_fst_3131_);
lean_closure_set(v___f_3156_, 4, v___x_3148_);
lean_closure_set(v___f_3156_, 5, v___x_3147_);
lean_closure_set(v___f_3156_, 6, v___x_3109_);
lean_closure_set(v___f_3156_, 7, v___x_3155_);
lean_closure_set(v___f_3156_, 8, v___x_3146_);
lean_closure_set(v___f_3156_, 9, v_a_3110_);
lean_closure_set(v___f_3156_, 10, v___x_3111_);
lean_closure_set(v___f_3156_, 11, v___x_3112_);
lean_closure_set(v___f_3156_, 12, v___x_3113_);
lean_closure_set(v___f_3156_, 13, v_matchDeclName_3114_);
lean_closure_set(v___f_3156_, 14, v___x_3154_);
lean_closure_set(v___f_3156_, 15, v___x_3115_);
lean_closure_set(v___f_3156_, 16, v___x_3149_);
lean_closure_set(v___f_3156_, 17, v___x_3116_);
lean_closure_set(v___f_3156_, 18, v___x_3117_);
v___x_3157_ = lean_array_push(v_fst_3130_, v___x_3154_);
v___x_3210_ = lean_nat_sub(v_stop_3144_, v_start_3143_);
v___x_3211_ = lean_nat_dec_lt(v_a_3118_, v___x_3210_);
lean_dec(v___x_3210_);
if (v___x_3211_ == 0)
{
lean_object* v___x_3212_; 
v___x_3212_ = l_outOfBounds___redArg(v___x_3146_);
v___y_3159_ = v___x_3212_;
goto v___jp_3158_;
}
else
{
lean_object* v___x_3213_; 
v___x_3213_ = l_Subarray_get___redArg(v___x_3116_, v_a_3118_);
v___y_3159_ = v___x_3213_;
goto v___jp_3158_;
}
v___jp_3158_:
{
lean_object* v___x_3160_; 
lean_inc(v___y_3123_);
lean_inc_ref(v___y_3122_);
lean_inc(v___y_3121_);
lean_inc_ref(v___y_3120_);
v___x_3160_ = lean_infer_type(v___y_3159_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_a_3161_; lean_object* v___x_3162_; 
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
lean_inc(v_a_3161_);
lean_dec_ref_known(v___x_3160_, 1);
lean_inc(v___x_3117_);
lean_inc(v___x_3151_);
v___x_3162_ = l_Lean_Meta_Match_forallAltTelescope___redArg(v_a_3161_, v___x_3151_, v___x_3117_, v___f_3156_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; lean_object* v_snd_3164_; lean_object* v_fst_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3193_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3163_);
lean_dec_ref_known(v___x_3162_, 1);
v_snd_3164_ = lean_ctor_get(v_a_3163_, 1);
v_fst_3165_ = lean_ctor_get(v_a_3163_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v_a_3163_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3167_ = v_a_3163_;
v_isShared_3168_ = v_isSharedCheck_3193_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_snd_3164_);
lean_inc(v_fst_3165_);
lean_dec(v_a_3163_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3193_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v_fst_3169_; lean_object* v_snd_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3192_; 
v_fst_3169_ = lean_ctor_get(v_snd_3164_, 0);
v_snd_3170_ = lean_ctor_get(v_snd_3164_, 1);
v_isSharedCheck_3192_ = !lean_is_exclusive(v_snd_3164_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3172_ = v_snd_3164_;
v_isShared_3173_ = v_isSharedCheck_3192_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_snd_3170_);
lean_inc(v_fst_3169_);
lean_dec(v_snd_3164_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3192_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3179_; 
v___x_3174_ = lean_array_push(v_fst_3131_, v_fst_3165_);
v___x_3175_ = lean_array_push(v_fst_3136_, v_fst_3169_);
v___x_3176_ = lean_array_push(v_snd_3137_, v_snd_3170_);
v___x_3177_ = lean_nat_add(v_fst_3132_, v___x_3150_);
lean_dec(v_fst_3132_);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 1, v___x_3176_);
lean_ctor_set(v___x_3172_, 0, v___x_3175_);
v___x_3179_ = v___x_3172_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3175_);
lean_ctor_set(v_reuseFailAlloc_3191_, 1, v___x_3176_);
v___x_3179_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
lean_object* v___x_3181_; 
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 1, v___x_3179_);
lean_ctor_set(v___x_3167_, 0, v___x_3177_);
v___x_3181_ = v___x_3167_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3177_);
lean_ctor_set(v_reuseFailAlloc_3190_, 1, v___x_3179_);
v___x_3181_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
lean_object* v___x_3183_; 
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 1, v___x_3181_);
lean_ctor_set(v___x_3139_, 0, v___x_3174_);
v___x_3183_ = v___x_3139_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v___x_3174_);
lean_ctor_set(v_reuseFailAlloc_3189_, 1, v___x_3181_);
v___x_3183_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
lean_object* v___x_3185_; 
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 1, v___x_3183_);
lean_ctor_set(v___x_3134_, 0, v___x_3157_);
v___x_3185_ = v___x_3134_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3157_);
lean_ctor_set(v_reuseFailAlloc_3188_, 1, v___x_3183_);
v___x_3185_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
lean_object* v___x_3186_; 
v___x_3186_ = lean_nat_add(v_a_3118_, v___x_3150_);
lean_dec(v_a_3118_);
v_a_3118_ = v___x_3186_;
v_b_3119_ = v___x_3185_;
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
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
lean_dec_ref(v___x_3157_);
lean_del_object(v___x_3139_);
lean_dec(v_snd_3137_);
lean_dec(v_fst_3136_);
lean_del_object(v___x_3134_);
lean_dec(v_fst_3132_);
lean_dec(v_fst_3131_);
lean_dec(v_a_3118_);
lean_dec(v___x_3117_);
lean_dec_ref(v___x_3116_);
lean_dec(v___x_3115_);
lean_dec(v_matchDeclName_3114_);
lean_dec_ref(v___x_3113_);
lean_dec_ref(v___x_3112_);
lean_dec(v___x_3111_);
lean_dec_ref(v_a_3110_);
lean_dec_ref(v___x_3109_);
lean_dec(v_baseName_3108_);
lean_dec_ref(v_val_3107_);
v_a_3194_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v___x_3162_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3162_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3194_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec_ref(v___x_3157_);
lean_dec_ref(v___f_3156_);
lean_del_object(v___x_3139_);
lean_dec(v_snd_3137_);
lean_dec(v_fst_3136_);
lean_del_object(v___x_3134_);
lean_dec(v_fst_3132_);
lean_dec(v_fst_3131_);
lean_dec(v_a_3118_);
lean_dec(v___x_3117_);
lean_dec_ref(v___x_3116_);
lean_dec(v___x_3115_);
lean_dec(v_matchDeclName_3114_);
lean_dec_ref(v___x_3113_);
lean_dec_ref(v___x_3112_);
lean_dec(v___x_3111_);
lean_dec_ref(v_a_3110_);
lean_dec_ref(v___x_3109_);
lean_dec(v_baseName_3108_);
lean_dec_ref(v_val_3107_);
v_a_3202_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3160_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3160_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
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
lean_object* v_upperBound_3217_ = _args[0];
lean_object* v_val_3218_ = _args[1];
lean_object* v_baseName_3219_ = _args[2];
lean_object* v___x_3220_ = _args[3];
lean_object* v_a_3221_ = _args[4];
lean_object* v___x_3222_ = _args[5];
lean_object* v___x_3223_ = _args[6];
lean_object* v___x_3224_ = _args[7];
lean_object* v_matchDeclName_3225_ = _args[8];
lean_object* v___x_3226_ = _args[9];
lean_object* v___x_3227_ = _args[10];
lean_object* v___x_3228_ = _args[11];
lean_object* v_a_3229_ = _args[12];
lean_object* v_b_3230_ = _args[13];
lean_object* v___y_3231_ = _args[14];
lean_object* v___y_3232_ = _args[15];
lean_object* v___y_3233_ = _args[16];
lean_object* v___y_3234_ = _args[17];
lean_object* v___y_3235_ = _args[18];
_start:
{
lean_object* v_res_3236_; 
v_res_3236_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3217_, v_val_3218_, v_baseName_3219_, v___x_3220_, v_a_3221_, v___x_3222_, v___x_3223_, v___x_3224_, v_matchDeclName_3225_, v___x_3226_, v___x_3227_, v___x_3228_, v_a_3229_, v_b_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v_upperBound_3217_);
return v_res_3236_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3240_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__2));
v___x_3241_ = lean_unsigned_to_nat(6u);
v___x_3242_ = lean_unsigned_to_nat(233u);
v___x_3243_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__1));
v___x_3244_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_3245_ = l_mkPanicMessageWithDecl(v___x_3244_, v___x_3243_, v___x_3242_, v___x_3241_, v___x_3240_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(lean_object* v_splitterName_3258_, lean_object* v_matchDeclName_3259_, lean_object* v_numParams_3260_, lean_object* v_val_3261_, lean_object* v___x_3262_, lean_object* v_numDiscrs_3263_, lean_object* v_baseName_3264_, lean_object* v_a_3265_, lean_object* v___x_3266_, lean_object* v___x_3267_, lean_object* v___x_3268_, lean_object* v_uElimPos_x3f_3269_, lean_object* v_discrInfos_3270_, lean_object* v_overlaps_3271_, lean_object* v___f_3272_, lean_object* v___x_3273_, lean_object* v_altInfos_3274_, lean_object* v_xs_3275_, lean_object* v___matchResultType_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; uint8_t v___y_3294_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v_lower_3302_; lean_object* v_upper_3303_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; uint8_t v___x_3359_; 
v___x_3296_ = lean_box(0);
v___x_3297_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3260_);
lean_inc_ref(v_xs_3275_);
v___x_3298_ = l_Array_toSubarray___redArg(v_xs_3275_, v___x_3297_, v_numParams_3260_);
v___x_3299_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_3261_);
v___x_3300_ = lean_array_get(v___x_3262_, v_xs_3275_, v___x_3299_);
lean_dec(v___x_3299_);
v___x_3356_ = lean_array_get_size(v_xs_3275_);
v___x_3357_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_3261_);
v___x_3358_ = lean_nat_sub(v___x_3356_, v___x_3357_);
lean_dec(v___x_3357_);
v___x_3359_ = lean_nat_dec_le(v___x_3358_, v___x_3297_);
if (v___x_3359_ == 0)
{
v_lower_3302_ = v___x_3358_;
v_upper_3303_ = v___x_3356_;
goto v___jp_3301_;
}
else
{
lean_dec(v___x_3358_);
v_lower_3302_ = v___x_3297_;
v_upper_3303_ = v___x_3356_;
goto v___jp_3301_;
}
v___jp_3282_:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3283_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__3);
v___x_3284_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3(v___x_3283_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
return v___x_3284_;
}
v___jp_3285_:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3288_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3288_, 0, v___y_3287_);
lean_ctor_set(v___x_3288_, 1, v_splitterName_3258_);
lean_ctor_set(v___x_3288_, 2, v___y_3286_);
v___x_3289_ = l_Lean_Meta_Match_registerMatchEqns___redArg(v_matchDeclName_3259_, v___x_3288_, v___y_3280_);
return v___x_3289_;
}
v___jp_3290_:
{
lean_object* v___x_3295_; 
lean_inc(v_matchDeclName_3259_);
v___x_3295_ = l_Lean_Meta_Match_withMkMatcherInput___redArg(v_matchDeclName_3259_, v___y_3294_, v___y_3292_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_dec_ref_known(v___x_3295_, 1);
v___y_3286_ = v___y_3291_;
v___y_3287_ = v___y_3293_;
goto v___jp_3285_;
}
else
{
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3291_);
lean_dec(v_matchDeclName_3259_);
lean_dec(v_splitterName_3258_);
return v___x_3295_;
}
}
v___jp_3301_:
{
lean_object* v___x_3304_; lean_object* v_start_3305_; lean_object* v_stop_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
lean_inc_ref(v_xs_3275_);
v___x_3304_ = l_Array_toSubarray___redArg(v_xs_3275_, v_lower_3302_, v_upper_3303_);
v_start_3305_ = lean_ctor_get(v___x_3304_, 1);
lean_inc(v_start_3305_);
v_stop_3306_ = lean_ctor_get(v___x_3304_, 2);
lean_inc(v_stop_3306_);
v___x_3307_ = lean_unsigned_to_nat(1u);
v___x_3308_ = lean_nat_add(v_numParams_3260_, v___x_3307_);
v___x_3309_ = lean_nat_add(v___x_3308_, v_numDiscrs_3263_);
v___x_3310_ = lean_nat_sub(v_stop_3306_, v_start_3305_);
lean_dec(v_start_3305_);
lean_dec(v_stop_3306_);
v___x_3311_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__7));
v___x_3312_ = l_Array_toSubarray___redArg(v_xs_3275_, v___x_3308_, v___x_3309_);
lean_inc(v___x_3267_);
lean_inc(v_matchDeclName_3259_);
lean_inc(v___x_3266_);
v___x_3313_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v___x_3310_, v_val_3261_, v_baseName_3264_, v___x_3312_, v_a_3265_, v___x_3266_, v___x_3298_, v___x_3300_, v_matchDeclName_3259_, v___x_3267_, v___x_3304_, v___x_3268_, v___x_3297_, v___x_3311_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
lean_dec(v___x_3310_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3314_; lean_object* v_snd_3315_; lean_object* v_snd_3316_; lean_object* v_snd_3317_; lean_object* v_fst_3318_; lean_object* v_fst_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3346_; 
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_a_3314_);
lean_dec_ref_known(v___x_3313_, 1);
v_snd_3315_ = lean_ctor_get(v_a_3314_, 1);
v_snd_3316_ = lean_ctor_get(v_snd_3315_, 1);
v_snd_3317_ = lean_ctor_get(v_snd_3316_, 1);
lean_inc(v_snd_3317_);
v_fst_3318_ = lean_ctor_get(v_a_3314_, 0);
lean_inc(v_fst_3318_);
lean_dec(v_a_3314_);
v_fst_3319_ = lean_ctor_get(v_snd_3317_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v_snd_3317_);
if (v_isSharedCheck_3346_ == 0)
{
lean_object* v_unused_3347_; 
v_unused_3347_ = lean_ctor_get(v_snd_3317_, 1);
lean_dec(v_unused_3347_);
v___x_3321_ = v_snd_3317_;
v_isShared_3322_ = v_isSharedCheck_3346_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_fst_3319_);
lean_dec(v_snd_3317_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3346_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3323_; uint8_t v___x_3324_; 
lean_inc_ref(v_overlaps_3271_);
lean_inc(v_fst_3319_);
v___x_3323_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3323_, 0, v_numParams_3260_);
lean_ctor_set(v___x_3323_, 1, v_numDiscrs_3263_);
lean_ctor_set(v___x_3323_, 2, v_fst_3319_);
lean_ctor_set(v___x_3323_, 3, v_uElimPos_x3f_3269_);
lean_ctor_set(v___x_3323_, 4, v_discrInfos_3270_);
lean_ctor_set(v___x_3323_, 5, v_overlaps_3271_);
v___x_3324_ = l_Lean_Meta_Match_Overlaps_isEmpty(v_overlaps_3271_);
lean_dec_ref(v_overlaps_3271_);
if (v___x_3324_ == 0)
{
uint8_t v___x_3325_; 
lean_del_object(v___x_3321_);
lean_dec(v_fst_3319_);
lean_dec_ref(v___x_3273_);
lean_dec(v___x_3267_);
lean_dec(v___x_3266_);
v___x_3325_ = 1;
v___y_3291_ = v___x_3323_;
v___y_3292_ = v___f_3272_;
v___y_3293_ = v_fst_3318_;
v___y_3294_ = v___x_3325_;
goto v___jp_3290_;
}
else
{
lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3326_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__8));
v___x_3327_ = lean_find_expr(v___x_3326_, v___x_3273_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v___x_3328_; lean_object* v___x_3329_; uint8_t v___x_3330_; 
lean_dec_ref(v___f_3272_);
v___x_3328_ = lean_array_get_size(v_altInfos_3274_);
v___x_3329_ = lean_array_get_size(v_fst_3319_);
v___x_3330_ = lean_nat_dec_eq(v___x_3328_, v___x_3329_);
if (v___x_3330_ == 0)
{
lean_dec_ref_known(v___x_3323_, 6);
lean_del_object(v___x_3321_);
lean_dec(v_fst_3319_);
lean_dec(v_fst_3318_);
lean_dec_ref(v___x_3273_);
lean_dec(v___x_3267_);
lean_dec(v___x_3266_);
lean_dec(v_matchDeclName_3259_);
lean_dec(v_splitterName_3258_);
goto v___jp_3282_;
}
else
{
uint8_t v___x_3331_; 
v___x_3331_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_altInfos_3274_, v_fst_3319_, v___x_3328_);
lean_dec(v_fst_3319_);
if (v___x_3331_ == 0)
{
lean_dec_ref_known(v___x_3323_, 6);
lean_del_object(v___x_3321_);
lean_dec(v_fst_3318_);
lean_dec_ref(v___x_3273_);
lean_dec(v___x_3267_);
lean_dec(v___x_3266_);
lean_dec(v_matchDeclName_3259_);
lean_dec(v_splitterName_3258_);
goto v___jp_3282_;
}
else
{
uint8_t v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; uint8_t v___x_3336_; lean_object* v___x_3338_; 
v___x_3332_ = 0;
lean_inc_n(v_splitterName_3258_, 2);
v___x_3333_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3333_, 0, v_splitterName_3258_);
lean_ctor_set(v___x_3333_, 1, v___x_3267_);
lean_ctor_set(v___x_3333_, 2, v___x_3273_);
lean_inc(v_matchDeclName_3259_);
v___x_3334_ = l_Lean_mkConst(v_matchDeclName_3259_, v___x_3266_);
v___x_3335_ = lean_box(1);
v___x_3336_ = 1;
if (v_isShared_3322_ == 0)
{
lean_ctor_set_tag(v___x_3321_, 1);
lean_ctor_set(v___x_3321_, 1, v___x_3296_);
lean_ctor_set(v___x_3321_, 0, v_splitterName_3258_);
v___x_3338_ = v___x_3321_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_splitterName_3258_);
lean_ctor_set(v_reuseFailAlloc_3345_, 1, v___x_3296_);
v___x_3338_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3339_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3339_, 0, v___x_3333_);
lean_ctor_set(v___x_3339_, 1, v___x_3334_);
lean_ctor_set(v___x_3339_, 2, v___x_3335_);
lean_ctor_set(v___x_3339_, 3, v___x_3338_);
lean_ctor_set_uint8(v___x_3339_, sizeof(void*)*4, v___x_3336_);
v___x_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3339_);
lean_inc_ref(v___x_3340_);
v___x_3341_ = l_Lean_addDecl(v___x_3340_, v___x_3332_, v___y_3279_, v___y_3280_);
if (lean_obj_tag(v___x_3341_) == 0)
{
uint8_t v___x_3342_; lean_object* v___x_3343_; 
lean_dec_ref_known(v___x_3341_, 1);
v___x_3342_ = 0;
lean_inc(v_splitterName_3258_);
v___x_3343_ = l_Lean_Meta_setInlineAttribute(v_splitterName_3258_, v___x_3342_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v___x_3344_; 
lean_dec_ref_known(v___x_3343_, 1);
v___x_3344_ = l_Lean_compileDecl(v___x_3340_, v___x_3332_, v___y_3279_, v___y_3280_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_dec_ref_known(v___x_3344_, 1);
v___y_3286_ = v___x_3323_;
v___y_3287_ = v_fst_3318_;
goto v___jp_3285_;
}
else
{
lean_dec_ref_known(v___x_3323_, 6);
lean_dec(v_fst_3318_);
lean_dec(v_matchDeclName_3259_);
lean_dec(v_splitterName_3258_);
return v___x_3344_;
}
}
else
{
lean_dec_ref_known(v___x_3340_, 1);
lean_dec_ref_known(v___x_3323_, 6);
lean_dec(v_fst_3318_);
lean_dec(v_matchDeclName_3259_);
lean_dec(v_splitterName_3258_);
return v___x_3343_;
}
}
else
{
lean_dec_ref_known(v___x_3340_, 1);
lean_dec_ref_known(v___x_3323_, 6);
lean_dec(v_fst_3318_);
lean_dec(v_matchDeclName_3259_);
lean_dec(v_splitterName_3258_);
return v___x_3341_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_3327_, 1);
lean_del_object(v___x_3321_);
lean_dec(v_fst_3319_);
lean_dec_ref(v___x_3273_);
lean_dec(v___x_3267_);
lean_dec(v___x_3266_);
v___y_3291_ = v___x_3323_;
v___y_3292_ = v___f_3272_;
v___y_3293_ = v_fst_3318_;
v___y_3294_ = v___x_3324_;
goto v___jp_3290_;
}
}
}
}
else
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3355_; 
lean_dec_ref(v___x_3273_);
lean_dec_ref(v___f_3272_);
lean_dec_ref(v_overlaps_3271_);
lean_dec_ref(v_discrInfos_3270_);
lean_dec(v_uElimPos_x3f_3269_);
lean_dec(v___x_3267_);
lean_dec(v___x_3266_);
lean_dec(v_numDiscrs_3263_);
lean_dec(v_numParams_3260_);
lean_dec(v_matchDeclName_3259_);
lean_dec(v_splitterName_3258_);
v_a_3348_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3350_ = v___x_3313_;
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3313_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3353_; 
if (v_isShared_3351_ == 0)
{
v___x_3353_ = v___x_3350_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_a_3348_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed(lean_object** _args){
lean_object* v_splitterName_3360_ = _args[0];
lean_object* v_matchDeclName_3361_ = _args[1];
lean_object* v_numParams_3362_ = _args[2];
lean_object* v_val_3363_ = _args[3];
lean_object* v___x_3364_ = _args[4];
lean_object* v_numDiscrs_3365_ = _args[5];
lean_object* v_baseName_3366_ = _args[6];
lean_object* v_a_3367_ = _args[7];
lean_object* v___x_3368_ = _args[8];
lean_object* v___x_3369_ = _args[9];
lean_object* v___x_3370_ = _args[10];
lean_object* v_uElimPos_x3f_3371_ = _args[11];
lean_object* v_discrInfos_3372_ = _args[12];
lean_object* v_overlaps_3373_ = _args[13];
lean_object* v___f_3374_ = _args[14];
lean_object* v___x_3375_ = _args[15];
lean_object* v_altInfos_3376_ = _args[16];
lean_object* v_xs_3377_ = _args[17];
lean_object* v___matchResultType_3378_ = _args[18];
lean_object* v___y_3379_ = _args[19];
lean_object* v___y_3380_ = _args[20];
lean_object* v___y_3381_ = _args[21];
lean_object* v___y_3382_ = _args[22];
lean_object* v___y_3383_ = _args[23];
_start:
{
lean_object* v_res_3384_; 
v_res_3384_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1(v_splitterName_3360_, v_matchDeclName_3361_, v_numParams_3362_, v_val_3363_, v___x_3364_, v_numDiscrs_3365_, v_baseName_3366_, v_a_3367_, v___x_3368_, v___x_3369_, v___x_3370_, v_uElimPos_x3f_3371_, v_discrInfos_3372_, v_overlaps_3373_, v___f_3374_, v___x_3375_, v_altInfos_3376_, v_xs_3377_, v___matchResultType_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec_ref(v___matchResultType_3378_);
lean_dec_ref(v_altInfos_3376_);
lean_dec_ref(v___x_3364_);
return v_res_3384_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3385_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__0, &l_Lean_Meta_Match_proveCondEqThm___closed__0_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__0);
v___x_3386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3385_);
return v___x_3386_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3387_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_3388_ = lean_unsigned_to_nat(0u);
v___x_3389_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3388_);
lean_ctor_set(v___x_3389_, 1, v___x_3388_);
lean_ctor_set(v___x_3389_, 2, v___x_3388_);
lean_ctor_set(v___x_3389_, 3, v___x_3388_);
lean_ctor_set(v___x_3389_, 4, v___x_3387_);
lean_ctor_set(v___x_3389_, 5, v___x_3387_);
lean_ctor_set(v___x_3389_, 6, v___x_3387_);
lean_ctor_set(v___x_3389_, 7, v___x_3387_);
lean_ctor_set(v___x_3389_, 8, v___x_3387_);
lean_ctor_set(v___x_3389_, 9, v___x_3387_);
lean_ctor_set(v___x_3389_, 10, v___x_3387_);
return v___x_3389_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3390_ = lean_box(1);
v___x_3391_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_3392_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_3393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3392_);
lean_ctor_set(v___x_3393_, 1, v___x_3391_);
lean_ctor_set(v___x_3393_, 2, v___x_3390_);
return v___x_3393_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3395_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3));
v___x_3396_ = l_Lean_stringToMessageData(v___x_3395_);
return v___x_3396_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6(void){
_start:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3398_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5));
v___x_3399_ = l_Lean_stringToMessageData(v___x_3398_);
return v___x_3399_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8(void){
_start:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3401_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7));
v___x_3402_ = l_Lean_stringToMessageData(v___x_3401_);
return v___x_3402_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10(void){
_start:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3404_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9));
v___x_3405_ = l_Lean_stringToMessageData(v___x_3404_);
return v___x_3405_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12(void){
_start:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3407_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11));
v___x_3408_ = l_Lean_stringToMessageData(v___x_3407_);
return v___x_3408_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14(void){
_start:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3410_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13));
v___x_3411_ = l_Lean_stringToMessageData(v___x_3410_);
return v___x_3411_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16(void){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3413_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15));
v___x_3414_ = l_Lean_stringToMessageData(v___x_3413_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_3415_, lean_object* v_declHint_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v_env_3421_; uint8_t v___x_3422_; 
v___x_3419_ = lean_box(0);
v___x_3420_ = lean_st_ref_get(v___y_3417_);
v_env_3421_ = lean_ctor_get(v___x_3420_, 0);
lean_inc_ref(v_env_3421_);
lean_dec(v___x_3420_);
v___x_3422_ = l_Lean_Name_isAnonymous(v_declHint_3416_);
if (v___x_3422_ == 0)
{
uint8_t v_isExporting_3423_; 
v_isExporting_3423_ = lean_ctor_get_uint8(v_env_3421_, sizeof(void*)*8);
if (v_isExporting_3423_ == 0)
{
lean_object* v___x_3424_; 
lean_dec_ref(v_env_3421_);
lean_dec(v_declHint_3416_);
v___x_3424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3424_, 0, v_msg_3415_);
return v___x_3424_;
}
else
{
lean_object* v___x_3425_; uint8_t v___x_3426_; 
lean_inc_ref(v_env_3421_);
v___x_3425_ = l_Lean_Environment_setExporting(v_env_3421_, v___x_3422_);
lean_inc(v_declHint_3416_);
lean_inc_ref(v___x_3425_);
v___x_3426_ = l_Lean_Environment_contains(v___x_3425_, v_declHint_3416_, v_isExporting_3423_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; 
lean_dec_ref(v___x_3425_);
lean_dec_ref(v_env_3421_);
lean_dec(v_declHint_3416_);
v___x_3427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3427_, 0, v_msg_3415_);
return v___x_3427_;
}
else
{
lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v_c_3433_; lean_object* v___x_3434_; 
v___x_3428_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_3429_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_3430_ = l_Lean_Options_empty;
v___x_3431_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3425_);
lean_ctor_set(v___x_3431_, 1, v___x_3428_);
lean_ctor_set(v___x_3431_, 2, v___x_3429_);
lean_ctor_set(v___x_3431_, 3, v___x_3430_);
lean_inc(v_declHint_3416_);
v___x_3432_ = l_Lean_MessageData_ofConstName(v_declHint_3416_, v___x_3422_);
v_c_3433_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3433_, 0, v___x_3431_);
lean_ctor_set(v_c_3433_, 1, v___x_3432_);
v___x_3434_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3421_, v_declHint_3416_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
lean_dec_ref(v_env_3421_);
lean_dec(v_declHint_3416_);
v___x_3435_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_3436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3435_);
lean_ctor_set(v___x_3436_, 1, v_c_3433_);
v___x_3437_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6);
v___x_3438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3436_);
lean_ctor_set(v___x_3438_, 1, v___x_3437_);
v___x_3439_ = l_Lean_MessageData_note(v___x_3438_);
v___x_3440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3440_, 0, v_msg_3415_);
lean_ctor_set(v___x_3440_, 1, v___x_3439_);
v___x_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3440_);
return v___x_3441_;
}
else
{
lean_object* v_val_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3476_; 
v_val_3442_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3444_ = v___x_3434_;
v_isShared_3445_ = v_isSharedCheck_3476_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_val_3442_);
lean_dec(v___x_3434_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3476_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v_mod_3448_; uint8_t v___x_3449_; 
v___x_3446_ = l_Lean_Environment_header(v_env_3421_);
lean_dec_ref(v_env_3421_);
v___x_3447_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3446_);
v_mod_3448_ = lean_array_get(v___x_3419_, v___x_3447_, v_val_3442_);
lean_dec(v_val_3442_);
lean_dec_ref(v___x_3447_);
v___x_3449_ = l_Lean_isPrivateName(v_declHint_3416_);
lean_dec(v_declHint_3416_);
if (v___x_3449_ == 0)
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3461_; 
v___x_3450_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8);
v___x_3451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3450_);
lean_ctor_set(v___x_3451_, 1, v_c_3433_);
v___x_3452_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10);
v___x_3453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3451_);
lean_ctor_set(v___x_3453_, 1, v___x_3452_);
v___x_3454_ = l_Lean_MessageData_ofName(v_mod_3448_);
v___x_3455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3453_);
lean_ctor_set(v___x_3455_, 1, v___x_3454_);
v___x_3456_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12);
v___x_3457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3455_);
lean_ctor_set(v___x_3457_, 1, v___x_3456_);
v___x_3458_ = l_Lean_MessageData_note(v___x_3457_);
v___x_3459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3459_, 0, v_msg_3415_);
lean_ctor_set(v___x_3459_, 1, v___x_3458_);
if (v_isShared_3445_ == 0)
{
lean_ctor_set_tag(v___x_3444_, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3459_);
v___x_3461_ = v___x_3444_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v___x_3459_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
else
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3474_; 
v___x_3463_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_3464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3463_);
lean_ctor_set(v___x_3464_, 1, v_c_3433_);
v___x_3465_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14);
v___x_3466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3464_);
lean_ctor_set(v___x_3466_, 1, v___x_3465_);
v___x_3467_ = l_Lean_MessageData_ofName(v_mod_3448_);
v___x_3468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3466_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
v___x_3469_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16);
v___x_3470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3468_);
lean_ctor_set(v___x_3470_, 1, v___x_3469_);
v___x_3471_ = l_Lean_MessageData_note(v___x_3470_);
v___x_3472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3472_, 0, v_msg_3415_);
lean_ctor_set(v___x_3472_, 1, v___x_3471_);
if (v_isShared_3445_ == 0)
{
lean_ctor_set_tag(v___x_3444_, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3472_);
v___x_3474_ = v___x_3444_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v___x_3472_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3477_; 
lean_dec_ref(v_env_3421_);
lean_dec(v_declHint_3416_);
v___x_3477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3477_, 0, v_msg_3415_);
return v___x_3477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_3478_, lean_object* v_declHint_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_){
_start:
{
lean_object* v_res_3482_; 
v_res_3482_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3478_, v_declHint_3479_, v___y_3480_);
lean_dec(v___y_3480_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(lean_object* v_msg_3483_, lean_object* v_declHint_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_){
_start:
{
lean_object* v___x_3490_; lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3500_; 
v___x_3490_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3483_, v_declHint_3484_, v___y_3488_);
v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3493_ = v___x_3490_;
v_isShared_3494_ = v_isSharedCheck_3500_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3490_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3500_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3498_; 
v___x_3495_ = l_Lean_unknownIdentifierMessageTag;
v___x_3496_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3495_);
lean_ctor_set(v___x_3496_, 1, v_a_3491_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 0, v___x_3496_);
v___x_3498_ = v___x_3493_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v___x_3496_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12___boxed(lean_object* v_msg_3501_, lean_object* v_declHint_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3501_, v_declHint_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(lean_object* v_ref_3509_, lean_object* v_msg_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_){
_start:
{
lean_object* v_toCold_3516_; lean_object* v_currRecDepth_3517_; lean_object* v_ref_3518_; uint16_t v_optionFlags_3519_; uint8_t v_suppressElabErrors_3520_; uint8_t v_isRecordingDeps_3521_; lean_object* v_ref_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v_toCold_3516_ = lean_ctor_get(v___y_3513_, 0);
v_currRecDepth_3517_ = lean_ctor_get(v___y_3513_, 1);
v_ref_3518_ = lean_ctor_get(v___y_3513_, 2);
v_optionFlags_3519_ = lean_ctor_get_uint16(v___y_3513_, sizeof(void*)*3);
v_suppressElabErrors_3520_ = lean_ctor_get_uint8(v___y_3513_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3521_ = lean_ctor_get_uint8(v___y_3513_, sizeof(void*)*3 + 3);
v_ref_3522_ = l_Lean_replaceRef(v_ref_3509_, v_ref_3518_);
lean_inc(v_currRecDepth_3517_);
lean_inc_ref(v_toCold_3516_);
v___x_3523_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3523_, 0, v_toCold_3516_);
lean_ctor_set(v___x_3523_, 1, v_currRecDepth_3517_);
lean_ctor_set(v___x_3523_, 2, v_ref_3522_);
lean_ctor_set_uint16(v___x_3523_, sizeof(void*)*3, v_optionFlags_3519_);
lean_ctor_set_uint8(v___x_3523_, sizeof(void*)*3 + 2, v_suppressElabErrors_3520_);
lean_ctor_set_uint8(v___x_3523_, sizeof(void*)*3 + 3, v_isRecordingDeps_3521_);
v___x_3524_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v_msg_3510_, v___y_3511_, v___y_3512_, v___x_3523_, v___y_3514_);
lean_dec_ref_known(v___x_3523_, 3);
return v___x_3524_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg___boxed(lean_object* v_ref_3525_, lean_object* v_msg_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_){
_start:
{
lean_object* v_res_3532_; 
v_res_3532_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3525_, v_msg_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
lean_dec(v_ref_3525_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(lean_object* v_ref_3533_, lean_object* v_msg_3534_, lean_object* v_declHint_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v___x_3541_; lean_object* v_a_3542_; lean_object* v___x_3543_; 
v___x_3541_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_3534_, v_declHint_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_);
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_a_3542_);
lean_dec_ref(v___x_3541_);
v___x_3543_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3533_, v_a_3542_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg___boxed(lean_object* v_ref_3544_, lean_object* v_msg_3545_, lean_object* v_declHint_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_){
_start:
{
lean_object* v_res_3552_; 
v_res_3552_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3544_, v_msg_3545_, v_declHint_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec(v___y_3548_);
lean_dec_ref(v___y_3547_);
lean_dec(v_ref_3544_);
return v_res_3552_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3554_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_3555_ = l_Lean_stringToMessageData(v___x_3554_);
return v___x_3555_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__2));
v___x_3558_ = l_Lean_stringToMessageData(v___x_3557_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(lean_object* v_ref_3559_, lean_object* v_constName_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
lean_object* v___x_3566_; uint8_t v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3566_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__1);
v___x_3567_ = 0;
lean_inc(v_constName_3560_);
v___x_3568_ = l_Lean_MessageData_ofConstName(v_constName_3560_, v___x_3567_);
v___x_3569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3566_);
lean_ctor_set(v___x_3569_, 1, v___x_3568_);
v___x_3570_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3569_);
lean_ctor_set(v___x_3571_, 1, v___x_3570_);
v___x_3572_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3559_, v___x_3571_, v_constName_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
return v___x_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_ref_3573_, lean_object* v_constName_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v_res_3580_; 
v_res_3580_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3573_, v_constName_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
lean_dec(v_ref_3573_);
return v_res_3580_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(lean_object* v_constName_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
lean_object* v_ref_3587_; lean_object* v___x_3588_; 
v_ref_3587_ = lean_ctor_get(v___y_3584_, 2);
v___x_3588_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3587_, v_constName_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg___boxed(lean_object* v_constName_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(lean_object* v_constName_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v___x_3602_; lean_object* v_env_3603_; uint8_t v___x_3604_; lean_object* v___x_3605_; 
v___x_3602_ = lean_st_ref_get(v___y_3600_);
v_env_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc_ref(v_env_3603_);
lean_dec(v___x_3602_);
v___x_3604_ = 0;
lean_inc(v_constName_3596_);
v___x_3605_ = l_Lean_Environment_find_x3f(v_env_3603_, v_constName_3596_, v___x_3604_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v___x_3606_; 
v___x_3606_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
return v___x_3606_;
}
else
{
lean_object* v_val_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3614_; 
lean_dec(v_constName_3596_);
v_val_3607_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3609_ = v___x_3605_;
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_val_3607_);
lean_dec(v___x_3605_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3612_; 
if (v_isShared_3610_ == 0)
{
lean_ctor_set_tag(v___x_3609_, 0);
v___x_3612_ = v___x_3609_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_val_3607_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0___boxed(lean_object* v_constName_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_){
_start:
{
lean_object* v_res_3621_; 
v_res_3621_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_constName_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_);
lean_dec(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(lean_object* v_a_3622_, lean_object* v_a_3623_){
_start:
{
if (lean_obj_tag(v_a_3622_) == 0)
{
lean_object* v___x_3624_; 
v___x_3624_ = l_List_reverse___redArg(v_a_3623_);
return v___x_3624_;
}
else
{
lean_object* v_head_3625_; lean_object* v_tail_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3635_; 
v_head_3625_ = lean_ctor_get(v_a_3622_, 0);
v_tail_3626_ = lean_ctor_get(v_a_3622_, 1);
v_isSharedCheck_3635_ = !lean_is_exclusive(v_a_3622_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3628_ = v_a_3622_;
v_isShared_3629_ = v_isSharedCheck_3635_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_tail_3626_);
lean_inc(v_head_3625_);
lean_dec(v_a_3622_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3635_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3630_; lean_object* v___x_3632_; 
v___x_3630_ = l_Lean_mkLevelParam(v_head_3625_);
if (v_isShared_3629_ == 0)
{
lean_ctor_set(v___x_3628_, 1, v_a_3623_);
lean_ctor_set(v___x_3628_, 0, v___x_3630_);
v___x_3632_ = v___x_3628_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v___x_3630_);
lean_ctor_set(v_reuseFailAlloc_3634_, 1, v_a_3623_);
v___x_3632_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
v_a_3622_ = v_tail_3626_;
v_a_3623_ = v___x_3632_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1(void){
_start:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3637_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__0));
v___x_3638_ = l_Lean_stringToMessageData(v___x_3637_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(lean_object* v_matchDeclName_3639_, lean_object* v_baseName_3640_, lean_object* v_splitterName_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_){
_start:
{
lean_object* v___x_3647_; uint8_t v_foApprox_3648_; uint8_t v_ctxApprox_3649_; uint8_t v_quasiPatternApprox_3650_; uint8_t v_constApprox_3651_; uint8_t v_isDefEqStuckEx_3652_; uint8_t v_unificationHints_3653_; uint8_t v_proofIrrelevance_3654_; uint8_t v_assignSyntheticOpaque_3655_; uint8_t v_offsetCnstrs_3656_; uint8_t v_transparency_3657_; uint8_t v_univApprox_3658_; uint8_t v_iota_3659_; uint8_t v_beta_3660_; uint8_t v_proj_3661_; uint8_t v_zeta_3662_; uint8_t v_zetaDelta_3663_; uint8_t v_zetaUnused_3664_; uint8_t v_zetaHave_3665_; uint8_t v_canUnfoldPredicateConfig_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3729_; 
v___x_3647_ = l_Lean_Meta_Context_config(v_a_3642_);
v_foApprox_3648_ = lean_ctor_get_uint8(v___x_3647_, 0);
v_ctxApprox_3649_ = lean_ctor_get_uint8(v___x_3647_, 1);
v_quasiPatternApprox_3650_ = lean_ctor_get_uint8(v___x_3647_, 2);
v_constApprox_3651_ = lean_ctor_get_uint8(v___x_3647_, 3);
v_isDefEqStuckEx_3652_ = lean_ctor_get_uint8(v___x_3647_, 4);
v_unificationHints_3653_ = lean_ctor_get_uint8(v___x_3647_, 5);
v_proofIrrelevance_3654_ = lean_ctor_get_uint8(v___x_3647_, 6);
v_assignSyntheticOpaque_3655_ = lean_ctor_get_uint8(v___x_3647_, 7);
v_offsetCnstrs_3656_ = lean_ctor_get_uint8(v___x_3647_, 8);
v_transparency_3657_ = lean_ctor_get_uint8(v___x_3647_, 9);
v_univApprox_3658_ = lean_ctor_get_uint8(v___x_3647_, 11);
v_iota_3659_ = lean_ctor_get_uint8(v___x_3647_, 12);
v_beta_3660_ = lean_ctor_get_uint8(v___x_3647_, 13);
v_proj_3661_ = lean_ctor_get_uint8(v___x_3647_, 14);
v_zeta_3662_ = lean_ctor_get_uint8(v___x_3647_, 15);
v_zetaDelta_3663_ = lean_ctor_get_uint8(v___x_3647_, 16);
v_zetaUnused_3664_ = lean_ctor_get_uint8(v___x_3647_, 17);
v_zetaHave_3665_ = lean_ctor_get_uint8(v___x_3647_, 18);
v_canUnfoldPredicateConfig_3666_ = lean_ctor_get_uint8(v___x_3647_, 19);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3668_ = v___x_3647_;
v_isShared_3669_ = v_isSharedCheck_3729_;
goto v_resetjp_3667_;
}
else
{
lean_dec(v___x_3647_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3729_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
uint8_t v_trackZetaDelta_3670_; lean_object* v_zetaDeltaSet_3671_; lean_object* v_lctx_3672_; lean_object* v_localInstances_3673_; lean_object* v_defEqCtx_x3f_3674_; lean_object* v_synthPendingDepth_3675_; lean_object* v_customCanUnfoldPredicate_x3f_3676_; uint8_t v_univApprox_3677_; uint8_t v_inTypeClassResolution_3678_; uint8_t v_cacheInferType_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3727_; 
v_trackZetaDelta_3670_ = lean_ctor_get_uint8(v_a_3642_, sizeof(void*)*7);
v_zetaDeltaSet_3671_ = lean_ctor_get(v_a_3642_, 1);
v_lctx_3672_ = lean_ctor_get(v_a_3642_, 2);
v_localInstances_3673_ = lean_ctor_get(v_a_3642_, 3);
v_defEqCtx_x3f_3674_ = lean_ctor_get(v_a_3642_, 4);
v_synthPendingDepth_3675_ = lean_ctor_get(v_a_3642_, 5);
v_customCanUnfoldPredicate_x3f_3676_ = lean_ctor_get(v_a_3642_, 6);
v_univApprox_3677_ = lean_ctor_get_uint8(v_a_3642_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3678_ = lean_ctor_get_uint8(v_a_3642_, sizeof(void*)*7 + 2);
v_cacheInferType_3679_ = lean_ctor_get_uint8(v_a_3642_, sizeof(void*)*7 + 3);
v_isSharedCheck_3727_ = !lean_is_exclusive(v_a_3642_);
if (v_isSharedCheck_3727_ == 0)
{
lean_object* v_unused_3728_; 
v_unused_3728_ = lean_ctor_get(v_a_3642_, 0);
lean_dec(v_unused_3728_);
v___x_3681_ = v_a_3642_;
v_isShared_3682_ = v_isSharedCheck_3727_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_3676_);
lean_inc(v_synthPendingDepth_3675_);
lean_inc(v_defEqCtx_x3f_3674_);
lean_inc(v_localInstances_3673_);
lean_inc(v_lctx_3672_);
lean_inc(v_zetaDeltaSet_3671_);
lean_dec(v_a_3642_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3727_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
uint8_t v___x_3683_; lean_object* v___x_3685_; 
v___x_3683_ = 2;
if (v_isShared_3669_ == 0)
{
v___x_3685_ = v___x_3668_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_3726_, 0, v_foApprox_3648_);
lean_ctor_set_uint8(v_reuseFailAlloc_3726_, 1, v_ctxApprox_3649_);
lean_ctor_set_uint8(v_reuseFailAlloc_3726_, 2, v_quasiPatternApprox_3650_);
lean_ctor_set_uint8(v_reuseFailAlloc_3726_, 3, v_constApprox_3651_);
lean_ctor_set_uint8(v_reuseFailAlloc_3726_, 4, v_isDefEqStuckEx_3652_);
lean_ctor_set_uint8(v_reuseFailAlloc_3726_, 5, v_unificationHints_3653_);
lean_ctor_set_uint8(v_reuseFailAlloc_3726_, 6, v_proofIrrelevance_3654_);
lean_ctor_set_uint8(v_reuseFailAlloc_3726_, 7, v_assignSyntheticOpaque_3655_);
lean_ctor_set_uint8(v_reuseFailAlloc_3726_, 8, v_offsetCnstrs_3656_);
lean_ctor_set_uint8(v_reuseFailAlloc_3726_, 9, v_transparency_3657_);
lean_ctor_set_uint8(v_reuseFailAlloc_3726_, 11, v_univApprox_3658_);
lean_ctor_set_uint8(v_reuseFailAlloc_3726_, 12, v_iota_3659_);
lean_ctor_set_uint8(v_reuseFailAlloc_3726_, 13, v_beta_3660_);
lean_ctor_set_uint8(v_reuseFailAlloc_3726_, 14, v_proj_3661_);
lean_ctor_set_uint8(v_reuseFailAlloc_3726_, 15, v_zeta_3662_);
lean_ctor_set_uint8(v_reuseFailAlloc_3726_, 16, v_zetaDelta_3663_);
lean_ctor_set_uint8(v_reuseFailAlloc_3726_, 17, v_zetaUnused_3664_);
lean_ctor_set_uint8(v_reuseFailAlloc_3726_, 18, v_zetaHave_3665_);
lean_ctor_set_uint8(v_reuseFailAlloc_3726_, 19, v_canUnfoldPredicateConfig_3666_);
v___x_3685_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
uint64_t v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3690_; 
lean_ctor_set_uint8(v___x_3685_, 10, v___x_3683_);
v___x_3686_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3685_);
v___x_3687_ = l_Lean_instInhabitedExpr;
v___x_3688_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3688_, 0, v___x_3685_);
lean_ctor_set_uint64(v___x_3688_, sizeof(void*)*1, v___x_3686_);
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 0, v___x_3688_);
v___x_3690_ = v___x_3681_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3688_);
lean_ctor_set(v_reuseFailAlloc_3725_, 1, v_zetaDeltaSet_3671_);
lean_ctor_set(v_reuseFailAlloc_3725_, 2, v_lctx_3672_);
lean_ctor_set(v_reuseFailAlloc_3725_, 3, v_localInstances_3673_);
lean_ctor_set(v_reuseFailAlloc_3725_, 4, v_defEqCtx_x3f_3674_);
lean_ctor_set(v_reuseFailAlloc_3725_, 5, v_synthPendingDepth_3675_);
lean_ctor_set(v_reuseFailAlloc_3725_, 6, v_customCanUnfoldPredicate_x3f_3676_);
lean_ctor_set_uint8(v_reuseFailAlloc_3725_, sizeof(void*)*7, v_trackZetaDelta_3670_);
lean_ctor_set_uint8(v_reuseFailAlloc_3725_, sizeof(void*)*7 + 1, v_univApprox_3677_);
lean_ctor_set_uint8(v_reuseFailAlloc_3725_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3678_);
lean_ctor_set_uint8(v_reuseFailAlloc_3725_, sizeof(void*)*7 + 3, v_cacheInferType_3679_);
v___x_3690_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
lean_object* v___x_3691_; 
lean_inc(v_matchDeclName_3639_);
v___x_3691_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_3639_, v___x_3690_, v_a_3643_, v_a_3644_, v_a_3645_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_object* v_a_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v_a_3697_; 
v_a_3692_ = lean_ctor_get(v___x_3691_, 0);
lean_inc(v_a_3692_);
lean_dec_ref_known(v___x_3691_, 1);
v___x_3693_ = l_Lean_ConstantInfo_levelParams(v_a_3692_);
v___x_3694_ = lean_box(0);
lean_inc(v___x_3693_);
v___x_3695_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(v___x_3693_, v___x_3694_);
lean_inc(v_matchDeclName_3639_);
v___x_3696_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_matchDeclName_3639_, v_a_3645_);
v_a_3697_ = lean_ctor_get(v___x_3696_, 0);
lean_inc(v_a_3697_);
lean_dec_ref(v___x_3696_);
if (lean_obj_tag(v_a_3697_) == 1)
{
lean_object* v_val_3698_; lean_object* v_numParams_3699_; lean_object* v_numDiscrs_3700_; lean_object* v_altInfos_3701_; lean_object* v_uElimPos_x3f_3702_; lean_object* v_discrInfos_3703_; lean_object* v_overlaps_3704_; lean_object* v___f_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___f_3708_; uint8_t v___x_3709_; lean_object* v___x_3710_; 
v_val_3698_ = lean_ctor_get(v_a_3697_, 0);
lean_inc(v_val_3698_);
lean_dec_ref_known(v_a_3697_, 1);
v_numParams_3699_ = lean_ctor_get(v_val_3698_, 0);
lean_inc(v_numParams_3699_);
v_numDiscrs_3700_ = lean_ctor_get(v_val_3698_, 1);
lean_inc(v_numDiscrs_3700_);
v_altInfos_3701_ = lean_ctor_get(v_val_3698_, 2);
lean_inc_ref(v_altInfos_3701_);
v_uElimPos_x3f_3702_ = lean_ctor_get(v_val_3698_, 3);
lean_inc(v_uElimPos_x3f_3702_);
v_discrInfos_3703_ = lean_ctor_get(v_val_3698_, 4);
lean_inc_ref(v_discrInfos_3703_);
v_overlaps_3704_ = lean_ctor_get(v_val_3698_, 5);
lean_inc_ref_n(v_overlaps_3704_, 2);
lean_inc(v_splitterName_3641_);
v___f_3705_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3705_, 0, v_overlaps_3704_);
lean_closure_set(v___f_3705_, 1, v_splitterName_3641_);
v___x_3706_ = l_Lean_Meta_Match_getNumEqsFromDiscrInfos(v_discrInfos_3703_);
v___x_3707_ = l_Lean_ConstantInfo_type(v_a_3692_);
lean_inc_ref(v___x_3707_);
v___f_3708_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___boxed), 24, 17);
lean_closure_set(v___f_3708_, 0, v_splitterName_3641_);
lean_closure_set(v___f_3708_, 1, v_matchDeclName_3639_);
lean_closure_set(v___f_3708_, 2, v_numParams_3699_);
lean_closure_set(v___f_3708_, 3, v_val_3698_);
lean_closure_set(v___f_3708_, 4, v___x_3687_);
lean_closure_set(v___f_3708_, 5, v_numDiscrs_3700_);
lean_closure_set(v___f_3708_, 6, v_baseName_3640_);
lean_closure_set(v___f_3708_, 7, v_a_3692_);
lean_closure_set(v___f_3708_, 8, v___x_3695_);
lean_closure_set(v___f_3708_, 9, v___x_3693_);
lean_closure_set(v___f_3708_, 10, v___x_3706_);
lean_closure_set(v___f_3708_, 11, v_uElimPos_x3f_3702_);
lean_closure_set(v___f_3708_, 12, v_discrInfos_3703_);
lean_closure_set(v___f_3708_, 13, v_overlaps_3704_);
lean_closure_set(v___f_3708_, 14, v___f_3705_);
lean_closure_set(v___f_3708_, 15, v___x_3707_);
lean_closure_set(v___f_3708_, 16, v_altInfos_3701_);
v___x_3709_ = 0;
v___x_3710_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_3707_, v___f_3708_, v___x_3709_, v___x_3709_, v___x_3690_, v_a_3643_, v_a_3644_, v_a_3645_);
lean_dec_ref(v___x_3690_);
return v___x_3710_;
}
else
{
lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
lean_dec(v_a_3697_);
lean_dec(v___x_3695_);
lean_dec(v___x_3693_);
lean_dec(v_a_3692_);
lean_dec(v_splitterName_3641_);
lean_dec(v_baseName_3640_);
v___x_3711_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_3712_ = l_Lean_MessageData_ofName(v_matchDeclName_3639_);
v___x_3713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3711_);
lean_ctor_set(v___x_3713_, 1, v___x_3712_);
v___x_3714_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_3715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3713_);
lean_ctor_set(v___x_3715_, 1, v___x_3714_);
v___x_3716_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_3715_, v___x_3690_, v_a_3643_, v_a_3644_, v_a_3645_);
lean_dec_ref(v___x_3690_);
return v___x_3716_;
}
}
else
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
lean_dec_ref(v___x_3690_);
lean_dec(v_splitterName_3641_);
lean_dec(v_baseName_3640_);
lean_dec(v_matchDeclName_3639_);
v_a_3717_ = lean_ctor_get(v___x_3691_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3719_ = v___x_3691_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3691_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3722_; 
if (v_isShared_3720_ == 0)
{
v___x_3722_ = v___x_3719_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3717_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed(lean_object* v_matchDeclName_3730_, lean_object* v_baseName_3731_, lean_object* v_splitterName_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_){
_start:
{
lean_object* v_res_3738_; 
v_res_3738_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go(v_matchDeclName_3730_, v_baseName_3731_, v_splitterName_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_);
lean_dec(v_a_3736_);
lean_dec_ref(v_a_3735_);
lean_dec(v_a_3734_);
return v_res_3738_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(lean_object* v_xs_3739_, lean_object* v_ys_3740_, lean_object* v_hsz_3741_, lean_object* v_x_3742_, lean_object* v_x_3743_){
_start:
{
uint8_t v___x_3744_; 
v___x_3744_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___redArg(v_xs_3739_, v_ys_3740_, v_x_3742_);
return v___x_3744_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4___boxed(lean_object* v_xs_3745_, lean_object* v_ys_3746_, lean_object* v_hsz_3747_, lean_object* v_x_3748_, lean_object* v_x_3749_){
_start:
{
uint8_t v_res_3750_; lean_object* v_r_3751_; 
v_res_3750_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__4(v_xs_3745_, v_ys_3746_, v_hsz_3747_, v_x_3748_, v_x_3749_);
lean_dec_ref(v_ys_3746_);
lean_dec_ref(v_xs_3745_);
v_r_3751_ = lean_box(v_res_3750_);
return v_r_3751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6(lean_object* v_inst_3752_, lean_object* v_R_3753_, lean_object* v_a_3754_, lean_object* v_b_3755_){
_start:
{
lean_object* v___x_3756_; 
v___x_3756_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v_a_3754_, v_b_3755_);
return v___x_3756_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(lean_object* v_upperBound_3757_, lean_object* v_val_3758_, lean_object* v_baseName_3759_, lean_object* v___x_3760_, lean_object* v_a_3761_, lean_object* v___x_3762_, lean_object* v___x_3763_, lean_object* v___x_3764_, lean_object* v_matchDeclName_3765_, lean_object* v___x_3766_, lean_object* v___x_3767_, lean_object* v___x_3768_, lean_object* v_inst_3769_, lean_object* v_R_3770_, lean_object* v_a_3771_, lean_object* v_b_3772_, lean_object* v_c_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v___x_3779_; 
v___x_3779_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg(v_upperBound_3757_, v_val_3758_, v_baseName_3759_, v___x_3760_, v_a_3761_, v___x_3762_, v___x_3763_, v___x_3764_, v_matchDeclName_3765_, v___x_3766_, v___x_3767_, v___x_3768_, v_a_3771_, v_b_3772_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_3780_ = _args[0];
lean_object* v_val_3781_ = _args[1];
lean_object* v_baseName_3782_ = _args[2];
lean_object* v___x_3783_ = _args[3];
lean_object* v_a_3784_ = _args[4];
lean_object* v___x_3785_ = _args[5];
lean_object* v___x_3786_ = _args[6];
lean_object* v___x_3787_ = _args[7];
lean_object* v_matchDeclName_3788_ = _args[8];
lean_object* v___x_3789_ = _args[9];
lean_object* v___x_3790_ = _args[10];
lean_object* v___x_3791_ = _args[11];
lean_object* v_inst_3792_ = _args[12];
lean_object* v_R_3793_ = _args[13];
lean_object* v_a_3794_ = _args[14];
lean_object* v_b_3795_ = _args[15];
lean_object* v_c_3796_ = _args[16];
lean_object* v___y_3797_ = _args[17];
lean_object* v___y_3798_ = _args[18];
lean_object* v___y_3799_ = _args[19];
lean_object* v___y_3800_ = _args[20];
lean_object* v___y_3801_ = _args[21];
_start:
{
lean_object* v_res_3802_; 
v_res_3802_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8(v_upperBound_3780_, v_val_3781_, v_baseName_3782_, v___x_3783_, v_a_3784_, v___x_3785_, v___x_3786_, v___x_3787_, v_matchDeclName_3788_, v___x_3789_, v___x_3790_, v___x_3791_, v_inst_3792_, v_R_3793_, v_a_3794_, v_b_3795_, v_c_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
lean_dec(v___y_3800_);
lean_dec_ref(v___y_3799_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec(v_upperBound_3780_);
return v_res_3802_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(lean_object* v_00_u03b1_3803_, lean_object* v_constName_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v___x_3810_; 
v___x_3810_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___redArg(v_constName_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3811_, lean_object* v_constName_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0(v_00_u03b1_3811_, v_constName_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
return v_res_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_3819_, lean_object* v_ref_3820_, lean_object* v_constName_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_){
_start:
{
lean_object* v___x_3827_; 
v___x_3827_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg(v_ref_3820_, v_constName_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
return v___x_3827_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_3828_, lean_object* v_ref_3829_, lean_object* v_constName_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4(v_00_u03b1_3828_, v_ref_3829_, v_constName_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v_ref_3829_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(lean_object* v_00_u03b1_3837_, lean_object* v_ref_3838_, lean_object* v_msg_3839_, lean_object* v_declHint_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_){
_start:
{
lean_object* v___x_3846_; 
v___x_3846_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_3838_, v_msg_3839_, v_declHint_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11___boxed(lean_object* v_00_u03b1_3847_, lean_object* v_ref_3848_, lean_object* v_msg_3849_, lean_object* v_declHint_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_){
_start:
{
lean_object* v_res_3856_; 
v_res_3856_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11(v_00_u03b1_3847_, v_ref_3848_, v_msg_3849_, v_declHint_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
lean_dec(v_ref_3848_);
return v_res_3856_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(lean_object* v_msg_3857_, lean_object* v_declHint_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
lean_object* v___x_3864_; 
v___x_3864_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_3857_, v_declHint_3858_, v___y_3862_);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_3865_, lean_object* v_declHint_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(v_msg_3865_, v_declHint_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(lean_object* v_00_u03b1_3873_, lean_object* v_ref_3874_, lean_object* v_msg_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_){
_start:
{
lean_object* v___x_3881_; 
v___x_3881_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_3874_, v_msg_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_);
return v___x_3881_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13___boxed(lean_object* v_00_u03b1_3882_, lean_object* v_ref_3883_, lean_object* v_msg_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4_spec__11_spec__13(v_00_u03b1_3882_, v_ref_3883_, v_msg_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
lean_dec(v_ref_3883_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3891_, lean_object* v_vals_3892_, lean_object* v_i_3893_, lean_object* v_k_3894_){
_start:
{
lean_object* v___x_3895_; uint8_t v___x_3896_; 
v___x_3895_ = lean_array_get_size(v_keys_3891_);
v___x_3896_ = lean_nat_dec_lt(v_i_3893_, v___x_3895_);
if (v___x_3896_ == 0)
{
lean_object* v___x_3897_; 
lean_dec(v_i_3893_);
v___x_3897_ = lean_box(0);
return v___x_3897_;
}
else
{
lean_object* v_k_x27_3898_; uint8_t v___x_3899_; 
v_k_x27_3898_ = lean_array_fget_borrowed(v_keys_3891_, v_i_3893_);
v___x_3899_ = lean_name_eq(v_k_3894_, v_k_x27_3898_);
if (v___x_3899_ == 0)
{
lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3900_ = lean_unsigned_to_nat(1u);
v___x_3901_ = lean_nat_add(v_i_3893_, v___x_3900_);
lean_dec(v_i_3893_);
v_i_3893_ = v___x_3901_;
goto _start;
}
else
{
lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3903_ = lean_array_fget_borrowed(v_vals_3892_, v_i_3893_);
lean_dec(v_i_3893_);
lean_inc(v___x_3903_);
v___x_3904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3903_);
return v___x_3904_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3905_, lean_object* v_vals_3906_, lean_object* v_i_3907_, lean_object* v_k_3908_){
_start:
{
lean_object* v_res_3909_; 
v_res_3909_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_3905_, v_vals_3906_, v_i_3907_, v_k_3908_);
lean_dec(v_k_3908_);
lean_dec_ref(v_vals_3906_);
lean_dec_ref(v_keys_3905_);
return v_res_3909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(lean_object* v_x_3910_, size_t v_x_3911_, lean_object* v_x_3912_){
_start:
{
if (lean_obj_tag(v_x_3910_) == 0)
{
lean_object* v_es_3913_; lean_object* v___x_3914_; size_t v___x_3915_; size_t v___x_3916_; lean_object* v_j_3917_; lean_object* v___x_3918_; 
v_es_3913_ = lean_ctor_get(v_x_3910_, 0);
v___x_3914_ = lean_box(2);
v___x_3915_ = ((size_t)31ULL);
v___x_3916_ = lean_usize_land(v_x_3911_, v___x_3915_);
v_j_3917_ = lean_usize_to_nat(v___x_3916_);
v___x_3918_ = lean_array_get_borrowed(v___x_3914_, v_es_3913_, v_j_3917_);
lean_dec(v_j_3917_);
switch(lean_obj_tag(v___x_3918_))
{
case 0:
{
lean_object* v_key_3919_; lean_object* v_val_3920_; uint8_t v___x_3921_; 
v_key_3919_ = lean_ctor_get(v___x_3918_, 0);
v_val_3920_ = lean_ctor_get(v___x_3918_, 1);
v___x_3921_ = lean_name_eq(v_x_3912_, v_key_3919_);
if (v___x_3921_ == 0)
{
lean_object* v___x_3922_; 
v___x_3922_ = lean_box(0);
return v___x_3922_;
}
else
{
lean_object* v___x_3923_; 
lean_inc(v_val_3920_);
v___x_3923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3923_, 0, v_val_3920_);
return v___x_3923_;
}
}
case 1:
{
lean_object* v_node_3924_; size_t v___x_3925_; size_t v___x_3926_; 
v_node_3924_ = lean_ctor_get(v___x_3918_, 0);
v___x_3925_ = ((size_t)5ULL);
v___x_3926_ = lean_usize_shift_right(v_x_3911_, v___x_3925_);
v_x_3910_ = v_node_3924_;
v_x_3911_ = v___x_3926_;
goto _start;
}
default: 
{
lean_object* v___x_3928_; 
v___x_3928_ = lean_box(0);
return v___x_3928_;
}
}
}
else
{
lean_object* v_ks_3929_; lean_object* v_vs_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; 
v_ks_3929_ = lean_ctor_get(v_x_3910_, 0);
v_vs_3930_ = lean_ctor_get(v_x_3910_, 1);
v___x_3931_ = lean_unsigned_to_nat(0u);
v___x_3932_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_ks_3929_, v_vs_3930_, v___x_3931_, v_x_3912_);
return v___x_3932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_3933_, lean_object* v_x_3934_, lean_object* v_x_3935_){
_start:
{
size_t v_x_703__boxed_3936_; lean_object* v_res_3937_; 
v_x_703__boxed_3936_ = lean_unbox_usize(v_x_3934_);
lean_dec(v_x_3934_);
v_res_3937_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3933_, v_x_703__boxed_3936_, v_x_3935_);
lean_dec(v_x_3935_);
lean_dec_ref(v_x_3933_);
return v_res_3937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(lean_object* v_x_3938_, lean_object* v_x_3939_){
_start:
{
uint64_t v___y_3941_; 
if (lean_obj_tag(v_x_3939_) == 0)
{
uint64_t v___x_3944_; 
v___x_3944_ = 1723ULL;
v___y_3941_ = v___x_3944_;
goto v___jp_3940_;
}
else
{
uint64_t v_hash_3945_; 
v_hash_3945_ = lean_ctor_get_uint64(v_x_3939_, sizeof(void*)*2);
v___y_3941_ = v_hash_3945_;
goto v___jp_3940_;
}
v___jp_3940_:
{
size_t v___x_3942_; lean_object* v___x_3943_; 
v___x_3942_ = lean_uint64_to_usize(v___y_3941_);
v___x_3943_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_3938_, v___x_3942_, v_x_3939_);
return v___x_3943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg___boxed(lean_object* v_x_3946_, lean_object* v_x_3947_){
_start:
{
lean_object* v_res_3948_; 
v_res_3948_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_3946_, v_x_3947_);
lean_dec(v_x_3947_);
lean_dec_ref(v_x_3946_);
return v_res_3948_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4(void){
_start:
{
lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___x_3955_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__3));
v___x_3956_ = l_Lean_stringToMessageData(v___x_3955_);
return v___x_3956_;
}
}
static lean_object* _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6(void){
_start:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3958_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__5));
v___x_3959_ = l_Lean_stringToMessageData(v___x_3958_);
return v___x_3959_;
}
}
LEAN_EXPORT lean_object* lean_get_match_equations_for(lean_object* v_matchDeclName_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_){
_start:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v_env_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3966_ = l_Lean_Meta_Match_instInhabitedMatchEqnsExtState_default;
v___x_3967_ = lean_st_ref_get(v_a_3964_);
v_env_3968_ = lean_ctor_get(v___x_3967_, 0);
lean_inc_ref(v_env_3968_);
lean_dec(v___x_3967_);
lean_inc_n(v_matchDeclName_3960_, 3);
v___x_3969_ = l_Lean_mkPrivateName(v_env_3968_, v_matchDeclName_3960_);
lean_dec_ref(v_env_3968_);
v___x_3970_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__1));
lean_inc(v___x_3969_);
v___x_3971_ = l_Lean_Name_append(v___x_3969_, v___x_3970_);
lean_inc_n(v___x_3971_, 2);
v___x_3972_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___boxed), 8, 3);
lean_closure_set(v___x_3972_, 0, v_matchDeclName_3960_);
lean_closure_set(v___x_3972_, 1, v___x_3969_);
lean_closure_set(v___x_3972_, 2, v___x_3971_);
v___x_3973_ = l_Lean_Meta_realizeConst(v_matchDeclName_3960_, v___x_3971_, v___x_3972_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_4001_; 
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_4001_ == 0)
{
lean_object* v_unused_4002_; 
v_unused_4002_ = lean_ctor_get(v___x_3973_, 0);
lean_dec(v_unused_4002_);
v___x_3975_ = v___x_3973_;
v_isShared_3976_ = v_isSharedCheck_4001_;
goto v_resetjp_3974_;
}
else
{
lean_dec(v___x_3973_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_4001_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3977_; lean_object* v_env_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v_map_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3999_; 
v___x_3977_ = lean_st_ref_get(v_a_3964_);
v_env_3978_ = lean_ctor_get(v___x_3977_, 0);
lean_inc_ref(v_env_3978_);
lean_dec(v___x_3977_);
v___x_3979_ = l_Lean_Meta_Match_matchEqnsExt;
v___x_3980_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__2));
v___x_3981_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3966_, v___x_3979_, v_env_3978_, v___x_3980_, v___x_3971_);
v_map_3982_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_3999_ == 0)
{
lean_object* v_unused_4000_; 
v_unused_4000_ = lean_ctor_get(v___x_3981_, 1);
lean_dec(v_unused_4000_);
v___x_3984_ = v___x_3981_;
v_isShared_3985_ = v_isSharedCheck_3999_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_map_3982_);
lean_dec(v___x_3981_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3999_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3986_; 
v___x_3986_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_map_3982_, v_matchDeclName_3960_);
lean_dec_ref(v_map_3982_);
if (lean_obj_tag(v___x_3986_) == 0)
{
lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3990_; 
lean_del_object(v___x_3975_);
v___x_3987_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__4, &l_Lean_Meta_Match_getEquationsForImpl___closed__4_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__4);
v___x_3988_ = l_Lean_MessageData_ofName(v_matchDeclName_3960_);
if (v_isShared_3985_ == 0)
{
lean_ctor_set_tag(v___x_3984_, 7);
lean_ctor_set(v___x_3984_, 1, v___x_3988_);
lean_ctor_set(v___x_3984_, 0, v___x_3987_);
v___x_3990_ = v___x_3984_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v___x_3987_);
lean_ctor_set(v_reuseFailAlloc_3994_, 1, v___x_3988_);
v___x_3990_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; 
v___x_3991_ = lean_obj_once(&l_Lean_Meta_Match_getEquationsForImpl___closed__6, &l_Lean_Meta_Match_getEquationsForImpl___closed__6_once, _init_l_Lean_Meta_Match_getEquationsForImpl___closed__6);
v___x_3992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3990_);
lean_ctor_set(v___x_3992_, 1, v___x_3991_);
v___x_3993_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_3992_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_);
lean_dec(v_a_3964_);
lean_dec_ref(v_a_3963_);
lean_dec(v_a_3962_);
lean_dec_ref(v_a_3961_);
return v___x_3993_;
}
}
else
{
lean_object* v_val_3995_; lean_object* v___x_3997_; 
lean_del_object(v___x_3984_);
lean_dec(v_a_3964_);
lean_dec_ref(v_a_3963_);
lean_dec(v_a_3962_);
lean_dec_ref(v_a_3961_);
lean_dec(v_matchDeclName_3960_);
v_val_3995_ = lean_ctor_get(v___x_3986_, 0);
lean_inc(v_val_3995_);
lean_dec_ref_known(v___x_3986_, 1);
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 0, v_val_3995_);
v___x_3997_ = v___x_3975_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_val_3995_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
}
}
}
else
{
lean_object* v_a_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4010_; 
lean_dec(v___x_3971_);
lean_dec(v_a_3964_);
lean_dec_ref(v_a_3963_);
lean_dec(v_a_3962_);
lean_dec_ref(v_a_3961_);
lean_dec(v_matchDeclName_3960_);
v_a_4003_ = lean_ctor_get(v___x_3973_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_4005_ = v___x_3973_;
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_a_4003_);
lean_dec(v___x_3973_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4008_; 
if (v_isShared_4006_ == 0)
{
v___x_4008_ = v___x_4005_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_a_4003_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
return v___x_4008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_getEquationsForImpl___boxed(lean_object* v_matchDeclName_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_){
_start:
{
lean_object* v_res_4017_; 
v_res_4017_ = lean_get_match_equations_for(v_matchDeclName_4011_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_);
return v_res_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(lean_object* v_00_u03b2_4018_, lean_object* v_x_4019_, lean_object* v_x_4020_){
_start:
{
lean_object* v___x_4021_; 
v___x_4021_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___redArg(v_x_4019_, v_x_4020_);
return v___x_4021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0___boxed(lean_object* v_00_u03b2_4022_, lean_object* v_x_4023_, lean_object* v_x_4024_){
_start:
{
lean_object* v_res_4025_; 
v_res_4025_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0(v_00_u03b2_4022_, v_x_4023_, v_x_4024_);
lean_dec(v_x_4024_);
lean_dec_ref(v_x_4023_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(lean_object* v_00_u03b2_4026_, lean_object* v_x_4027_, size_t v_x_4028_, lean_object* v_x_4029_){
_start:
{
lean_object* v___x_4030_; 
v___x_4030_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___redArg(v_x_4027_, v_x_4028_, v_x_4029_);
return v___x_4030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4031_, lean_object* v_x_4032_, lean_object* v_x_4033_, lean_object* v_x_4034_){
_start:
{
size_t v_x_895__boxed_4035_; lean_object* v_res_4036_; 
v_x_895__boxed_4035_ = lean_unbox_usize(v_x_4033_);
lean_dec(v_x_4033_);
v_res_4036_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0(v_00_u03b2_4031_, v_x_4032_, v_x_895__boxed_4035_, v_x_4034_);
lean_dec(v_x_4034_);
lean_dec_ref(v_x_4032_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4037_, lean_object* v_keys_4038_, lean_object* v_vals_4039_, lean_object* v_heq_4040_, lean_object* v_i_4041_, lean_object* v_k_4042_){
_start:
{
lean_object* v___x_4043_; 
v___x_4043_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___redArg(v_keys_4038_, v_vals_4039_, v_i_4041_, v_k_4042_);
return v___x_4043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4044_, lean_object* v_keys_4045_, lean_object* v_vals_4046_, lean_object* v_heq_4047_, lean_object* v_i_4048_, lean_object* v_k_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Match_getEquationsForImpl_spec__0_spec__0_spec__1(v_00_u03b2_4044_, v_keys_4045_, v_vals_4046_, v_heq_4047_, v_i_4048_, v_k_4049_);
lean_dec(v_k_4049_);
lean_dec_ref(v_vals_4046_);
lean_dec_ref(v_keys_4045_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(lean_object* v_type_4051_, lean_object* v_k_4052_, uint8_t v_cleanupAnnotations_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_){
_start:
{
lean_object* v___f_4059_; uint8_t v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___f_4059_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4059_, 0, v_k_4052_);
v___x_4060_ = 0;
v___x_4061_ = lean_box(0);
v___x_4062_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_4060_, v___x_4061_, v_type_4051_, v___f_4059_, v_cleanupAnnotations_4053_, v___x_4060_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_object* v_a_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4070_; 
v_a_4063_ = lean_ctor_get(v___x_4062_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4062_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4065_ = v___x_4062_;
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_a_4063_);
lean_dec(v___x_4062_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4068_; 
if (v_isShared_4066_ == 0)
{
v___x_4068_ = v___x_4065_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_a_4063_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
}
else
{
lean_object* v_a_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4078_; 
v_a_4071_ = lean_ctor_get(v___x_4062_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4062_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4073_ = v___x_4062_;
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v___x_4062_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4076_; 
if (v_isShared_4074_ == 0)
{
v___x_4076_ = v___x_4073_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_a_4071_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
return v___x_4076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg___boxed(lean_object* v_type_4079_, lean_object* v_k_4080_, lean_object* v_cleanupAnnotations_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4087_; lean_object* v_res_4088_; 
v_cleanupAnnotations_boxed_4087_ = lean_unbox(v_cleanupAnnotations_4081_);
v_res_4088_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4079_, v_k_4080_, v_cleanupAnnotations_boxed_4087_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec(v___y_4083_);
lean_dec_ref(v___y_4082_);
return v_res_4088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(lean_object* v_00_u03b1_4089_, lean_object* v_type_4090_, lean_object* v_k_4091_, uint8_t v_cleanupAnnotations_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
lean_object* v___x_4098_; 
v___x_4098_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_type_4090_, v_k_4091_, v_cleanupAnnotations_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___boxed(lean_object* v_00_u03b1_4099_, lean_object* v_type_4100_, lean_object* v_k_4101_, lean_object* v_cleanupAnnotations_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4108_; lean_object* v_res_4109_; 
v_cleanupAnnotations_boxed_4108_ = lean_unbox(v_cleanupAnnotations_4102_);
v_res_4109_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0(v_00_u03b1_4099_, v_type_4100_, v_k_4101_, v_cleanupAnnotations_boxed_4108_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
return v_res_4109_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(lean_object* v_msg_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_){
_start:
{
lean_object* v___f_4116_; lean_object* v___x_18837__overap_4117_; lean_object* v___x_4118_; 
v___f_4116_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__3___closed__0));
v___x_18837__overap_4117_ = lean_panic_fn_borrowed(v___f_4116_, v_msg_4110_);
lean_inc(v___y_4114_);
lean_inc_ref(v___y_4113_);
lean_inc(v___y_4112_);
lean_inc_ref(v___y_4111_);
v___x_4118_ = lean_apply_5(v___x_18837__overap_4117_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, lean_box(0));
return v___x_4118_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2___boxed(lean_object* v_msg_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_){
_start:
{
lean_object* v_res_4125_; 
v_res_4125_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(v_msg_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
return v_res_4125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(lean_object* v_c_4126_){
_start:
{
uint8_t v_foApprox_4127_; uint8_t v_ctxApprox_4128_; uint8_t v_quasiPatternApprox_4129_; uint8_t v_constApprox_4130_; uint8_t v_isDefEqStuckEx_4131_; uint8_t v_unificationHints_4132_; uint8_t v_proofIrrelevance_4133_; uint8_t v_assignSyntheticOpaque_4134_; uint8_t v_offsetCnstrs_4135_; uint8_t v_transparency_4136_; uint8_t v_univApprox_4137_; uint8_t v_iota_4138_; uint8_t v_beta_4139_; uint8_t v_proj_4140_; uint8_t v_zeta_4141_; uint8_t v_zetaDelta_4142_; uint8_t v_zetaUnused_4143_; uint8_t v_zetaHave_4144_; uint8_t v_canUnfoldPredicateConfig_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4153_; 
v_foApprox_4127_ = lean_ctor_get_uint8(v_c_4126_, 0);
v_ctxApprox_4128_ = lean_ctor_get_uint8(v_c_4126_, 1);
v_quasiPatternApprox_4129_ = lean_ctor_get_uint8(v_c_4126_, 2);
v_constApprox_4130_ = lean_ctor_get_uint8(v_c_4126_, 3);
v_isDefEqStuckEx_4131_ = lean_ctor_get_uint8(v_c_4126_, 4);
v_unificationHints_4132_ = lean_ctor_get_uint8(v_c_4126_, 5);
v_proofIrrelevance_4133_ = lean_ctor_get_uint8(v_c_4126_, 6);
v_assignSyntheticOpaque_4134_ = lean_ctor_get_uint8(v_c_4126_, 7);
v_offsetCnstrs_4135_ = lean_ctor_get_uint8(v_c_4126_, 8);
v_transparency_4136_ = lean_ctor_get_uint8(v_c_4126_, 9);
v_univApprox_4137_ = lean_ctor_get_uint8(v_c_4126_, 11);
v_iota_4138_ = lean_ctor_get_uint8(v_c_4126_, 12);
v_beta_4139_ = lean_ctor_get_uint8(v_c_4126_, 13);
v_proj_4140_ = lean_ctor_get_uint8(v_c_4126_, 14);
v_zeta_4141_ = lean_ctor_get_uint8(v_c_4126_, 15);
v_zetaDelta_4142_ = lean_ctor_get_uint8(v_c_4126_, 16);
v_zetaUnused_4143_ = lean_ctor_get_uint8(v_c_4126_, 17);
v_zetaHave_4144_ = lean_ctor_get_uint8(v_c_4126_, 18);
v_canUnfoldPredicateConfig_4145_ = lean_ctor_get_uint8(v_c_4126_, 19);
v_isSharedCheck_4153_ = !lean_is_exclusive(v_c_4126_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4147_ = v_c_4126_;
v_isShared_4148_ = v_isSharedCheck_4153_;
goto v_resetjp_4146_;
}
else
{
lean_dec(v_c_4126_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4153_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
uint8_t v___x_4149_; lean_object* v___x_4151_; 
v___x_4149_ = 2;
if (v_isShared_4148_ == 0)
{
v___x_4151_ = v___x_4147_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_4152_, 0, v_foApprox_4127_);
lean_ctor_set_uint8(v_reuseFailAlloc_4152_, 1, v_ctxApprox_4128_);
lean_ctor_set_uint8(v_reuseFailAlloc_4152_, 2, v_quasiPatternApprox_4129_);
lean_ctor_set_uint8(v_reuseFailAlloc_4152_, 3, v_constApprox_4130_);
lean_ctor_set_uint8(v_reuseFailAlloc_4152_, 4, v_isDefEqStuckEx_4131_);
lean_ctor_set_uint8(v_reuseFailAlloc_4152_, 5, v_unificationHints_4132_);
lean_ctor_set_uint8(v_reuseFailAlloc_4152_, 6, v_proofIrrelevance_4133_);
lean_ctor_set_uint8(v_reuseFailAlloc_4152_, 7, v_assignSyntheticOpaque_4134_);
lean_ctor_set_uint8(v_reuseFailAlloc_4152_, 8, v_offsetCnstrs_4135_);
lean_ctor_set_uint8(v_reuseFailAlloc_4152_, 9, v_transparency_4136_);
lean_ctor_set_uint8(v_reuseFailAlloc_4152_, 11, v_univApprox_4137_);
lean_ctor_set_uint8(v_reuseFailAlloc_4152_, 12, v_iota_4138_);
lean_ctor_set_uint8(v_reuseFailAlloc_4152_, 13, v_beta_4139_);
lean_ctor_set_uint8(v_reuseFailAlloc_4152_, 14, v_proj_4140_);
lean_ctor_set_uint8(v_reuseFailAlloc_4152_, 15, v_zeta_4141_);
lean_ctor_set_uint8(v_reuseFailAlloc_4152_, 16, v_zetaDelta_4142_);
lean_ctor_set_uint8(v_reuseFailAlloc_4152_, 17, v_zetaUnused_4143_);
lean_ctor_set_uint8(v_reuseFailAlloc_4152_, 18, v_zetaHave_4144_);
lean_ctor_set_uint8(v_reuseFailAlloc_4152_, 19, v_canUnfoldPredicateConfig_4145_);
v___x_4151_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
lean_ctor_set_uint8(v___x_4151_, 10, v___x_4149_);
return v___x_4151_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(lean_object* v_x_4154_, lean_object* v_t_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v_dummy_4161_; lean_object* v_nargs_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; 
v_dummy_4161_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__0);
v_nargs_4162_ = l_Lean_Expr_getAppNumArgs(v_t_4155_);
lean_inc(v_nargs_4162_);
v___x_4163_ = lean_mk_array(v_nargs_4162_, v_dummy_4161_);
v___x_4164_ = lean_unsigned_to_nat(1u);
v___x_4165_ = lean_nat_sub(v_nargs_4162_, v___x_4164_);
lean_dec(v_nargs_4162_);
v___x_4166_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_t_4155_, v___x_4163_, v___x_4165_);
v___x_4167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4166_);
return v___x_4167_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0___boxed(lean_object* v_x_4168_, lean_object* v_t_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_){
_start:
{
lean_object* v_res_4175_; 
v_res_4175_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__0(v_x_4168_, v_t_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec(v___y_4171_);
lean_dec_ref(v___y_4170_);
lean_dec_ref(v_x_4168_);
return v_res_4175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(lean_object* v_snd_4176_, lean_object* v_x_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_){
_start:
{
lean_object* v___x_4183_; 
v___x_4183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4183_, 0, v_snd_4176_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed(lean_object* v_snd_4184_, lean_object* v_x_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
lean_object* v_res_4191_; 
v_res_4191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0(v_snd_4184_, v_x_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
lean_dec_ref(v_x_4185_);
return v_res_4191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(size_t v_sz_4192_, size_t v_i_4193_, lean_object* v_bs_4194_){
_start:
{
uint8_t v___x_4195_; 
v___x_4195_ = lean_usize_dec_lt(v_i_4193_, v_sz_4192_);
if (v___x_4195_ == 0)
{
return v_bs_4194_;
}
else
{
lean_object* v_v_4196_; lean_object* v_fst_4197_; lean_object* v_snd_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4212_; 
v_v_4196_ = lean_array_uget(v_bs_4194_, v_i_4193_);
v_fst_4197_ = lean_ctor_get(v_v_4196_, 0);
v_snd_4198_ = lean_ctor_get(v_v_4196_, 1);
v_isSharedCheck_4212_ = !lean_is_exclusive(v_v_4196_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4200_ = v_v_4196_;
v_isShared_4201_ = v_isSharedCheck_4212_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_snd_4198_);
lean_inc(v_fst_4197_);
lean_dec(v_v_4196_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4212_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4202_; lean_object* v_bs_x27_4203_; lean_object* v___f_4204_; lean_object* v___x_4206_; 
v___x_4202_ = lean_unsigned_to_nat(0u);
v_bs_x27_4203_ = lean_array_uset(v_bs_4194_, v_i_4193_, v___x_4202_);
v___f_4204_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4204_, 0, v_snd_4198_);
if (v_isShared_4201_ == 0)
{
lean_ctor_set(v___x_4200_, 1, v___f_4204_);
v___x_4206_ = v___x_4200_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_fst_4197_);
lean_ctor_set(v_reuseFailAlloc_4211_, 1, v___f_4204_);
v___x_4206_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
size_t v___x_4207_; size_t v___x_4208_; lean_object* v___x_4209_; 
v___x_4207_ = ((size_t)1ULL);
v___x_4208_ = lean_usize_add(v_i_4193_, v___x_4207_);
v___x_4209_ = lean_array_uset(v_bs_x27_4203_, v_i_4193_, v___x_4206_);
v_i_4193_ = v___x_4208_;
v_bs_4194_ = v___x_4209_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4___boxed(lean_object* v_sz_4213_, lean_object* v_i_4214_, lean_object* v_bs_4215_){
_start:
{
size_t v_sz_boxed_4216_; size_t v_i_boxed_4217_; lean_object* v_res_4218_; 
v_sz_boxed_4216_ = lean_unbox_usize(v_sz_4213_);
lean_dec(v_sz_4213_);
v_i_boxed_4217_ = lean_unbox_usize(v_i_4214_);
lean_dec(v_i_4214_);
v_res_4218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_boxed_4216_, v_i_boxed_4217_, v_bs_4215_);
return v_res_4218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(size_t v_sz_4219_, size_t v_i_4220_, lean_object* v_bs_4221_){
_start:
{
uint8_t v___x_4222_; 
v___x_4222_ = lean_usize_dec_lt(v_i_4220_, v_sz_4219_);
if (v___x_4222_ == 0)
{
return v_bs_4221_;
}
else
{
lean_object* v_v_4223_; lean_object* v_fst_4224_; lean_object* v_snd_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4241_; 
v_v_4223_ = lean_array_uget(v_bs_4221_, v_i_4220_);
v_fst_4224_ = lean_ctor_get(v_v_4223_, 0);
v_snd_4225_ = lean_ctor_get(v_v_4223_, 1);
v_isSharedCheck_4241_ = !lean_is_exclusive(v_v_4223_);
if (v_isSharedCheck_4241_ == 0)
{
v___x_4227_ = v_v_4223_;
v_isShared_4228_ = v_isSharedCheck_4241_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_snd_4225_);
lean_inc(v_fst_4224_);
lean_dec(v_v_4223_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4241_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v___x_4229_; lean_object* v_bs_x27_4230_; uint8_t v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4234_; 
v___x_4229_ = lean_unsigned_to_nat(0u);
v_bs_x27_4230_ = lean_array_uset(v_bs_4221_, v_i_4220_, v___x_4229_);
v___x_4231_ = 0;
v___x_4232_ = lean_box(v___x_4231_);
if (v_isShared_4228_ == 0)
{
lean_ctor_set(v___x_4227_, 0, v___x_4232_);
v___x_4234_ = v___x_4227_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v___x_4232_);
lean_ctor_set(v_reuseFailAlloc_4240_, 1, v_snd_4225_);
v___x_4234_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
lean_object* v___x_4235_; size_t v___x_4236_; size_t v___x_4237_; lean_object* v___x_4238_; 
v___x_4235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4235_, 0, v_fst_4224_);
lean_ctor_set(v___x_4235_, 1, v___x_4234_);
v___x_4236_ = ((size_t)1ULL);
v___x_4237_ = lean_usize_add(v_i_4220_, v___x_4236_);
v___x_4238_ = lean_array_uset(v_bs_x27_4230_, v_i_4220_, v___x_4235_);
v_i_4220_ = v___x_4237_;
v_bs_4221_ = v___x_4238_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6___boxed(lean_object* v_sz_4242_, lean_object* v_i_4243_, lean_object* v_bs_4244_){
_start:
{
size_t v_sz_boxed_4245_; size_t v_i_boxed_4246_; lean_object* v_res_4247_; 
v_sz_boxed_4245_ = lean_unbox_usize(v_sz_4242_);
lean_dec(v_sz_4242_);
v_i_boxed_4246_ = lean_unbox_usize(v_i_4243_);
lean_dec(v_i_4243_);
v_res_4247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_boxed_4245_, v_i_boxed_4246_, v_bs_4244_);
return v_res_4247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(lean_object* v___x_4248_, lean_object* v___x_4249_, lean_object* v_a_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_){
_start:
{
lean_object* v___x_20543__overap_4256_; lean_object* v___x_4257_; 
v___x_20543__overap_4256_ = l_instInhabitedOfMonad___redArg(v___x_4248_, v___x_4249_);
lean_inc(v___y_4254_);
lean_inc_ref(v___y_4253_);
lean_inc(v___y_4252_);
lean_inc_ref(v___y_4251_);
v___x_4257_ = lean_apply_5(v___x_20543__overap_4256_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_, lean_box(0));
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed(lean_object* v___x_4258_, lean_object* v___x_4259_, lean_object* v_a_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0(v___x_4258_, v___x_4259_, v_a_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec_ref(v_a_4260_);
return v_res_4266_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0(void){
_start:
{
lean_object* v___x_4267_; 
v___x_4267_ = l_instMonadEIO___redArg();
return v___x_4267_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1(void){
_start:
{
lean_object* v___x_4268_; lean_object* v___x_4269_; 
v___x_4268_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__0);
v___x_4269_ = l_StateRefT_x27_instMonad___redArg(v___x_4268_);
return v___x_4269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed(lean_object* v_acc_4274_, lean_object* v_declInfos_4275_, lean_object* v_k_4276_, lean_object* v_kind_4277_, lean_object* v_x_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_){
_start:
{
uint8_t v_kind_boxed_4284_; lean_object* v_res_4285_; 
v_kind_boxed_4284_ = lean_unbox(v_kind_4277_);
v_res_4285_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(v_acc_4274_, v_declInfos_4275_, v_k_4276_, v_kind_boxed_4284_, v_x_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
lean_dec(v___y_4282_);
lean_dec_ref(v___y_4281_);
lean_dec(v___y_4280_);
lean_dec_ref(v___y_4279_);
return v_res_4285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(lean_object* v_declInfos_4286_, lean_object* v_k_4287_, uint8_t v_kind_4288_, lean_object* v_acc_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_){
_start:
{
lean_object* v___x_4295_; lean_object* v_toApplicative_4296_; lean_object* v_toFunctor_4297_; lean_object* v_toSeq_4298_; lean_object* v_toSeqLeft_4299_; lean_object* v_toSeqRight_4300_; lean_object* v___f_4301_; lean_object* v___f_4302_; lean_object* v___f_4303_; lean_object* v___f_4304_; lean_object* v___x_4305_; lean_object* v___f_4306_; lean_object* v___f_4307_; lean_object* v___f_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v_toApplicative_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4362_; 
v___x_4295_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__1);
v_toApplicative_4296_ = lean_ctor_get(v___x_4295_, 0);
v_toFunctor_4297_ = lean_ctor_get(v_toApplicative_4296_, 0);
v_toSeq_4298_ = lean_ctor_get(v_toApplicative_4296_, 2);
v_toSeqLeft_4299_ = lean_ctor_get(v_toApplicative_4296_, 3);
v_toSeqRight_4300_ = lean_ctor_get(v_toApplicative_4296_, 4);
v___f_4301_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__2));
v___f_4302_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_4297_, 2);
v___f_4303_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4303_, 0, v_toFunctor_4297_);
v___f_4304_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4304_, 0, v_toFunctor_4297_);
v___x_4305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4305_, 0, v___f_4303_);
lean_ctor_set(v___x_4305_, 1, v___f_4304_);
lean_inc(v_toSeqRight_4300_);
v___f_4306_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4306_, 0, v_toSeqRight_4300_);
lean_inc(v_toSeqLeft_4299_);
v___f_4307_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4307_, 0, v_toSeqLeft_4299_);
lean_inc(v_toSeq_4298_);
v___f_4308_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4308_, 0, v_toSeq_4298_);
v___x_4309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4309_, 0, v___x_4305_);
lean_ctor_set(v___x_4309_, 1, v___f_4301_);
lean_ctor_set(v___x_4309_, 2, v___f_4308_);
lean_ctor_set(v___x_4309_, 3, v___f_4307_);
lean_ctor_set(v___x_4309_, 4, v___f_4306_);
v___x_4310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4310_, 0, v___x_4309_);
lean_ctor_set(v___x_4310_, 1, v___f_4302_);
v___x_4311_ = l_StateRefT_x27_instMonad___redArg(v___x_4310_);
v_toApplicative_4312_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4362_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4362_ == 0)
{
lean_object* v_unused_4363_; 
v_unused_4363_ = lean_ctor_get(v___x_4311_, 1);
lean_dec(v_unused_4363_);
v___x_4314_ = v___x_4311_;
v_isShared_4315_ = v_isSharedCheck_4362_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_toApplicative_4312_);
lean_dec(v___x_4311_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4362_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v_toFunctor_4316_; lean_object* v_toSeq_4317_; lean_object* v_toSeqLeft_4318_; lean_object* v_toSeqRight_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4360_; 
v_toFunctor_4316_ = lean_ctor_get(v_toApplicative_4312_, 0);
v_toSeq_4317_ = lean_ctor_get(v_toApplicative_4312_, 2);
v_toSeqLeft_4318_ = lean_ctor_get(v_toApplicative_4312_, 3);
v_toSeqRight_4319_ = lean_ctor_get(v_toApplicative_4312_, 4);
v_isSharedCheck_4360_ = !lean_is_exclusive(v_toApplicative_4312_);
if (v_isSharedCheck_4360_ == 0)
{
lean_object* v_unused_4361_; 
v_unused_4361_ = lean_ctor_get(v_toApplicative_4312_, 1);
lean_dec(v_unused_4361_);
v___x_4321_ = v_toApplicative_4312_;
v_isShared_4322_ = v_isSharedCheck_4360_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_toSeqRight_4319_);
lean_inc(v_toSeqLeft_4318_);
lean_inc(v_toSeq_4317_);
lean_inc(v_toFunctor_4316_);
lean_dec(v_toApplicative_4312_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4360_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v___f_4323_; lean_object* v___f_4324_; lean_object* v___f_4325_; lean_object* v___f_4326_; lean_object* v___x_4327_; lean_object* v___f_4328_; lean_object* v___f_4329_; lean_object* v___f_4330_; lean_object* v___x_4332_; 
v___f_4323_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__4));
v___f_4324_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___closed__5));
lean_inc_ref(v_toFunctor_4316_);
v___f_4325_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4325_, 0, v_toFunctor_4316_);
v___f_4326_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4326_, 0, v_toFunctor_4316_);
v___x_4327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4327_, 0, v___f_4325_);
lean_ctor_set(v___x_4327_, 1, v___f_4326_);
v___f_4328_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4328_, 0, v_toSeqRight_4319_);
v___f_4329_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4329_, 0, v_toSeqLeft_4318_);
v___f_4330_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4330_, 0, v_toSeq_4317_);
if (v_isShared_4322_ == 0)
{
lean_ctor_set(v___x_4321_, 4, v___f_4328_);
lean_ctor_set(v___x_4321_, 3, v___f_4329_);
lean_ctor_set(v___x_4321_, 2, v___f_4330_);
lean_ctor_set(v___x_4321_, 1, v___f_4323_);
lean_ctor_set(v___x_4321_, 0, v___x_4327_);
v___x_4332_ = v___x_4321_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4359_; 
v_reuseFailAlloc_4359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4359_, 0, v___x_4327_);
lean_ctor_set(v_reuseFailAlloc_4359_, 1, v___f_4323_);
lean_ctor_set(v_reuseFailAlloc_4359_, 2, v___f_4330_);
lean_ctor_set(v_reuseFailAlloc_4359_, 3, v___f_4329_);
lean_ctor_set(v_reuseFailAlloc_4359_, 4, v___f_4328_);
v___x_4332_ = v_reuseFailAlloc_4359_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
lean_object* v___x_4334_; 
if (v_isShared_4315_ == 0)
{
lean_ctor_set(v___x_4314_, 1, v___f_4324_);
lean_ctor_set(v___x_4314_, 0, v___x_4332_);
v___x_4334_ = v___x_4314_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4358_; 
v_reuseFailAlloc_4358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4358_, 0, v___x_4332_);
lean_ctor_set(v_reuseFailAlloc_4358_, 1, v___f_4324_);
v___x_4334_ = v_reuseFailAlloc_4358_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; uint8_t v___x_4337_; 
v___x_4335_ = lean_array_get_size(v_acc_4289_);
v___x_4336_ = lean_array_get_size(v_declInfos_4286_);
v___x_4337_ = lean_nat_dec_lt(v___x_4335_, v___x_4336_);
if (v___x_4337_ == 0)
{
lean_object* v___x_4338_; 
lean_dec_ref(v___x_4334_);
lean_dec_ref(v_declInfos_4286_);
lean_inc(v___y_4293_);
lean_inc_ref(v___y_4292_);
lean_inc(v___y_4291_);
lean_inc_ref(v___y_4290_);
v___x_4338_ = lean_apply_6(v_k_4287_, v_acc_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, lean_box(0));
return v___x_4338_;
}
else
{
lean_object* v___x_4339_; uint8_t v___x_4340_; lean_object* v___x_4341_; lean_object* v___f_4342_; lean_object* v___f_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v_snd_4348_; lean_object* v_fst_4349_; lean_object* v_fst_4350_; lean_object* v_snd_4351_; lean_object* v___x_4352_; lean_object* v___f_4353_; lean_object* v___x_4354_; 
v___x_4339_ = lean_box(0);
v___x_4340_ = 0;
v___x_4341_ = l_Lean_instInhabitedExpr;
v___f_4342_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4342_, 0, v___x_4334_);
lean_closure_set(v___f_4342_, 1, v___x_4341_);
v___f_4343_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4343_, 0, v___f_4342_);
v___x_4344_ = lean_box(v___x_4340_);
v___x_4345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4345_, 0, v___x_4344_);
lean_ctor_set(v___x_4345_, 1, v___f_4343_);
v___x_4346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4346_, 0, v___x_4339_);
lean_ctor_set(v___x_4346_, 1, v___x_4345_);
v___x_4347_ = lean_array_get(v___x_4346_, v_declInfos_4286_, v___x_4335_);
lean_dec_ref_known(v___x_4346_, 2);
v_snd_4348_ = lean_ctor_get(v___x_4347_, 1);
lean_inc(v_snd_4348_);
v_fst_4349_ = lean_ctor_get(v___x_4347_, 0);
lean_inc(v_fst_4349_);
lean_dec(v___x_4347_);
v_fst_4350_ = lean_ctor_get(v_snd_4348_, 0);
lean_inc(v_fst_4350_);
v_snd_4351_ = lean_ctor_get(v_snd_4348_, 1);
lean_inc(v_snd_4351_);
lean_dec(v_snd_4348_);
v___x_4352_ = lean_box(v_kind_4288_);
lean_inc_ref(v_acc_4289_);
v___f_4353_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1___boxed), 10, 4);
lean_closure_set(v___f_4353_, 0, v_acc_4289_);
lean_closure_set(v___f_4353_, 1, v_declInfos_4286_);
lean_closure_set(v___f_4353_, 2, v_k_4287_);
lean_closure_set(v___f_4353_, 3, v___x_4352_);
lean_inc(v___y_4293_);
lean_inc_ref(v___y_4292_);
lean_inc(v___y_4291_);
lean_inc_ref(v___y_4290_);
v___x_4354_ = lean_apply_6(v_snd_4351_, v_acc_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, lean_box(0));
if (lean_obj_tag(v___x_4354_) == 0)
{
lean_object* v_a_4355_; uint8_t v___x_4356_; lean_object* v___x_4357_; 
v_a_4355_ = lean_ctor_get(v___x_4354_, 0);
lean_inc(v_a_4355_);
lean_dec_ref_known(v___x_4354_, 1);
v___x_4356_ = lean_unbox(v_fst_4350_);
lean_dec(v_fst_4350_);
v___x_4357_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts_go_spec__0___redArg(v_fst_4349_, v___x_4356_, v_a_4355_, v___f_4353_, v_kind_4288_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_);
return v___x_4357_;
}
else
{
lean_dec_ref(v___f_4353_);
lean_dec(v_fst_4350_);
lean_dec(v_fst_4349_);
return v___x_4354_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___lam__1(lean_object* v_acc_4364_, lean_object* v_declInfos_4365_, lean_object* v_k_4366_, uint8_t v_kind_4367_, lean_object* v_x_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_){
_start:
{
lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___x_4374_ = lean_array_push(v_acc_4364_, v_x_4368_);
v___x_4375_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4365_, v_k_4366_, v_kind_4367_, v___x_4374_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
return v___x_4375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9___boxed(lean_object* v_declInfos_4376_, lean_object* v_k_4377_, lean_object* v_kind_4378_, lean_object* v_acc_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_){
_start:
{
uint8_t v_kind_boxed_4385_; lean_object* v_res_4386_; 
v_kind_boxed_4385_ = lean_unbox(v_kind_4378_);
v_res_4386_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4376_, v_k_4377_, v_kind_boxed_4385_, v_acc_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
lean_dec(v___y_4383_);
lean_dec_ref(v___y_4382_);
lean_dec(v___y_4381_);
lean_dec_ref(v___y_4380_);
return v_res_4386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(lean_object* v_declInfos_4387_, lean_object* v_k_4388_, uint8_t v_kind_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_){
_start:
{
lean_object* v___x_4395_; lean_object* v___x_4396_; 
v___x_4395_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4396_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7_spec__9(v_declInfos_4387_, v_k_4388_, v_kind_4389_, v___x_4395_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_);
return v___x_4396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7___boxed(lean_object* v_declInfos_4397_, lean_object* v_k_4398_, lean_object* v_kind_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_){
_start:
{
uint8_t v_kind_boxed_4405_; lean_object* v_res_4406_; 
v_kind_boxed_4405_ = lean_unbox(v_kind_4399_);
v_res_4406_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v_declInfos_4397_, v_k_4398_, v_kind_boxed_4405_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_);
lean_dec(v___y_4403_);
lean_dec_ref(v___y_4402_);
lean_dec(v___y_4401_);
lean_dec_ref(v___y_4400_);
return v_res_4406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(lean_object* v_declInfos_4407_, lean_object* v_k_4408_, uint8_t v_kind_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_){
_start:
{
size_t v_sz_4415_; size_t v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; 
v_sz_4415_ = lean_array_size(v_declInfos_4407_);
v___x_4416_ = ((size_t)0ULL);
v___x_4417_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__6(v_sz_4415_, v___x_4416_, v_declInfos_4407_);
v___x_4418_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5_spec__7(v___x_4417_, v_k_4408_, v_kind_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
return v___x_4418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5___boxed(lean_object* v_declInfos_4419_, lean_object* v_k_4420_, lean_object* v_kind_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_){
_start:
{
uint8_t v_kind_boxed_4427_; lean_object* v_res_4428_; 
v_kind_boxed_4427_ = lean_unbox(v_kind_4421_);
v_res_4428_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v_declInfos_4419_, v_k_4420_, v_kind_boxed_4427_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_);
lean_dec(v___y_4425_);
lean_dec_ref(v___y_4424_);
lean_dec(v___y_4423_);
lean_dec_ref(v___y_4422_);
return v_res_4428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(lean_object* v_declInfos_4429_, lean_object* v_k_4430_, uint8_t v_kind_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_){
_start:
{
size_t v_sz_4437_; size_t v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; 
v_sz_4437_ = lean_array_size(v_declInfos_4429_);
v___x_4438_ = ((size_t)0ULL);
v___x_4439_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__4(v_sz_4437_, v___x_4438_, v_declInfos_4429_);
v___x_4440_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4_spec__5(v___x_4439_, v_k_4430_, v_kind_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
return v___x_4440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4___boxed(lean_object* v_declInfos_4441_, lean_object* v_k_4442_, lean_object* v_kind_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_){
_start:
{
uint8_t v_kind_boxed_4449_; lean_object* v_res_4450_; 
v_kind_boxed_4449_ = lean_unbox(v_kind_4443_);
v_res_4450_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_declInfos_4441_, v_k_4442_, v_kind_boxed_4449_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
lean_dec(v___y_4445_);
lean_dec_ref(v___y_4444_);
return v_res_4450_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(lean_object* v_a_4454_, lean_object* v_b_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_){
_start:
{
lean_object* v_array_4461_; lean_object* v_start_4462_; lean_object* v_stop_4463_; lean_object* v___x_4465_; uint8_t v_isShared_4466_; uint8_t v_isSharedCheck_4521_; 
v_array_4461_ = lean_ctor_get(v_a_4454_, 0);
v_start_4462_ = lean_ctor_get(v_a_4454_, 1);
v_stop_4463_ = lean_ctor_get(v_a_4454_, 2);
v_isSharedCheck_4521_ = !lean_is_exclusive(v_a_4454_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4465_ = v_a_4454_;
v_isShared_4466_ = v_isSharedCheck_4521_;
goto v_resetjp_4464_;
}
else
{
lean_inc(v_stop_4463_);
lean_inc(v_start_4462_);
lean_inc(v_array_4461_);
lean_dec(v_a_4454_);
v___x_4465_ = lean_box(0);
v_isShared_4466_ = v_isSharedCheck_4521_;
goto v_resetjp_4464_;
}
v_resetjp_4464_:
{
uint8_t v___x_4467_; 
v___x_4467_ = lean_nat_dec_lt(v_start_4462_, v_stop_4463_);
if (v___x_4467_ == 0)
{
lean_object* v___x_4468_; 
lean_del_object(v___x_4465_);
lean_dec(v_stop_4463_);
lean_dec(v_start_4462_);
lean_dec_ref(v_array_4461_);
v___x_4468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4468_, 0, v_b_4455_);
return v___x_4468_;
}
else
{
lean_object* v_snd_4469_; lean_object* v_fst_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4520_; 
v_snd_4469_ = lean_ctor_get(v_b_4455_, 1);
v_fst_4470_ = lean_ctor_get(v_b_4455_, 0);
v_isSharedCheck_4520_ = !lean_is_exclusive(v_b_4455_);
if (v_isSharedCheck_4520_ == 0)
{
v___x_4472_ = v_b_4455_;
v_isShared_4473_ = v_isSharedCheck_4520_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_snd_4469_);
lean_inc(v_fst_4470_);
lean_dec(v_b_4455_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4520_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v_array_4474_; lean_object* v_start_4475_; lean_object* v_stop_4476_; uint8_t v___x_4477_; 
v_array_4474_ = lean_ctor_get(v_snd_4469_, 0);
v_start_4475_ = lean_ctor_get(v_snd_4469_, 1);
v_stop_4476_ = lean_ctor_get(v_snd_4469_, 2);
v___x_4477_ = lean_nat_dec_lt(v_start_4475_, v_stop_4476_);
if (v___x_4477_ == 0)
{
lean_object* v___x_4479_; 
lean_del_object(v___x_4465_);
lean_dec(v_stop_4463_);
lean_dec(v_start_4462_);
lean_dec_ref(v_array_4461_);
if (v_isShared_4473_ == 0)
{
v___x_4479_ = v___x_4472_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v_fst_4470_);
lean_ctor_set(v_reuseFailAlloc_4481_, 1, v_snd_4469_);
v___x_4479_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
lean_object* v___x_4480_; 
v___x_4480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4480_, 0, v___x_4479_);
return v___x_4480_;
}
}
else
{
lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4516_; 
lean_inc(v_stop_4476_);
lean_inc(v_start_4475_);
lean_inc_ref(v_array_4474_);
v_isSharedCheck_4516_ = !lean_is_exclusive(v_snd_4469_);
if (v_isSharedCheck_4516_ == 0)
{
lean_object* v_unused_4517_; lean_object* v_unused_4518_; lean_object* v_unused_4519_; 
v_unused_4517_ = lean_ctor_get(v_snd_4469_, 2);
lean_dec(v_unused_4517_);
v_unused_4518_ = lean_ctor_get(v_snd_4469_, 1);
lean_dec(v_unused_4518_);
v_unused_4519_ = lean_ctor_get(v_snd_4469_, 0);
lean_dec(v_unused_4519_);
v___x_4483_ = v_snd_4469_;
v_isShared_4484_ = v_isSharedCheck_4516_;
goto v_resetjp_4482_;
}
else
{
lean_dec(v_snd_4469_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4516_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4488_; 
v___x_4485_ = lean_unsigned_to_nat(1u);
v___x_4486_ = lean_nat_add(v_start_4462_, v___x_4485_);
lean_inc_ref(v_array_4461_);
if (v_isShared_4484_ == 0)
{
lean_ctor_set(v___x_4483_, 2, v_stop_4463_);
lean_ctor_set(v___x_4483_, 1, v___x_4486_);
lean_ctor_set(v___x_4483_, 0, v_array_4461_);
v___x_4488_ = v___x_4483_;
goto v_reusejp_4487_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v_array_4461_);
lean_ctor_set(v_reuseFailAlloc_4515_, 1, v___x_4486_);
lean_ctor_set(v_reuseFailAlloc_4515_, 2, v_stop_4463_);
v___x_4488_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4487_;
}
v_reusejp_4487_:
{
lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4493_; 
v___x_4489_ = lean_array_fget(v_array_4461_, v_start_4462_);
lean_dec(v_start_4462_);
lean_dec_ref(v_array_4461_);
v___x_4490_ = lean_array_fget(v_array_4474_, v_start_4475_);
v___x_4491_ = lean_nat_add(v_start_4475_, v___x_4485_);
lean_dec(v_start_4475_);
if (v_isShared_4466_ == 0)
{
lean_ctor_set(v___x_4465_, 2, v_stop_4476_);
lean_ctor_set(v___x_4465_, 1, v___x_4491_);
lean_ctor_set(v___x_4465_, 0, v_array_4474_);
v___x_4493_ = v___x_4465_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_array_4474_);
lean_ctor_set(v_reuseFailAlloc_4514_, 1, v___x_4491_);
lean_ctor_set(v_reuseFailAlloc_4514_, 2, v_stop_4476_);
v___x_4493_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
lean_object* v___x_4494_; 
v___x_4494_ = l_Lean_Meta_mkEqHEq(v___x_4489_, v___x_4490_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_);
if (lean_obj_tag(v___x_4494_) == 0)
{
lean_object* v_a_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4501_; 
v_a_4495_ = lean_ctor_get(v___x_4494_, 0);
lean_inc(v_a_4495_);
lean_dec_ref_known(v___x_4494_, 1);
v___x_4496_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg___closed__1));
v___x_4497_ = lean_array_get_size(v_fst_4470_);
v___x_4498_ = lean_nat_add(v___x_4497_, v___x_4485_);
v___x_4499_ = lean_name_append_index_after(v___x_4496_, v___x_4498_);
if (v_isShared_4473_ == 0)
{
lean_ctor_set(v___x_4472_, 1, v_a_4495_);
lean_ctor_set(v___x_4472_, 0, v___x_4499_);
v___x_4501_ = v___x_4472_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v___x_4499_);
lean_ctor_set(v_reuseFailAlloc_4505_, 1, v_a_4495_);
v___x_4501_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
lean_object* v___x_4502_; lean_object* v___x_4503_; 
v___x_4502_ = lean_array_push(v_fst_4470_, v___x_4501_);
v___x_4503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4503_, 0, v___x_4502_);
lean_ctor_set(v___x_4503_, 1, v___x_4493_);
v_a_4454_ = v___x_4488_;
v_b_4455_ = v___x_4503_;
goto _start;
}
}
else
{
lean_object* v_a_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4513_; 
lean_dec_ref(v___x_4493_);
lean_dec_ref(v___x_4488_);
lean_del_object(v___x_4472_);
lean_dec(v_fst_4470_);
v_a_4506_ = lean_ctor_get(v___x_4494_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4494_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4508_ = v___x_4494_;
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_a_4506_);
lean_dec(v___x_4494_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4511_; 
if (v_isShared_4509_ == 0)
{
v___x_4511_ = v___x_4508_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4506_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
return v___x_4511_;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg___boxed(lean_object* v_a_4522_, lean_object* v_b_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_){
_start:
{
lean_object* v_res_4529_; 
v_res_4529_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(v_a_4522_, v_b_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
lean_dec(v___y_4527_);
lean_dec_ref(v___y_4526_);
lean_dec(v___y_4525_);
lean_dec_ref(v___y_4524_);
return v_res_4529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(lean_object* v___x_4530_, lean_object* v_a_4531_, lean_object* v___x_4532_, lean_object* v_as_4533_, size_t v_sz_4534_, size_t v_i_4535_, lean_object* v_b_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_){
_start:
{
lean_object* v_a_4543_; uint8_t v___x_4547_; 
v___x_4547_ = lean_usize_dec_lt(v_i_4535_, v_sz_4534_);
if (v___x_4547_ == 0)
{
lean_object* v___x_4548_; 
lean_dec(v___x_4532_);
v___x_4548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4548_, 0, v_b_4536_);
return v___x_4548_;
}
else
{
lean_object* v___x_4549_; lean_object* v_a_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; 
v___x_4549_ = l_Lean_instInhabitedExpr;
v_a_4550_ = lean_array_uget_borrowed(v_as_4533_, v_i_4535_);
v___x_4551_ = lean_array_get_borrowed(v___x_4549_, v___x_4530_, v_a_4550_);
lean_inc(v___x_4551_);
v___x_4552_ = l_Lean_Meta_instantiateForall(v___x_4551_, v_a_4531_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_);
if (lean_obj_tag(v___x_4552_) == 0)
{
lean_object* v_a_4553_; lean_object* v___x_4554_; 
v_a_4553_ = lean_ctor_get(v___x_4552_, 0);
lean_inc(v_a_4553_);
lean_dec_ref_known(v___x_4552_, 1);
lean_inc(v___x_4532_);
v___x_4554_ = l_Lean_Meta_Match_simpH_x3f(v_a_4553_, v___x_4532_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_);
if (lean_obj_tag(v___x_4554_) == 0)
{
lean_object* v_a_4555_; 
v_a_4555_ = lean_ctor_get(v___x_4554_, 0);
lean_inc(v_a_4555_);
lean_dec_ref_known(v___x_4554_, 1);
if (lean_obj_tag(v_a_4555_) == 1)
{
lean_object* v_val_4556_; lean_object* v___x_4557_; 
v_val_4556_ = lean_ctor_get(v_a_4555_, 0);
lean_inc(v_val_4556_);
lean_dec_ref_known(v_a_4555_, 1);
v___x_4557_ = lean_array_push(v_b_4536_, v_val_4556_);
v_a_4543_ = v___x_4557_;
goto v___jp_4542_;
}
else
{
lean_dec(v_a_4555_);
v_a_4543_ = v_b_4536_;
goto v___jp_4542_;
}
}
else
{
lean_object* v_a_4558_; lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4565_; 
lean_dec_ref(v_b_4536_);
lean_dec(v___x_4532_);
v_a_4558_ = lean_ctor_get(v___x_4554_, 0);
v_isSharedCheck_4565_ = !lean_is_exclusive(v___x_4554_);
if (v_isSharedCheck_4565_ == 0)
{
v___x_4560_ = v___x_4554_;
v_isShared_4561_ = v_isSharedCheck_4565_;
goto v_resetjp_4559_;
}
else
{
lean_inc(v_a_4558_);
lean_dec(v___x_4554_);
v___x_4560_ = lean_box(0);
v_isShared_4561_ = v_isSharedCheck_4565_;
goto v_resetjp_4559_;
}
v_resetjp_4559_:
{
lean_object* v___x_4563_; 
if (v_isShared_4561_ == 0)
{
v___x_4563_ = v___x_4560_;
goto v_reusejp_4562_;
}
else
{
lean_object* v_reuseFailAlloc_4564_; 
v_reuseFailAlloc_4564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4564_, 0, v_a_4558_);
v___x_4563_ = v_reuseFailAlloc_4564_;
goto v_reusejp_4562_;
}
v_reusejp_4562_:
{
return v___x_4563_;
}
}
}
}
else
{
lean_object* v_a_4566_; lean_object* v___x_4568_; uint8_t v_isShared_4569_; uint8_t v_isSharedCheck_4573_; 
lean_dec_ref(v_b_4536_);
lean_dec(v___x_4532_);
v_a_4566_ = lean_ctor_get(v___x_4552_, 0);
v_isSharedCheck_4573_ = !lean_is_exclusive(v___x_4552_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4568_ = v___x_4552_;
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
else
{
lean_inc(v_a_4566_);
lean_dec(v___x_4552_);
v___x_4568_ = lean_box(0);
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
v_resetjp_4567_:
{
lean_object* v___x_4571_; 
if (v_isShared_4569_ == 0)
{
v___x_4571_ = v___x_4568_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_a_4566_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
return v___x_4571_;
}
}
}
}
v___jp_4542_:
{
size_t v___x_4544_; size_t v___x_4545_; 
v___x_4544_ = ((size_t)1ULL);
v___x_4545_ = lean_usize_add(v_i_4535_, v___x_4544_);
v_i_4535_ = v___x_4545_;
v_b_4536_ = v_a_4543_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1___boxed(lean_object* v___x_4574_, lean_object* v_a_4575_, lean_object* v___x_4576_, lean_object* v_as_4577_, lean_object* v_sz_4578_, lean_object* v_i_4579_, lean_object* v_b_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_){
_start:
{
size_t v_sz_boxed_4586_; size_t v_i_boxed_4587_; lean_object* v_res_4588_; 
v_sz_boxed_4586_ = lean_unbox_usize(v_sz_4578_);
lean_dec(v_sz_4578_);
v_i_boxed_4587_ = lean_unbox_usize(v_i_4579_);
lean_dec(v_i_4579_);
v_res_4588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v___x_4574_, v_a_4575_, v___x_4576_, v_as_4577_, v_sz_boxed_4586_, v_i_boxed_4587_, v_b_4580_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_);
lean_dec(v___y_4584_);
lean_dec_ref(v___y_4583_);
lean_dec(v___y_4582_);
lean_dec_ref(v___y_4581_);
lean_dec_ref(v_as_4577_);
lean_dec_ref(v_a_4575_);
lean_dec_ref(v___x_4574_);
return v_res_4588_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(lean_object* v___y_4589_, lean_object* v_args_4590_, lean_object* v___x_4591_, lean_object* v_overlaps_4592_, lean_object* v_a_4593_, lean_object* v_fst_4594_, lean_object* v_a_4595_, lean_object* v___x_4596_, lean_object* v___x_4597_, lean_object* v___x_4598_, lean_object* v___x_4599_, lean_object* v_altVars_4600_, uint8_t v___x_4601_, uint8_t v___x_4602_, lean_object* v_a_4603_, lean_object* v___x_4604_, lean_object* v___x_4605_, lean_object* v___x_4606_, lean_object* v___x_4607_, lean_object* v___x_4608_, lean_object* v___x_4609_, lean_object* v___x_4610_, lean_object* v_matchDeclName_4611_, lean_object* v___x_4612_, lean_object* v___x_4613_, lean_object* v___x_4614_, lean_object* v_heqs_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_){
_start:
{
lean_object* v___x_4621_; lean_object* v___x_4622_; 
v___x_4621_ = l_Lean_mkAppN(v___y_4589_, v_args_4590_);
lean_inc_ref(v_heqs_4615_);
v___x_4622_ = l_Lean_Meta_Match_mkAppDiscrEqs(v___x_4621_, v_heqs_4615_, v___x_4591_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_);
if (lean_obj_tag(v___x_4622_) == 0)
{
lean_object* v_a_4623_; lean_object* v___x_4624_; size_t v_sz_4625_; size_t v___x_4626_; lean_object* v___x_4627_; 
v_a_4623_ = lean_ctor_get(v___x_4622_, 0);
lean_inc(v_a_4623_);
lean_dec_ref_known(v___x_4622_, 1);
v___x_4624_ = l_Lean_Meta_Match_Overlaps_overlapping(v_overlaps_4592_, v_a_4593_);
v_sz_4625_ = lean_array_size(v___x_4624_);
v___x_4626_ = ((size_t)0ULL);
lean_inc_ref(v___x_4597_);
v___x_4627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__1(v_fst_4594_, v_a_4595_, v___x_4596_, v___x_4624_, v_sz_4625_, v___x_4626_, v___x_4597_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_);
lean_dec_ref(v___x_4624_);
if (lean_obj_tag(v___x_4627_) == 0)
{
lean_object* v_a_4628_; lean_object* v___y_4630_; lean_object* v___y_4631_; lean_object* v___y_4632_; lean_object* v___y_4633_; lean_object* v_toCold_4740_; lean_object* v_options_4741_; uint8_t v_hasTrace_4742_; 
v_a_4628_ = lean_ctor_get(v___x_4627_, 0);
lean_inc(v_a_4628_);
lean_dec_ref_known(v___x_4627_, 1);
v_toCold_4740_ = lean_ctor_get(v___y_4618_, 0);
v_options_4741_ = lean_ctor_get(v_toCold_4740_, 2);
v_hasTrace_4742_ = lean_ctor_get_uint8(v_options_4741_, sizeof(void*)*1);
if (v_hasTrace_4742_ == 0)
{
v___y_4630_ = v___y_4616_;
v___y_4631_ = v___y_4617_;
v___y_4632_ = v___y_4618_;
v___y_4633_ = v___y_4619_;
goto v___jp_4629_;
}
else
{
lean_object* v_inheritedTraceOptions_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; uint8_t v___x_4746_; 
v_inheritedTraceOptions_4743_ = lean_ctor_get(v_toCold_4740_, 11);
v___x_4744_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_4745_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__16);
v___x_4746_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4743_, v_options_4741_, v___x_4745_);
if (v___x_4746_ == 0)
{
v___y_4630_ = v___y_4616_;
v___y_4631_ = v___y_4617_;
v___y_4632_ = v___y_4618_;
v___y_4633_ = v___y_4619_;
goto v___jp_4629_;
}
else
{
lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; 
v___x_4747_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__5);
lean_inc(v_a_4628_);
v___x_4748_ = lean_array_to_list(v_a_4628_);
v___x_4749_ = lean_box(0);
v___x_4750_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__1(v___x_4748_, v___x_4749_);
v___x_4751_ = l_Lean_MessageData_ofList(v___x_4750_);
v___x_4752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4752_, 0, v___x_4747_);
lean_ctor_set(v___x_4752_, 1, v___x_4751_);
v___x_4753_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go_spec__1(v___x_4744_, v___x_4752_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_);
if (lean_obj_tag(v___x_4753_) == 0)
{
lean_dec_ref_known(v___x_4753_, 1);
v___y_4630_ = v___y_4616_;
v___y_4631_ = v___y_4617_;
v___y_4632_ = v___y_4618_;
v___y_4633_ = v___y_4619_;
goto v___jp_4629_;
}
else
{
lean_object* v_a_4754_; lean_object* v___x_4756_; uint8_t v_isShared_4757_; uint8_t v_isSharedCheck_4761_; 
lean_dec(v_a_4628_);
lean_dec(v_a_4623_);
lean_dec_ref(v_heqs_4615_);
lean_dec(v___x_4614_);
lean_dec(v___x_4613_);
lean_dec(v___x_4612_);
lean_dec(v_matchDeclName_4611_);
lean_dec_ref(v___x_4608_);
lean_dec_ref(v___x_4607_);
lean_dec_ref(v___x_4605_);
lean_dec(v___x_4604_);
lean_dec_ref(v___x_4599_);
lean_dec(v___x_4598_);
lean_dec_ref(v___x_4597_);
lean_dec_ref(v_a_4595_);
v_a_4754_ = lean_ctor_get(v___x_4753_, 0);
v_isSharedCheck_4761_ = !lean_is_exclusive(v___x_4753_);
if (v_isSharedCheck_4761_ == 0)
{
v___x_4756_ = v___x_4753_;
v_isShared_4757_ = v_isSharedCheck_4761_;
goto v_resetjp_4755_;
}
else
{
lean_inc(v_a_4754_);
lean_dec(v___x_4753_);
v___x_4756_ = lean_box(0);
v_isShared_4757_ = v_isSharedCheck_4761_;
goto v_resetjp_4755_;
}
v_resetjp_4755_:
{
lean_object* v___x_4759_; 
if (v_isShared_4757_ == 0)
{
v___x_4759_ = v___x_4756_;
goto v_reusejp_4758_;
}
else
{
lean_object* v_reuseFailAlloc_4760_; 
v_reuseFailAlloc_4760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4760_, 0, v_a_4754_);
v___x_4759_ = v_reuseFailAlloc_4760_;
goto v_reusejp_4758_;
}
v_reusejp_4758_:
{
return v___x_4759_;
}
}
}
}
}
v___jp_4629_:
{
lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; size_t v_sz_4641_; lean_object* v___x_4642_; 
v___x_4634_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__8___redArg___lam__1___closed__3);
v___x_4635_ = l_Array_reverse___redArg(v_a_4595_);
v___x_4636_ = lean_array_get_size(v___x_4635_);
v___x_4637_ = l_Array_toSubarray___redArg(v___x_4635_, v___x_4598_, v___x_4636_);
lean_inc_ref(v___x_4599_);
v___x_4638_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__6___redArg(v___x_4599_, v___x_4597_);
v___x_4639_ = l_Array_reverse___redArg(v___x_4638_);
v___x_4640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4634_);
lean_ctor_set(v___x_4640_, 1, v___x_4637_);
v_sz_4641_ = lean_array_size(v___x_4639_);
v___x_4642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__7(v___x_4639_, v_sz_4641_, v___x_4626_, v___x_4640_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_);
lean_dec_ref(v___x_4639_);
if (lean_obj_tag(v___x_4642_) == 0)
{
lean_object* v_a_4643_; lean_object* v_fst_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4730_; 
v_a_4643_ = lean_ctor_get(v___x_4642_, 0);
lean_inc(v_a_4643_);
lean_dec_ref_known(v___x_4642_, 1);
v_fst_4644_ = lean_ctor_get(v_a_4643_, 0);
v_isSharedCheck_4730_ = !lean_is_exclusive(v_a_4643_);
if (v_isSharedCheck_4730_ == 0)
{
lean_object* v_unused_4731_; 
v_unused_4731_ = lean_ctor_get(v_a_4643_, 1);
lean_dec(v_unused_4731_);
v___x_4646_ = v_a_4643_;
v_isShared_4647_ = v_isSharedCheck_4730_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_fst_4644_);
lean_dec(v_a_4643_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4730_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v___x_4648_; lean_object* v___x_4649_; uint8_t v___x_4650_; lean_object* v___x_4651_; 
v___x_4648_ = l_Subarray_copy___redArg(v___x_4599_);
lean_inc_ref(v___x_4648_);
v___x_4649_ = l_Array_append___redArg(v___x_4648_, v_altVars_4600_);
v___x_4650_ = 1;
v___x_4651_ = l_Lean_Meta_mkForallFVars(v___x_4649_, v_fst_4644_, v___x_4601_, v___x_4602_, v___x_4602_, v___x_4650_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_);
lean_dec_ref(v___x_4649_);
if (lean_obj_tag(v___x_4651_) == 0)
{
lean_object* v_a_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; 
v_a_4652_ = lean_ctor_get(v___x_4651_, 0);
lean_inc(v_a_4652_);
lean_dec_ref_known(v___x_4651_, 1);
v___x_4653_ = l_Lean_ConstantInfo_name(v_a_4603_);
v___x_4654_ = l_Lean_mkConst(v___x_4653_, v___x_4604_);
lean_inc_ref(v___x_4605_);
v___x_4655_ = l_Subarray_copy___redArg(v___x_4605_);
v___x_4656_ = lean_mk_empty_array_with_capacity(v___x_4606_);
v___x_4657_ = lean_array_push(v___x_4656_, v___x_4607_);
v___x_4658_ = l_Array_append___redArg(v___x_4655_, v___x_4657_);
lean_dec_ref(v___x_4657_);
v___x_4659_ = l_Array_append___redArg(v___x_4658_, v___x_4648_);
lean_dec_ref(v___x_4648_);
v___x_4660_ = l_Subarray_copy___redArg(v___x_4608_);
v___x_4661_ = l_Array_append___redArg(v___x_4659_, v___x_4660_);
lean_dec_ref(v___x_4660_);
v___x_4662_ = l_Lean_mkAppN(v___x_4654_, v___x_4661_);
v___x_4663_ = l_Lean_Meta_mkHEq(v___x_4662_, v_a_4623_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_);
if (lean_obj_tag(v___x_4663_) == 0)
{
lean_object* v_a_4664_; lean_object* v___x_4665_; 
v_a_4664_ = lean_ctor_get(v___x_4663_, 0);
lean_inc(v_a_4664_);
lean_dec_ref_known(v___x_4663_, 1);
v___x_4665_ = l_Lean_mkArrowN(v_a_4628_, v_a_4664_, v___y_4632_, v___y_4633_);
lean_dec(v_a_4628_);
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_object* v_a_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; 
v_a_4666_ = lean_ctor_get(v___x_4665_, 0);
lean_inc(v_a_4666_);
lean_dec_ref_known(v___x_4665_, 1);
v___x_4667_ = l_Array_append___redArg(v___x_4661_, v_altVars_4600_);
v___x_4668_ = l_Array_append___redArg(v___x_4667_, v_heqs_4615_);
v___x_4669_ = l_Lean_Meta_mkForallFVars(v___x_4668_, v_a_4666_, v___x_4601_, v___x_4602_, v___x_4602_, v___x_4650_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_);
lean_dec_ref(v___x_4668_);
if (lean_obj_tag(v___x_4669_) == 0)
{
lean_object* v_a_4670_; lean_object* v___x_4671_; 
v_a_4670_ = lean_ctor_get(v___x_4669_, 0);
lean_inc(v_a_4670_);
lean_dec_ref_known(v___x_4669_, 1);
v___x_4671_ = l_Lean_Meta_Match_unfoldNamedPattern(v_a_4670_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_);
if (lean_obj_tag(v___x_4671_) == 0)
{
lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4729_; 
v_a_4672_ = lean_ctor_get(v___x_4671_, 0);
v_isSharedCheck_4729_ = !lean_is_exclusive(v___x_4671_);
if (v_isSharedCheck_4729_ == 0)
{
v___x_4674_ = v___x_4671_;
v_isShared_4675_ = v_isSharedCheck_4729_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v___x_4671_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4729_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v_start_4676_; lean_object* v_stop_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4727_; 
v_start_4676_ = lean_ctor_get(v___x_4605_, 1);
v_stop_4677_ = lean_ctor_get(v___x_4605_, 2);
v_isSharedCheck_4727_ = !lean_is_exclusive(v___x_4605_);
if (v_isSharedCheck_4727_ == 0)
{
lean_object* v_unused_4728_; 
v_unused_4728_ = lean_ctor_get(v___x_4605_, 0);
lean_dec(v_unused_4728_);
v___x_4679_ = v___x_4605_;
v_isShared_4680_ = v_isSharedCheck_4727_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_stop_4677_);
lean_inc(v_start_4676_);
lean_dec(v___x_4605_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4727_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; 
v___x_4681_ = lean_nat_sub(v_stop_4677_, v_start_4676_);
lean_dec(v_start_4676_);
lean_dec(v_stop_4677_);
v___x_4682_ = lean_nat_add(v___x_4681_, v___x_4606_);
lean_dec(v___x_4681_);
v___x_4683_ = lean_nat_add(v___x_4682_, v___x_4609_);
lean_dec(v___x_4682_);
v___x_4684_ = lean_nat_add(v___x_4683_, v___x_4610_);
lean_dec(v___x_4683_);
v___x_4685_ = lean_array_get_size(v_altVars_4600_);
v___x_4686_ = lean_nat_add(v___x_4684_, v___x_4685_);
lean_dec(v___x_4684_);
v___x_4687_ = lean_array_get_size(v_heqs_4615_);
lean_dec_ref(v_heqs_4615_);
lean_inc(v_a_4672_);
v___x_4688_ = l_Lean_Meta_Match_proveCondEqThm(v_matchDeclName_4611_, v_a_4672_, v___x_4686_, v___x_4687_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_);
if (lean_obj_tag(v___x_4688_) == 0)
{
lean_object* v_a_4689_; lean_object* v___x_4691_; uint8_t v_isShared_4692_; uint8_t v_isSharedCheck_4726_; 
v_a_4689_ = lean_ctor_get(v___x_4688_, 0);
v_isSharedCheck_4726_ = !lean_is_exclusive(v___x_4688_);
if (v_isSharedCheck_4726_ == 0)
{
v___x_4691_ = v___x_4688_;
v_isShared_4692_ = v_isSharedCheck_4726_;
goto v_resetjp_4690_;
}
else
{
lean_inc(v_a_4689_);
lean_dec(v___x_4688_);
v___x_4691_ = lean_box(0);
v_isShared_4692_ = v_isSharedCheck_4726_;
goto v_resetjp_4690_;
}
v_resetjp_4690_:
{
lean_object* v___x_4693_; lean_object* v_env_4694_; uint8_t v___x_4695_; 
v___x_4693_ = lean_st_ref_get(v___y_4633_);
v_env_4694_ = lean_ctor_get(v___x_4693_, 0);
lean_inc_ref(v_env_4694_);
lean_dec(v___x_4693_);
lean_inc(v___x_4612_);
v___x_4695_ = l_Lean_Environment_contains(v_env_4694_, v___x_4612_, v___x_4602_);
if (v___x_4695_ == 0)
{
lean_object* v___x_4697_; 
lean_del_object(v___x_4691_);
lean_inc(v___x_4612_);
if (v_isShared_4680_ == 0)
{
lean_ctor_set(v___x_4679_, 2, v_a_4672_);
lean_ctor_set(v___x_4679_, 1, v___x_4613_);
lean_ctor_set(v___x_4679_, 0, v___x_4612_);
v___x_4697_ = v___x_4679_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v___x_4612_);
lean_ctor_set(v_reuseFailAlloc_4722_, 1, v___x_4613_);
lean_ctor_set(v_reuseFailAlloc_4722_, 2, v_a_4672_);
v___x_4697_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
lean_object* v___x_4699_; 
if (v_isShared_4647_ == 0)
{
lean_ctor_set_tag(v___x_4646_, 1);
lean_ctor_set(v___x_4646_, 1, v___x_4614_);
lean_ctor_set(v___x_4646_, 0, v___x_4612_);
v___x_4699_ = v___x_4646_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4721_; 
v_reuseFailAlloc_4721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4721_, 0, v___x_4612_);
lean_ctor_set(v_reuseFailAlloc_4721_, 1, v___x_4614_);
v___x_4699_ = v_reuseFailAlloc_4721_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
lean_object* v___x_4700_; lean_object* v___x_4702_; 
v___x_4700_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4700_, 0, v___x_4697_);
lean_ctor_set(v___x_4700_, 1, v_a_4689_);
lean_ctor_set(v___x_4700_, 2, v___x_4699_);
if (v_isShared_4675_ == 0)
{
lean_ctor_set_tag(v___x_4674_, 2);
lean_ctor_set(v___x_4674_, 0, v___x_4700_);
v___x_4702_ = v___x_4674_;
goto v_reusejp_4701_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v___x_4700_);
v___x_4702_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4701_;
}
v_reusejp_4701_:
{
lean_object* v___x_4703_; 
v___x_4703_ = l_Lean_addDecl(v___x_4702_, v___x_4601_, v___y_4632_, v___y_4633_);
if (lean_obj_tag(v___x_4703_) == 0)
{
lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4710_; 
v_isSharedCheck_4710_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4710_ == 0)
{
lean_object* v_unused_4711_; 
v_unused_4711_ = lean_ctor_get(v___x_4703_, 0);
lean_dec(v_unused_4711_);
v___x_4705_ = v___x_4703_;
v_isShared_4706_ = v_isSharedCheck_4710_;
goto v_resetjp_4704_;
}
else
{
lean_dec(v___x_4703_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4710_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v___x_4708_; 
if (v_isShared_4706_ == 0)
{
lean_ctor_set(v___x_4705_, 0, v_a_4652_);
v___x_4708_ = v___x_4705_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4709_; 
v_reuseFailAlloc_4709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4709_, 0, v_a_4652_);
v___x_4708_ = v_reuseFailAlloc_4709_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
return v___x_4708_;
}
}
}
else
{
lean_object* v_a_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4719_; 
lean_dec(v_a_4652_);
v_a_4712_ = lean_ctor_get(v___x_4703_, 0);
v_isSharedCheck_4719_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4719_ == 0)
{
v___x_4714_ = v___x_4703_;
v_isShared_4715_ = v_isSharedCheck_4719_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_a_4712_);
lean_dec(v___x_4703_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4719_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v___x_4717_; 
if (v_isShared_4715_ == 0)
{
v___x_4717_ = v___x_4714_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4718_; 
v_reuseFailAlloc_4718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4718_, 0, v_a_4712_);
v___x_4717_ = v_reuseFailAlloc_4718_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
return v___x_4717_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4724_; 
lean_dec(v_a_4689_);
lean_del_object(v___x_4679_);
lean_del_object(v___x_4674_);
lean_dec(v_a_4672_);
lean_del_object(v___x_4646_);
lean_dec(v___x_4614_);
lean_dec(v___x_4613_);
lean_dec(v___x_4612_);
if (v_isShared_4692_ == 0)
{
lean_ctor_set(v___x_4691_, 0, v_a_4652_);
v___x_4724_ = v___x_4691_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v_a_4652_);
v___x_4724_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
return v___x_4724_;
}
}
}
}
else
{
lean_del_object(v___x_4679_);
lean_del_object(v___x_4674_);
lean_dec(v_a_4672_);
lean_dec(v_a_4652_);
lean_del_object(v___x_4646_);
lean_dec(v___x_4614_);
lean_dec(v___x_4613_);
lean_dec(v___x_4612_);
return v___x_4688_;
}
}
}
}
else
{
lean_dec(v_a_4652_);
lean_del_object(v___x_4646_);
lean_dec_ref(v_heqs_4615_);
lean_dec(v___x_4614_);
lean_dec(v___x_4613_);
lean_dec(v___x_4612_);
lean_dec(v_matchDeclName_4611_);
lean_dec_ref(v___x_4605_);
return v___x_4671_;
}
}
else
{
lean_dec(v_a_4652_);
lean_del_object(v___x_4646_);
lean_dec_ref(v_heqs_4615_);
lean_dec(v___x_4614_);
lean_dec(v___x_4613_);
lean_dec(v___x_4612_);
lean_dec(v_matchDeclName_4611_);
lean_dec_ref(v___x_4605_);
return v___x_4669_;
}
}
else
{
lean_dec_ref(v___x_4661_);
lean_dec(v_a_4652_);
lean_del_object(v___x_4646_);
lean_dec_ref(v_heqs_4615_);
lean_dec(v___x_4614_);
lean_dec(v___x_4613_);
lean_dec(v___x_4612_);
lean_dec(v_matchDeclName_4611_);
lean_dec_ref(v___x_4605_);
return v___x_4665_;
}
}
else
{
lean_dec_ref(v___x_4661_);
lean_dec(v_a_4652_);
lean_del_object(v___x_4646_);
lean_dec(v_a_4628_);
lean_dec_ref(v_heqs_4615_);
lean_dec(v___x_4614_);
lean_dec(v___x_4613_);
lean_dec(v___x_4612_);
lean_dec(v_matchDeclName_4611_);
lean_dec_ref(v___x_4605_);
return v___x_4663_;
}
}
else
{
lean_dec_ref(v___x_4648_);
lean_del_object(v___x_4646_);
lean_dec(v_a_4628_);
lean_dec(v_a_4623_);
lean_dec_ref(v_heqs_4615_);
lean_dec(v___x_4614_);
lean_dec(v___x_4613_);
lean_dec(v___x_4612_);
lean_dec(v_matchDeclName_4611_);
lean_dec_ref(v___x_4608_);
lean_dec_ref(v___x_4607_);
lean_dec_ref(v___x_4605_);
lean_dec(v___x_4604_);
return v___x_4651_;
}
}
}
else
{
lean_object* v_a_4732_; lean_object* v___x_4734_; uint8_t v_isShared_4735_; uint8_t v_isSharedCheck_4739_; 
lean_dec(v_a_4628_);
lean_dec(v_a_4623_);
lean_dec_ref(v_heqs_4615_);
lean_dec(v___x_4614_);
lean_dec(v___x_4613_);
lean_dec(v___x_4612_);
lean_dec(v_matchDeclName_4611_);
lean_dec_ref(v___x_4608_);
lean_dec_ref(v___x_4607_);
lean_dec_ref(v___x_4605_);
lean_dec(v___x_4604_);
lean_dec_ref(v___x_4599_);
v_a_4732_ = lean_ctor_get(v___x_4642_, 0);
v_isSharedCheck_4739_ = !lean_is_exclusive(v___x_4642_);
if (v_isSharedCheck_4739_ == 0)
{
v___x_4734_ = v___x_4642_;
v_isShared_4735_ = v_isSharedCheck_4739_;
goto v_resetjp_4733_;
}
else
{
lean_inc(v_a_4732_);
lean_dec(v___x_4642_);
v___x_4734_ = lean_box(0);
v_isShared_4735_ = v_isSharedCheck_4739_;
goto v_resetjp_4733_;
}
v_resetjp_4733_:
{
lean_object* v___x_4737_; 
if (v_isShared_4735_ == 0)
{
v___x_4737_ = v___x_4734_;
goto v_reusejp_4736_;
}
else
{
lean_object* v_reuseFailAlloc_4738_; 
v_reuseFailAlloc_4738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4738_, 0, v_a_4732_);
v___x_4737_ = v_reuseFailAlloc_4738_;
goto v_reusejp_4736_;
}
v_reusejp_4736_:
{
return v___x_4737_;
}
}
}
}
}
else
{
lean_object* v_a_4762_; lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4769_; 
lean_dec(v_a_4623_);
lean_dec_ref(v_heqs_4615_);
lean_dec(v___x_4614_);
lean_dec(v___x_4613_);
lean_dec(v___x_4612_);
lean_dec(v_matchDeclName_4611_);
lean_dec_ref(v___x_4608_);
lean_dec_ref(v___x_4607_);
lean_dec_ref(v___x_4605_);
lean_dec(v___x_4604_);
lean_dec_ref(v___x_4599_);
lean_dec(v___x_4598_);
lean_dec_ref(v___x_4597_);
lean_dec_ref(v_a_4595_);
v_a_4762_ = lean_ctor_get(v___x_4627_, 0);
v_isSharedCheck_4769_ = !lean_is_exclusive(v___x_4627_);
if (v_isSharedCheck_4769_ == 0)
{
v___x_4764_ = v___x_4627_;
v_isShared_4765_ = v_isSharedCheck_4769_;
goto v_resetjp_4763_;
}
else
{
lean_inc(v_a_4762_);
lean_dec(v___x_4627_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4769_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
lean_object* v___x_4767_; 
if (v_isShared_4765_ == 0)
{
v___x_4767_ = v___x_4764_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v_a_4762_);
v___x_4767_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4766_;
}
v_reusejp_4766_:
{
return v___x_4767_;
}
}
}
}
else
{
lean_dec_ref(v_heqs_4615_);
lean_dec(v___x_4614_);
lean_dec(v___x_4613_);
lean_dec(v___x_4612_);
lean_dec(v_matchDeclName_4611_);
lean_dec_ref(v___x_4608_);
lean_dec_ref(v___x_4607_);
lean_dec_ref(v___x_4605_);
lean_dec(v___x_4604_);
lean_dec_ref(v___x_4599_);
lean_dec(v___x_4598_);
lean_dec_ref(v___x_4597_);
lean_dec(v___x_4596_);
lean_dec_ref(v_a_4595_);
return v___x_4622_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___y_4770_ = _args[0];
lean_object* v_args_4771_ = _args[1];
lean_object* v___x_4772_ = _args[2];
lean_object* v_overlaps_4773_ = _args[3];
lean_object* v_a_4774_ = _args[4];
lean_object* v_fst_4775_ = _args[5];
lean_object* v_a_4776_ = _args[6];
lean_object* v___x_4777_ = _args[7];
lean_object* v___x_4778_ = _args[8];
lean_object* v___x_4779_ = _args[9];
lean_object* v___x_4780_ = _args[10];
lean_object* v_altVars_4781_ = _args[11];
lean_object* v___x_4782_ = _args[12];
lean_object* v___x_4783_ = _args[13];
lean_object* v_a_4784_ = _args[14];
lean_object* v___x_4785_ = _args[15];
lean_object* v___x_4786_ = _args[16];
lean_object* v___x_4787_ = _args[17];
lean_object* v___x_4788_ = _args[18];
lean_object* v___x_4789_ = _args[19];
lean_object* v___x_4790_ = _args[20];
lean_object* v___x_4791_ = _args[21];
lean_object* v_matchDeclName_4792_ = _args[22];
lean_object* v___x_4793_ = _args[23];
lean_object* v___x_4794_ = _args[24];
lean_object* v___x_4795_ = _args[25];
lean_object* v_heqs_4796_ = _args[26];
lean_object* v___y_4797_ = _args[27];
lean_object* v___y_4798_ = _args[28];
lean_object* v___y_4799_ = _args[29];
lean_object* v___y_4800_ = _args[30];
lean_object* v___y_4801_ = _args[31];
_start:
{
uint8_t v___x_21286__boxed_4802_; uint8_t v___x_21287__boxed_4803_; lean_object* v_res_4804_; 
v___x_21286__boxed_4802_ = lean_unbox(v___x_4782_);
v___x_21287__boxed_4803_ = lean_unbox(v___x_4783_);
v_res_4804_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1(v___y_4770_, v_args_4771_, v___x_4772_, v_overlaps_4773_, v_a_4774_, v_fst_4775_, v_a_4776_, v___x_4777_, v___x_4778_, v___x_4779_, v___x_4780_, v_altVars_4781_, v___x_21286__boxed_4802_, v___x_21287__boxed_4803_, v_a_4784_, v___x_4785_, v___x_4786_, v___x_4787_, v___x_4788_, v___x_4789_, v___x_4790_, v___x_4791_, v_matchDeclName_4792_, v___x_4793_, v___x_4794_, v___x_4795_, v_heqs_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_);
lean_dec(v___y_4800_);
lean_dec_ref(v___y_4799_);
lean_dec(v___y_4798_);
lean_dec_ref(v___y_4797_);
lean_dec(v___x_4791_);
lean_dec(v___x_4790_);
lean_dec(v___x_4787_);
lean_dec_ref(v_a_4784_);
lean_dec_ref(v_altVars_4781_);
lean_dec(v_fst_4775_);
lean_dec(v_a_4774_);
lean_dec_ref(v_overlaps_4773_);
lean_dec_ref(v_args_4771_);
return v_res_4804_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2(void){
_start:
{
lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; 
v___x_4807_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__1));
v___x_4808_ = lean_unsigned_to_nat(8u);
v___x_4809_ = lean_unsigned_to_nat(295u);
v___x_4810_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__0));
v___x_4811_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___lam__1___closed__0));
v___x_4812_ = l_mkPanicMessageWithDecl(v___x_4811_, v___x_4810_, v___x_4809_, v___x_4808_, v___x_4807_);
return v___x_4812_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(lean_object* v___f_4813_, lean_object* v___x_4814_, lean_object* v___y_4815_, lean_object* v___x_4816_, lean_object* v_overlaps_4817_, lean_object* v_a_4818_, lean_object* v_fst_4819_, lean_object* v___x_4820_, lean_object* v___x_4821_, uint8_t v___x_4822_, lean_object* v_a_4823_, lean_object* v___x_4824_, lean_object* v___x_4825_, lean_object* v___x_4826_, lean_object* v___x_4827_, lean_object* v___x_4828_, lean_object* v___x_4829_, lean_object* v_matchDeclName_4830_, lean_object* v___x_4831_, lean_object* v___x_4832_, lean_object* v___x_4833_, lean_object* v_altVars_4834_, lean_object* v_args_4835_, lean_object* v___mask_4836_, lean_object* v_altResultType_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_){
_start:
{
uint8_t v___x_4843_; lean_object* v___x_4844_; 
v___x_4843_ = 0;
v___x_4844_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__0___redArg(v_altResultType_4837_, v___f_4813_, v___x_4843_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_);
if (lean_obj_tag(v___x_4844_) == 0)
{
lean_object* v_a_4845_; lean_object* v_start_4846_; lean_object* v_stop_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; uint8_t v___x_4850_; 
v_a_4845_ = lean_ctor_get(v___x_4844_, 0);
lean_inc(v_a_4845_);
lean_dec_ref_known(v___x_4844_, 1);
v_start_4846_ = lean_ctor_get(v___x_4814_, 1);
v_stop_4847_ = lean_ctor_get(v___x_4814_, 2);
v___x_4848_ = lean_array_get_size(v_a_4845_);
v___x_4849_ = lean_nat_sub(v_stop_4847_, v_start_4846_);
v___x_4850_ = lean_nat_dec_eq(v___x_4848_, v___x_4849_);
if (v___x_4850_ == 0)
{
lean_object* v___x_4851_; lean_object* v___x_4852_; 
lean_dec(v___x_4849_);
lean_dec(v_a_4845_);
lean_dec_ref(v_args_4835_);
lean_dec_ref(v_altVars_4834_);
lean_dec(v___x_4833_);
lean_dec(v___x_4832_);
lean_dec(v___x_4831_);
lean_dec(v_matchDeclName_4830_);
lean_dec(v___x_4829_);
lean_dec_ref(v___x_4828_);
lean_dec_ref(v___x_4827_);
lean_dec(v___x_4826_);
lean_dec_ref(v___x_4825_);
lean_dec(v___x_4824_);
lean_dec_ref(v_a_4823_);
lean_dec(v___x_4821_);
lean_dec_ref(v___x_4820_);
lean_dec(v_fst_4819_);
lean_dec(v_a_4818_);
lean_dec_ref(v_overlaps_4817_);
lean_dec(v___x_4816_);
lean_dec_ref(v___y_4815_);
lean_dec_ref(v___x_4814_);
v___x_4851_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___closed__2);
v___x_4852_ = l_panic___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__2(v___x_4851_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_);
return v___x_4852_;
}
else
{
lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___f_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; 
v___x_4853_ = lean_box(v___x_4843_);
v___x_4854_ = lean_box(v___x_4822_);
lean_inc_ref(v___x_4814_);
lean_inc(v___x_4821_);
lean_inc(v_a_4845_);
v___f_4855_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__1___boxed), 32, 26);
lean_closure_set(v___f_4855_, 0, v___y_4815_);
lean_closure_set(v___f_4855_, 1, v_args_4835_);
lean_closure_set(v___f_4855_, 2, v___x_4816_);
lean_closure_set(v___f_4855_, 3, v_overlaps_4817_);
lean_closure_set(v___f_4855_, 4, v_a_4818_);
lean_closure_set(v___f_4855_, 5, v_fst_4819_);
lean_closure_set(v___f_4855_, 6, v_a_4845_);
lean_closure_set(v___f_4855_, 7, v___x_4848_);
lean_closure_set(v___f_4855_, 8, v___x_4820_);
lean_closure_set(v___f_4855_, 9, v___x_4821_);
lean_closure_set(v___f_4855_, 10, v___x_4814_);
lean_closure_set(v___f_4855_, 11, v_altVars_4834_);
lean_closure_set(v___f_4855_, 12, v___x_4853_);
lean_closure_set(v___f_4855_, 13, v___x_4854_);
lean_closure_set(v___f_4855_, 14, v_a_4823_);
lean_closure_set(v___f_4855_, 15, v___x_4824_);
lean_closure_set(v___f_4855_, 16, v___x_4825_);
lean_closure_set(v___f_4855_, 17, v___x_4826_);
lean_closure_set(v___f_4855_, 18, v___x_4827_);
lean_closure_set(v___f_4855_, 19, v___x_4828_);
lean_closure_set(v___f_4855_, 20, v___x_4849_);
lean_closure_set(v___f_4855_, 21, v___x_4829_);
lean_closure_set(v___f_4855_, 22, v_matchDeclName_4830_);
lean_closure_set(v___f_4855_, 23, v___x_4831_);
lean_closure_set(v___f_4855_, 24, v___x_4832_);
lean_closure_set(v___f_4855_, 25, v___x_4833_);
v___x_4856_ = lean_mk_empty_array_with_capacity(v___x_4821_);
v___x_4857_ = l_Array_toSubarray___redArg(v_a_4845_, v___x_4821_, v___x_4848_);
v___x_4858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4858_, 0, v___x_4856_);
lean_ctor_set(v___x_4858_, 1, v___x_4857_);
v___x_4859_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(v___x_4814_, v___x_4858_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_);
if (lean_obj_tag(v___x_4859_) == 0)
{
lean_object* v_a_4860_; lean_object* v_fst_4861_; uint8_t v___x_4862_; lean_object* v___x_4863_; 
v_a_4860_ = lean_ctor_get(v___x_4859_, 0);
lean_inc(v_a_4860_);
lean_dec_ref_known(v___x_4859_, 1);
v_fst_4861_ = lean_ctor_get(v_a_4860_, 0);
lean_inc(v_fst_4861_);
lean_dec(v_a_4860_);
v___x_4862_ = 0;
v___x_4863_ = l_Lean_Meta_withLocalDeclsDND___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__4(v_fst_4861_, v___f_4855_, v___x_4862_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_);
return v___x_4863_;
}
else
{
lean_object* v_a_4864_; lean_object* v___x_4866_; uint8_t v_isShared_4867_; uint8_t v_isSharedCheck_4871_; 
lean_dec_ref(v___f_4855_);
v_a_4864_ = lean_ctor_get(v___x_4859_, 0);
v_isSharedCheck_4871_ = !lean_is_exclusive(v___x_4859_);
if (v_isSharedCheck_4871_ == 0)
{
v___x_4866_ = v___x_4859_;
v_isShared_4867_ = v_isSharedCheck_4871_;
goto v_resetjp_4865_;
}
else
{
lean_inc(v_a_4864_);
lean_dec(v___x_4859_);
v___x_4866_ = lean_box(0);
v_isShared_4867_ = v_isSharedCheck_4871_;
goto v_resetjp_4865_;
}
v_resetjp_4865_:
{
lean_object* v___x_4869_; 
if (v_isShared_4867_ == 0)
{
v___x_4869_ = v___x_4866_;
goto v_reusejp_4868_;
}
else
{
lean_object* v_reuseFailAlloc_4870_; 
v_reuseFailAlloc_4870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4870_, 0, v_a_4864_);
v___x_4869_ = v_reuseFailAlloc_4870_;
goto v_reusejp_4868_;
}
v_reusejp_4868_:
{
return v___x_4869_;
}
}
}
}
}
else
{
lean_object* v_a_4872_; lean_object* v___x_4874_; uint8_t v_isShared_4875_; uint8_t v_isSharedCheck_4879_; 
lean_dec_ref(v_args_4835_);
lean_dec_ref(v_altVars_4834_);
lean_dec(v___x_4833_);
lean_dec(v___x_4832_);
lean_dec(v___x_4831_);
lean_dec(v_matchDeclName_4830_);
lean_dec(v___x_4829_);
lean_dec_ref(v___x_4828_);
lean_dec_ref(v___x_4827_);
lean_dec(v___x_4826_);
lean_dec_ref(v___x_4825_);
lean_dec(v___x_4824_);
lean_dec_ref(v_a_4823_);
lean_dec(v___x_4821_);
lean_dec_ref(v___x_4820_);
lean_dec(v_fst_4819_);
lean_dec(v_a_4818_);
lean_dec_ref(v_overlaps_4817_);
lean_dec(v___x_4816_);
lean_dec_ref(v___y_4815_);
lean_dec_ref(v___x_4814_);
v_a_4872_ = lean_ctor_get(v___x_4844_, 0);
v_isSharedCheck_4879_ = !lean_is_exclusive(v___x_4844_);
if (v_isSharedCheck_4879_ == 0)
{
v___x_4874_ = v___x_4844_;
v_isShared_4875_ = v_isSharedCheck_4879_;
goto v_resetjp_4873_;
}
else
{
lean_inc(v_a_4872_);
lean_dec(v___x_4844_);
v___x_4874_ = lean_box(0);
v_isShared_4875_ = v_isSharedCheck_4879_;
goto v_resetjp_4873_;
}
v_resetjp_4873_:
{
lean_object* v___x_4877_; 
if (v_isShared_4875_ == 0)
{
v___x_4877_ = v___x_4874_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v_a_4872_);
v___x_4877_ = v_reuseFailAlloc_4878_;
goto v_reusejp_4876_;
}
v_reusejp_4876_:
{
return v___x_4877_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___f_4880_ = _args[0];
lean_object* v___x_4881_ = _args[1];
lean_object* v___y_4882_ = _args[2];
lean_object* v___x_4883_ = _args[3];
lean_object* v_overlaps_4884_ = _args[4];
lean_object* v_a_4885_ = _args[5];
lean_object* v_fst_4886_ = _args[6];
lean_object* v___x_4887_ = _args[7];
lean_object* v___x_4888_ = _args[8];
lean_object* v___x_4889_ = _args[9];
lean_object* v_a_4890_ = _args[10];
lean_object* v___x_4891_ = _args[11];
lean_object* v___x_4892_ = _args[12];
lean_object* v___x_4893_ = _args[13];
lean_object* v___x_4894_ = _args[14];
lean_object* v___x_4895_ = _args[15];
lean_object* v___x_4896_ = _args[16];
lean_object* v_matchDeclName_4897_ = _args[17];
lean_object* v___x_4898_ = _args[18];
lean_object* v___x_4899_ = _args[19];
lean_object* v___x_4900_ = _args[20];
lean_object* v_altVars_4901_ = _args[21];
lean_object* v_args_4902_ = _args[22];
lean_object* v___mask_4903_ = _args[23];
lean_object* v_altResultType_4904_ = _args[24];
lean_object* v___y_4905_ = _args[25];
lean_object* v___y_4906_ = _args[26];
lean_object* v___y_4907_ = _args[27];
lean_object* v___y_4908_ = _args[28];
lean_object* v___y_4909_ = _args[29];
_start:
{
uint8_t v___x_21673__boxed_4910_; lean_object* v_res_4911_; 
v___x_21673__boxed_4910_ = lean_unbox(v___x_4889_);
v_res_4911_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2(v___f_4880_, v___x_4881_, v___y_4882_, v___x_4883_, v_overlaps_4884_, v_a_4885_, v_fst_4886_, v___x_4887_, v___x_4888_, v___x_21673__boxed_4910_, v_a_4890_, v___x_4891_, v___x_4892_, v___x_4893_, v___x_4894_, v___x_4895_, v___x_4896_, v_matchDeclName_4897_, v___x_4898_, v___x_4899_, v___x_4900_, v_altVars_4901_, v_args_4902_, v___mask_4903_, v_altResultType_4904_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_);
lean_dec(v___y_4908_);
lean_dec_ref(v___y_4907_);
lean_dec(v___y_4906_);
lean_dec_ref(v___y_4905_);
lean_dec_ref(v___mask_4903_);
return v_res_4911_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(lean_object* v_upperBound_4913_, lean_object* v_val_4914_, lean_object* v_matchDeclName_4915_, lean_object* v___x_4916_, lean_object* v___x_4917_, lean_object* v_a_4918_, lean_object* v___x_4919_, lean_object* v___x_4920_, lean_object* v___x_4921_, lean_object* v___x_4922_, lean_object* v___x_4923_, lean_object* v___x_4924_, lean_object* v_a_4925_, lean_object* v_b_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_){
_start:
{
uint8_t v___x_4932_; 
v___x_4932_ = lean_nat_dec_lt(v_a_4925_, v_upperBound_4913_);
if (v___x_4932_ == 0)
{
lean_object* v___x_4933_; 
lean_dec(v_a_4925_);
lean_dec(v___x_4924_);
lean_dec(v___x_4923_);
lean_dec_ref(v___x_4922_);
lean_dec_ref(v___x_4921_);
lean_dec_ref(v___x_4920_);
lean_dec(v___x_4919_);
lean_dec_ref(v_a_4918_);
lean_dec(v___x_4917_);
lean_dec_ref(v___x_4916_);
lean_dec(v_matchDeclName_4915_);
lean_dec_ref(v_val_4914_);
v___x_4933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4933_, 0, v_b_4926_);
return v___x_4933_;
}
else
{
lean_object* v_snd_4934_; lean_object* v_fst_4935_; lean_object* v___x_4937_; uint8_t v_isShared_4938_; uint8_t v_isSharedCheck_4999_; 
v_snd_4934_ = lean_ctor_get(v_b_4926_, 1);
v_fst_4935_ = lean_ctor_get(v_b_4926_, 0);
v_isSharedCheck_4999_ = !lean_is_exclusive(v_b_4926_);
if (v_isSharedCheck_4999_ == 0)
{
v___x_4937_ = v_b_4926_;
v_isShared_4938_ = v_isSharedCheck_4999_;
goto v_resetjp_4936_;
}
else
{
lean_inc(v_snd_4934_);
lean_inc(v_fst_4935_);
lean_dec(v_b_4926_);
v___x_4937_ = lean_box(0);
v_isShared_4938_ = v_isSharedCheck_4999_;
goto v_resetjp_4936_;
}
v_resetjp_4936_:
{
lean_object* v_fst_4939_; lean_object* v_snd_4940_; lean_object* v___x_4942_; uint8_t v_isShared_4943_; uint8_t v_isSharedCheck_4998_; 
v_fst_4939_ = lean_ctor_get(v_snd_4934_, 0);
v_snd_4940_ = lean_ctor_get(v_snd_4934_, 1);
v_isSharedCheck_4998_ = !lean_is_exclusive(v_snd_4934_);
if (v_isSharedCheck_4998_ == 0)
{
v___x_4942_ = v_snd_4934_;
v_isShared_4943_ = v_isSharedCheck_4998_;
goto v_resetjp_4941_;
}
else
{
lean_inc(v_snd_4940_);
lean_inc(v_fst_4939_);
lean_dec(v_snd_4934_);
v___x_4942_ = lean_box(0);
v_isShared_4943_ = v_isSharedCheck_4998_;
goto v_resetjp_4941_;
}
v_resetjp_4941_:
{
lean_object* v_altInfos_4944_; lean_object* v_overlaps_4945_; lean_object* v_start_4946_; lean_object* v_stop_4947_; lean_object* v___f_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___y_4960_; lean_object* v___x_4993_; uint8_t v___x_4994_; 
v_altInfos_4944_ = lean_ctor_get(v_val_4914_, 2);
v_overlaps_4945_ = lean_ctor_get(v_val_4914_, 5);
v_start_4946_ = lean_ctor_get(v___x_4922_, 1);
v_stop_4947_ = lean_ctor_get(v___x_4922_, 2);
v___f_4948_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___closed__0));
v___x_4949_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_4950_ = lean_unsigned_to_nat(0u);
v___x_4951_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_withNewAlts___redArg___closed__0));
v___x_4952_ = lean_unsigned_to_nat(1u);
v___x_4953_ = lean_box(0);
v___x_4954_ = lean_array_get_borrowed(v___x_4949_, v_altInfos_4944_, v_a_4925_);
v___x_4955_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_4915_);
v___x_4956_ = l_Lean_Name_str___override(v_matchDeclName_4915_, v___x_4955_);
lean_inc(v_snd_4940_);
v___x_4957_ = lean_name_append_index_after(v___x_4956_, v_snd_4940_);
lean_inc(v___x_4957_);
v___x_4958_ = lean_array_push(v_fst_4935_, v___x_4957_);
v___x_4993_ = lean_nat_sub(v_stop_4947_, v_start_4946_);
v___x_4994_ = lean_nat_dec_lt(v_a_4925_, v___x_4993_);
lean_dec(v___x_4993_);
if (v___x_4994_ == 0)
{
lean_object* v___x_4995_; lean_object* v___x_4996_; 
v___x_4995_ = l_Lean_instInhabitedExpr;
v___x_4996_ = l_outOfBounds___redArg(v___x_4995_);
v___y_4960_ = v___x_4996_;
goto v___jp_4959_;
}
else
{
lean_object* v___x_4997_; 
v___x_4997_ = l_Subarray_get___redArg(v___x_4922_, v_a_4925_);
v___y_4960_ = v___x_4997_;
goto v___jp_4959_;
}
v___jp_4959_:
{
lean_object* v___x_4961_; lean_object* v___f_4962_; lean_object* v___x_4963_; 
v___x_4961_ = lean_box(v___x_4932_);
lean_inc(v___x_4924_);
lean_inc(v_matchDeclName_4915_);
lean_inc(v___x_4923_);
lean_inc_ref(v___x_4922_);
lean_inc_ref(v___x_4921_);
lean_inc_ref(v___x_4920_);
lean_inc(v___x_4919_);
lean_inc_ref(v_a_4918_);
lean_inc(v_fst_4939_);
lean_inc(v_a_4925_);
lean_inc_ref(v_overlaps_4945_);
lean_inc(v___x_4917_);
lean_inc_ref(v___y_4960_);
lean_inc_ref(v___x_4916_);
v___f_4962_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg___lam__2___boxed), 30, 21);
lean_closure_set(v___f_4962_, 0, v___f_4948_);
lean_closure_set(v___f_4962_, 1, v___x_4916_);
lean_closure_set(v___f_4962_, 2, v___y_4960_);
lean_closure_set(v___f_4962_, 3, v___x_4917_);
lean_closure_set(v___f_4962_, 4, v_overlaps_4945_);
lean_closure_set(v___f_4962_, 5, v_a_4925_);
lean_closure_set(v___f_4962_, 6, v_fst_4939_);
lean_closure_set(v___f_4962_, 7, v___x_4951_);
lean_closure_set(v___f_4962_, 8, v___x_4950_);
lean_closure_set(v___f_4962_, 9, v___x_4961_);
lean_closure_set(v___f_4962_, 10, v_a_4918_);
lean_closure_set(v___f_4962_, 11, v___x_4919_);
lean_closure_set(v___f_4962_, 12, v___x_4920_);
lean_closure_set(v___f_4962_, 13, v___x_4952_);
lean_closure_set(v___f_4962_, 14, v___x_4921_);
lean_closure_set(v___f_4962_, 15, v___x_4922_);
lean_closure_set(v___f_4962_, 16, v___x_4923_);
lean_closure_set(v___f_4962_, 17, v_matchDeclName_4915_);
lean_closure_set(v___f_4962_, 18, v___x_4957_);
lean_closure_set(v___f_4962_, 19, v___x_4924_);
lean_closure_set(v___f_4962_, 20, v___x_4953_);
lean_inc(v___y_4930_);
lean_inc_ref(v___y_4929_);
lean_inc(v___y_4928_);
lean_inc_ref(v___y_4927_);
v___x_4963_ = lean_infer_type(v___y_4960_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_);
if (lean_obj_tag(v___x_4963_) == 0)
{
lean_object* v_a_4964_; lean_object* v___x_4965_; 
v_a_4964_ = lean_ctor_get(v___x_4963_, 0);
lean_inc(v_a_4964_);
lean_dec_ref_known(v___x_4963_, 1);
lean_inc(v___x_4954_);
v___x_4965_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_a_4964_, v___x_4954_, v___f_4962_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_);
if (lean_obj_tag(v___x_4965_) == 0)
{
lean_object* v_a_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4970_; 
v_a_4966_ = lean_ctor_get(v___x_4965_, 0);
lean_inc(v_a_4966_);
lean_dec_ref_known(v___x_4965_, 1);
v___x_4967_ = lean_array_push(v_fst_4939_, v_a_4966_);
v___x_4968_ = lean_nat_add(v_snd_4940_, v___x_4952_);
lean_dec(v_snd_4940_);
if (v_isShared_4943_ == 0)
{
lean_ctor_set(v___x_4942_, 1, v___x_4968_);
lean_ctor_set(v___x_4942_, 0, v___x_4967_);
v___x_4970_ = v___x_4942_;
goto v_reusejp_4969_;
}
else
{
lean_object* v_reuseFailAlloc_4976_; 
v_reuseFailAlloc_4976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4976_, 0, v___x_4967_);
lean_ctor_set(v_reuseFailAlloc_4976_, 1, v___x_4968_);
v___x_4970_ = v_reuseFailAlloc_4976_;
goto v_reusejp_4969_;
}
v_reusejp_4969_:
{
lean_object* v___x_4972_; 
if (v_isShared_4938_ == 0)
{
lean_ctor_set(v___x_4937_, 1, v___x_4970_);
lean_ctor_set(v___x_4937_, 0, v___x_4958_);
v___x_4972_ = v___x_4937_;
goto v_reusejp_4971_;
}
else
{
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v___x_4958_);
lean_ctor_set(v_reuseFailAlloc_4975_, 1, v___x_4970_);
v___x_4972_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4971_;
}
v_reusejp_4971_:
{
lean_object* v___x_4973_; 
v___x_4973_ = lean_nat_add(v_a_4925_, v___x_4952_);
lean_dec(v_a_4925_);
v_a_4925_ = v___x_4973_;
v_b_4926_ = v___x_4972_;
goto _start;
}
}
}
else
{
lean_object* v_a_4977_; lean_object* v___x_4979_; uint8_t v_isShared_4980_; uint8_t v_isSharedCheck_4984_; 
lean_dec_ref(v___x_4958_);
lean_del_object(v___x_4942_);
lean_dec(v_snd_4940_);
lean_dec(v_fst_4939_);
lean_del_object(v___x_4937_);
lean_dec(v_a_4925_);
lean_dec(v___x_4924_);
lean_dec(v___x_4923_);
lean_dec_ref(v___x_4922_);
lean_dec_ref(v___x_4921_);
lean_dec_ref(v___x_4920_);
lean_dec(v___x_4919_);
lean_dec_ref(v_a_4918_);
lean_dec(v___x_4917_);
lean_dec_ref(v___x_4916_);
lean_dec(v_matchDeclName_4915_);
lean_dec_ref(v_val_4914_);
v_a_4977_ = lean_ctor_get(v___x_4965_, 0);
v_isSharedCheck_4984_ = !lean_is_exclusive(v___x_4965_);
if (v_isSharedCheck_4984_ == 0)
{
v___x_4979_ = v___x_4965_;
v_isShared_4980_ = v_isSharedCheck_4984_;
goto v_resetjp_4978_;
}
else
{
lean_inc(v_a_4977_);
lean_dec(v___x_4965_);
v___x_4979_ = lean_box(0);
v_isShared_4980_ = v_isSharedCheck_4984_;
goto v_resetjp_4978_;
}
v_resetjp_4978_:
{
lean_object* v___x_4982_; 
if (v_isShared_4980_ == 0)
{
v___x_4982_ = v___x_4979_;
goto v_reusejp_4981_;
}
else
{
lean_object* v_reuseFailAlloc_4983_; 
v_reuseFailAlloc_4983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4983_, 0, v_a_4977_);
v___x_4982_ = v_reuseFailAlloc_4983_;
goto v_reusejp_4981_;
}
v_reusejp_4981_:
{
return v___x_4982_;
}
}
}
}
else
{
lean_object* v_a_4985_; lean_object* v___x_4987_; uint8_t v_isShared_4988_; uint8_t v_isSharedCheck_4992_; 
lean_dec_ref(v___f_4962_);
lean_dec_ref(v___x_4958_);
lean_del_object(v___x_4942_);
lean_dec(v_snd_4940_);
lean_dec(v_fst_4939_);
lean_del_object(v___x_4937_);
lean_dec(v_a_4925_);
lean_dec(v___x_4924_);
lean_dec(v___x_4923_);
lean_dec_ref(v___x_4922_);
lean_dec_ref(v___x_4921_);
lean_dec_ref(v___x_4920_);
lean_dec(v___x_4919_);
lean_dec_ref(v_a_4918_);
lean_dec(v___x_4917_);
lean_dec_ref(v___x_4916_);
lean_dec(v_matchDeclName_4915_);
lean_dec_ref(v_val_4914_);
v_a_4985_ = lean_ctor_get(v___x_4963_, 0);
v_isSharedCheck_4992_ = !lean_is_exclusive(v___x_4963_);
if (v_isSharedCheck_4992_ == 0)
{
v___x_4987_ = v___x_4963_;
v_isShared_4988_ = v_isSharedCheck_4992_;
goto v_resetjp_4986_;
}
else
{
lean_inc(v_a_4985_);
lean_dec(v___x_4963_);
v___x_4987_ = lean_box(0);
v_isShared_4988_ = v_isSharedCheck_4992_;
goto v_resetjp_4986_;
}
v_resetjp_4986_:
{
lean_object* v___x_4990_; 
if (v_isShared_4988_ == 0)
{
v___x_4990_ = v___x_4987_;
goto v_reusejp_4989_;
}
else
{
lean_object* v_reuseFailAlloc_4991_; 
v_reuseFailAlloc_4991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4991_, 0, v_a_4985_);
v___x_4990_ = v_reuseFailAlloc_4991_;
goto v_reusejp_4989_;
}
v_reusejp_4989_:
{
return v___x_4990_;
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
lean_object* v_upperBound_5000_ = _args[0];
lean_object* v_val_5001_ = _args[1];
lean_object* v_matchDeclName_5002_ = _args[2];
lean_object* v___x_5003_ = _args[3];
lean_object* v___x_5004_ = _args[4];
lean_object* v_a_5005_ = _args[5];
lean_object* v___x_5006_ = _args[6];
lean_object* v___x_5007_ = _args[7];
lean_object* v___x_5008_ = _args[8];
lean_object* v___x_5009_ = _args[9];
lean_object* v___x_5010_ = _args[10];
lean_object* v___x_5011_ = _args[11];
lean_object* v_a_5012_ = _args[12];
lean_object* v_b_5013_ = _args[13];
lean_object* v___y_5014_ = _args[14];
lean_object* v___y_5015_ = _args[15];
lean_object* v___y_5016_ = _args[16];
lean_object* v___y_5017_ = _args[17];
lean_object* v___y_5018_ = _args[18];
_start:
{
lean_object* v_res_5019_; 
v_res_5019_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5000_, v_val_5001_, v_matchDeclName_5002_, v___x_5003_, v___x_5004_, v_a_5005_, v___x_5006_, v___x_5007_, v___x_5008_, v___x_5009_, v___x_5010_, v___x_5011_, v_a_5012_, v_b_5013_, v___y_5014_, v___y_5015_, v___y_5016_, v___y_5017_);
lean_dec(v___y_5017_);
lean_dec_ref(v___y_5016_);
lean_dec(v___y_5015_);
lean_dec_ref(v___y_5014_);
lean_dec(v_upperBound_5000_);
return v_res_5019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(lean_object* v_val_5026_, lean_object* v___x_5027_, lean_object* v_matchDeclName_5028_, lean_object* v___x_5029_, lean_object* v_a_5030_, lean_object* v___x_5031_, lean_object* v___x_5032_, lean_object* v_xs_5033_, lean_object* v___matchResultType_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_, lean_object* v___y_5037_, lean_object* v___y_5038_){
_start:
{
lean_object* v_numParams_5040_; lean_object* v_numDiscrs_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v_lower_5047_; lean_object* v_upper_5048_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; uint8_t v___x_5079_; 
v_numParams_5040_ = lean_ctor_get(v_val_5026_, 0);
v_numDiscrs_5041_ = lean_ctor_get(v_val_5026_, 1);
v___x_5042_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_5040_);
lean_inc_ref(v_xs_5033_);
v___x_5043_ = l_Array_toSubarray___redArg(v_xs_5033_, v___x_5042_, v_numParams_5040_);
v___x_5044_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_5026_);
v___x_5045_ = lean_array_get(v___x_5027_, v_xs_5033_, v___x_5044_);
lean_dec(v___x_5044_);
v___x_5076_ = lean_array_get_size(v_xs_5033_);
v___x_5077_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5026_);
v___x_5078_ = lean_nat_sub(v___x_5076_, v___x_5077_);
lean_dec(v___x_5077_);
v___x_5079_ = lean_nat_dec_le(v___x_5078_, v___x_5042_);
if (v___x_5079_ == 0)
{
v_lower_5047_ = v___x_5078_;
v_upper_5048_ = v___x_5076_;
goto v___jp_5046_;
}
else
{
lean_dec(v___x_5078_);
v_lower_5047_ = v___x_5042_;
v_upper_5048_ = v___x_5076_;
goto v___jp_5046_;
}
v___jp_5046_:
{
lean_object* v___x_5049_; lean_object* v_start_5050_; lean_object* v_stop_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; 
lean_inc_ref(v_xs_5033_);
v___x_5049_ = l_Array_toSubarray___redArg(v_xs_5033_, v_lower_5047_, v_upper_5048_);
v_start_5050_ = lean_ctor_get(v___x_5049_, 1);
lean_inc(v_start_5050_);
v_stop_5051_ = lean_ctor_get(v___x_5049_, 2);
lean_inc(v_stop_5051_);
v___x_5052_ = lean_unsigned_to_nat(1u);
v___x_5053_ = lean_nat_add(v_numParams_5040_, v___x_5052_);
v___x_5054_ = lean_nat_add(v___x_5053_, v_numDiscrs_5041_);
v___x_5055_ = lean_nat_sub(v_stop_5051_, v_start_5050_);
lean_dec(v_start_5050_);
lean_dec(v_stop_5051_);
v___x_5056_ = l_Array_toSubarray___redArg(v_xs_5033_, v___x_5053_, v___x_5054_);
v___x_5057_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___closed__1));
lean_inc(v___x_5055_);
v___x_5058_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v___x_5055_, v_val_5026_, v_matchDeclName_5028_, v___x_5056_, v___x_5029_, v_a_5030_, v___x_5031_, v___x_5043_, v___x_5045_, v___x_5049_, v___x_5055_, v___x_5032_, v___x_5042_, v___x_5057_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_);
lean_dec(v___x_5055_);
if (lean_obj_tag(v___x_5058_) == 0)
{
lean_object* v___x_5060_; uint8_t v_isShared_5061_; uint8_t v_isSharedCheck_5066_; 
v_isSharedCheck_5066_ = !lean_is_exclusive(v___x_5058_);
if (v_isSharedCheck_5066_ == 0)
{
lean_object* v_unused_5067_; 
v_unused_5067_ = lean_ctor_get(v___x_5058_, 0);
lean_dec(v_unused_5067_);
v___x_5060_ = v___x_5058_;
v_isShared_5061_ = v_isSharedCheck_5066_;
goto v_resetjp_5059_;
}
else
{
lean_dec(v___x_5058_);
v___x_5060_ = lean_box(0);
v_isShared_5061_ = v_isSharedCheck_5066_;
goto v_resetjp_5059_;
}
v_resetjp_5059_:
{
lean_object* v___x_5062_; lean_object* v___x_5064_; 
v___x_5062_ = lean_box(0);
if (v_isShared_5061_ == 0)
{
lean_ctor_set(v___x_5060_, 0, v___x_5062_);
v___x_5064_ = v___x_5060_;
goto v_reusejp_5063_;
}
else
{
lean_object* v_reuseFailAlloc_5065_; 
v_reuseFailAlloc_5065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5065_, 0, v___x_5062_);
v___x_5064_ = v_reuseFailAlloc_5065_;
goto v_reusejp_5063_;
}
v_reusejp_5063_:
{
return v___x_5064_;
}
}
}
else
{
lean_object* v_a_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5075_; 
v_a_5068_ = lean_ctor_get(v___x_5058_, 0);
v_isSharedCheck_5075_ = !lean_is_exclusive(v___x_5058_);
if (v_isSharedCheck_5075_ == 0)
{
v___x_5070_ = v___x_5058_;
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
else
{
lean_inc(v_a_5068_);
lean_dec(v___x_5058_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
lean_object* v___x_5073_; 
if (v_isShared_5071_ == 0)
{
v___x_5073_ = v___x_5070_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5074_; 
v_reuseFailAlloc_5074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5074_, 0, v_a_5068_);
v___x_5073_ = v_reuseFailAlloc_5074_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
return v___x_5073_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed(lean_object* v_val_5080_, lean_object* v___x_5081_, lean_object* v_matchDeclName_5082_, lean_object* v___x_5083_, lean_object* v_a_5084_, lean_object* v___x_5085_, lean_object* v___x_5086_, lean_object* v_xs_5087_, lean_object* v___matchResultType_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_){
_start:
{
lean_object* v_res_5094_; 
v_res_5094_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1(v_val_5080_, v___x_5081_, v_matchDeclName_5082_, v___x_5083_, v_a_5084_, v___x_5085_, v___x_5086_, v_xs_5087_, v___matchResultType_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_);
lean_dec(v___y_5092_);
lean_dec_ref(v___y_5091_);
lean_dec(v___y_5090_);
lean_dec_ref(v___y_5089_);
lean_dec_ref(v___matchResultType_5088_);
lean_dec_ref(v___x_5081_);
return v_res_5094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(lean_object* v_matchDeclName_5095_, lean_object* v_a_5096_, lean_object* v_a_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_){
_start:
{
uint8_t v_trackZetaDelta_5101_; lean_object* v_zetaDeltaSet_5102_; lean_object* v_lctx_5103_; lean_object* v_localInstances_5104_; lean_object* v_defEqCtx_x3f_5105_; lean_object* v_synthPendingDepth_5106_; lean_object* v_customCanUnfoldPredicate_x3f_5107_; uint8_t v_univApprox_5108_; uint8_t v_inTypeClassResolution_5109_; uint8_t v_cacheInferType_5110_; lean_object* v___x_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5154_; 
v_trackZetaDelta_5101_ = lean_ctor_get_uint8(v_a_5096_, sizeof(void*)*7);
v_zetaDeltaSet_5102_ = lean_ctor_get(v_a_5096_, 1);
lean_inc(v_zetaDeltaSet_5102_);
v_lctx_5103_ = lean_ctor_get(v_a_5096_, 2);
lean_inc_ref(v_lctx_5103_);
v_localInstances_5104_ = lean_ctor_get(v_a_5096_, 3);
lean_inc_ref(v_localInstances_5104_);
v_defEqCtx_x3f_5105_ = lean_ctor_get(v_a_5096_, 4);
lean_inc(v_defEqCtx_x3f_5105_);
v_synthPendingDepth_5106_ = lean_ctor_get(v_a_5096_, 5);
lean_inc(v_synthPendingDepth_5106_);
v_customCanUnfoldPredicate_x3f_5107_ = lean_ctor_get(v_a_5096_, 6);
lean_inc(v_customCanUnfoldPredicate_x3f_5107_);
v_univApprox_5108_ = lean_ctor_get_uint8(v_a_5096_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_5109_ = lean_ctor_get_uint8(v_a_5096_, sizeof(void*)*7 + 2);
v_cacheInferType_5110_ = lean_ctor_get_uint8(v_a_5096_, sizeof(void*)*7 + 3);
v___x_5111_ = l_Lean_Meta_Context_config(v_a_5096_);
v_isSharedCheck_5154_ = !lean_is_exclusive(v_a_5096_);
if (v_isSharedCheck_5154_ == 0)
{
lean_object* v_unused_5155_; lean_object* v_unused_5156_; lean_object* v_unused_5157_; lean_object* v_unused_5158_; lean_object* v_unused_5159_; lean_object* v_unused_5160_; lean_object* v_unused_5161_; 
v_unused_5155_ = lean_ctor_get(v_a_5096_, 6);
lean_dec(v_unused_5155_);
v_unused_5156_ = lean_ctor_get(v_a_5096_, 5);
lean_dec(v_unused_5156_);
v_unused_5157_ = lean_ctor_get(v_a_5096_, 4);
lean_dec(v_unused_5157_);
v_unused_5158_ = lean_ctor_get(v_a_5096_, 3);
lean_dec(v_unused_5158_);
v_unused_5159_ = lean_ctor_get(v_a_5096_, 2);
lean_dec(v_unused_5159_);
v_unused_5160_ = lean_ctor_get(v_a_5096_, 1);
lean_dec(v_unused_5160_);
v_unused_5161_ = lean_ctor_get(v_a_5096_, 0);
lean_dec(v_unused_5161_);
v___x_5113_ = v_a_5096_;
v_isShared_5114_ = v_isSharedCheck_5154_;
goto v_resetjp_5112_;
}
else
{
lean_dec(v_a_5096_);
v___x_5113_ = lean_box(0);
v_isShared_5114_ = v_isSharedCheck_5154_;
goto v_resetjp_5112_;
}
v_resetjp_5112_:
{
lean_object* v___x_5115_; uint64_t v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5120_; 
v___x_5115_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5111_);
v___x_5116_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5115_);
v___x_5117_ = l_Lean_instInhabitedExpr;
v___x_5118_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5118_, 0, v___x_5115_);
lean_ctor_set_uint64(v___x_5118_, sizeof(void*)*1, v___x_5116_);
lean_inc(v_customCanUnfoldPredicate_x3f_5107_);
lean_inc(v_synthPendingDepth_5106_);
lean_inc(v_defEqCtx_x3f_5105_);
lean_inc_ref(v_localInstances_5104_);
lean_inc_ref(v_lctx_5103_);
lean_inc(v_zetaDeltaSet_5102_);
if (v_isShared_5114_ == 0)
{
lean_ctor_set(v___x_5113_, 0, v___x_5118_);
v___x_5120_ = v___x_5113_;
goto v_reusejp_5119_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v___x_5118_);
lean_ctor_set(v_reuseFailAlloc_5153_, 1, v_zetaDeltaSet_5102_);
lean_ctor_set(v_reuseFailAlloc_5153_, 2, v_lctx_5103_);
lean_ctor_set(v_reuseFailAlloc_5153_, 3, v_localInstances_5104_);
lean_ctor_set(v_reuseFailAlloc_5153_, 4, v_defEqCtx_x3f_5105_);
lean_ctor_set(v_reuseFailAlloc_5153_, 5, v_synthPendingDepth_5106_);
lean_ctor_set(v_reuseFailAlloc_5153_, 6, v_customCanUnfoldPredicate_x3f_5107_);
lean_ctor_set_uint8(v_reuseFailAlloc_5153_, sizeof(void*)*7, v_trackZetaDelta_5101_);
lean_ctor_set_uint8(v_reuseFailAlloc_5153_, sizeof(void*)*7 + 1, v_univApprox_5108_);
lean_ctor_set_uint8(v_reuseFailAlloc_5153_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5109_);
lean_ctor_set_uint8(v_reuseFailAlloc_5153_, sizeof(void*)*7 + 3, v_cacheInferType_5110_);
v___x_5120_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5119_;
}
v_reusejp_5119_:
{
lean_object* v___x_5121_; lean_object* v___x_5122_; uint64_t v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; 
v___x_5121_ = l_Lean_Meta_Context_config(v___x_5120_);
lean_dec_ref(v___x_5120_);
v___x_5122_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__0(v___x_5121_);
v___x_5123_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5122_);
v___x_5124_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5124_, 0, v___x_5122_);
lean_ctor_set_uint64(v___x_5124_, sizeof(void*)*1, v___x_5123_);
v___x_5125_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5125_, 0, v___x_5124_);
lean_ctor_set(v___x_5125_, 1, v_zetaDeltaSet_5102_);
lean_ctor_set(v___x_5125_, 2, v_lctx_5103_);
lean_ctor_set(v___x_5125_, 3, v_localInstances_5104_);
lean_ctor_set(v___x_5125_, 4, v_defEqCtx_x3f_5105_);
lean_ctor_set(v___x_5125_, 5, v_synthPendingDepth_5106_);
lean_ctor_set(v___x_5125_, 6, v_customCanUnfoldPredicate_x3f_5107_);
lean_ctor_set_uint8(v___x_5125_, sizeof(void*)*7, v_trackZetaDelta_5101_);
lean_ctor_set_uint8(v___x_5125_, sizeof(void*)*7 + 1, v_univApprox_5108_);
lean_ctor_set_uint8(v___x_5125_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5109_);
lean_ctor_set_uint8(v___x_5125_, sizeof(void*)*7 + 3, v_cacheInferType_5110_);
lean_inc(v_matchDeclName_5095_);
v___x_5126_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0(v_matchDeclName_5095_, v___x_5125_, v_a_5097_, v_a_5098_, v_a_5099_);
if (lean_obj_tag(v___x_5126_) == 0)
{
lean_object* v_a_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v_a_5132_; 
v_a_5127_ = lean_ctor_get(v___x_5126_, 0);
lean_inc(v_a_5127_);
lean_dec_ref_known(v___x_5126_, 1);
v___x_5128_ = l_Lean_ConstantInfo_levelParams(v_a_5127_);
v___x_5129_ = lean_box(0);
lean_inc(v___x_5128_);
v___x_5130_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__1(v___x_5128_, v___x_5129_);
lean_inc(v_matchDeclName_5095_);
v___x_5131_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_matchDeclName_5095_, v_a_5099_);
v_a_5132_ = lean_ctor_get(v___x_5131_, 0);
lean_inc(v_a_5132_);
lean_dec_ref(v___x_5131_);
if (lean_obj_tag(v_a_5132_) == 1)
{
lean_object* v_val_5133_; lean_object* v___x_5134_; lean_object* v___f_5135_; lean_object* v___x_5136_; uint8_t v___x_5137_; lean_object* v___x_5138_; 
v_val_5133_ = lean_ctor_get(v_a_5132_, 0);
lean_inc(v_val_5133_);
lean_dec_ref_known(v_a_5132_, 1);
v___x_5134_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_5133_);
lean_inc(v_a_5127_);
v___f_5135_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___lam__1___boxed), 14, 7);
lean_closure_set(v___f_5135_, 0, v_val_5133_);
lean_closure_set(v___f_5135_, 1, v___x_5117_);
lean_closure_set(v___f_5135_, 2, v_matchDeclName_5095_);
lean_closure_set(v___f_5135_, 3, v___x_5134_);
lean_closure_set(v___f_5135_, 4, v_a_5127_);
lean_closure_set(v___f_5135_, 5, v___x_5130_);
lean_closure_set(v___f_5135_, 6, v___x_5128_);
v___x_5136_ = l_Lean_ConstantInfo_type(v_a_5127_);
lean_dec(v_a_5127_);
v___x_5137_ = 0;
v___x_5138_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__9___redArg(v___x_5136_, v___f_5135_, v___x_5137_, v___x_5137_, v___x_5125_, v_a_5097_, v_a_5098_, v_a_5099_);
lean_dec_ref_known(v___x_5125_, 7);
return v___x_5138_;
}
else
{
lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; 
lean_dec(v_a_5132_);
lean_dec(v___x_5130_);
lean_dec(v___x_5128_);
lean_dec(v_a_5127_);
v___x_5139_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5140_ = l_Lean_MessageData_ofName(v_matchDeclName_5095_);
v___x_5141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5141_, 0, v___x_5139_);
lean_ctor_set(v___x_5141_, 1, v___x_5140_);
v___x_5142_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5143_, 0, v___x_5141_);
lean_ctor_set(v___x_5143_, 1, v___x_5142_);
v___x_5144_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5143_, v___x_5125_, v_a_5097_, v_a_5098_, v_a_5099_);
lean_dec_ref_known(v___x_5125_, 7);
return v___x_5144_;
}
}
else
{
lean_object* v_a_5145_; lean_object* v___x_5147_; uint8_t v_isShared_5148_; uint8_t v_isSharedCheck_5152_; 
lean_dec_ref_known(v___x_5125_, 7);
lean_dec(v_matchDeclName_5095_);
v_a_5145_ = lean_ctor_get(v___x_5126_, 0);
v_isSharedCheck_5152_ = !lean_is_exclusive(v___x_5126_);
if (v_isSharedCheck_5152_ == 0)
{
v___x_5147_ = v___x_5126_;
v_isShared_5148_ = v_isSharedCheck_5152_;
goto v_resetjp_5146_;
}
else
{
lean_inc(v_a_5145_);
lean_dec(v___x_5126_);
v___x_5147_ = lean_box(0);
v_isShared_5148_ = v_isSharedCheck_5152_;
goto v_resetjp_5146_;
}
v_resetjp_5146_:
{
lean_object* v___x_5150_; 
if (v_isShared_5148_ == 0)
{
v___x_5150_ = v___x_5147_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5151_; 
v_reuseFailAlloc_5151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5151_, 0, v_a_5145_);
v___x_5150_ = v_reuseFailAlloc_5151_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
return v___x_5150_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed(lean_object* v_matchDeclName_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_){
_start:
{
lean_object* v_res_5168_; 
v_res_5168_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go(v_matchDeclName_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_);
lean_dec(v_a_5166_);
lean_dec_ref(v_a_5165_);
lean_dec(v_a_5164_);
return v_res_5168_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(lean_object* v_inst_5169_, lean_object* v_R_5170_, lean_object* v_a_5171_, lean_object* v_b_5172_, lean_object* v_c_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_){
_start:
{
lean_object* v___x_5179_; 
v___x_5179_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___redArg(v_a_5171_, v_b_5172_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_);
return v___x_5179_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3___boxed(lean_object* v_inst_5180_, lean_object* v_R_5181_, lean_object* v_a_5182_, lean_object* v_b_5183_, lean_object* v_c_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_){
_start:
{
lean_object* v_res_5190_; 
v_res_5190_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__3(v_inst_5180_, v_R_5181_, v_a_5182_, v_b_5183_, v_c_5184_, v___y_5185_, v___y_5186_, v___y_5187_, v___y_5188_);
lean_dec(v___y_5188_);
lean_dec_ref(v___y_5187_);
lean_dec(v___y_5186_);
lean_dec_ref(v___y_5185_);
return v_res_5190_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(lean_object* v_upperBound_5191_, lean_object* v_val_5192_, lean_object* v_matchDeclName_5193_, lean_object* v___x_5194_, lean_object* v___x_5195_, lean_object* v_a_5196_, lean_object* v___x_5197_, lean_object* v___x_5198_, lean_object* v___x_5199_, lean_object* v___x_5200_, lean_object* v___x_5201_, lean_object* v___x_5202_, lean_object* v_inst_5203_, lean_object* v_R_5204_, lean_object* v_a_5205_, lean_object* v_b_5206_, lean_object* v_c_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_){
_start:
{
lean_object* v___x_5213_; 
v___x_5213_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___redArg(v_upperBound_5191_, v_val_5192_, v_matchDeclName_5193_, v___x_5194_, v___x_5195_, v_a_5196_, v___x_5197_, v___x_5198_, v___x_5199_, v___x_5200_, v___x_5201_, v___x_5202_, v_a_5205_, v_b_5206_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_);
return v___x_5213_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5___boxed(lean_object** _args){
lean_object* v_upperBound_5214_ = _args[0];
lean_object* v_val_5215_ = _args[1];
lean_object* v_matchDeclName_5216_ = _args[2];
lean_object* v___x_5217_ = _args[3];
lean_object* v___x_5218_ = _args[4];
lean_object* v_a_5219_ = _args[5];
lean_object* v___x_5220_ = _args[6];
lean_object* v___x_5221_ = _args[7];
lean_object* v___x_5222_ = _args[8];
lean_object* v___x_5223_ = _args[9];
lean_object* v___x_5224_ = _args[10];
lean_object* v___x_5225_ = _args[11];
lean_object* v_inst_5226_ = _args[12];
lean_object* v_R_5227_ = _args[13];
lean_object* v_a_5228_ = _args[14];
lean_object* v_b_5229_ = _args[15];
lean_object* v_c_5230_ = _args[16];
lean_object* v___y_5231_ = _args[17];
lean_object* v___y_5232_ = _args[18];
lean_object* v___y_5233_ = _args[19];
lean_object* v___y_5234_ = _args[20];
lean_object* v___y_5235_ = _args[21];
_start:
{
lean_object* v_res_5236_; 
v_res_5236_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go_spec__5(v_upperBound_5214_, v_val_5215_, v_matchDeclName_5216_, v___x_5217_, v___x_5218_, v_a_5219_, v___x_5220_, v___x_5221_, v___x_5222_, v___x_5223_, v___x_5224_, v___x_5225_, v_inst_5226_, v_R_5227_, v_a_5228_, v_b_5229_, v_c_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_);
lean_dec(v___y_5234_);
lean_dec_ref(v___y_5233_);
lean_dec(v___y_5232_);
lean_dec_ref(v___y_5231_);
lean_dec(v_upperBound_5214_);
return v_res_5236_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(lean_object* v_upperBound_5237_, lean_object* v_matchDeclName_5238_, lean_object* v_a_5239_, lean_object* v_b_5240_){
_start:
{
uint8_t v___x_5242_; 
v___x_5242_ = lean_nat_dec_lt(v_a_5239_, v_upperBound_5237_);
if (v___x_5242_ == 0)
{
lean_object* v___x_5243_; 
lean_dec(v_a_5239_);
lean_dec(v_matchDeclName_5238_);
v___x_5243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5243_, 0, v_b_5240_);
return v___x_5243_;
}
else
{
lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; 
v___x_5244_ = l_Lean_Meta_Match_congrEqnThmSuffixBase;
lean_inc(v_matchDeclName_5238_);
v___x_5245_ = l_Lean_Name_str___override(v_matchDeclName_5238_, v___x_5244_);
v___x_5246_ = lean_unsigned_to_nat(1u);
v___x_5247_ = lean_nat_add(v_a_5239_, v___x_5246_);
lean_dec(v_a_5239_);
lean_inc(v___x_5247_);
v___x_5248_ = lean_name_append_index_after(v___x_5245_, v___x_5247_);
v___x_5249_ = lean_array_push(v_b_5240_, v___x_5248_);
v_a_5239_ = v___x_5247_;
v_b_5240_ = v___x_5249_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg___boxed(lean_object* v_upperBound_5251_, lean_object* v_matchDeclName_5252_, lean_object* v_a_5253_, lean_object* v_b_5254_, lean_object* v___y_5255_){
_start:
{
lean_object* v_res_5256_; 
v_res_5256_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5251_, v_matchDeclName_5252_, v_a_5253_, v_b_5254_);
lean_dec(v_upperBound_5251_);
return v_res_5256_;
}
}
LEAN_EXPORT lean_object* lean_get_congr_match_equations_for(lean_object* v_matchDeclName_5257_, lean_object* v_a_5258_, lean_object* v_a_5259_, lean_object* v_a_5260_, lean_object* v_a_5261_){
_start:
{
lean_object* v___x_5263_; lean_object* v_firstEqnName_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; 
v___x_5263_ = l_Lean_Meta_Match_congrEqn1ThmSuffix;
lean_inc_n(v_matchDeclName_5257_, 3);
v_firstEqnName_5264_ = l_Lean_Name_str___override(v_matchDeclName_5257_, v___x_5263_);
v___x_5265_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_genMatchCongrEqnsImpl_go___boxed), 6, 1);
lean_closure_set(v___x_5265_, 0, v_matchDeclName_5257_);
v___x_5266_ = l_Lean_Meta_realizeConst(v_matchDeclName_5257_, v_firstEqnName_5264_, v___x_5265_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_);
if (lean_obj_tag(v___x_5266_) == 0)
{
lean_object* v___x_5267_; lean_object* v_a_5268_; 
lean_dec_ref_known(v___x_5266_, 1);
lean_inc(v_matchDeclName_5257_);
v___x_5267_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__2___redArg(v_matchDeclName_5257_, v_a_5261_);
v_a_5268_ = lean_ctor_get(v___x_5267_, 0);
lean_inc(v_a_5268_);
lean_dec_ref(v___x_5267_);
if (lean_obj_tag(v_a_5268_) == 1)
{
lean_object* v_val_5269_; lean_object* v___x_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; 
lean_dec(v_a_5261_);
lean_dec_ref(v_a_5260_);
lean_dec(v_a_5259_);
lean_dec_ref(v_a_5258_);
v_val_5269_ = lean_ctor_get(v_a_5268_, 0);
lean_inc(v_val_5269_);
lean_dec_ref_known(v_a_5268_, 1);
v___x_5270_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_5269_);
lean_dec(v_val_5269_);
v___x_5271_ = lean_unsigned_to_nat(0u);
v___x_5272_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__8));
v___x_5273_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v___x_5270_, v_matchDeclName_5257_, v___x_5271_, v___x_5272_);
lean_dec(v___x_5270_);
return v___x_5273_;
}
else
{
lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; 
lean_dec(v_a_5268_);
v___x_5274_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go_spec__0_spec__0_spec__4___redArg___closed__3);
v___x_5275_ = l_Lean_MessageData_ofName(v_matchDeclName_5257_);
v___x_5276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5276_, 0, v___x_5274_);
lean_ctor_set(v___x_5276_, 1, v___x_5275_);
v___x_5277_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1_once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_getEquationsForImpl_go___closed__1);
v___x_5278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5278_, 0, v___x_5276_);
lean_ctor_set(v___x_5278_, 1, v___x_5277_);
v___x_5279_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_mkAppDiscrEqs_go_spec__2___redArg(v___x_5278_, v_a_5258_, v_a_5259_, v_a_5260_, v_a_5261_);
lean_dec(v_a_5261_);
lean_dec_ref(v_a_5260_);
lean_dec(v_a_5259_);
lean_dec_ref(v_a_5258_);
return v___x_5279_;
}
}
else
{
lean_object* v_a_5280_; lean_object* v___x_5282_; uint8_t v_isShared_5283_; uint8_t v_isSharedCheck_5287_; 
lean_dec(v_a_5261_);
lean_dec_ref(v_a_5260_);
lean_dec(v_a_5259_);
lean_dec_ref(v_a_5258_);
lean_dec(v_matchDeclName_5257_);
v_a_5280_ = lean_ctor_get(v___x_5266_, 0);
v_isSharedCheck_5287_ = !lean_is_exclusive(v___x_5266_);
if (v_isSharedCheck_5287_ == 0)
{
v___x_5282_ = v___x_5266_;
v_isShared_5283_ = v_isSharedCheck_5287_;
goto v_resetjp_5281_;
}
else
{
lean_inc(v_a_5280_);
lean_dec(v___x_5266_);
v___x_5282_ = lean_box(0);
v_isShared_5283_ = v_isSharedCheck_5287_;
goto v_resetjp_5281_;
}
v_resetjp_5281_:
{
lean_object* v___x_5285_; 
if (v_isShared_5283_ == 0)
{
v___x_5285_ = v___x_5282_;
goto v_reusejp_5284_;
}
else
{
lean_object* v_reuseFailAlloc_5286_; 
v_reuseFailAlloc_5286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5286_, 0, v_a_5280_);
v___x_5285_ = v_reuseFailAlloc_5286_;
goto v_reusejp_5284_;
}
v_reusejp_5284_:
{
return v___x_5285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_genMatchCongrEqnsImpl___boxed(lean_object* v_matchDeclName_5288_, lean_object* v_a_5289_, lean_object* v_a_5290_, lean_object* v_a_5291_, lean_object* v_a_5292_, lean_object* v_a_5293_){
_start:
{
lean_object* v_res_5294_; 
v_res_5294_ = lean_get_congr_match_equations_for(v_matchDeclName_5288_, v_a_5289_, v_a_5290_, v_a_5291_, v_a_5292_);
return v_res_5294_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(lean_object* v_upperBound_5295_, lean_object* v_matchDeclName_5296_, lean_object* v_inst_5297_, lean_object* v_R_5298_, lean_object* v_a_5299_, lean_object* v_b_5300_, lean_object* v_c_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_){
_start:
{
lean_object* v___x_5307_; 
v___x_5307_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___redArg(v_upperBound_5295_, v_matchDeclName_5296_, v_a_5299_, v_b_5300_);
return v___x_5307_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0___boxed(lean_object* v_upperBound_5308_, lean_object* v_matchDeclName_5309_, lean_object* v_inst_5310_, lean_object* v_R_5311_, lean_object* v_a_5312_, lean_object* v_b_5313_, lean_object* v_c_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_){
_start:
{
lean_object* v_res_5320_; 
v_res_5320_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Match_genMatchCongrEqnsImpl_spec__0(v_upperBound_5308_, v_matchDeclName_5309_, v_inst_5310_, v_R_5311_, v_a_5312_, v_b_5313_, v_c_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_);
lean_dec(v___y_5318_);
lean_dec_ref(v___y_5317_);
lean_dec(v___y_5316_);
lean_dec_ref(v___y_5315_);
lean_dec(v_upperBound_5308_);
return v_res_5320_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; 
v___x_5371_ = lean_unsigned_to_nat(3248161880u);
v___x_5372_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__19_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5373_ = l_Lean_Name_num___override(v___x_5372_, v___x_5371_);
return v___x_5373_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; 
v___x_5375_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__21_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5376_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__20_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5377_ = l_Lean_Name_str___override(v___x_5376_, v___x_5375_);
return v___x_5377_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; 
v___x_5379_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__23_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_));
v___x_5380_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__22_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5381_ = l_Lean_Name_str___override(v___x_5380_, v___x_5379_);
return v___x_5381_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; 
v___x_5382_ = lean_unsigned_to_nat(2u);
v___x_5383_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__24_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5384_ = l_Lean_Name_num___override(v___x_5383_, v___x_5382_);
return v___x_5384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5386_; uint8_t v___x_5387_; lean_object* v___x_5388_; lean_object* v___x_5389_; 
v___x_5386_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_proveCondEqThm_go___closed__13));
v___x_5387_ = 0;
v___x_5388_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__25_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_);
v___x_5389_ = l_Lean_registerTraceClass(v___x_5386_, v___x_5387_, v___x_5388_);
return v___x_5389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2____boxed(lean_object* v_a_5390_){
_start:
{
lean_object* v_res_5391_; 
v_res_5391_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3248161880____hygCtx___hyg_2_();
return v_res_5391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(lean_object* v_env_5392_, lean_object* v_n_5393_){
_start:
{
if (lean_obj_tag(v_n_5393_) == 1)
{
lean_object* v_pre_5394_; lean_object* v_str_5395_; uint8_t v___y_5397_; uint8_t v___x_5403_; 
v_pre_5394_ = lean_ctor_get(v_n_5393_, 0);
lean_inc(v_pre_5394_);
v_str_5395_ = lean_ctor_get(v_n_5393_, 1);
lean_inc_ref_n(v_str_5395_, 2);
lean_dec_ref_known(v_n_5393_, 2);
v___x_5403_ = l_Lean_Meta_isEqnReservedNameSuffix(v_str_5395_);
if (v___x_5403_ == 0)
{
lean_object* v___x_5404_; uint8_t v___x_5405_; 
v___x_5404_ = ((lean_object*)(l_Lean_Meta_Match_getEquationsForImpl___closed__0));
v___x_5405_ = lean_string_dec_eq(v_str_5395_, v___x_5404_);
lean_dec_ref(v_str_5395_);
v___y_5397_ = v___x_5405_;
goto v___jp_5396_;
}
else
{
lean_dec_ref(v_str_5395_);
v___y_5397_ = v___x_5403_;
goto v___jp_5396_;
}
v___jp_5396_:
{
if (v___y_5397_ == 0)
{
lean_object* v___x_5398_; 
lean_dec(v_pre_5394_);
lean_dec_ref(v_env_5392_);
v___x_5398_ = lean_box(0);
return v___x_5398_;
}
else
{
lean_object* v___x_5399_; 
v___x_5399_ = l_Lean_privateToUserName_x3f(v_pre_5394_);
if (lean_obj_tag(v___x_5399_) == 0)
{
lean_dec_ref(v_env_5392_);
return v___x_5399_;
}
else
{
lean_object* v_val_5400_; uint8_t v___x_5401_; 
v_val_5400_ = lean_ctor_get(v___x_5399_, 0);
lean_inc(v_val_5400_);
v___x_5401_ = l_Lean_Meta_isMatcherCore(v_env_5392_, v_val_5400_);
if (v___x_5401_ == 0)
{
lean_object* v___x_5402_; 
lean_dec_ref_known(v___x_5399_, 1);
v___x_5402_ = lean_box(0);
return v___x_5402_;
}
else
{
return v___x_5399_;
}
}
}
}
}
else
{
lean_object* v___x_5406_; 
lean_dec(v_n_5393_);
lean_dec_ref(v_env_5392_);
v___x_5406_ = lean_box(0);
return v___x_5406_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(lean_object* v_x1_5407_, lean_object* v_x2_5408_){
_start:
{
lean_object* v___x_5409_; 
v___x_5409_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_x1_5407_, v_x2_5408_);
if (lean_obj_tag(v___x_5409_) == 0)
{
uint8_t v___x_5410_; 
v___x_5410_ = 0;
return v___x_5410_;
}
else
{
uint8_t v___x_5411_; 
lean_dec_ref_known(v___x_5409_, 1);
v___x_5411_ = 1;
return v___x_5411_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_x1_5412_, lean_object* v_x2_5413_){
_start:
{
uint8_t v_res_5414_; lean_object* v_r_5415_; 
v_res_5414_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(v_x1_5412_, v_x2_5413_);
v_r_5415_ = lean_box(v_res_5414_);
return v_r_5415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5418_; lean_object* v___x_5419_; 
v___f_5418_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_));
v___x_5419_ = l_Lean_registerReservedNamePredicate(v___f_5418_);
return v___x_5419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2____boxed(lean_object* v_a_5420_){
_start:
{
lean_object* v_res_5421_; 
v_res_5421_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_1597551399____hygCtx___hyg_2_();
return v_res_5421_;
}
}
static uint64_t _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5428_; uint64_t v___x_5429_; 
v___x_5428_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5429_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5428_);
return v___x_5429_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; 
v___x_5430_ = lean_uint64_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__1_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5431_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5432_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5432_, 0, v___x_5431_);
lean_ctor_set_uint64(v___x_5432_, sizeof(void*)*1, v___x_5430_);
return v___x_5432_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; 
v___x_5435_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5436_ = lean_unsigned_to_nat(0u);
v___x_5437_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_5437_, 0, v___x_5436_);
lean_ctor_set(v___x_5437_, 1, v___x_5436_);
lean_ctor_set(v___x_5437_, 2, v___x_5436_);
lean_ctor_set(v___x_5437_, 3, v___x_5436_);
lean_ctor_set(v___x_5437_, 4, v___x_5435_);
lean_ctor_set(v___x_5437_, 5, v___x_5435_);
lean_ctor_set(v___x_5437_, 6, v___x_5435_);
lean_ctor_set(v___x_5437_, 7, v___x_5435_);
lean_ctor_set(v___x_5437_, 8, v___x_5435_);
lean_ctor_set(v___x_5437_, 9, v___x_5435_);
lean_ctor_set(v___x_5437_, 10, v___x_5435_);
return v___x_5437_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5438_; lean_object* v___x_5439_; 
v___x_5438_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5439_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5439_, 0, v___x_5438_);
lean_ctor_set(v___x_5439_, 1, v___x_5438_);
lean_ctor_set(v___x_5439_, 2, v___x_5438_);
lean_ctor_set(v___x_5439_, 3, v___x_5438_);
lean_ctor_set(v___x_5439_, 4, v___x_5438_);
lean_ctor_set(v___x_5439_, 5, v___x_5438_);
return v___x_5439_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5440_; lean_object* v___x_5441_; 
v___x_5440_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__1, &l_Lean_Meta_Match_proveCondEqThm___closed__1_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__1);
v___x_5441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5441_, 0, v___x_5440_);
lean_ctor_set(v___x_5441_, 1, v___x_5440_);
lean_ctor_set(v___x_5441_, 2, v___x_5440_);
lean_ctor_set(v___x_5441_, 3, v___x_5440_);
lean_ctor_set(v___x_5441_, 4, v___x_5440_);
return v___x_5441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(lean_object* v___x_5442_, lean_object* v_name_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_){
_start:
{
lean_object* v___x_5447_; lean_object* v_env_5448_; lean_object* v___x_5449_; 
v___x_5447_ = lean_st_ref_get(v___y_5445_);
v_env_5448_ = lean_ctor_get(v___x_5447_, 0);
lean_inc_ref(v_env_5448_);
lean_dec(v___x_5447_);
v___x_5449_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchEqName_x3f(v_env_5448_, v_name_5443_);
if (lean_obj_tag(v___x_5449_) == 1)
{
lean_object* v_val_5450_; uint8_t v___x_5451_; uint8_t v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; lean_object* v___x_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; 
v_val_5450_ = lean_ctor_get(v___x_5449_, 0);
lean_inc(v_val_5450_);
lean_dec_ref_known(v___x_5449_, 1);
v___x_5451_ = 0;
v___x_5452_ = 1;
v___x_5453_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5454_ = lean_unsigned_to_nat(0u);
v___x_5455_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5456_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5457_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5458_ = lean_box(0);
lean_inc(v___x_5442_);
v___x_5459_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5459_, 0, v___x_5453_);
lean_ctor_set(v___x_5459_, 1, v___x_5442_);
lean_ctor_set(v___x_5459_, 2, v___x_5456_);
lean_ctor_set(v___x_5459_, 3, v___x_5457_);
lean_ctor_set(v___x_5459_, 4, v___x_5458_);
lean_ctor_set(v___x_5459_, 5, v___x_5454_);
lean_ctor_set(v___x_5459_, 6, v___x_5458_);
lean_ctor_set_uint8(v___x_5459_, sizeof(void*)*7, v___x_5451_);
lean_ctor_set_uint8(v___x_5459_, sizeof(void*)*7 + 1, v___x_5451_);
lean_ctor_set_uint8(v___x_5459_, sizeof(void*)*7 + 2, v___x_5451_);
lean_ctor_set_uint8(v___x_5459_, sizeof(void*)*7 + 3, v___x_5452_);
v___x_5460_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5461_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5462_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5463_, 0, v___x_5460_);
lean_ctor_set(v___x_5463_, 1, v___x_5461_);
lean_ctor_set(v___x_5463_, 2, v___x_5442_);
lean_ctor_set(v___x_5463_, 3, v___x_5455_);
lean_ctor_set(v___x_5463_, 4, v___x_5462_);
v___x_5464_ = lean_st_mk_ref(v___x_5463_);
lean_inc(v___y_5445_);
lean_inc_ref(v___y_5444_);
lean_inc(v___x_5464_);
v___x_5465_ = lean_get_match_equations_for(v_val_5450_, v___x_5459_, v___x_5464_, v___y_5444_, v___y_5445_);
if (lean_obj_tag(v___x_5465_) == 0)
{
lean_object* v___x_5467_; uint8_t v_isShared_5468_; uint8_t v_isSharedCheck_5474_; 
v_isSharedCheck_5474_ = !lean_is_exclusive(v___x_5465_);
if (v_isSharedCheck_5474_ == 0)
{
lean_object* v_unused_5475_; 
v_unused_5475_ = lean_ctor_get(v___x_5465_, 0);
lean_dec(v_unused_5475_);
v___x_5467_ = v___x_5465_;
v_isShared_5468_ = v_isSharedCheck_5474_;
goto v_resetjp_5466_;
}
else
{
lean_dec(v___x_5465_);
v___x_5467_ = lean_box(0);
v_isShared_5468_ = v_isSharedCheck_5474_;
goto v_resetjp_5466_;
}
v_resetjp_5466_:
{
lean_object* v___x_5469_; lean_object* v___x_5470_; lean_object* v___x_5472_; 
v___x_5469_ = lean_st_ref_get(v___x_5464_);
lean_dec(v___x_5464_);
lean_dec(v___x_5469_);
v___x_5470_ = lean_box(v___x_5452_);
if (v_isShared_5468_ == 0)
{
lean_ctor_set(v___x_5467_, 0, v___x_5470_);
v___x_5472_ = v___x_5467_;
goto v_reusejp_5471_;
}
else
{
lean_object* v_reuseFailAlloc_5473_; 
v_reuseFailAlloc_5473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5473_, 0, v___x_5470_);
v___x_5472_ = v_reuseFailAlloc_5473_;
goto v_reusejp_5471_;
}
v_reusejp_5471_:
{
return v___x_5472_;
}
}
}
else
{
lean_dec(v___x_5464_);
if (lean_obj_tag(v___x_5465_) == 0)
{
lean_object* v___x_5477_; uint8_t v_isShared_5478_; uint8_t v_isSharedCheck_5483_; 
v_isSharedCheck_5483_ = !lean_is_exclusive(v___x_5465_);
if (v_isSharedCheck_5483_ == 0)
{
lean_object* v_unused_5484_; 
v_unused_5484_ = lean_ctor_get(v___x_5465_, 0);
lean_dec(v_unused_5484_);
v___x_5477_ = v___x_5465_;
v_isShared_5478_ = v_isSharedCheck_5483_;
goto v_resetjp_5476_;
}
else
{
lean_dec(v___x_5465_);
v___x_5477_ = lean_box(0);
v_isShared_5478_ = v_isSharedCheck_5483_;
goto v_resetjp_5476_;
}
v_resetjp_5476_:
{
lean_object* v___x_5479_; lean_object* v___x_5481_; 
v___x_5479_ = lean_box(v___x_5452_);
if (v_isShared_5478_ == 0)
{
lean_ctor_set_tag(v___x_5477_, 0);
lean_ctor_set(v___x_5477_, 0, v___x_5479_);
v___x_5481_ = v___x_5477_;
goto v_reusejp_5480_;
}
else
{
lean_object* v_reuseFailAlloc_5482_; 
v_reuseFailAlloc_5482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5482_, 0, v___x_5479_);
v___x_5481_ = v_reuseFailAlloc_5482_;
goto v_reusejp_5480_;
}
v_reusejp_5480_:
{
return v___x_5481_;
}
}
}
else
{
lean_object* v_a_5485_; lean_object* v___x_5487_; uint8_t v_isShared_5488_; uint8_t v_isSharedCheck_5492_; 
v_a_5485_ = lean_ctor_get(v___x_5465_, 0);
v_isSharedCheck_5492_ = !lean_is_exclusive(v___x_5465_);
if (v_isSharedCheck_5492_ == 0)
{
v___x_5487_ = v___x_5465_;
v_isShared_5488_ = v_isSharedCheck_5492_;
goto v_resetjp_5486_;
}
else
{
lean_inc(v_a_5485_);
lean_dec(v___x_5465_);
v___x_5487_ = lean_box(0);
v_isShared_5488_ = v_isSharedCheck_5492_;
goto v_resetjp_5486_;
}
v_resetjp_5486_:
{
lean_object* v___x_5490_; 
if (v_isShared_5488_ == 0)
{
v___x_5490_ = v___x_5487_;
goto v_reusejp_5489_;
}
else
{
lean_object* v_reuseFailAlloc_5491_; 
v_reuseFailAlloc_5491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5491_, 0, v_a_5485_);
v___x_5490_ = v_reuseFailAlloc_5491_;
goto v_reusejp_5489_;
}
v_reusejp_5489_:
{
return v___x_5490_;
}
}
}
}
}
else
{
uint8_t v___x_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; 
lean_dec(v___x_5449_);
lean_dec(v___x_5442_);
v___x_5493_ = 0;
v___x_5494_ = lean_box(v___x_5493_);
v___x_5495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5495_, 0, v___x_5494_);
return v___x_5495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v___x_5496_, lean_object* v_name_5497_, lean_object* v___y_5498_, lean_object* v___y_5499_, lean_object* v___y_5500_){
_start:
{
lean_object* v_res_5501_; 
v_res_5501_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(v___x_5496_, v_name_5497_, v___y_5498_, v___y_5499_);
lean_dec(v___y_5499_);
lean_dec_ref(v___y_5498_);
return v_res_5501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5505_; lean_object* v___x_5506_; 
v___f_5505_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5506_ = l_Lean_registerReservedNameAction(v___f_5505_);
return v___x_5506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2____boxed(lean_object* v_a_5507_){
_start:
{
lean_object* v_res_5508_; 
v_res_5508_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_();
return v_res_5508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(lean_object* v_env_5509_, lean_object* v_n_5510_){
_start:
{
if (lean_obj_tag(v_n_5510_) == 1)
{
lean_object* v_pre_5511_; lean_object* v_str_5512_; uint8_t v___x_5513_; 
v_pre_5511_ = lean_ctor_get(v_n_5510_, 0);
lean_inc(v_pre_5511_);
v_str_5512_ = lean_ctor_get(v_n_5510_, 1);
lean_inc_ref(v_str_5512_);
lean_dec_ref_known(v_n_5510_, 2);
v___x_5513_ = l_Lean_Meta_Match_isCongrEqnReservedNameSuffix(v_str_5512_);
if (v___x_5513_ == 0)
{
lean_object* v___x_5514_; 
lean_dec(v_pre_5511_);
lean_dec_ref(v_env_5509_);
v___x_5514_ = lean_box(0);
return v___x_5514_;
}
else
{
uint8_t v___x_5515_; 
lean_inc(v_pre_5511_);
v___x_5515_ = l_Lean_Meta_isMatcherCore(v_env_5509_, v_pre_5511_);
if (v___x_5515_ == 0)
{
lean_object* v___x_5516_; 
lean_dec(v_pre_5511_);
v___x_5516_ = lean_box(0);
return v___x_5516_;
}
else
{
lean_object* v___x_5517_; 
v___x_5517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5517_, 0, v_pre_5511_);
return v___x_5517_;
}
}
}
else
{
lean_object* v___x_5518_; 
lean_dec(v_n_5510_);
lean_dec_ref(v_env_5509_);
v___x_5518_ = lean_box(0);
return v___x_5518_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(lean_object* v_x1_5519_, lean_object* v_x2_5520_){
_start:
{
lean_object* v___x_5521_; 
v___x_5521_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_x1_5519_, v_x2_5520_);
if (lean_obj_tag(v___x_5521_) == 0)
{
uint8_t v___x_5522_; 
v___x_5522_ = 0;
return v___x_5522_;
}
else
{
uint8_t v___x_5523_; 
lean_dec_ref_known(v___x_5521_, 1);
v___x_5523_ = 1;
return v___x_5523_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_x1_5524_, lean_object* v_x2_5525_){
_start:
{
uint8_t v_res_5526_; lean_object* v_r_5527_; 
v_res_5526_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(v_x1_5524_, v_x2_5525_);
v_r_5527_ = lean_box(v_res_5526_);
return v_r_5527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5530_; lean_object* v___x_5531_; 
v___f_5530_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_));
v___x_5531_ = l_Lean_registerReservedNamePredicate(v___f_5530_);
return v___x_5531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2____boxed(lean_object* v_a_5532_){
_start:
{
lean_object* v_res_5533_; 
v_res_5533_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_136844199____hygCtx___hyg_2_();
return v_res_5533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(lean_object* v___x_5534_, lean_object* v_name_5535_, lean_object* v___y_5536_, lean_object* v___y_5537_){
_start:
{
lean_object* v___x_5539_; lean_object* v_env_5540_; lean_object* v___x_5541_; 
v___x_5539_ = lean_st_ref_get(v___y_5537_);
v_env_5540_ = lean_ctor_get(v___x_5539_, 0);
lean_inc_ref(v_env_5540_);
lean_dec(v___x_5539_);
v___x_5541_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchCongrEqName_x3f(v_env_5540_, v_name_5535_);
if (lean_obj_tag(v___x_5541_) == 1)
{
lean_object* v_val_5542_; uint8_t v___x_5543_; uint8_t v___x_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; 
v_val_5542_ = lean_ctor_get(v___x_5541_, 0);
lean_inc(v_val_5542_);
lean_dec_ref_known(v___x_5541_, 1);
v___x_5543_ = 0;
v___x_5544_ = 1;
v___x_5545_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__2_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5546_ = lean_unsigned_to_nat(32u);
v___x_5547_ = lean_mk_empty_array_with_capacity(v___x_5546_);
lean_dec_ref(v___x_5547_);
v___x_5548_ = lean_unsigned_to_nat(0u);
v___x_5549_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__3, &l_Lean_Meta_Match_proveCondEqThm___closed__3_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__3);
v___x_5550_ = lean_obj_once(&l_Lean_Meta_Match_proveCondEqThm___closed__4, &l_Lean_Meta_Match_proveCondEqThm___closed__4_once, _init_l_Lean_Meta_Match_proveCondEqThm___closed__4);
v___x_5551_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__3_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_));
v___x_5552_ = lean_box(0);
lean_inc(v___x_5534_);
v___x_5553_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5553_, 0, v___x_5545_);
lean_ctor_set(v___x_5553_, 1, v___x_5534_);
lean_ctor_set(v___x_5553_, 2, v___x_5550_);
lean_ctor_set(v___x_5553_, 3, v___x_5551_);
lean_ctor_set(v___x_5553_, 4, v___x_5552_);
lean_ctor_set(v___x_5553_, 5, v___x_5548_);
lean_ctor_set(v___x_5553_, 6, v___x_5552_);
lean_ctor_set_uint8(v___x_5553_, sizeof(void*)*7, v___x_5543_);
lean_ctor_set_uint8(v___x_5553_, sizeof(void*)*7 + 1, v___x_5543_);
lean_ctor_set_uint8(v___x_5553_, sizeof(void*)*7 + 2, v___x_5543_);
lean_ctor_set_uint8(v___x_5553_, sizeof(void*)*7 + 3, v___x_5544_);
v___x_5554_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__4_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5555_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__5_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5556_ = lean_obj_once(&l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_, &l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0___closed__6_00___x40_Lean_Meta_Match_MatchEqs_3170112230____hygCtx___hyg_2_);
v___x_5557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5557_, 0, v___x_5554_);
lean_ctor_set(v___x_5557_, 1, v___x_5555_);
lean_ctor_set(v___x_5557_, 2, v___x_5534_);
lean_ctor_set(v___x_5557_, 3, v___x_5549_);
lean_ctor_set(v___x_5557_, 4, v___x_5556_);
v___x_5558_ = lean_st_mk_ref(v___x_5557_);
lean_inc(v___y_5537_);
lean_inc_ref(v___y_5536_);
lean_inc(v___x_5558_);
v___x_5559_ = lean_get_congr_match_equations_for(v_val_5542_, v___x_5553_, v___x_5558_, v___y_5536_, v___y_5537_);
if (lean_obj_tag(v___x_5559_) == 0)
{
lean_object* v___x_5561_; uint8_t v_isShared_5562_; uint8_t v_isSharedCheck_5568_; 
v_isSharedCheck_5568_ = !lean_is_exclusive(v___x_5559_);
if (v_isSharedCheck_5568_ == 0)
{
lean_object* v_unused_5569_; 
v_unused_5569_ = lean_ctor_get(v___x_5559_, 0);
lean_dec(v_unused_5569_);
v___x_5561_ = v___x_5559_;
v_isShared_5562_ = v_isSharedCheck_5568_;
goto v_resetjp_5560_;
}
else
{
lean_dec(v___x_5559_);
v___x_5561_ = lean_box(0);
v_isShared_5562_ = v_isSharedCheck_5568_;
goto v_resetjp_5560_;
}
v_resetjp_5560_:
{
lean_object* v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5566_; 
v___x_5563_ = lean_st_ref_get(v___x_5558_);
lean_dec(v___x_5558_);
lean_dec(v___x_5563_);
v___x_5564_ = lean_box(v___x_5544_);
if (v_isShared_5562_ == 0)
{
lean_ctor_set(v___x_5561_, 0, v___x_5564_);
v___x_5566_ = v___x_5561_;
goto v_reusejp_5565_;
}
else
{
lean_object* v_reuseFailAlloc_5567_; 
v_reuseFailAlloc_5567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5567_, 0, v___x_5564_);
v___x_5566_ = v_reuseFailAlloc_5567_;
goto v_reusejp_5565_;
}
v_reusejp_5565_:
{
return v___x_5566_;
}
}
}
else
{
lean_dec(v___x_5558_);
if (lean_obj_tag(v___x_5559_) == 0)
{
lean_object* v___x_5571_; uint8_t v_isShared_5572_; uint8_t v_isSharedCheck_5577_; 
v_isSharedCheck_5577_ = !lean_is_exclusive(v___x_5559_);
if (v_isSharedCheck_5577_ == 0)
{
lean_object* v_unused_5578_; 
v_unused_5578_ = lean_ctor_get(v___x_5559_, 0);
lean_dec(v_unused_5578_);
v___x_5571_ = v___x_5559_;
v_isShared_5572_ = v_isSharedCheck_5577_;
goto v_resetjp_5570_;
}
else
{
lean_dec(v___x_5559_);
v___x_5571_ = lean_box(0);
v_isShared_5572_ = v_isSharedCheck_5577_;
goto v_resetjp_5570_;
}
v_resetjp_5570_:
{
lean_object* v___x_5573_; lean_object* v___x_5575_; 
v___x_5573_ = lean_box(v___x_5544_);
if (v_isShared_5572_ == 0)
{
lean_ctor_set_tag(v___x_5571_, 0);
lean_ctor_set(v___x_5571_, 0, v___x_5573_);
v___x_5575_ = v___x_5571_;
goto v_reusejp_5574_;
}
else
{
lean_object* v_reuseFailAlloc_5576_; 
v_reuseFailAlloc_5576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5576_, 0, v___x_5573_);
v___x_5575_ = v_reuseFailAlloc_5576_;
goto v_reusejp_5574_;
}
v_reusejp_5574_:
{
return v___x_5575_;
}
}
}
else
{
lean_object* v_a_5579_; lean_object* v___x_5581_; uint8_t v_isShared_5582_; uint8_t v_isSharedCheck_5586_; 
v_a_5579_ = lean_ctor_get(v___x_5559_, 0);
v_isSharedCheck_5586_ = !lean_is_exclusive(v___x_5559_);
if (v_isSharedCheck_5586_ == 0)
{
v___x_5581_ = v___x_5559_;
v_isShared_5582_ = v_isSharedCheck_5586_;
goto v_resetjp_5580_;
}
else
{
lean_inc(v_a_5579_);
lean_dec(v___x_5559_);
v___x_5581_ = lean_box(0);
v_isShared_5582_ = v_isSharedCheck_5586_;
goto v_resetjp_5580_;
}
v_resetjp_5580_:
{
lean_object* v___x_5584_; 
if (v_isShared_5582_ == 0)
{
v___x_5584_ = v___x_5581_;
goto v_reusejp_5583_;
}
else
{
lean_object* v_reuseFailAlloc_5585_; 
v_reuseFailAlloc_5585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5585_, 0, v_a_5579_);
v___x_5584_ = v_reuseFailAlloc_5585_;
goto v_reusejp_5583_;
}
v_reusejp_5583_:
{
return v___x_5584_;
}
}
}
}
}
else
{
uint8_t v___x_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; 
lean_dec(v___x_5541_);
lean_dec(v___x_5534_);
v___x_5587_ = 0;
v___x_5588_ = lean_box(v___x_5587_);
v___x_5589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5589_, 0, v___x_5588_);
return v___x_5589_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v___x_5590_, lean_object* v_name_5591_, lean_object* v___y_5592_, lean_object* v___y_5593_, lean_object* v___y_5594_){
_start:
{
lean_object* v_res_5595_; 
v_res_5595_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___lam__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(v___x_5590_, v_name_5591_, v___y_5592_, v___y_5593_);
lean_dec(v___y_5593_);
lean_dec_ref(v___y_5592_);
return v_res_5595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_5599_; lean_object* v___x_5600_; 
v___f_5599_ = ((lean_object*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn___closed__0_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_));
v___x_5600_ = l_Lean_registerReservedNameAction(v___f_5599_);
return v___x_5600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2____boxed(lean_object* v_a_5601_){
_start:
{
lean_object* v_res_5602_; 
v_res_5602_ = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_initFn_00___x40_Lean_Meta_Match_MatchEqs_2767730534____hygCtx___hyg_2_();
return v_res_5602_;
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
